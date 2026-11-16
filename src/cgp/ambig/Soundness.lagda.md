# Soundness: the `pd-Idemp` direction and the criterion lifts

This module holds the *soundness* half of the A3 mechanism — the lemmas
whose content is "a fired criterion (or test) implies `Ambig`" — split
out of `cgp.ambig.Canonic`, which keeps the shared statements: the
similarity `≈₀` and `canonic`, the tests themselves (`pd-Idemp?`,
`A3?`, `A3-list?`), the scan correctness and the member classification
(Canonic §4.2), the generic path lifts (Canonic §5),
the state constructions (Canonic §6/§7) and the
example data of Canonic §4.1.  `cgp.ambig.Completeness`
holds the converse direction.

Section numbers are local to this module; references into the other
modules are qualified by name.  What lives here: §1
(`dup-sum→Ambig` / `Ctx-dup→Ambig`), §2 (the `a + a`
example), §3 (the continuation-pair closer) and §4
(the example records), §5 (inverting the fusion at a `+`
clause), §6 (the Ctx-dup lifts), §7–§11
(the complete `pdU`-clause inversion chain, ending in the unconditional
soundness theorem `pd-Idemp`), and §12 (the soundness
direction over the pd-states, moved from the old `Complete` module).
Names shared with `cgp.ambig.Canonic` (`pd-expr`, `sum-spine`,
`Dups-w`, `pd-alts-Dups-w-classify`, the lifts, …) are imported from
there.



```agda
{-# OPTIONS --rewriting #-}
module cgp.ambig.Soundness where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉ ; ε∉$ ; ε∈ ; ε∈?)

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU; LetterU; LeftU; RightU; PairU; ListU ; unListU ; flat ; r-∃u ; LeftU≢RightU )

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using ( Ambig ; AmbigA1 ; AmbigA2 ; Ctx ; 𝟘 ; Ctx●R ; L●Ctx ; Ctx+R ; L+Ctx ; plug ; CtxT ; CtxT-pres-flat ; CtxT-injective ; A1→Ambig ; A2→Ambig )

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; pdinstance-left ; pdinstance-right ; pdinstance-fst ; PDInstance* ; pdinstance* )

import cgp.empty.AllEmptyParseTree as AllEmpty

import cgp.posix.PartialDerivative as PosixPD

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; map ; concatMap ; length)

open import Data.List.Properties using (++-assoc ; ∷-injectiveˡ ; ∷-injectiveʳ ; length-map ; length-++ ; ∷-injective ; ++-identityʳ)

import Data.List.Relation.Unary.Any as ListAny
open ListAny using (Any; here; there)

import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)

import Data.Empty as Empty
open Empty using (⊥; ⊥-elim)

import Data.Bool.Base as Bool
open Bool using (Bool; true; false; _∨_)

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using ( ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-refl ; ≤-trans ; m≤n⇒m≤1+n )

import Data.List.Relation.Unary.All as ListAll

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym; cong₂; subst)

import Data.Product as Product
open Product using ( Σ ; Σ-syntax ; ∃-syntax ; _,_ ; _×_ )

import Data.Sum as Sum
-- (not opened: `inj₁`/`inj₂` are used as pattern variables in §3)
open Σ using (proj₁ ; proj₂)

import Data.Maybe as Maybe
open Maybe using ( Maybe ; just ; nothing )

import Relation.Nullary as Nullary
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using ( Dec; yes; no; ⌊_⌋)

import cgp.ambig.Canonic as Canonic
open Canonic using ( _≈₀_ ; ≈₀-sym ; Cast ; Cast-pres-flat ; canonic ; sum-spine ; sum-spine∷
  ; pd-expr ; pd-inj ; pd*-expr ; pd-alts ; dups-≈₀ ; pd-Idemp? ; pd-alts∈ ; pd-alts∈-inv
  ; ∈-++-inv ; ∈-++ʳ ; ∈-map⁻ ; ∈-concatMap⁻ ; dups-≈₀-dups ; Dups-w ; Dups-w-++-split
  ; Dups-w-cross ; pd-alts-Dups-w-classify ; pd-Idemp?-member-witness ; pd-a3-target
  ; pd-a3-Idemp-applied ; pd-a3-continuations ; lift-Ambig ; lift-Ctx ; pd*-inj ; pd*-Desc
  ; pd*-Ambig→Ambig ; pd*-A1→Ambig ; pd*-A2→Ambig ; crit ; crit-A3-test )
open Canonic._≈₀_ using ( ≈₀-ε ; ≈₀-$ ; ≈₀-● ; ≈₀-+ ; ≈₀-* )
open Canonic.Dups-w using ( dups-at )
```


## 1. Soundness: `Idemp` applied implies ambiguity

If a sum contains two `≈₀`-equal alternatives then the expression is
ambiguous: the same inhabitant tree (all expressions are inhabited,
`r-∃u`) embedded via `LeftU` and, transported along `≈₀`, via `RightU`
(the two parse trees the paper gets when applying `Idemp`).

```agda
dup-sum→Ambig : ∀ { l s : RE } { loc : ℕ }
  → l ≈₀ s
  → Ambig (l + s ` loc)
dup-sum→Ambig {l} {s} {loc} p =
  let u = proj₁ (r-∃u l) in
  ( LeftU {l} {s} {loc} u
  , RightU {l} {s} {loc} (Cast p u)
  , sym (Cast-pres-flat p u)
  , LeftU≢RightU u (Cast p u) )

-- the same under a hole context R[]:  A3 fires on the subterm  ⇒  r ambiguous
Ctx-dup→Ambig : ∀ ( ctx : Ctx ) { l s : RE } { loc : ℕ }
  → ( r : RE )
  → plug ctx (l + s ` loc) ≡ r
  → l ≈₀ s
  → Ambig r
Ctx-dup→Ambig ctx {l} {s} {loc} .(plug ctx (l + s ` loc)) refl p =
  let u = proj₁ (r-∃u l) in
  ( CtxT ctx (LeftU {l} {s} {loc} u)
  , CtxT ctx (RightU {l} {s} {loc} (Cast p u))
  , CtxT-pres-flat ctx (sym (Cast-pres-flat p u))
  , λ trees≡ → LeftU≢RightU u (Cast p u) (CtxT-injective ctx trees≡) )

```

## 2. The A3 example: `a + a` (missed by A1/A2, caught by Idemp)

`cgp.ambig.AmbigCheck` proves that `($ 'a' ` 1) + ($ 'a' ` 2) ` 3` is
ambiguous (`ambiguousSum`) although it satisfies neither A1 (`notA1Sum`) nor
A2 (`notA2Sum`).  Here `canonic` detects it: the canonical representative
removes the second alternative and reports that `Idemp` was applied, and
`Ctx-dup→Ambig` turns this into the ambiguity witness.

```agda
a3-target : RE
a3-target = ($ 'a' ` 1) + ($ 'a' ` 2) ` 3

-- A1 and A2 do not fire (from cgp.ambig.AmbigCheck)
a3-notA1 : ¬ AmbigA1 a3-target
a3-notA1 = AmbigCheck.notA1Sum

a3-notA2 : ¬ AmbigA2 a3-target
a3-notA2 = AmbigCheck.notA2Sum

-- computing the canonical representative removes the duplicate alternative:
a3-canonic : proj₁ (canonic a3-target) ≡ ($ 'a' ` 1)
a3-canonic = refl

-- and reports that rule Idemp was applied:
a3-Idemp-applied : proj₂ (canonic a3-target) ≡ true
a3-Idemp-applied = refl

-- soundness of the detection:
a3-ambiguous : Ambig a3-target
a3-ambiguous = Ctx-dup→Ambig 𝟘 _ refl (≈₀-$ 'a' 1 2)

-- a duplicate under a context (here R[] = [] ● b) is detected as well
a3-nested-target : RE
a3-nested-target = a3-target ● ($ 'b' ` 4) ` 5

a3-nested-Idemp-applied : proj₂ (canonic a3-nested-target) ≡ true
a3-nested-Idemp-applied = refl

a3-nested-ambiguous : Ambig a3-nested-target
a3-nested-ambiguous = Ctx-dup→Ambig (Ctx●R 𝟘 ($ 'b' ` 4) 5) _ refl (≈₀-$ 'a' 1 2)

```

## 3. Soundness: a duplicated continuation pair implies ambiguity

The two injections embed the (equal up to `≈₀`) continuations through
*different* sum branches, so the transported parse trees are distinct —
this is the paper's A3 ambiguity witness, built from the pd injections.

```agda
pd-pairs→Ambig : ∀ { l s : RE } { loc : ℕ } { c : Char }
  → ( pdi₁ : PDInstance l c )
  → ( pdi₂ : PDInstance s c )
  → pd-expr pdi₁ ≈₀ pd-expr pdi₂
  → Ambig (l + s ` loc)
pd-pairs→Ambig {l} {s} {loc} {c} (pdinstance {d₁} inj₁ ev₁) (pdinstance {d₂} inj₂ ev₂) p =
  let u = proj₁ (r-∃u d₁) in
  ( LeftU {l} {s} {loc} (inj₁ u)
  , RightU {l} {s} {loc} (inj₂ (Cast p u))
  , trans (ev₁ u) (trans (cong ( λ z → c ∷ z) (sym (Cast-pres-flat p u))) (sym (ev₂ (Cast p u))))
  , LeftU≢RightU (inj₁ u) (inj₂ (Cast p u)) )

-- the same for whole word prefixes (mimics deriv s x for a state s reached
-- after consuming w; PDInstance* is produced by pdUMany[ r , w ])
pd*-pairs→Ambig : ∀ { l s : RE } { loc : ℕ } { w : List Char }
  → ( pdi₁ : PDInstance* l w )
  → ( pdi₂ : PDInstance* s w )
  → pd*-expr pdi₁ ≈₀ pd*-expr pdi₂
  → Ambig (l + s ` loc)
pd*-pairs→Ambig {l} {s} {loc} {w} (pdinstance* {d₁} inj₁ ev₁) (pdinstance* {d₂} inj₂ ev₂) p =
  let u = proj₁ (r-∃u d₁) in
  ( LeftU {l} {s} {loc} (inj₁ u)
  , RightU {l} {s} {loc} (inj₂ (Cast p u))
  , trans (ev₁ u) (trans (cong ( λ z → w ++ z) (sym (Cast-pres-flat p u))) (sym (ev₂ (Cast p u))))
  , LeftU≢RightU (inj₁ u) (inj₂ (Cast p u)) )

```

## 4. The example pairs of the Canonic §4.1 state

The continuation-level records behind Canonic §4.1's `pd-a3-target`
(the state itself, `pd-a3-Idemp-applied` and the flattened continuations
stay with the test in `cgp.ambig.Canonic`), and the pair-level ambiguity
of that state:

```agda
-- level ε ● ($ 'c' ` 4) ` 5  and  ε ● ($ 'c' ` 7) ` 8 :
-- soundness evidence for a letter partial derivative (cf. the letter case of pdU)
letter-ev : ( c : Char ) ( loc : ℕ ) ( u : U ε )
  → proj₁ (flat (LetterU {loc} c)) ≡ c ∷ proj₁ (flat u)
letter-ev c loc EmptyU = refl

a1-inst : PDInstance ($ 'a' ` 1) 'a'
a1-inst = pdinstance {ε} {($ 'a' ` 1)} {'a'}
            ( λ u → LetterU {1} 'a')
            ( letter-ev 'a' 1)

a6-inst : PDInstance ($ 'a' ` 6) 'a'
a6-inst = pdinstance {ε} {($ 'a' ` 6)} {'a'}
            ( λ u → LetterU {6} 'a')
            ( letter-ev 'a' 6)

left-pdi : PDInstance ((( $ 'a' ` 1) + ($ 'b' ` 2) ` 3) ● ($ 'c' ` 4) ` 5) 'a'
left-pdi = pdinstance-fst {(($ 'a' ` 1) + ($ 'b' ` 2) ` 3)} {($ 'c' ` 4)} {5} {'a'}
             ( pdinstance-left {($ 'a' ` 1)} {($ 'b' ` 2)} {3} {'a'} a1-inst)

right-pdi : PDInstance (($ 'a' ` 6) ● ($ 'c' ` 7) ` 8) 'a'
right-pdi = pdinstance-fst {($ 'a' ` 6)} {($ 'c' ` 7)} {8} {'a'} a6-inst

pd-a3-ambiguous : Ambig pd-a3-target
pd-a3-ambiguous = pd-pairs→Ambig left-pdi right-pdi
                    (≈₀-● (≈₀-ε) (≈₀-$ 'c' 4 7))
```


## 5. Inverting the fusion: a crossing configuration

`fuse` (in `cgp.posix.PartialDerivative`) joins two records into one whose
continuation is a *sum* of the two continuations: `mkfuseInj` reads
`LeftU v` through the left record's map and `RightU v` through the right
record's map, so the fused record's `+`-spine is the concatenation of the
two spines.  When the pair of a fired test lies on both sides of that
node, the ambiguity needs no injectivity: each tree travels through its
own *pre-fusion* record and enters the parent sum through a different
branch, so distinctness is the node's own (`LeftU≢RightU`).  This is
§3's mechanism with the word-equal tree pair supplied as data instead
of built from an `≈₀` of the whole continuations — §3's
`pd-pairs→Ambig` is the special case where the two continuations are
themselves the pair.

A located position is a structural judgement (`_◁_`): the membership form
`p ∈ sum-spine r` cannot be case-split at a sum node — its list is a stuck
`sum-spine l ++ sum-spine s` — while `_◁_` recurses along the expression,
and `∈→◁` converts the computed membership back.  `spine-read` reads a tree
at a position without moving its word, which gives the soundness theorem
for the *located* pair, `pd-cross-positions→Ambig`.

```agda
-- (purpose): an alternative located *structurally* in the +-spine of an
--   expression — the inductive form of `∈ sum-spine`
-- (used in): `∈→◁`, `spine-read`, `spine-read-pres-flat`,
--   `pd-cross-positions→Ambig` below
-- (proof idea): the membership form cannot be case-split at a sum node
--   (`sum-spine l ++ sum-spine s` is stuck for variable `l`, `s`), so the
--   position is carried as a datatype that follows the +-structure
data _◁_ : RE → RE → Set where
  sp-node  : ( r : RE ) → r ◁ r
  sp-left  : ∀ { l s p : RE } { loc : ℕ } → l ◁ p → ( l + s ` loc ) ◁ p
  sp-right : ∀ { l s p : RE } { loc : ℕ } → s ◁ p → ( l + s ` loc ) ◁ p

-- (purpose): membership in the computed spine gives the structural position
-- (used in): converting `pd-Idemp?-member-witness` / `pd-alts∈-inv`
--   memberships into `spine-read` inputs (Canonic §6.1 configurations (a)/(b))
-- (proof idea): induction on the expression; at a sum node expose the
--   spine head with `sum-spine∷`, split the concatenation with
--   `∈-++-inv`, and transport the memberships along the head equation
∈→◁ : ( r p : RE ) → p ∈ sum-spine r → r ◁ p
∈→◁ ε p (here refl) = sp-node ε
∈→◁ ( $ c ` loc ) p (here refl) = sp-node _
∈→◁ ( l ● s ` loc ) p (here refl) = sp-node _
∈→◁ ( l * n ` loc ) p (here refl) = sp-node _
∈→◁ ( l + s ` loc ) p pos with sum-spine∷ l
...   | ( h₁ , t₁ , eq₁)
    with ∈-++-inv (h₁ ∷ t₁) (sum-spine s)
       (subst ( λ K → p ∈ K ) (cong ( λ K → K ++ sum-spine s) eq₁) pos)
...   | Sum.inj₁ pos₁ =
      sp-left (∈→◁ l p (subst ( λ K → p ∈ K ) (sym eq₁) pos₁))
...   | Sum.inj₂ pos₂ = sp-right (∈→◁ s p pos₂)

-- (purpose): reading a tree through a spine position — the tree of `r`
--   that reads the word of `u : U p` at the position `pos`
-- (used in): `pd-cross-positions→Ambig` below
-- (proof idea): recursion on `_◁_`: wrap with `LeftU`/`RightU` at the
--   sum branches, stop at the located node
spine-read : ( r p : RE ) → r ◁ p → U p → U r
spine-read r p (sp-node .r) u = u
spine-read (l + s ` loc) p (sp-left pos) u = LeftU {l} {s} {loc} (spine-read l p pos u)
spine-read (l + s ` loc) p (sp-right pos) u = RightU {l} {s} {loc} (spine-read s p pos u)

-- (purpose): entering a left sum branch does not move a word
-- (used in): `spine-read-pres-flat` below
-- (proof idea): `flat` of a branch is defined through a `with` on
--   `flat u`, so it does not reduce at a variable tree — case-split
--   `flat u` to expose the pair, then `refl`
flat∘LeftU : ∀ { l s : RE } { loc : ℕ } ( u : U l )
  → proj₁ (flat { l + s ` loc } (LeftU {l} {s} {loc} u)) ≡ proj₁ (flat {l} u)
flat∘LeftU {l} {s} {loc} u with flat u
...   | ( xs , xs∈ ) = refl

-- (purpose): entering a right sum branch does not move a word
-- (used in): `spine-read-pres-flat` below
-- (proof idea): as `flat∘LeftU`
flat∘RightU : ∀ { l s : RE } { loc : ℕ } ( u : U s )
  → proj₁ (flat { l + s ` loc } (RightU {l} {s} {loc} u)) ≡ proj₁ (flat {s} u)
flat∘RightU {l} {s} {loc} u with flat u
...   | ( xs , xs∈ ) = refl

-- (purpose): reading a position does not move the word
-- (used in): `pd-cross-positions→Ambig` below
-- (proof idea): induction on `_◁_`; `refl` at the located node,
--   `flat∘LeftU`/`flat∘RightU` to step over the sum branches (their
--   implicits are given explicitly: the goal does not determine them
--   through the stuck `flat`)
spine-read-pres-flat : ( r p : RE ) ( pos : r ◁ p ) ( u : U p )
  → proj₁ (flat {r} (spine-read r p pos u)) ≡ proj₁ (flat {p} u)
spine-read-pres-flat r p (sp-node .r) u = refl
spine-read-pres-flat (l + s ` loc) p (sp-left pos) u =
  trans (flat∘LeftU {l} {s} {loc} (spine-read l p pos u))
        (spine-read-pres-flat l p pos u)
spine-read-pres-flat (l + s ` loc) p (sp-right pos) u =
  trans (flat∘RightU {l} {s} {loc} (spine-read s p pos u))
        (spine-read-pres-flat s p pos u)

-- (purpose): the record half of the crossing case — two records whose
--   continuations hold trees with one word ⇒ the parent sum is ambiguous
-- (used in): `pd-cross-positions→Ambig` below; Canonic §6.1's configuration (a)
-- (proof idea): the two trees enter `l + s` through *different* branches,
--   so distinctness is `LeftU≢RightU` — no injectivity of the records is
--   needed; the word equation runs both records' soundness evidence
--   through one `c ∷`_ congruence
pd-fuse-cross→Ambig : ∀ { l s : RE } { loc : ℕ } { c : Char }
  → ( pdi₁ : PDInstance l c ) ( pdi₂ : PDInstance s c )
  → ( u : U (pd-expr pdi₁) ) ( v : U (pd-expr pdi₂) )
  → proj₁ (flat {pd-expr pdi₁} u) ≡ proj₁ (flat {pd-expr pdi₂} v)
  → Ambig ( l + s ` loc )
pd-fuse-cross→Ambig {l} {s} {loc} {c} (pdinstance i₁ e₁) (pdinstance i₂ e₂) u v word≡ =
    ( LeftU {l} {s} {loc} (i₁ u)
    , RightU {l} {s} {loc} (i₂ v)
    , trans (e₁ u) (trans (cong ( λ z → c ∷ z) word≡) (sym (e₂ v)))
    , LeftU≢RightU (i₁ u) (i₂ v) )

-- (purpose): the crossing case complete — records whose continuations
--   hold `≈₀`-equal alternatives at located positions ⇒ the parent sum is
--   ambiguous
-- (used in): `pd-a3-ambiguous-via-positions` below; Canonic §6.1's configuration
--   (a) reduces to this lemma plus the `pdinstance-oplus`/`map`
--   membership inversion into pre-fusion records
-- (proof idea): read the two trees at the positions (`spine-read`),
--   transport one across `≈₀` (`Cast`, word-preserving by
--   `Cast-pres-flat`), then `pd-fuse-cross→Ambig`
pd-cross-positions→Ambig : ∀ { l s : RE } { loc : ℕ } { c : Char }
  → ( pdi₁ : PDInstance l c ) ( pdi₂ : PDInstance s c )
  → ( p q : RE )
  → pd-expr pdi₁ ◁ p → pd-expr pdi₂ ◁ q
  → p ≈₀ q
  → Ambig ( l + s ` loc )
pd-cross-positions→Ambig pdi₁ pdi₂ p q pos₁ pos₂ p≈₀q =
  pd-fuse-cross→Ambig pdi₁ pdi₂
    (spine-read (pd-expr pdi₁) p pos₁ (proj₁ (r-∃u p)))
    (spine-read (pd-expr pdi₂) q pos₂ (Cast p≈₀q (proj₁ (r-∃u p))))
    (trans (spine-read-pres-flat (pd-expr pdi₁) p pos₁ (proj₁ (r-∃u p)))
       (sym (trans (spine-read-pres-flat (pd-expr pdi₂) q pos₂
                       (Cast p≈₀q (proj₁ (r-∃u p))))
                   (Cast-pres-flat p≈₀q (proj₁ (r-∃u p))))))

-- (purpose): the general located-position theorem reproduces the Canonic §4.1
--   hand-built witness (both continuations are non-sums, so each
--   position is `sp-node`)
-- (used in): the §5 prose — checks the closer subsumes the example
-- (proof idea): `pd-cross-positions→Ambig` at `left-pdi`/`right-pdi`
--   with the computed `≈₀` of the two continuations
pd-a3-ambiguous-via-positions : Ambig pd-a3-target
pd-a3-ambiguous-via-positions =
  pd-cross-positions→Ambig left-pdi right-pdi
    (pd-expr left-pdi) (pd-expr right-pdi)
    (sp-node (pd-expr left-pdi)) (sp-node (pd-expr right-pdi))
    (≈₀-● (≈₀-ε) (≈₀-$ 'c' 4 7))
```

## 6. The Ctx-dup lifts (continuing Canonic §5)

`lift-Ctx-dup→Ambig` and `pd*-Ctx-dup→Ambig` compose the generic lifts of
`cgp.ambig.Canonic` §5 with this module's §1 `Ctx-dup→Ambig`; the
A1/A2 lifts stay with the shared statement.

```agda
-- Idemp inside the state (the A3 shape) ⇒ r ambiguous
lift-Ctx-dup→Ambig : ∀ { r p : RE } { w : List Char }
  → ( inj : U p → U r )
  → ( ev : ∀ ( u : U p ) → proj₁ (flat {r} (inj u)) ≡ w ++ proj₁ (flat {p} u) )
  → ( inj-inj : ∀ ( u v : U p ) → inj u ≡ inj v → u ≡ v )
  → ( ctx : Ctx ) { l s : RE } { loc : ℕ }
  → plug ctx (l + s ` loc) ≡ p
  → l ≈₀ s
  → Ambig r
lift-Ctx-dup→Ambig {p = p} inj ev inj-inj ctx {l} {s} {loc} eq dup =
  lift-Ambig inj ev inj-inj (Ctx-dup→Ambig ctx {l} {s} {loc} p eq dup)
pd*-Ctx-dup→Ambig : ∀ { r : RE } { pref : List Char }
  → ( pdi : PDInstance* r pref )
  → ( ∀ ( u v : U (pd*-expr pdi) ) → pd*-inj pdi u ≡ pd*-inj pdi v → u ≡ v )
  → ( ctx : Ctx ) { l s : RE } { loc : ℕ }
  → plug ctx (l + s ` loc) ≡ pd*-expr pdi
  → l ≈₀ s
  → Ambig r
pd*-Ctx-dup→Ambig pdi inj-inj ctx eq dup =
  pd*-Ambig→Ambig pdi inj-inj (Ctx-dup→Ambig ctx (pd*-expr pdi) eq dup)

```
## 7. Branch location: inverting the `pdU` clauses

The classification of Canonic §4.2 speaks about `pd-alts pdis` for a plain
member list.  `pd-Idemp` instantiates it at `pdis = PosixPD.pdU[ q , c ]`,
whose clauses (in `cgp.posix.PartialDerivative`) build their lists with
`map`, `concatMap` and `pdinstance-oplus`.  This section inverts those
constructions — the membership shapes first, then the continuations the
clause maps write into the records.

```agda

-- (purpose): membership in `pdinstance-oplus` resolves to one of its
--   three shapes: an unfused left-list member, an unfused right-list
--   member, or the fusion of one member of each list
-- (used in): the branch location of a `+` clause (below), `pd-Idemp`
-- (proof idea): case on the two lists; the nil shapes read the
--   membership off the defining equations directly, the both-non-nil
--   shape inverts the `concatMap`/`map` structure
∈-oplus⁻ : ∀ { r : RE } { loc : ℕ } { c : Char }
  ( xs ys : List (PDInstance r c) ) ( w : PDInstance r c )
  → w ∈ PosixPD.pdinstance-oplus {r} {loc} {c} xs ys
  → Sum._⊎_
      (Σ[ z ∈ PDInstance r c ] ( (z ∈ xs) × (w ≡ z) ))
      (Sum._⊎_
        (Σ[ z ∈ PDInstance r c ] ( (z ∈ ys) × (w ≡ z) ))
        (Σ[ z ∈ PDInstance r c ] Σ[ z′ ∈ PDInstance r c ]
          ( (z ∈ xs) × (z′ ∈ ys)
          × (w ≡ PosixPD.fuse {r} {loc} {c} z z′) )))
∈-oplus⁻ []        ys       w w∈ = Sum.inj₂ (Sum.inj₁ ( w , ( w∈ , refl ) ))
∈-oplus⁻ (x ∷ xs)  []      w w∈ = Sum.inj₁ ( w , ( w∈ , refl ) )
∈-oplus⁻ {r} {loc} {c} (x ∷ xs)  (y ∷ ys) w w∈
  with ∈-concatMap⁻
         ( λ a → map (PosixPD.fuse {r} {loc} {c} a) (y ∷ ys) ) (x ∷ xs) w w∈
...   | ( a , a∈ , w∈ₘ ) with ∈-map⁻ (PosixPD.fuse {r} {loc} {c} a) (y ∷ ys) w w∈ₘ
...     | ( b , b∈ , eq ) = Sum.inj₂ (Sum.inj₂ ( a , b , ( a∈ , b∈ , sym eq ) ))

-- (purpose): the branch maps of a `+` clause write the continuation of
--   their argument through unchanged
-- (used in): the branch location of a `+` clause (below)
-- (proof idea): `pdinstance-left`/`pdinstance-right` keep the implicit
--   continuation of the record; both equations reduce to `refl` after
--   splitting the record
pd-expr-left : ∀ { l s : RE } { loc : ℕ } { c : Char } ( z : PDInstance l c )
  → pd-expr (pdinstance-left {l} {s} {loc} {c} z) ≡ pd-expr z
pd-expr-left (pdinstance {p} inj ev) = refl

pd-expr-right : ∀ { l s : RE } { loc : ℕ } { c : Char } ( z : PDInstance s c )
  → pd-expr (pdinstance-right {l} {s} {loc} {c} z) ≡ pd-expr z
pd-expr-right (pdinstance {p} inj ev) = refl

-- (purpose): a fused record's continuation is the sum of the two
--   pre-fusion continuations at the clause's location — this is where
--   Canonic §6.1's configuration (a) gets its inner `+` node
-- (used in): the branch location of a `+` clause (below)
-- (proof idea): read off `fuse`'s definition (`pd-expr` reads the
--   implicit continuation of the produced record)
pd-expr-fuse : ∀ { r : RE } { loc : ℕ } { c : Char }
  ( z z′ : PDInstance r c )
  → pd-expr (PosixPD.fuse {r} {loc} {c} z z′)
       ≡ pd-expr z + pd-expr z′ ` loc
pd-expr-fuse (pdinstance {pˡ} inj-l ev-l) (pdinstance {pʳ} inj-r ev-r) = refl

-- the three shapes a member of a `+` clause's list can have: an
-- unfused left-branch instance, an unfused right-branch instance, or
-- the fusion of one instance of each branch
pdU-+-shape : ( l s : RE ) ( loc : ℕ ) ( c : Char )
  → PDInstance ( l + s ` loc ) c → Set
pdU-+-shape l s loc c z =
  Sum._⊎_
    (Σ[ z₁ ∈ PDInstance l c ]
      ( (z₁ ∈ PosixPD.pdU[ l , c ])
      × (z ≡ pdinstance-left {l} {s} {loc} {c} z₁) ))
    (Sum._⊎_
      (Σ[ z₂ ∈ PDInstance s c ]
        ( (z₂ ∈ PosixPD.pdU[ s , c ])
        × (z ≡ pdinstance-right {l} {s} {loc} {c} z₂) ))
      (Σ[ pdi₁ ∈ PDInstance l c ] Σ[ pdi₂ ∈ PDInstance s c ]
        ( (pdi₁ ∈ PosixPD.pdU[ l , c ]) × (pdi₂ ∈ PosixPD.pdU[ s , c ])
        × (z ≡ PosixPD.fuse {l + s ` loc} {loc} {c}
                (pdinstance-left {l} {s} {loc} {c} pdi₁)
                (pdinstance-right {l} {s} {loc} {c} pdi₂)) )))

-- (purpose): a member of `pdU[ l + s ` loc , c ]` has one of the three
--   shapes, with the branch instances named
-- (used in): `pdU-+-location` below
-- (proof idea): `∈-oplus⁻`, then `∈-map⁻` on the branch-list
--   memberships in the unfused shapes
pdU-+-shape-of : ( l s : RE ) ( loc : ℕ ) ( c : Char )
  → ( z : PDInstance ( l + s ` loc ) c )
  → z ∈ PosixPD.pdU[ l + s ` loc , c ]
  → pdU-+-shape l s loc c z
pdU-+-shape-of l s loc c z z∈
  with ∈-oplus⁻ {l + s ` loc} {loc} {c}
         ( map (pdinstance-left {l} {s} {loc} {c}) (PosixPD.pdU[ l , c ]) )
         ( map (pdinstance-right {l} {s} {loc} {c}) (PosixPD.pdU[ s , c ]) )
         z z∈
...   | Sum.inj₁ ( z₁ , ( z₁∈ , z≡z₁ ) ) =
    let ( pdi₁ , pdi₁∈ , eq₁ ) =
          ∈-map⁻ (pdinstance-left {l} {s} {loc} {c}) (PosixPD.pdU[ l , c ])
                 z₁ z₁∈
    in  Sum.inj₁ ( pdi₁ , ( pdi₁∈ , trans z≡z₁ (sym eq₁) ) )
...   | Sum.inj₂ (Sum.inj₁ ( z₂ , ( z₂∈ , z≡z₂ ) )) =
    let ( pdi₂ , pdi₂∈ , eq₂ ) =
          ∈-map⁻ (pdinstance-right {l} {s} {loc} {c}) (PosixPD.pdU[ s , c ])
                 z₂ z₂∈
    in  Sum.inj₂ (Sum.inj₁ ( pdi₂ , ( pdi₂∈ , trans z≡z₂ (sym eq₂) ) ))
...   | Sum.inj₂ (Sum.inj₂ ( a , b , ( a∈ , b∈ , z≡ ) )) =
    let ( pdi₁ , pdi₁∈ , eq₁ ) =
          ∈-map⁻ (pdinstance-left {l} {s} {loc} {c}) (PosixPD.pdU[ l , c ])
                 a a∈
        ( pdi₂ , pdi₂∈ , eq₂ ) =
          ∈-map⁻ (pdinstance-right {l} {s} {loc} {c}) (PosixPD.pdU[ s , c ])
                 b b∈
    in  Sum.inj₂ (Sum.inj₂
          ( pdi₁ , pdi₂ , ( pdi₁∈ , pdi₂∈
                          , trans z≡ (cong₂ (PosixPD.fuse {l + s ` loc} {loc} {c})
                                            (sym eq₁) (sym eq₂))
                          ) ) )

-- (purpose): branch location of a `+` clause — a positioned pair placed
--   by Canonic §4.2's classification inside the continuation of one member of
--   the sum node `l + s ` loc` either has its occurrences on the two
--   sides of the clause (the A3 pattern: the two branch instances with
--   the alternatives at positions of their continuations — material
--   consumed by `pd-cross-positions→Ambig`), or lies inside the spine
--   of one branch instance (a subgoal on a strictly smaller expression)
-- (used in): the `pd-Idemp` composition of §11 (the `+` clause)
-- (proof idea): `pdU-+-shape-of` names the branch instances;
--   `pd-expr-fuse`/`pd-expr-left`/`pd-expr-right` unfold the member's
--   spine to `sum-spine (pd-expr pdi₁) ++ sum-spine (pd-expr pdi₂)`;
--   `Dups-w-++-split` cuts at that join.  In the crossing case the
--   pair's occurrences are recovered at their positions from the
--   `Dups-w-cross` record's equations (`∈-++ʳ` + `here`) and read as
--   `_◁_`-positions with `∈→◁`; `≈₀-sym` turns the split's positional
--   orientation `later ≈₀ earlier` into the left-to-right one
pdU-+-location : ( l s : RE ) ( loc : ℕ ) ( c : Char )
  → ( z : PDInstance ( l + s ` loc ) c )
  → z ∈ PosixPD.pdU[ l + s ` loc , c ]
  → Dups-w (sum-spine (pd-expr z))
  → Sum._⊎_
      (Σ[ pdi₁ ∈ PDInstance l c ] Σ[ pdi₂ ∈ PDInstance s c ]
        Σ[ p ∈ RE ] Σ[ q ∈ RE ]
          ( (pd-expr pdi₁ ◁ p) × (pd-expr pdi₂ ◁ q) × (p ≈₀ q) ))
      (Sum._⊎_
        (Σ[ z₁ ∈ PDInstance l c ]
          ( (z₁ ∈ PosixPD.pdU[ l , c ])
          × Dups-w (sum-spine (pd-expr z₁)) ))
        (Σ[ z₂ ∈ PDInstance s c ]
          ( (z₂ ∈ PosixPD.pdU[ s , c ])
          × Dups-w (sum-spine (pd-expr z₂)) )))
pdU-+-location l s loc c z z∈ d
  with pdU-+-shape-of l s loc c z z∈
...   | Sum.inj₁ ( z₁ , ( z₁∈ , z≡ ) ) =
        Sum.inj₂ (Sum.inj₁
          ( z₁ , ( z₁∈ , subst Dups-w
              (cong sum-spine (trans (cong ( λ w → pd-expr w ) z≡)
                                     (pd-expr-left {l} {s} {loc} {c} z₁)))
              d ) ))
...   | Sum.inj₂ (Sum.inj₁ ( z₂ , ( z₂∈ , z≡ ) )) =
        Sum.inj₂ (Sum.inj₂
          ( z₂ , ( z₂∈ , subst Dups-w
              (cong sum-spine (trans (cong ( λ w → pd-expr w ) z≡)
                                     (pd-expr-right {l} {s} {loc} {c} z₂)))
              d ) ))
...   | Sum.inj₂ (Sum.inj₂ ( pdi₁ , pdi₂ , ( pdi₁∈ , pdi₂∈ , z≡ ) ))
    with Dups-w-++-split (sum-spine (pd-expr pdi₁)) (sum-spine (pd-expr pdi₂))
           ( subst Dups-w
               (trans (trans (cong ( λ w → sum-spine (pd-expr w) ) z≡)
                             (cong sum-spine
                                (pd-expr-fuse {l + s ` loc} {loc} {c}
                                   (pdinstance-left {l} {s} {loc} {c} pdi₁)
                                   (pdinstance-right {l} {s} {loc} {c} pdi₂))))
                       (cong sum-spine
                          (trans (cong ( λ x → x + pd-expr
                                             (pdinstance-right {l} {s} {loc} {c} pdi₂)
                                        ` loc)
                                       (pd-expr-left {l} {s} {loc} {c} pdi₁))
                                 (cong ( λ y → pd-expr pdi₁ + y ` loc)
                                       (pd-expr-right {l} {s} {loc} {c} pdi₂)))))
               d)
...     | Sum.inj₁ d₁ = Sum.inj₂ (Sum.inj₁ ( pdi₁ , ( pdi₁∈ , d₁ ) ))
...     | Sum.inj₂ (Sum.inj₂ d₂) = Sum.inj₂ (Sum.inj₂ ( pdi₂ , ( pdi₂∈ , d₂ ) ))
...     | Sum.inj₂ (Sum.inj₁ ( pre , mid₁ , mid₂ , post , p , q
                             , ( xs≡ , ys≡ , q≈₀p ) )) =
            Sum.inj₁ ( pdi₁ , pdi₂ , p , q
                     , ( ∈→◁ (pd-expr pdi₁) p
                          ( subst ( λ L → p ∈ L ) (sym xs≡)
                              ( ∈-++ʳ pre (p ∷ mid₁) p (here refl) ) )
                     , ∈→◁ (pd-expr pdi₂) q
                          ( subst ( λ L → q ∈ L ) (sym ys≡)
                              ( ∈-++ʳ mid₂ (q ∷ post) q (here refl) ) )
                     , ≈₀-sym q≈₀p ) )

-- the location machinery instantiated at the Canonic §4.1 example: the pair of
-- the fired test, positioned inside the single fused member by Canonic §4.2's
-- chain, located at the target's top sum node — either its two
-- occurrences on the sides of the top `+`, or inside one branch
-- instance (the first disjunct is what happens; its consumption is the
-- existing `pd-a3-ambiguous-via-positions`)
pd-a3-branch-location :
  Sum._⊎_
    (Σ[ pdi₁ ∈ PDInstance ((($ 'a' ` 1) + ($ 'b' ` 2) ` 3) ● ($ 'c' ` 4) ` 5) 'a' ]
      Σ[ pdi₂ ∈ PDInstance (($ 'a' ` 6) ● ($ 'c' ` 7) ` 8) 'a' ]
      Σ[ p ∈ RE ] Σ[ q ∈ RE ]
        ( (pd-expr pdi₁ ◁ p) × (pd-expr pdi₂ ◁ q) × (p ≈₀ q) ))
    (Sum._⊎_
      (Σ[ z₁ ∈ PDInstance ((($ 'a' ` 1) + ($ 'b' ` 2) ` 3) ● ($ 'c' ` 4) ` 5) 'a' ]
        ( (z₁ ∈ PosixPD.pdU[ (($ 'a' ` 1) + ($ 'b' ` 2) ` 3) ● ($ 'c' ` 4) ` 5 , 'a' ])
        × Dups-w (sum-spine (pd-expr z₁)) ))
      (Σ[ z₂ ∈ PDInstance (($ 'a' ` 6) ● ($ 'c' ` 7) ` 8) 'a' ]
        ( (z₂ ∈ PosixPD.pdU[ ($ 'a' ` 6) ● ($ 'c' ` 7) ` 8 , 'a' ])
        × Dups-w (sum-spine (pd-expr z₂)) )))
-- the empty list is not a non-empty list (absurd on the index)
[]≢_∷_ : { A : Set } { x : A } { xs : List A } → [] ≡ x ∷ xs → ⊥
[]≢_∷_ ()

-- the single member of the a3 derivative list, exactly as `pdU`
-- computes it.  Naming it by evaluation keeps the smoke test's
-- membership `here refl`: a hand-built record carries its own
-- soundness evidence, which is not definitionally equal to the
-- evidence the `pdU` clause inlines
pd-a3-member : PDInstance pd-a3-target 'a'
pd-a3-member = go (PosixPD.pdU[ pd-a3-target , 'a' ]) refl
  where
    pds : List (PDInstance pd-a3-target 'a')
    pds = PosixPD.pdU[ pd-a3-target , 'a' ]
    go : ( pdis : List (PDInstance pd-a3-target 'a') )
      → pds ≡ pdis → PDInstance pd-a3-target 'a'
    go ( z ∷ _ ) eq = z
    go [] eq = ⊥-elim
      ([]≢_∷_
        (trans (sym (cong pd-alts eq)) pd-a3-continuations))

pd-a3-branch-location =
  pdU-+-location
    ((($ 'a' ` 1) + ($ 'b' ` 2) ` 3) ● ($ 'c' ` 4) ` 5)
    (( $ 'a' ` 6) ● ($ 'c' ` 7) ` 8)
    9 'a'
    pd-a3-member
    (here refl)
    (dups-≈₀-dups (pd-alts (PosixPD.pdU[ pd-a3-target , 'a' ]))
       pd-a3-Idemp-applied)
```

## 8. Lifting an ambiguity through a record's map

Configuration (b) of Canonic §6.1 closes an ambiguity *inside* the continuation
of a member record of `pdU`; reaching `Ambig q` carries that witness
through the record's own transition map `pd-inj z : U (pd-expr z) → U q`
with Canonic §5's `lift-Ambig`, which asks for that map's injectivity.  The pd
builders (`pdinstance-left/right/fst/snd`) preserve injectivity — a chain
of them composed from the leaf `$` records (whose map is a `LetterU`
embedding) is injective.  The one exception is the *fused* record's map
`mkfuseInj`: the two pre-fusion maps both land in `U r` and could
identify trees, so that link stays a gap.  It is never entered here:
configuration (a) closes through §5 at the sum node of the fused
continuation itself, and `pdU-+-location` pushes a pair *inside* a fused
member down to the unfused branch lists, so no lift ever crosses a fused
record.

```agda
-- (purpose): one link of the chain — an ambiguity of a member record's
--   continuation transfers to the record's input expression
-- (used in): `pd-Idemp` of §11 (configuration (b))
-- (proof idea): `lift-Ambig` at the record's own map, the word [ c ]
--   and the record's evidence (the record's `c ∷ _` shape is [ c ] ++ _)
lift-pdinstance : ∀ { q : RE } { c : Char } ( z : PDInstance q c )
  → ( ∀ ( u v : U (pd-expr z) )
      → pd-inj z refl u ≡ pd-inj z refl v → u ≡ v )
  → Ambig (pd-expr z) → Ambig q
lift-pdinstance {q} {c} (pdinstance {p} inj ev) inj-inj =
  lift-Ambig {r = q} {p = p} {c ∷ []} inj ev inj-inj

-- (purpose): the `+`-branch builders preserve the injectivity of a
--   record's transition map
-- (used in): the chain of Canonic §6.1 configuration (b)
-- (proof idea): the constructed maps reduce to `LeftU ∘ inj` and
--   `RightU ∘ inj`; `inv-leftU`/`inv-rightU` reflect back through the
--   constructor
pdinj-inj-left : ∀ { l s : RE } { loc : ℕ } { c : Char } ( z : PDInstance l c )
  → ( ∀ ( u v : U (pd-expr z) )
      → pd-inj z refl u ≡ pd-inj z refl v → u ≡ v )
  → ( ∀ ( u v : U (pd-expr (pdinstance-left {l} {s} {loc} {c} z)) )
      → pd-inj (pdinstance-left {l} {s} {loc} {c} z) refl u
      ≡ pd-inj (pdinstance-left {l} {s} {loc} {c} z) refl v
      → u ≡ v )
pdinj-inj-left {l} {s} {loc} {c} (pdinstance {p} inj ev) inj-inj u v eq =
  inj-inj u v (ParseTree.inv-leftU {l} {s} {loc} (inj u) (inj v) eq)

pdinj-inj-right : ∀ { l s : RE } { loc : ℕ } { c : Char } ( z : PDInstance s c )
  → ( ∀ ( u v : U (pd-expr z) )
      → pd-inj z refl u ≡ pd-inj z refl v → u ≡ v )
  → ( ∀ ( u v : U (pd-expr (pdinstance-right {l} {s} {loc} {c} z)) )
      → pd-inj (pdinstance-right {l} {s} {loc} {c} z) refl u
      ≡ pd-inj (pdinstance-right {l} {s} {loc} {c} z) refl v
      → u ≡ v )
pdinj-inj-right {l} {s} {loc} {c} (pdinstance {p} inj ev) inj-inj u v eq =
  inj-inj u v (ParseTree.inv-rightU {l} {s} {loc} (inj u) (inj v) eq)

-- (purpose): the `●`-first builder preserves map injectivity
-- (used in): the chain of Canonic §6.1 configuration (b)
-- (proof idea): the constructed map reduces to `mkinjFst inj`, which
--   rewrites at a pair tree to `PairU (inj u) v`; `inv-pairU` splits the
--   equation and the hypothesis reflects the first component
pdinj-inj-fst : ∀ { l s : RE } { loc : ℕ } { c : Char } ( z : PDInstance l c )
  → ( ∀ ( u v : U (pd-expr z) )
      → pd-inj z refl u ≡ pd-inj z refl v → u ≡ v )
  → ( ∀ ( u v : U (pd-expr (pdinstance-fst {l} {s} {loc} {c} z)) )
      → pd-inj (pdinstance-fst {l} {s} {loc} {c} z) refl u
      ≡ pd-inj (pdinstance-fst {l} {s} {loc} {c} z) refl v
      → u ≡ v )
pdinj-inj-fst {l} {s} {loc} {c} (pdinstance {p} inj ev) inj-inj
  (PairU u₁ u₂) (PairU v₁ v₂) eq
  with ParseTree.inv-pairU {l} {s} {loc} (inj u₁) u₂ (inj v₁) v₂ eq
...   | ( head-eq , tail-eq ) =
      cong₂ ( λ x y → PairU {p} {s} {loc} x y )
             (inj-inj u₁ v₁ head-eq) tail-eq

-- (purpose): the `●`-second builder (`concatmap-pdinstance-snd` maps
--   `PDI.mk-snd-pdi` over the empty-tree witnesses) preserves map
--   injectivity
-- (used in): the chain of Canonic §6.1 configuration (b)
-- (proof idea): pattern-matching the pair *and* its `Flat-[]` evidence
--   makes the constructed map reduce to `mkinjSnd inj e` (the pd builder
--   does not reduce on a variable evidence), which rewrites to
--   `PairU e (inj u)`; `inv-pairU`'s second component feeds the hypothesis
pdinj-inj-snd : ∀ { l s : RE } { loc : ℕ } { c : Char }
  → ( ef : Σ[ x ∈ U l ] AllEmpty.Flat-[] l x ) ( z : PDInstance s c )
  → ( ∀ ( u v : U (pd-expr z) )
      → pd-inj z refl u ≡ pd-inj z refl v → u ≡ v )
  → ( ∀ ( u v : U (pd-expr (PDI.mk-snd-pdi {l} {s} {loc} {c} ef z)) )
      → pd-inj (PDI.mk-snd-pdi {l} {s} {loc} {c} ef z) refl u
      ≡ pd-inj (PDI.mk-snd-pdi {l} {s} {loc} {c} ef z) refl v
      → u ≡ v )
pdinj-inj-snd {l} {s} {loc} {c} ( e , AllEmpty.flat-[] .e fl )
  (pdinstance {p} inj ev) inj-inj u v eq =
    inj-inj u v
      (proj₂ (ParseTree.inv-pairU {l} {s} {loc} e (inj u) e (inj v) eq))
```

## 9. Configuration (b): a pair inside one member's spine

The left branch of the classification (Canonic §4.2) hands over a member whose
continuation spine *itself* carries the positioned pair.  The pair is
located by descending the expression: at each `+` node
`Dups-w-++-split` cuts the spine join, a crossing pair closes at that
node by the §5 construction one level deeper (no records: both trees
are read at positions of the *same* continuation, and the branch
constructors keep them apart), a pair wholly on one side recurses and is
re-embedded by `lift-Ctx`.  Non-sum nodes carry no spine pair at all.
The resulting ambiguity of the continuation reaches the member's
expression through the record's own map — §8's chain.

```agda
-- an append whose right half starts with a named element is never []
-- (both shapes reduce to the absurd `cons ≡ []`)
++-∷≢[] : ( xs ys : List RE ) ( y : RE ) → xs ++ (y ∷ ys) ≡ [] → ⊥
++-∷≢[] []       ys y eq = []≢_∷_ (sym eq)
++-∷≢[] (x ∷ xs) ys y eq = []≢_∷_ (sym eq)

-- (purpose): a one-element list never carries a positioned pair — the
--   witness always names two positions
-- (used in): the non-sum clauses of `spine-pair→Ambig` below, the leaf
--   clauses of the pdU-clause induction
-- (proof idea): case-split the witness's outer split point; each branch
--   reduces (with `∷-injectiveʳ` where needed) to `cons ≡ []`
Dups-w-∷[]-absurd : ( x : RE ) → Dups-w ( x ∷ [] ) → ⊥
Dups-w-∷[]-absurd
  x (dups-at {pre = pre} {mid = mid} {post = post}
              {earlier = earlier} {later = later} eq l≈₀e)
  with pre
...   | []         = ++-∷≢[] mid post later (∷-injectiveʳ eq)
...   | ( p ∷ ps ) = ++-∷≢[] ps (mid ++ (later ∷ post)) earlier
                       (∷-injectiveʳ eq)

-- (purpose): Canonic §6.1 configuration (b) — a positioned pair located anywhere
--   in the single continuation spine of a sum-bearing expression makes
--   that expression ambiguous
-- (used in): `member-pair→Ambig` below
-- (proof idea): structural recursion on the expression; see the cases
--   inline
spine-pair→Ambig : ( r : RE ) → Dups-w ( sum-spine r ) → Ambig r
spine-pair→Ambig ( l + s ` loc ) w
  with Dups-w-++-split (sum-spine l) (sum-spine s) w
...   | Sum.inj₁ d =
      lift-Ctx (Ctx+R 𝟘 s loc) (spine-pair→Ambig l d)
...   | Sum.inj₂ (Sum.inj₁ ( pre , mid₁ , mid₂ , post , p , q
                           , ( xs≡ , ys≡ , q≈₀p ) )) =
        let u    = proj₁ (r-∃u p)
            p≈₀q = ≈₀-sym q≈₀p
            pos₁ = ∈→◁ l p (subst ( λ L → p ∈ L ) (sym xs≡)
                       ( ∈-++ʳ pre (p ∷ mid₁) p (here refl) ))
            pos₂ = ∈→◁ s q (subst ( λ L → q ∈ L ) (sym ys≡)
                       ( ∈-++ʳ mid₂ (q ∷ post) q (here refl) ))
            t₁   = spine-read l p pos₁ u
            t₂   = spine-read s q pos₂ (Cast p≈₀q u)
        in  ( LeftU {l} {s} {loc} t₁
            , RightU {l} {s} {loc} t₂
            , trans (flat∘LeftU {l} {s} {loc} t₁)
                (trans (trans (spine-read-pres-flat l p pos₁ u)
                               (sym (Cast-pres-flat p≈₀q u)))
                       (sym (trans (flat∘RightU {l} {s} {loc} t₂)
                                   (spine-read-pres-flat s q pos₂
                                      (Cast p≈₀q u)))))
            , LeftU≢RightU t₁ t₂ )
...   | Sum.inj₂ (Sum.inj₂ d) =
      lift-Ctx (L+Ctx l 𝟘 loc) (spine-pair→Ambig s d)
spine-pair→Ambig ε w = ⊥-elim (Dups-w-∷[]-absurd ε w)
spine-pair→Ambig ( $ c ` loc ) w = ⊥-elim (Dups-w-∷[]-absurd ( $ c ` loc ) w)
spine-pair→Ambig ( l ● s ` loc ) w =
  ⊥-elim (Dups-w-∷[]-absurd ( l ● s ` loc ) w)
spine-pair→Ambig ( r * nε ` loc ) w =
  ⊥-elim (Dups-w-∷[]-absurd ( r * nε ` loc ) w)

-- (purpose): configuration (b) at a member record — the pair located
--   inside the member's continuation closes at the continuation and is
--   carried to the member's expression by the record's own map
-- (used in): `pd-Idemp` of §11
-- (proof idea): `spine-pair→Ambig` then `lift-pdinstance` (§8); the
--   map's injectivity comes from the builder chain (an `mkfuseInj` link
--   never appears: `pdU-+-location` already pushed any pair inside a
--   fused member to the unfused branch lists)
member-pair→Ambig : ∀ { q : RE } { c : Char } ( z : PDInstance q c )
  → ( ∀ ( u v : U (pd-expr z) )
      → pd-inj z refl u ≡ pd-inj z refl v → u ≡ v )
  → Dups-w (sum-spine (pd-expr z))
  → Ambig q
member-pair→Ambig {q} {c} z inj-inj d =
  lift-pdinstance {q} {c} z inj-inj (spine-pair→Ambig (pd-expr z) d)
```

## 10. The left branch, closed clause by clause

The classification's left branch names a *member of* `pdU[ q , c ]` whose
continuation carries the positioned pair.  This section closes it by
induction along the *clause structure* of `q`, case-splitting the
membership hypothesis against each `pdU` clause:

* `ε`, `$`: the member list is empty or a single letter record whose
  continuation is `ε` — a one-element spine carries no positioned pair.
* `+`: `pdU-+-location` (§7) either produces the crossing material,
  which §5's `pd-cross-positions→Ambig` closes at the clause's own sum
  node, or a subgoal on a branch instance, closed by recursion and
  re-embedded by `lift-Ctx`.
* `*`: the member's continuation is `p ● (r * nε \` loc) \` loc` — a
  non-sum, absurd spine pair (no recursion into `r` is needed).
* `●` with `ε∉ l`: only the first-factor instances, again non-sum
  continuations.
* `●` with `ε∈ l` (the nullable clause): first-factor instances are
  absurd as before; empty-first-factor instances (`mk-snd-pdi`) continue
  exactly where their `pdU[ s , c ]` preimage continues, so the pair
  recurses there; a *fused* member splits at its own sum node — left
  side absurd, right side recurses, and a crossing pair between the two
  sides is closed by `pd-cross-●→Ambig` below.

The crossing of the nullable clause needs its own closing lemma: unlike
§5, both records have the *same* input expression `l ● s \` loc`, so
distinctness cannot come from branch constructors — it comes from the
words: the first-factor instance's tree pairs a `c ∷ _` tree (the letter
record's own soundness evidence) with the right factor, while the
empty-first-factor instance's tree has the empty tree `e` in that
component (`flat-[]` gives `[]`), and `c ∷ _ ≡ []` is absurd.

```agda
-- (purpose): a record's soundness evidence as an accessor
-- (used in): `pd-cross-●→Ambig` below
-- (proof idea): the record stores the evidence as its second field
pd-ev : ∀ { q : RE } { c : Char } ( z : PDInstance q c )
  → ( u : U (pd-expr z) )
  → proj₁ (flat (pd-inj z refl u)) ≡ c ∷ proj₁ (flat u)
pd-ev (pdinstance inj ev) = ev

-- (purpose): the crossing case of the nullable-● clause — one
--   continuation at the whole first-factor instance (its spine is a
--   singleton) and one inside an empty-first-factor instance make the
--   concatenation ambiguous
-- (used in): the `●` clause of `pdU-member-pair→Ambig` below; Canonic §6.1's
--   configuration (c) through the same shape
-- (proof idea): the trees are the two records' maps applied to trees
--   read at the positions (word-preserving as in §5); the word
--   equation runs both records' `c ∷`_ evidences; distinctness: at the
--   first component of the pair node, the letter instance's map gives a
--   tree of word `c ∷ _` (`ev₁`) while `flat-[]` gives `[]` for `e`
pd-cross-●→Ambig : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( w₁ : PDInstance l c )
  → ( ef : Σ[ x ∈ U l ] AllEmpty.Flat-[] l x )
  → ( z₂ : PDInstance r c )
  → ( p q : RE )
  → p ≡ pd-expr w₁ ● r ` loc
  → ( pd-expr z₂ ) ◁ q
  → q ≈₀ p
  → Ambig ( l ● r ` loc )
pd-cross-●→Ambig {l} {r} {loc} {c} (pdinstance {p₁} i₁ ev₁)
  ( e , AllEmpty.flat-[] .e fl ) (pdinstance {p₂} i₂ ev₂) p q p≡ pos₂ q≈₀p =
    let w₁-rec = pdinstance {p₁} i₁ ev₁
        z₂-rec = pdinstance {p₂} i₂ ev₂
        u      = proj₁ (r-∃u (pd-expr w₁-rec ● r ` loc))
        p≈₀q   = ≈₀-sym q≈₀p
        cast-t = Cast p≈₀q (proj₁ (r-∃u p))
        v      = spine-read (pd-expr z₂-rec) q pos₂ cast-t
        x₁     = proj₁ (r-∃u p₁)
        word≡  = trans (pd-ev (pdinstance-fst {l} {r} {loc} {c} w₁-rec) u)
                     (trans (cong ( λ xs → c ∷ xs )
                             (trans (cong ( λ w → proj₁ (flat (proj₁ (r-∃u w))))
                                            (sym p≡))
                                    (trans (sym (Cast-pres-flat
                                            p≈₀q (proj₁ (r-∃u p))))
                                       (sym (spine-read-pres-flat
                                              (pd-expr z₂-rec) q pos₂ cast-t)))))
                        (sym (pd-ev (PDI.mk-snd-pdi {l} {r} {loc} {c}
                                          ( e , AllEmpty.flat-[] e fl ) z₂-rec) v)))
      in  ( pd-inj (pdinstance-fst {l} {r} {loc} {c} w₁-rec) refl u
          , pd-inj (PDI.mk-snd-pdi {l} {r} {loc} {c}
                      ( e , AllEmpty.flat-[] e fl ) z₂-rec) refl v
          , word≡
          , λ trees≡ →
              let contra : [] ≡ c ∷ proj₁ (flat x₁)
                  contra = sym (trans (trans (sym (ev₁ x₁))
                                        (cong ( λ t → proj₁ (flat t))
                                           (proj₁ (ParseTree.inv-pairU
                                                    {l} {r} {loc}
                                                    (i₁ x₁) (proj₁ (r-∃u r))
                                                    e (i₂ v) trees≡))))
                                 fl)
              in  []≢_∷_ contra )

-- (purpose): a member built by `pdinstance-fst` continues at the
--   non-sum expression `p ● s \` loc` — a one-element spine, so no
--   positioned pair can lie in it
-- (used in): the `●` clause of `pdU-member-pair→Ambig`
-- (proof idea): the continuation equation reduces once the input record
--   is pattern-matched; transport the pair into the singleton spine and
--   derive absurdity (`Dups-w-∷[]-absurd`)
pd-fst-inst→⊥ : ∀ { c : Char } { l s : RE } { loc : ℕ }
  → ( z : PDInstance ( l ● s ` loc ) c )
  → Σ[ w₁ ∈ PDInstance l c ]
      ( (w₁ ∈ PosixPD.pdU[ l , c ])
      × (pdinstance-fst {l} {s} {loc} {c} w₁ ≡ z) )
  → Dups-w (sum-spine (pd-expr z))
  → ⊥
pd-fst-inst→⊥ {c} {l} {s} {loc} z ( (pdinstance {p₁} i₁ ev₁) , ( w₁∈ , eq₁) ) d =
  ⊥-elim (Dups-w-∷[]-absurd (p₁ ● s ` loc)
    (subst Dups-w (cong sum-spine (sym (cong ( λ w → pd-expr w ) eq₁))) d))

-- (purpose): a member built by `pdinstance-star` continues at the
--   non-sum expression `p ● (r * nε \` loc) \` loc` — no positioned pair
-- (used in): the `*` clause of `pdU-member-pair→Ambig`)
pd-star-inst→⊥ : ∀ { c : Char } { r : RE } { nε : ε∉ r } { loc : ℕ }
  → ( z : PDInstance ( r * nε ` loc ) c )
  → Σ[ w₁ ∈ PDInstance r c ]
      ( (w₁ ∈ PosixPD.pdU[ r , c ])
      × (PDI.pdinstance-star {r} {nε} {loc} {c} w₁ ≡ z) )
  → Dups-w (sum-spine (pd-expr z))
  → ⊥
pd-star-inst→⊥ {c} {r} {nε} {loc} z ( (pdinstance {p₁} i₁ ev₁) , ( w₁∈ , eq₁) ) d =
  ⊥-elim (Dups-w-∷[]-absurd (p₁ ● (r * nε ` loc) ` loc)
    (subst Dups-w (cong sum-spine (sym (cong ( λ w → pd-expr w ) eq₁))) d))

-- (purpose): an `mk-snd-pdi` instance continues exactly where its
--   `pdU[ s , c ]` preimage continues — the empty tree of the nullable
--   left factor does not change the continuation expression
-- (used in): `●-snd-subgoal` below
pd-snd-continues : ∀ { c : Char } { l s : RE } { loc : ℕ }
  → ( ef : Σ[ x ∈ U l ] AllEmpty.Flat-[] l x )
  → ( w₁ : PDInstance s c )
  → ( z : PDInstance ( l ● s ` loc ) c )
  → PDI.mk-snd-pdi {l} {s} {loc} {c} ef w₁ ≡ z
  → Dups-w (sum-spine (pd-expr z))
  → Dups-w (sum-spine (pd-expr w₁))
pd-snd-continues ( e , AllEmpty.flat-[] .e fl ) (pdinstance {p₂} i₂ ev₂) z eq d =
  subst Dups-w (cong sum-spine (cong ( λ w → pd-expr w ) (sym eq))) d

-- (purpose): invert a member of the nullable clause's right (empty-tree)
--   list down to a subgoal on its `pdU[ s , c ]` preimage
-- (used in): the `●` clause of `pdU-member-pair→Ambig`
-- (proof idea): `∈-concatMap⁻` names the empty-tree witness, `∈-map⁻`
--   the preimage record; `pd-snd-continues` transports the pair
●-snd-subgoal : ∀ { c : Char } { l s : RE } { ε∈l : ε∈ l } { loc : ℕ }
  → ( z₁ : PDInstance ( l ● s ` loc ) c )
  → z₁ ∈ PDI.concatmap-pdinstance-snd {l} {s} {ε∈l} {loc} {c}
      (PosixPD.pdU[ s , c ])
  → Dups-w (sum-spine (pd-expr z₁))
  → Σ[ z₂ ∈ PDInstance s c ]
      ( (z₂ ∈ PosixPD.pdU[ s , c ]) × Dups-w (sum-spine (pd-expr z₂)) )
●-snd-subgoal {c} {l} {s} {ε∈l} {loc} z₁ z₁∈ d
  with ∈-concatMap⁻
         ( λ x → PDI.pdinstance-snd {l} {s} {loc} {c} x
             (PosixPD.pdU[ s , c ]) )
         ( PDI.zip-es-flat-[]-es {l} {ε∈l}
             (AllEmpty.mkAllEmptyU {l} ε∈l)
             (AllEmpty.mkAllEmptyU-sound {l} ε∈l) )
         z₁ z₁∈
...   | ( ef , ef∈ , z₁∈₂ ) with ef
...     | ( e , AllEmpty.flat-[] .e fl )
        with ∈-map⁻ (PDI.mk-snd-pdi {l} {s} {loc} {c}
                         ( e , AllEmpty.flat-[] e fl ))
                       (PosixPD.pdU[ s , c ]) z₁ z₁∈₂
...       | ( z₂ , z₂∈ , eq₂ ) =
          ( z₂ , z₂∈
          , pd-snd-continues ( e , AllEmpty.flat-[] e fl ) z₂ z₁ eq₂ d )

-- (purpose): analyze a positioned pair inside the continuation of a
--   FUSED member of the nullable clause: the pair is either impossible
--   (first-factor side, a non-sum spine), closes at the fused sum node
--   (`pd-cross-●→Ambig`), or descends to a subgoal on the right
--   preimage
-- (used in): the `●` clause of `pdU-member-pair→Ambig`
-- (proof idea): invert both memberships to named preimages
--   (`∈-map⁻`, `∈-concatMap⁻` + witness pattern, `∈-map⁻`), pattern-match
--   the records so the fused continuation equation reduces
--   (`pd-expr-fuse`), and cut the spine at the fused node with
--   `Dups-w-++-split`
●-fused-case : ∀ { c : Char } { l s : RE } { ε∈l : ε∈ l } { loc : ℕ }
  → ( z a b : PDInstance ( l ● s ` loc ) c )
  → a ∈ map (pdinstance-fst {l} {s} {loc} {c}) (PosixPD.pdU[ l , c ])
  → b ∈ PDI.concatmap-pdinstance-snd {l} {s} {ε∈l} {loc} {c}
      (PosixPD.pdU[ s , c ])
  → z ≡ PosixPD.fuse {l ● s ` loc} {loc} {c} a b
  → Dups-w (sum-spine (pd-expr z))
  → Sum._⊎_ (Ambig ( l ● s ` loc ))
      (Σ[ z₂ ∈ PDInstance s c ]
        ( (z₂ ∈ PosixPD.pdU[ s , c ]) × Dups-w (sum-spine (pd-expr z₂)) ))
●-fused-case {c} {l} {s} {ε∈l} {loc} z a b a∈ b∈ z≡ d
  with ∈-map⁻ (pdinstance-fst {l} {s} {loc} {c})
         (PosixPD.pdU[ l , c ]) a a∈
...   | ( w₁ , w₁∈ , eq₁ )
    with ∈-concatMap⁻
           ( λ x → PDI.pdinstance-snd {l} {s} {loc} {c} x
               (PosixPD.pdU[ s , c ]) )
           ( PDI.zip-es-flat-[]-es {l} {ε∈l}
               (AllEmpty.mkAllEmptyU {l} ε∈l)
               (AllEmpty.mkAllEmptyU-sound {l} ε∈l) )
           b b∈
...     | ( ef , ef∈ , b∈₂ ) with ef
...       | ( e , AllEmpty.flat-[] .e fl )
        with ∈-map⁻ (PDI.mk-snd-pdi {l} {s} {loc} {c}
                         ( e , AllEmpty.flat-[] e fl ))
                       (PosixPD.pdU[ s , c ]) b b∈₂
...         | ( z₂ , z₂∈ , eq₂ ) with w₁ | z₂
...           | (pdinstance {p₁} i₁ ev₁) | (pdinstance {p₂} i₂ ev₂)
            with Dups-w-++-split (sum-spine (p₁ ● s ` loc))
                   (sum-spine p₂)
                   (subst Dups-w
                      (cong sum-spine
                         (trans (cong ( λ w → pd-expr w ) z≡)
                            (trans (pd-expr-fuse {l ● s ` loc} {loc} {c} a b)
                               (cong₂ ( λ x y → x + y ` loc )
                                  (cong ( λ w → pd-expr w ) (sym eq₁))
                                  (cong ( λ w → pd-expr w ) (sym eq₂))))))
                      d)
...             | Sum.inj₁ d₁ =
                ⊥-elim (Dups-w-∷[]-absurd (p₁ ● s ` loc) d₁)
...             | Sum.inj₂ (Sum.inj₂ d₂) =
                Sum.inj₂ ( (pdinstance {p₂} i₂ ev₂) ,
                  ( subst ( λ w → Any ( _≡_ w )
                        (PosixPD.pdU[ s , c ]) ) refl z₂∈
                  , d₂ ) )
...             | Sum.inj₂ (Sum.inj₁ ( pre , mid₁ , mid₂ , post , p , q
                                    , ( xs≡ , ys≡ , q≈₀p ) ))
                with subst ( λ L → p ∈ L ) (sym xs≡)
                     ( ∈-++ʳ pre (p ∷ mid₁) p (here refl) )
...               | ( here p≡ ) = Sum.inj₁
                  ( pd-cross-●→Ambig {l} {s} {loc} {c}
                      (pdinstance {p₁} i₁ ev₁)
                      ( e , AllEmpty.flat-[] e fl )
                      (pdinstance {p₂} i₂ ev₂)
                      p q p≡
                      ( ∈→◁ (pd-expr (pdinstance {p₂} i₂ ev₂)) q
                          ( subst ( λ L → q ∈ L ) (sym ys≡)
                              ( ∈-++ʳ mid₂ (q ∷ post) q (here refl) ) ) )
                      q≈₀p )
...               | ( there () )

-- (purpose): Canonic §6.1's classification left branch, closed at pdU members —
--   a positioned pair inside the continuation of a member of
--   `pdU[ r , c ]` makes r ambiguous
-- (used in): `pd-Idemp` of §11
-- (proof idea): the case analysis of the section text above; the
--   transports between a record's continuation and its builder's input
--   are the §7 equations (`pd-expr-left/right/fuse` and direct
--   reduction of the `pdinstance-fst`/`mk-snd-pdi`/`pdinstance-star`
--   builders after pattern-matching their inputs)
pdU-member-pair→Ambig : ∀ { c : Char } ( r : RE )
  → ( z : PDInstance r c )
  → z ∈ PosixPD.pdU[ r , c ]
  → Dups-w (sum-spine (pd-expr z))
  → Ambig r
pdU-member-pair→Ambig {c} ε z () d
pdU-member-pair→Ambig {c} ( $ c₀ ` loc ) z z∈ d with c₀ Char.≟ c | z∈
...   | yes refl | here p =
      ⊥-elim (Dups-w-∷[]-absurd ε
          (subst Dups-w (cong sum-spine (cong ( λ w → pd-expr w ) p)) d))
...   | yes refl | there ()
...   | no  _    | ()
pdU-member-pair→Ambig {c} ( l + s ` loc ) z z∈ d
  with pdU-+-location l s loc c z z∈ d
...   | Sum.inj₁ ( pdi₁ , pdi₂ , p , q , ( pos₁ , pos₂ , p≈₀q ) ) =
      pd-cross-positions→Ambig pdi₁ pdi₂ p q pos₁ pos₂ p≈₀q
...   | Sum.inj₂ (Sum.inj₁ ( z₁ , ( z₁∈ , d₁ ) )) =
      lift-Ctx (Ctx+R 𝟘 s loc) (pdU-member-pair→Ambig l z₁ z₁∈ d₁)
...   | Sum.inj₂ (Sum.inj₂ ( z₂ , ( z₂∈ , d₂ ) )) =
      lift-Ctx (L+Ctx l 𝟘 loc) (pdU-member-pair→Ambig s z₂ z₂∈ d₂)
pdU-member-pair→Ambig {c} ( r * nε ` loc ) z z∈ d
  = ⊥-elim (pd-star-inst→⊥ z
      (∈-map⁻ (PDI.pdinstance-star {r} {nε} {loc} {c})
         (PosixPD.pdU[ r , c ]) z z∈) d)
pdU-member-pair→Ambig {c} ( l ● s ` loc ) z z∈ d with ε∈? l
...   | no ¬ε∈l =
      ⊥-elim (pd-fst-inst→⊥ z (∈-map⁻ (pdinstance-fst {l} {s} {loc} {c})
                         (PosixPD.pdU[ l , c ]) z z∈) d)
...   | yes ε∈l with ∈-oplus⁻ {l ● s ` loc} {loc} {c}
           ( map (pdinstance-fst {l} {s} {loc} {c}) (PosixPD.pdU[ l , c ]) )
           ( PDI.concatmap-pdinstance-snd {l} {s} {ε∈l} {loc} {c}
               (PosixPD.pdU[ s , c ]) )
           z z∈
...     | Sum.inj₁ ( z₁ , ( z₁∈ , z≡z₁ ) ) =
        let ( w₁ , ( w₁∈ , eq₁ ) ) =
              ∈-map⁻ (pdinstance-fst {l} {s} {loc} {c})
                     (PosixPD.pdU[ l , c ]) z₁ z₁∈
        in  ⊥-elim (pd-fst-inst→⊥ z ( w₁ , ( w₁∈ , trans eq₁ (sym z≡z₁) ) ) d)
...     | Sum.inj₂ (Sum.inj₁ ( z₁ , ( z₁∈ , z≡z₁ ) )) =
        let ( z₂ , ( z₂∈ , d₂ ) ) = ●-snd-subgoal z₁ z₁∈
              (subst Dups-w (cong sum-spine
                         (cong ( λ w → pd-expr w ) z≡z₁)) d)
        in  lift-Ctx (L●Ctx l 𝟘 loc) (pdU-member-pair→Ambig s z₂ z₂∈ d₂)
...     | Sum.inj₂ (Sum.inj₂ ( a , b , ( a∈ , b∈ , z≡ ) ))
        with ●-fused-case z a b a∈ b∈ z≡ d
...       | Sum.inj₁ amb = amb
...       | Sum.inj₂ ( z₂ , ( z₂∈ , d₂ ) ) =
            lift-Ctx (L●Ctx l 𝟘 loc) (pdU-member-pair→Ambig s z₂ z₂∈ d₂)
```

## 11. The soundness theorem, composed

The pieces assembled: the scan reflection, the classification, §10's
closure of the left branch, and the closure of configuration (c) proved
here.  The classification's second branch now also hands over
`2 ≤ length pdis` (Canonic §4.2: the two members are at distinct positions of
the list), and the *length* alone is enough: inverting the `pdU` clause
structure along the member list, a list of two members can only come
from a `+`/`●` node with an already-long branch list (the recursion
lifts the ambiguity back through the sum/consumption contexts), from a
`*` clause (the continuation copies are `r * ε∉r \` loc`-wrapped, and
`star-Ambig` embeds two trees into the star), or from the nullable-`●`
clause's cross product `| mkAllEmptyU l | × | pdU[ s , c ] |` — where a
factor `≥ 2` is either the recursion into `s` or *the empty-tree list of
`l` itself*, whose `≥ 2` record is exactly the A2 criterion at the
clause's own concatenation node.

```agda
-- (purpose): right unit of addition on natural numbers
-- (used in): `×-≥2→` and `pdU-2members→Ambig` below
n+0 : ( n : ℕ ) → n Nat.+ zero ≡ n
n+0 zero = refl
n+0 (suc n) = cong suc (n+0 n)

-- (purpose): the letter clause of `pdU` has at most one member
-- (used in): the `$` clause of `pdU-2members→Ambig` below
-- (proof idea): the clause's own `Char.≟` decides between a singleton
--   and the empty list
pdU-$-len : ∀ { c c₀ : Char } { loc : ℕ }
  → length (PosixPD.pdU[ $ c₀ ` loc , c ]) ≤ suc zero
pdU-$-len {c} {c₀} with (c₀ Char.≟ c)
...   | yes refl = ≤-refl
...   | no  _    = z≤n

-- (purpose): no number is both ≥ 2 and ≤ 1
-- (used in): the `ε` and `$` clauses of `pdU-2members→Ambig` below
¬2≤n≤1→ : ∀ { n : ℕ } → suc (suc zero) ≤ n → n ≤ suc zero → ⊥
¬2≤n≤1→ {n} h q with (≤-trans h q)
...   | s≤s ()

-- (purpose): a product of lengths ≥ 2 already has a factor ≥ 2
-- (used in): `pdU-2members→Ambig` below (the multiplicative clauses)
-- (proof idea): split the left factor at 0/1/≥ 2; the 0 case is absurd,
--   the 1 case leaves the other factor (after `n+0`), the ≥ 2 case is
--   `2 ≤ 2 + m` (induction with `m≤n⇒m≤1+n`)
2≤2+m : ∀ { m : ℕ } → suc (suc zero) ≤ suc (suc m)
2≤2+m {zero} = ≤-refl
2≤2+m {suc m} = m≤n⇒m≤1+n 2≤2+m

×-≥2→ : ∀ { m n : ℕ }
  → suc (suc zero) ≤ m Nat.* n
  → Sum._⊎_ (suc (suc zero) ≤ m) (suc (suc zero) ≤ n)
×-≥2→ {zero} {n} ()
×-≥2→ {suc zero} {n} h =
  Sum.inj₂ (subst ( λ k → suc (suc zero) ≤ k ) (n+0 n) h)
×-≥2→ {suc (suc m)} {n} h = Sum.inj₁ 2≤2+m

-- (purpose): one `pdinstance-snd` call maps its right argument through
--   unchanged in length
-- (used in): `len-cms` below
-- (proof idea): `pdinstance-snd` reduces to `List.map (mk-snd-pdi …)`
--   at the pair argument; `length-map` closes the goal
len-pdsnd : ∀ { l r : RE } { loc : ℕ } { c : Char }
  ( pdis : List (PDInstance r c) )
  ( ef : Σ[ e ∈ U l ] AllEmpty.Flat-[] l e )
  → length (PDI.pdinstance-snd {l} {r} {loc} {c} ef pdis) ≡ length pdis
len-pdsnd {l} {r} {loc} {c} pdis ( x , x∈ ) =
  length-map (PDI.mk-snd-pdi {l} {r} {loc} {c} ( x , x∈ )) pdis

-- (purpose): `zip-es-flat-[]-es` is length preserving
-- (used in): `pdU-cms-len` below
len-zip : ∀ { l : RE } { ε∈l : ε∈ l }
  ( es : List (U l) )
  ( allfl : ListAll.All (AllEmpty.Flat-[] l) es )
  → length (PDI.zip-es-flat-[]-es {l} {ε∈l} es allfl) ≡ length es
len-zip {l} {ε∈l} [] ListAll.[] = refl
len-zip {l} {ε∈l} ( e ∷ es ) ( ListAll._∷_ x∈ allfl ) =
  cong suc (len-zip {l} {ε∈l} es allfl)

-- (purpose): concatenating the copies of `pdis` indexed by a witness
--   list gives the product of the lengths
-- (used in): `pdU-cms-len` below
-- (proof idea): induction on the witness list; each cell contributes
--   `length pdis` (`len-pdsnd`) and `_×_` is defined by recursion on
--   the left factor
len-cms : ∀ { l r : RE } { loc : ℕ } { c : Char }
  ( pdis : List (PDInstance r c) )
  ( ws : List ( Σ[ e ∈ U l ] AllEmpty.Flat-[] l e ) )
  → length ( List.concatMap
               ( λ x → PDI.pdinstance-snd {l} {r} {loc} {c} x pdis ) ws )
      ≡ length ws Nat.* length pdis
len-cms pdis [] = refl
len-cms {l} {r} {loc} {c} pdis ( x ∷ ws ) =
  trans (length-++ (PDI.pdinstance-snd {l} {r} {loc} {c} x pdis))
        (trans (cong ( λ k → length (PDI.pdinstance-snd {l} {r} {loc} {c} x pdis) Nat.+ k)
                     (len-cms {l} {r} {loc} {c} pdis ws))
               (trans (cong ( λ k → k Nat.+ length ws Nat.* length pdis )
                            (len-pdsnd {l} {r} {loc} {c} pdis x))
                      refl))

-- (purpose): the length of the nullable clause's empty-tree copy list
--   is the product of the empty-tree count and the right member count
-- (used in): the `●` clause of `pdU-2members→Ambig` below
-- (proof idea): `concatmap-pdinstance-snd` unfolds to `len-cms` at the
--   witness zip, whose length is `length (mkAllEmptyU …)` (`len-zip`)
pdU-cms-len : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  ( pdis : List (PDInstance r c) )
  → length (PDI.concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis)
      ≡ length (AllEmpty.mkAllEmptyU {l} ε∈l) Nat.* length pdis
pdU-cms-len {l} {r} {ε∈l} pdis =
  trans (len-cms pdis
          (PDI.zip-es-flat-[]-es {l} {ε∈l}
             (AllEmpty.mkAllEmptyU {l} ε∈l)
             (AllEmpty.mkAllEmptyU-sound {l} ε∈l)))
        (cong ( λ k → k Nat.* length pdis )
              (len-zip {l} {ε∈l}
                 (AllEmpty.mkAllEmptyU {l} ε∈l)
                 (AllEmpty.mkAllEmptyU-sound {l} ε∈l)))

-- (purpose): concatenating copies of a fixed-length list keeps the
--   product of the lengths
-- (used in): `pdU-oplus-≥2` below
len-concatMap-const : ∀ { A B : Set }
  ( xs : List A ) ( ys : List B ) ( g : A → List B )
  → ( ∀ x → length (g x) ≡ length ys )
  → length (List.concatMap g xs) ≡ length xs Nat.* length ys
len-concatMap-const [] ys g len-g = refl
len-concatMap-const ( x ∷ xs ) ys g len-g =
  trans (length-++ (g x))
        (trans (cong ( λ k → length (g x) Nat.+ k )
                     (len-concatMap-const xs ys g len-g))
               (trans (cong ( λ k → k Nat.+ length xs Nat.* length ys ) (len-g x))
                      refl))

-- (purpose): a fired ≥ 2 bound on an `pdinstance-oplus` already holds
--   of one of its input lists
-- (used in): the `+` and `●` clauses of `pdU-2members→Ambig` below
-- (proof idea): the two pass-through clauses keep one side's length;
--   the cross clause is `len-concatMap-const` at per-element maps
--   (`length-map`), and `×-≥2→` splits the product
pdU-oplus-≥2 : ∀ { r : RE } { loc : ℕ } { c : Char }
  ( pdis qs : List (PDInstance r c) )
  → suc (suc zero) ≤ length (PosixPD.pdinstance-oplus {r} {loc} {c} pdis qs)
  → Sum._⊎_ (suc (suc zero) ≤ length pdis) (suc (suc zero) ≤ length qs)
pdU-oplus-≥2 [] qs h = Sum.inj₂ h
pdU-oplus-≥2 (pdiˡ ∷ pdisˡ) [] h = Sum.inj₁ h
pdU-oplus-≥2 {r} {loc} {c} (pdiˡ ∷ pdisˡ) (pdiʳ ∷ pdisʳ) h =
  ×-≥2→ {length (pdiˡ ∷ pdisˡ)} {length (pdiʳ ∷ pdisʳ)}
    (subst ( λ k → suc (suc zero) ≤ k )
       (len-concatMap-const (pdiˡ ∷ pdisˡ) (pdiʳ ∷ pdisʳ)
          ( λ pdiˡ₁ → List.map (PosixPD.fuse {r} {loc} {c} pdiˡ₁)
                                (pdiʳ ∷ pdisʳ) )
          ( λ x → length-map (PosixPD.fuse {r} {loc} {c} x) (pdiʳ ∷ pdisʳ)))
       h)

-- (purpose): ambiguity of `r` persists under Kleene star
-- (used in): the `*` clause of `pdU-2members→Ambig` below
-- (proof idea): `ListU [ u ]` / `ListU [ v ]` flatten to
--   `flat u ++ []` and `flat v ++ []` (`++-identityʳ`); `unListU`
--   reads the component list back off the singleton
star-Ambig : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ }
  → Ambig r → Ambig ( r * nε ` loc )
star-Ambig {r} {nε} {loc} ( u , v , word≡ , u≢v ) =
  ( ListU ( u ∷ [] ) , ListU ( v ∷ [] ) ,
    trans eq₁ (trans word≡ eq₃) ,
    λ trees≡ → u≢v (proj₁ (∷-injective (cong unListU trees≡))) )
  where
    eq₁ : proj₁ (flat (ListU {r} {nε} {loc} (u ∷ []))) ≡ proj₁ (flat u)
    eq₁ = ++-identityʳ (proj₁ (flat u))
    eq₃ : proj₁ (flat v) ≡ proj₁ (flat (ListU {r} {nε} {loc} (v ∷ [])))
    eq₃ = sym (++-identityʳ (proj₁ (flat v)))

-- (purpose): Canonic §6.1's configuration (c), closed — a two-member
--   continuation list of a single-character partial derivative makes
--   the state ambiguous
-- (used in): `pd-Idemp` below
-- (proof idea): the case analysis of the section text above; the
--   multiplicative clauses are decomposed by `pdU-oplus-≥2` /
--   `pdU-cms-len` / `×-≥2→`, and the ambiguity is carried back by
--   `lift-Ctx` (the sum/consumption contexts), `star-Ambig`, or — for
--   the empty-tree factor — the A2 criterion record itself
pdU-2members→Ambig : ∀ { c : Char } ( q : RE )
  → suc (suc zero) ≤ length (PosixPD.pdU[ q , c ])
  → Ambig q
pdU-2members→Ambig {c} ε ()
pdU-2members→Ambig {c} ( $ c₀ ` loc ) h =
  ⊥-elim (¬2≤n≤1→ h (pdU-$-len {c} {c₀} {loc}))
pdU-2members→Ambig {c} ( l + s ` loc ) h
  with pdU-oplus-≥2 {l + s ` loc} {loc} {c}
         ( List.map pdinstance-left (PosixPD.pdU[ l , c ]) )
         ( List.map pdinstance-right (PosixPD.pdU[ s , c ]) ) h
...   | Sum.inj₁ h₂ = lift-Ctx (Ctx+R 𝟘 s loc)
          (pdU-2members→Ambig {c} l
            (subst ( λ k → suc (suc zero) ≤ k )
               (length-map pdinstance-left (PosixPD.pdU[ l , c ])) h₂))
...   | Sum.inj₂ h₂ = lift-Ctx (L+Ctx l 𝟘 loc)
          (pdU-2members→Ambig {c} s
            (subst ( λ k → suc (suc zero) ≤ k )
               (length-map pdinstance-right (PosixPD.pdU[ s , c ])) h₂))
pdU-2members→Ambig {c} ( r * nε ` loc ) h =
  star-Ambig (pdU-2members→Ambig {c} r
    (subst ( λ k → suc (suc zero) ≤ k )
       (length-map PDI.pdinstance-star (PosixPD.pdU[ r , c ])) h))
pdU-2members→Ambig {c} ( l ● s ` loc ) h with (ε∈? l)
...   | no ¬ε∈l = lift-Ctx (Ctx●R 𝟘 s loc)
          (pdU-2members→Ambig {c} l
            (subst ( λ k → suc (suc zero) ≤ k )
               (length-map pdinstance-fst (PosixPD.pdU[ l , c ])) h))
...   | yes ε∈l
    with pdU-oplus-≥2 {l ● s ` loc} {loc} {c}
           ( List.map pdinstance-fst (PosixPD.pdU[ l , c ]) )
           ( PDI.concatmap-pdinstance-snd {l} {s} {ε∈l} {loc} {c}
               (PosixPD.pdU[ s , c ]) ) h
...     | Sum.inj₁ h₂ = lift-Ctx (Ctx●R 𝟘 s loc)
          (pdU-2members→Ambig {c} l
            (subst ( λ k → suc (suc zero) ≤ k )
               (length-map pdinstance-fst (PosixPD.pdU[ l , c ])) h₂))
...     | Sum.inj₂ h₂
      with ×-≥2→ {length (AllEmpty.mkAllEmptyU {l} ε∈l)}
                  {length (PosixPD.pdU[ s , c ])}
                  (subst ( λ k → suc (suc zero) ≤ k )
                     (pdU-cms-len {l} {s} {ε∈l} {loc} {c}
                        (PosixPD.pdU[ s , c ])) h₂)
...       | Sum.inj₁ h₃ = A2→Ambig ( l ● s ` loc )
          ( 𝟘 , l , s , loc , ( refl , ( ε∈l , h₃ ) ) )
...       | Sum.inj₂ h₃ = lift-Ctx (L●Ctx l 𝟘 loc)
          (pdU-2members→Ambig {c} s h₃)

-- (purpose): the Canonic §6.1 goal theorem — its A3-as-test, reflected:
--   a fired `pd-Idemp?` on the `pdU` member list implies ambiguity
-- (used in): `pd-a3-Ambig-via-pd-Idemp` below (the composition check on the
--   Canonic §4.1 example)
-- (proof idea): the hypothesis unpacking of Canonic §6.1's text — `dups-≈₀-dups`
--   reads the fired scan as a positioned pair (`pd-Idemp?` unfolds to
--   `dups-≈₀ ∘ pd-alts` definitionally), `pd-alts-Dups-w-classify`
--   places it relative to the members, the left branch is closed by
--   §10's `pdU-member-pair→Ambig`, the right branch by
--   `pdU-2members→Ambig` (the classification hands over the length bound)
pd-Idemp : ∀ { q : RE } { c : Char }
  → pd-Idemp? (PosixPD.pdU[ q , c ]) ≡ true
  → Ambig q
pd-Idemp {q} {c} eq
  with pd-alts-Dups-w-classify (PosixPD.pdU[ q , c ])
         (dups-≈₀-dups (pd-alts (PosixPD.pdU[ q , c ])) eq)
...   | Sum.inj₁ ( z , ( z∈ , d ) ) =
      pdU-member-pair→Ambig q z z∈ d
...   | Sum.inj₂ ( z , z′ , earlier , later
                 , ( z∈ , z′∈ , earlier∈ , later∈ , later≈₀earlier
                   , 2≤len ) ) =
      pdU-2members→Ambig {c} q 2≤len

-- the whole composition elaborates on the Canonic §4.1 example: applying `pd-Idemp`
-- to the fired test
pd-a3-Ambig-via-pd-Idemp : Ambig pd-a3-target
pd-a3-Ambig-via-pd-Idemp = pd-Idemp {pd-a3-target} {'a'} pd-a3-Idemp-applied
```

## 12. The soundness direction over the pd-states

The attempt to state the converse direction *about a given tree* —

> `∀ { r } { w₁ w₂ } ( u : U r ) → proj₁ (flat {r} u) ≡ w₁ ++ w₂`
> `→ ( p : RE ) → crit p → Any ( λ s → s ≡ p ) (Canonic.pd*-Desc r w₁)`
> `→ ∃[ v ] ( proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) ) × ¬ ( u ≡ v )`

— is false, and the counterexample is small: `r = ( ε + ε ) + b` has two
ε-trees, so A1 (hence `crit`) fires at the state `r` itself, which `[]`
reaches; but the word `b` has exactly one parse tree — take it for `u` and
no `v ≢ u` exists.  Nothing in the statement ties `u` to the state `p`: the
criterion's witness may live in a part of `r` the parse of `u` never
traverses.  Constraining `u` would not repair the *shape* either: an A1
witness at a state twins only the word `w₁` (its state trees read `ε`), and
A1 at a state does not make every word of that state ambiguous —
`( ε + ε ) + ( b ● c )` has two ε-trees and a unique `b c`-tree.  What is
provable is the existential form at the end of this section, for the first
three disjuncts of `crit` — the fourth is sound too (this module's §11
`pd-Idemp` closes it on the `pdU` states; what the counterexample below shows
is that the *twin-of-a-fixed-`u`* form fails, not the criterion), with the
lift's injectivity hypothesis made explicit.

```agda
-- the counterexample expression: A1 fires at the top, `b` is unambiguous
fail-r : RE
fail-r = ( ( ε + ε ` 1 ) + ( $ 'b' ` 2 ) ` 3 )

fail-u : U fail-r
fail-u = RightU (LetterU 'b')

-- (purpose): the word `b` has exactly one parse tree in `fail-r` — the
--   conclusion of the twin-of-u form is uninhabited for this `u`
-- (used in): `soundness-fails`
-- (proof idea): case on `v`: the left branch of the sum can only read `ε`
--   (the equation then has type `[] ≡ 'b' ∷ []`, absurd), and the letter
--   node is determined by its letter (the index pins it to `'b'`)
fail-unique : ( v : U fail-r ) → proj₁ (flat {fail-r} v) ≡ 'b' ∷ [] → v ≡ fail-u
fail-unique (LeftU (LeftU EmptyU)) ()
fail-unique (LeftU (RightU EmptyU)) ()
fail-unique (RightU (LetterU 'b')) refl = refl

-- (purpose): A1 fires at `fail-r` — two ε-trees through the `ε + ε` branch
-- (used in): `soundness-fails`
-- (proof idea): computed nullability (left summand, right non-nullable) and
--   `mkAllEmptyU` listing two trees, so `2 ≤ 2`
fail-A1 : AmbigCheck.AmbigA1 fail-r
fail-A1 = ( RE.ε∈_<+_ (RE.ε∈_+_ RE.ε∈ε RE.ε∈ε) ε∉$ , s≤s (s≤s ≤-refl) )

-- (purpose): the state `fail-r` is reached by `[]`
-- (used in): `soundness-fails`
-- (proof idea): `pd*-Desc fail-r []` computes to the singleton `fail-r ∷ []`
fail-Desc : Any ( λ s → s ≡ fail-r ) (Canonic.pd*-Desc fail-r [])
fail-Desc = here refl

-- (purpose): the twin-of-u form above, refuted
-- (used in): the §12 prose
-- (proof idea): instantiate at `fail-r`, `u = fail-u`, `p = fail-r`; the
--   conclusion's `v` would be a second `b`-tree, and `fail-unique` forces
--   `v ≡ fail-u`, contradicting `¬ ( u ≡ v )`
soundness-fails : ¬ ( ∀ { r : RE } { w₁ w₂ : List Char }
    ( u : U r )
    → proj₁ (flat {r} u) ≡ w₁ ++ w₂
    → ( p : RE )
    → crit p
    → Any ( λ s → s ≡ p ) (Canonic.pd*-Desc r w₁)
    → ∃[ v ] ( proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) ) × ( ¬ ( u ≡ v ) ) )
soundness-fails h
  with h {fail-r} {[]} { 'b' ∷ [] } fail-u refl fail-r (Sum.inj₁ fail-A1) fail-Desc
...   | ( v , ( word≡ , u≢v ) ) = u≢v (sym (fail-unique v (sym word≡)))

-- the first three disjuncts of `crit` — the ones whose soundness lifts
-- exist unconditionally (the fourth is closed by `pd-Idemp` §11)
crit-3 : RE → Set
crit-3 p = Sum._⊎_
      (AmbigCheck.AmbigA1 p)
      (Sum._⊎_
        (AmbigCheck.AmbigA2 p)
        ( Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ l ∈ RE ] Σ[ l′ ∈ RE ] Σ[ loc ∈ ℕ ]
            ( ( AmbigCheck.plug ctx ( l + l′ ` loc ) ≡ p )
            × ( Canonic._≈₀_ l l′ ) ) ))

-- (purpose): the soundness direction read over the pd-states — a criterion
--   at a reached state lifts to an ambiguity of `r`
-- (used in): the §12 prose
-- (proof idea): case-split on the disjunction; each branch is the matching
--   `Canonic` lift (`pd*-A1→Ambig`, `pd*-A2→Ambig`, `pd*-Ctx-dup→Ambig`)
--   under the lift's injectivity hypothesis
soundness : ∀ { r : RE } { w : List Char }
  → ( pdi : PDInstance* r w )
  → ( ∀ ( x y : U (Canonic.pd*-expr pdi) )
        → Canonic.pd*-inj pdi x ≡ Canonic.pd*-inj pdi y → x ≡ y )
  → crit-3 (Canonic.pd*-expr pdi)
  → ∃[ u′ ] ∃[ v′ ]
      ( proj₁ (flat {r} u′) ≡ proj₁ (flat {r} v′) × ¬ ( u′ ≡ v′ ) )
soundness pdi inj-inj (Sum.inj₁ a1) = Canonic.pd*-A1→Ambig pdi inj-inj a1
soundness pdi inj-inj (Sum.inj₂ (Sum.inj₁ a2)) = Canonic.pd*-A2→Ambig pdi inj-inj a2
soundness pdi inj-inj (Sum.inj₂ (Sum.inj₂ (ctx , l , l′ , loc , ( eq , dup )))) =
  pd*-Ctx-dup→Ambig pdi inj-inj ctx eq dup
```
