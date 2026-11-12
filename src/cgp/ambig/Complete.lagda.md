# Completeness of the criteria: the injectivity half

`cgp.ambig.Canonic` §7 proves for each criterion of section 6 of

> Martin Sulzmann, Kenny Zhuo Ming Lu. *Derivative-Based Diagnosis of Regular
> Expression Ambiguity.* CIAA 2016.

that a witness *at a pd-state* lifts to an ambiguity of the original expression
(`pd*-A1→Ambig`, `pd*-A2→Ambig`, `pd*-Ctx-dup→Ambig`; all three are instances
of the master lift `lift-Ambig`).  `cgp.ambig.Converse` shows that
`sd = ( a + a · a ) ⋆` is **not** a counterexample to the paper's proposition:
A1 holds at the pd-state reached after `a a`, and the A3 test fires for that
state on the letter `a`.  What is left is the direction the paper obtains from
its `AllParseFST` construction:

> if `u ≢ v` are parse trees of `r` for the same word, then for the pd-state
> reached by that word the transition tree map identifies two distinct trees —
> that state is ambiguous — and hence (by the soundness proofs in
> `cgp.ambig.AmbigCheck`/`cgp.ambig.Canonic`) one of the criteria fires there.

This module develops the two ingredients of that argument.

* §1 isolates the witness: *two distinct trees identified by one transition
  map*.  Given it, the state is ambiguous, and `Canonic.lift-Ambig` finishes.
* §2–§3 prove that a transition map identifies no two trees, builder by builder
  — `injId`, the disjoint-sum map of `fuse`/`pdinstance-oplus`, the star
  extension `mkinjList`, the pair extensions used by `pdinstance-fst`/
  `pdinstance-snd`, the sum injections, and composition.  Most side conditions
  are exactly the negations of the criteria: no `+` with `≈₀`-congruent
  alternatives (`A3`/`Idemp`), and a unique empty parse tree where a
  concatenation is derived through its left factor (`A1`/`A2`).  The one that
  is not local is `mkfuseInj-inj`'s disjointness of the two branch ranges:
  whether the images of the two branches of a fused sum coincide is a fact
  about `r` as a whole — it *is* the Antimirov disjointness statement (§4.1).
* §4 separates what is *not* proved yet: uniqueness of the reconstructing
  instance (Antimirov disjointness, absent from the project — and visible as
  the one non-local side condition of `mkfuseInj-inj`), and the Agda-level
  obstacle that a *computed* instance cannot be bound by matching
  (`with`-abstraction over `pdUMany[ sd , a a ]` has unrefutable cases).
* §5 beats the second obstacle by mirroring the computation of
  `pdU[ sd-s1 , a ]` / `pdUMany[ sd , a a ]` with the same constructors: the
  named instances satisfy the computed-list equations, the continuation
  equation `pd*-expr pdi₂ ≡ sd-s2`, and `A1` at that state — all by `refl`.
* §6 discharges the third hypothesis: the transition map of `pdi₂` is
  injective, by running §3 along the builders of §5; the range-disjointness
  of its one fusion node falls out of the constructor heads of the two
  branch images (an instance of §4.1 proved by inspection, not by the
  general lemma).
* §7 assembles `Converse.sd-Ambig-from-descendant`, `sd-s2-A1` and §6 into a
  checked `Ambig sd`: a criterion at the reached state, lifted along an
  injective transition map, is a genuine ambiguity of `r`.
* §8 states the goal of the whole arc — the *completeness* direction proper
  (given an ambiguity witness, a pd-descendant state where a criterion
  fires) — with unchecked bodies: the general statement, and its reading
  tied to the ambiguity pair of `sd`.  Together with §12's `pair-complete`
  and `pdesc` these four holes are the only unsolved metas in the module
  (`--allow-unsolved-metas`).
* §9 is the base case of the descent: two distinct parse trees with empty
  word force `AmbigA1` at the state (`base-A1-at-root`), for any
  expression — via `flat`'s language component, `Word.[]∈⟦r⟧→ε∈r` and
  `mkAllEmptyU-complete`.
* §10 is the descent's pd-side plumbing: `chain*` (advances of a single
  instance) is `pdUMany-aux` on the singleton list (`chain-aux`), a chain
  from a member is contained in any advancement run containing that member
  (`any-aux`), and `chain-in-pd*-Desc` transfers a suffix chain from a
  reachable instance to a pd-descendant of `r` for the concatenated word.
* §11 is the descent's instance side: composing a prefix instance with an
  instance of its continuation (`pdni∘`) preserves pd-fields exactly
  (`pd*-expr-∘`, `∘-pres-∈`), and instances / `pdU` memberships transport
  along RE-equalities of their targets (`pdtransport*`, `pdU-transport-∈`)
  — every such transport is a J-definition that reduces at `refl`, which is
  where the descent's concrete calls land once the trees fix `r`.
* §12 opens the split case (B3b): the diagnosis disjunction of §8 is named
  (`crit`); A2 and the duplicate pattern are stable under hole contexts
  (`A2-Ctx`, `dup-Ctx` via `Ctx∘Ctx`); a pair of empty trees, one in each
  branch of a sum, fires A1 at the sum itself (`split-+-A1`); a criterion
  found below a branch is carried across the sum (`A1-+<`/`A1-+>`,
  `crit-+<`/`crit-+>`); descent paths that carry their `pdU` memberships
  as fields (`Path`) sidestep the stuck-list obstacle of §10–§11, and
  their end-state membership (`pdesc`) is stated with a hole; the pair
  theorem `pair-complete` — the structural-recursion core of the paper's
  ambiguity-criteria argument — is stated over paths, with a hole.

```agda
{-# OPTIONS --rewriting --allow-unsolved-metas #-}
module cgp.ambig.Complete where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉ ; ε∈)

import cgp.ParseTree as ParseTree
open ParseTree using ( U ; EmptyU ; LetterU ; LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unListU
                     ; flat-Uε≡[] ; inv-leftU ; inv-rightU ; inv-pairU
                     ; LeftU≢RightU ; RightU≢LeftU )

import cgp.Word as Word
open Word using (_∈⟦_⟧)

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance*
               ; mkinjList ; mkinjFst ; mkinjSnd ; compose-pdi-with
               ; pdinstance-left ; pdinstance-right ; pdinstance-fst ; pdinstance-star ; mk-snd-pdi )

import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( flat-[] ; mkAllEmptyU ; mkAllEmptyU-complete )

import cgp.posix.PartialDerivative as PosixPD
open PosixPD using ( mkfuseInj ; fuse ; pdinstance-oplus ; injId ; injId-sound )

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using ( Ambig )

import cgp.ambig.Canonic as Canonic

import cgp.ambig.Converse as Converse
open Converse using ( sd ; sd-body ; sd-ε∉ ; sd-s1 ; sd-s2 ; sd-x ; aa ; res-a ; sd-s2-A1 ; sd-Desc₂ )

import cgp.Recons as Recons
open Recons using ( Recons ; Recons* )

open import Data.Char using (Char)
open import Data.Nat using (ℕ; _≟_ ; suc ; zero ; _≤_ ; _+_ ; s≤s ; z≤n)
import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ; ≤-trans ; m≤m+n ; m≤n+m )
open import Data.List using (List; _∷_; _∷ʳ_; []; _++_; map; concatMap; [_]; length)
open import Data.List.Properties using (++-cancelˡ ; ++-identityʳ ; ++-assoc ; length-map ; length-++ )
{-# REWRITE ++-identityʳ #-}
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_×_; _,_; proj₁ ; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong₂ ; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; yes; no)
```

## 1. Two trees identified by one transition map

A transition map is a function `U p → U r` carrying the soundness evidence of
`lift-Ambig`; "the state is ambiguous, witnessed by the transition map" is

```agda
-- two distinct trees of the state that the map identifies
data Collapsed : ∀ {p r : RE} → ( U p → U r ) → Set where
  collapsed : ∀ {p r : RE} ( inj : U p → U r ) ( u v : U p )
    → inj u ≡ inj v → ¬ ( u ≡ v )
    → Collapsed {p} {r} inj

-- hence the state is ambiguous (the two trees have the same word: cancel the
-- path prefix from the soundness evidence of the transition map)
Collapsed→Ambig : ∀ {p r : RE} {w : List Char}
  → ( inj : U p → U r )
  → ( ev : ∀ ( u : U p ) → proj₁ (flat {r} (inj u)) ≡ w ++ proj₁ (flat {p} u) )
  → Collapsed inj → Ambig p
Collapsed→Ambig {p} {r} {w} inj ev (collapsed .inj u v eq u≢v) =
  ( u , v , ( ++-cancelˡ w (proj₁ (flat {p} u)) (proj₁ (flat {p} v))
                (trans (sym (ev u)) (trans (cong (λ x → proj₁ (flat {r} x)) eq) (ev v)))
            , u≢v ) )

-- and the ambiguity of the state lifts to the expression
Collapsed→Ambig-Top : ∀ {p r : RE} {w : List Char}
  → ( inj : U p → U r )
  → ( ev : ∀ ( u : U p ) → proj₁ (flat {r} (inj u)) ≡ w ++ proj₁ (flat {p} u) )
  → ( inj-inj : ∀ ( u v : U p ) → inj u ≡ inj v → u ≡ v )
  → Collapsed inj → Ambig r
Collapsed→Ambig-Top inj ev inj-inj c =
  Canonic.lift-Ambig inj ev inj-inj (Collapsed→Ambig inj ev c)
```

`Canonic.pd*-Ambig→Ambig` applies this to the map stored in a `PDInstance*`;
`Converse.sd-Ambig-from-descendant` is the resulting statement for `sd`.

## 2. Injectivity, and how it is composed

The accessors for the transition map stored in an instance, and the
injectivity predicates used in the rest of the module:

```agda
pdx : ∀ { r : RE } { pref : List Char } → ( pdi : PDInstance* r pref ) → RE
pdx (pdinstance* {p} inj ev) = p

pdi-inj : ∀ { r : RE } { pref : List Char } ( pdi : PDInstance* r pref )
  → U (pdx pdi) → U r
pdi-inj (pdinstance* {p} inj ev) = inj

pd1-expr : ∀ { r : RE } { c : Char } → ( pdi : PDInstance r c ) → RE
pd1-expr (pdinstance {p} inj ev) = p

pd1-inj : ∀ { r : RE } { c : Char } ( pdi : PDInstance r c )
  → U (pd1-expr pdi) → U r
pd1-inj (pdinstance {p} inj ev) = inj

-- the transition map of an instance identifies no two distinct trees
PInj : ∀ { r : RE } { pref : List Char } → ( pdi : PDInstance* r pref ) → Set
PInj {r} {pref} pdi = ∀ ( u v : U (pdx pdi) ) → pdi-inj pdi u ≡ pdi-inj pdi v → u ≡ v

Inj₁ : ∀ { r : RE } { c : Char } → ( pdi : PDInstance r c ) → Set
Inj₁ {r} {c} pdi = ∀ ( u v : U (pd1-expr pdi) ) → pd1-inj pdi u ≡ pd1-inj pdi v → u ≡ v

-- composing injective maps (the shape of a pd path: compose-pdi-with chains the
-- path map d→r in front of the one-step map p→d).  Extending a path this way
-- never introduces an identification: an identification made by the composed
-- map was already made by the one-step map
comp-inj : ∀ { p d r : RE }
  → ( d→r : U d → U r ) → ( p→d : U p → U d )
  → ( ∀ ( u v : U p ) → p→d u ≡ p→d v → u ≡ v )
  → ( ∀ ( u v : U d ) → d→r u ≡ d→r v → u ≡ v )
  → ∀ ( u v : U p ) → d→r (p→d u) ≡ d→r (p→d v) → u ≡ v
comp-inj d→r p→d p→d-inj d→r-inj u v eq = p→d-inj u v (d→r-inj (p→d u) (p→d v) eq)
```

## 3. The transition map of each `PDInstance` builder

These are the steps of the induction "no criterion fires ⇒ every transition map
is injective", one per pd construction.  They are stated for the map, not for
the instance, because a computed instance cannot be named (§4).

```agda
-- the empty path
injId-inj : ∀ { r : RE } → ∀ ( u v : U r ) → injId u ≡ injId v → u ≡ v
injId-inj u v eq = eq

-- the disjoint sum of two maps: the map built by `fuse`/`pdinstance-oplus`.
-- The two branches are only disjoint as trees of the *state* (LeftU/RightU);
-- their images under the branch maps can be equal — and if they are, the two
-- distinct trees LeftU u / RightU v of the state are identified, i.e. r is
-- ambiguous.  So injectivity of the fused map needs injectivity of the branch
-- maps *and* disjointness of their ranges; the latter is exactly the
-- Antimirov-disjointness half that this formalisation does not have yet (§4)
mkfuseInj-inj : ∀ { pˡ pʳ r : RE } { loc : ℕ }
  → ( inj-l : U pˡ → U r ) → ( inj-r : U pʳ → U r )
  → ( ∀ ( u v : U pˡ ) → inj-l u ≡ inj-l v → u ≡ v )
  → ( ∀ ( u v : U pʳ ) → inj-r u ≡ inj-r v → u ≡ v )
  → ( ranges-disjoint : ( u : U pˡ ) → ( v : U pʳ ) → ¬ ( inj-l u ≡ inj-r v ) )
  → ∀ ( u v : U (pˡ + pʳ ` loc) )
  → mkfuseInj inj-l inj-r u ≡ mkfuseInj inj-l inj-r v → u ≡ v
mkfuseInj-inj {pˡ} {pʳ} inj-l inj-r inj-l-inj inj-r-inj disjoint (LeftU u)  (LeftU v)  eq =
  cong LeftU (inj-l-inj u v eq)
mkfuseInj-inj {pˡ} {pʳ} inj-l inj-r inj-l-inj inj-r-inj disjoint (LeftU u)  (RightU v) eq =
  ⊥-elim (disjoint u v eq)
mkfuseInj-inj {pˡ} {pʳ} inj-l inj-r inj-l-inj inj-r-inj disjoint (RightU u) (LeftU v) eq =
  ⊥-elim (disjoint v u (sym eq))
mkfuseInj-inj {pˡ} {pʳ} inj-l inj-r inj-l-inj inj-r-inj disjoint (RightU u) (RightU v) eq =
  cong RightU (inj-r-inj u v eq)

-- from a cons equality, the head / tail equalities
∷-head : ∀ {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → x ≡ y
∷-head refl = refl

∷-tail : ∀ {A : Set} {x y : A} {xs ys : List A} → x ∷ xs ≡ y ∷ ys → xs ≡ ys
∷-tail refl = refl

-- the star extension (paper: deriv r* x = deriv r x · r*).  The map turns the
-- pair into a ListU-cons, so injectivity reads off the list: unListU, then the
-- head and tail equalities
mkinjList-inj : ∀ { r' r : RE } { nε : ε∉ r } { loc : ℕ }
  → ( f : U r' → U r )
  → ( ∀ ( u v : U r' ) → f u ≡ f v → u ≡ v )
  → ∀ ( u v : U (r' ● (r * nε ` loc) ` loc) )
  → mkinjList f u ≡ mkinjList f v → u ≡ v
mkinjList-inj {r'} {r} {nε} {loc} f f-inj (PairU v (ListU vs)) (PairU w (ListU ws)) eq
  with cong unListU eq
...   | xs≡ys =
    cong₂ (PairU {l = r'} {r * nε ` loc} {loc})
          (f-inj v w (∷-head xs≡ys)) (cong ListU (∷-tail xs≡ys))

-- concatenating a fixed tree on the left / on the right (the maps of
-- pdinstance-snd / pdinstance-fst).  The fixed component is unique when the
-- other factor has a single empty parse tree — the A1/A2 side condition, which
-- is where mkAllEmptyU's length enters
pairL-inj : ∀ { p l r : RE } { loc : ℕ } { t : U r }
  → ( f : U p → U l )
  → ( ∀ ( u v : U p ) → f u ≡ f v → u ≡ v )
  → ∀ ( u v : U p ) → PairU {l} {r} {loc} (f u) t ≡ PairU (f v) t → u ≡ v
pairL-inj {p} {l} {r} {loc} {t} f f-inj u v eq
  with inv-pairU {l = l} {r} {loc} _ _ _ _ eq
...   | fu≡fv , _ = f-inj u v fu≡fv

pairR-inj : ∀ { p l r : RE } { loc : ℕ } { t : U l }
  → ( f : U p → U r )
  → ( ∀ ( u v : U p ) → f u ≡ f v → u ≡ v )
  → ∀ ( u v : U p ) → PairU {l} {r} {loc} t (f u) ≡ PairU t (f v) → u ≡ v
pairR-inj {p} {l} {r} {loc} {t} f f-inj u v eq
  with inv-pairU {l = l} {r} {loc} _ _ _ _ eq
...   | _ , fu≡fv = f-inj u v fu≡fv

-- the concatenation maps of pdinstance-fst and mk-snd-pdi: the pair inversion
-- handles both components
mkinjFst-inj : ∀ { p l r : RE } { loc : ℕ }
  → ( f : U p → U l )
  → ( ∀ ( u v : U p ) → f u ≡ f v → u ≡ v )
  → ∀ ( u v : U (p ● r ` loc) ) → mkinjFst f u ≡ mkinjFst f v → u ≡ v
mkinjFst-inj {p} {l} {r} {loc} f f-inj (PairU a vs) (PairU b ws) eq
  with inv-pairU {l = l} {r} {loc} _ _ _ _ eq
...   | a≡b , vs≡ws = cong₂ (PairU {l = p} {r} {loc}) (f-inj a b a≡b) vs≡ws

mkinjSnd-inj : ∀ { p l r : RE } { loc : ℕ } { e : U l }
  → ( f : U p → U r )
  → ( ∀ ( u v : U p ) → f u ≡ f v → u ≡ v )
  → ∀ ( u v : U p ) → mkinjSnd {l} {r} {p} {loc} f e u ≡ mkinjSnd f e v → u ≡ v
mkinjSnd-inj {p} {l} {r} {loc} {e} f f-inj u v eq = pairR-inj f f-inj u v eq

-- the two sum injections (pdinstance-left / pdinstance-right)
leftU-inj : ∀ { l r : RE } { loc : ℕ } → ∀ ( u v : U l ) → LeftU {l} {r} {loc} u ≡ LeftU v → u ≡ v
leftU-inj u v = inv-leftU u v

rightU-inj : ∀ { l r : RE } { loc : ℕ } → ∀ ( u v : U r ) → RightU {l} {r} {loc} u ≡ RightU v → u ≡ v
rightU-inj u v = inv-rightU u v
```

## 4. What still separates this from a proof for `sd`

The completeness argument for `sd` and the word `a a` would be: two distinct
trees (Converse §2), the instance of `pdUMany[ sd , a a ]` reconstructs both
(§4.1), hence the state is ambiguous by §1, and the path map is injective by
§2–§3 — where the fusion step of §3 additionally needs the range disjointness
of §4.1.  Two things are missing.

**4.1 Uniqueness (Antimirov disjointness).**  The project proves *existence*:
`pdUMany-complete` (Lemma 23) gives `Any (Recons* u) (pdUMany[ r , |u| ])`.
Two distinct trees may be reconstructed by *different* instances, and then no
single state is ambiguous — which is exactly what the reconstruction relation
`Recons*` of `cgp.Recons` does not exclude.  The missing statement, for a fixed
word, is that distinct instances have disjoint tree sets.  This is also the one
side condition of §3 that cannot be discharged locally: `mkfuseInj-inj` has to
assume the two branch ranges disjoint (the branch trees are only distinct as
trees of the state, `LeftU u ≢ RightU v`; whether their images coincide is a
fact about `r`, not about the node).  The general form is an induction along
`pdU`, parallel to the existing `pdU-complete`/`pdUMany-complete` proofs.

**4.2 A computed instance cannot be named by `with`, but it can be mirrored.**
The injectivity proofs of §3 are about maps; to use one for a transition map
of `pdU` the instance has to be a term.  Naming it by *matching* fails:
the definitions

    pdUMany-sd-aa-named : PDInstance* sd aa
    pdUMany-sd-aa-named with PosixPD.pdUMany[ sd , aa ]
    ...   | pdi ∷ [] = pdi

    pdU-sd-s1-a-named : PDInstance sd-s1 'a'
    pdU-sd-s1-a-named with PosixPD.pdU[ sd-s1 , 'a' ]
    ...   | pdi ∷ [] = pdi

are rejected with `Missing cases: [] / x ∷ x₁ ∷ w`: nothing in the type of
those lists rules the other shapes out (being a singleton is a computational
fact, not a typing fact), so the case split cannot be closed.  And the
parametric substitute does not work either: given `pdis ≡ pdU[ … ]` and
`pdis ≡ pdi ∷ []` for *variables*, the goal `pd-expr pdi ≡ sd-s2` is not `refl`
— an equation about a list cannot rewrite the field of an abstract instance.

What closes the gap is §5: *build the instance the way `pdU` computes it* —
run the same case analysis by hand (`ε∈? res-a = yes`, `'a' ≟ 'a' = yes`, the
one empty parse tree of `res-a`) through the same constructors — and check by
`refl` that the computed list equals the singleton containing it.  Two facts
about `sd` that the rest needs, the list as a whole being computational:

```agda
-- the state after `a a`, as a computed list (Converse.sd-Desc₂)
sd-aa-state : Canonic.pd*-Desc sd aa ≡ ( sd-s2 ∷ [] )
sd-aa-state = refl

-- and A1 holds at it: the state is nullable twice over (Converse.sd-s2-A1)
sd-aa-A1 : AmbigCheck.AmbigA1 sd-s2
sd-aa-A1 = sd-s2-A1
```

With the named instance of §5 in hand, §3 gives injectivity of its map once
the range-disjointness of its `+` node is discharged (`mkfuseInj-inj` is the
only step that is not local — §4.1); §6 discharges it for this node and §7
then gives `Ambig sd`, the criterion that fires being `A1`, as computed by
`Converse.sd-s2-criteria`.

## 5. Naming the instances of `a` and `a a`

Mirroring the computation of `pdU[ sd-s1 , 'a' ]` and `pdUMany[ sd , a a ]`.
The pieces, in computation order: the three letter instances; the one-step
instance of `res-a = ε + (ε · a) ` 5` (only the right summand matches `a`, and
`ε · a` derives to `ε` through its empty tree `EmptyU`); then the two
branches of the concatenation node `res-a · r⋆ ` 6` of `sd-s1`:

* the left branch `pdinstance-fst`: a first `a` consumed inside `res-a`,
  continuation `sd-x = ε · r⋆`;
* the right branch `concatmap-pdinstance-snd`: nothing consumed in `res-a`
  (its empty parse tree `LeftU EmptyU` is carried along — this is a
  *singleton*, `ε · a` is not nullable), and `a` consumed inside `r⋆`, i.e.
  `pdinstance-star` of `pdU[ r , a ]`, continuation `sd-s1`.

`pdinstance-oplus` fuses the two branches (`fuse`), and the single resulting
instance has continuation `sd-x + sd-s1 ` 6 = sd-s2`.

```agda
-- the three letter instances (the two locations of r = a + a · a, and the a
-- inside res-a); the ev proof is copied verbatim from pdU's clause so the
-- comparisons below hold definitionally
letter-pdi : ∀ { loc : ℕ } → PDInstance ($ 'a' ` loc) 'a'
letter-pdi {loc} with (loc ≟ loc)
...   | yes refl = pdinstance {ε} {$ 'a' ` loc} {'a'}
                     (λ u → LetterU {loc} 'a')
                     (λ u → begin
                              [ 'a' ]
                            ≡⟨⟩
                              'a' ∷ []
                            ≡⟨ cong ( λ x → ( 'a' ∷  x) ) (sym (flat-Uε≡[] u)) ⟩
                              'a' ∷ (proj₁ (flat u))
                            ∎)
...   | no  ¬a   = ⊥-elim (¬a refl)

-- the one-step instance of res-a = ε + (ε · a) ` 5 : only the right summand
-- matches 'a'; ε · a derives to ε through its empty tree EmptyU
snd-₃ : PDInstance (ε ● ($ 'a' ` 3) ` 4) 'a'
snd-₃ = mk-snd-pdi {ε} {($ 'a' ` 3)} {4} {'a'} (EmptyU , flat-[] EmptyU refl) (letter-pdi {3})

r-res : PDInstance res-a 'a'
r-res = pdinstance-right {ε} {(ε ● ($ 'a' ` 3) ` 4)} {5} {'a'} snd-₃

-- the left branch of pdU[ res-a · r⋆ ` 6 , 'a' ]: continuation sd-x = ε · r⋆
pdi-L : PDInstance sd-s1 'a'
pdi-L = pdinstance-fst {res-a} {sd} {6} {'a'} r-res

-- the one-step instance of r⋆ = sd: pdinstance-star of the fused instance of
-- r = a + a · a (both summands match 'a', oplus fuses them into res-a · r⋆)
o₅ : List (PDInstance sd-body 'a')
o₅ = pdinstance-oplus {sd-body} {5} {'a'}
       ( map (pdinstance-left  {($ 'a' ` 1)} {(($ 'a' ` 2) ● ($ 'a' ` 3) ` 4)} {5} {'a'}) [ letter-pdi {1} ] )
       ( map (pdinstance-right {($ 'a' ` 1)} {(($ 'a' ` 2) ● ($ 'a' ` 3) ` 4)} {5} {'a'})
               [ pdinstance-fst {($ 'a' ` 2)} {($ 'a' ` 3)} {4} {'a'} (letter-pdi {2}) ] )

-- head of a computed list, with fallbacks for the (impossible here) empty /
-- longer shapes: with-abstraction cannot name the head (§4.2), a total helper
-- can; the refl checks below confirm the branch the computation takes
head-or : ∀ {A : Set} → A → List A → A
head-or d []       = d
head-or d (x ∷ _)  = x

star-fallback : PDInstance sd-body 'a'
star-fallback = pdinstance {ε} {sd-body} {'a'}
                  (λ u → LeftU {($ 'a' ` 1)} {(($ 'a' ` 2) ● ($ 'a' ` 3) ` 4)} {5} (LetterU {1} 'a'))
                  (λ EmptyU → cong (λ x → 'a' ∷ x) (sym (flat-Uε≡[] EmptyU)))

star-sd : PDInstance sd 'a'
star-sd = pdinstance-star {sd-body} {sd-ε∉} {6} {'a'} (head-or star-fallback o₅)

-- the right branch of pdU[ sd-s1 , 'a' ]: res-a contributes its single empty
-- parse tree LeftU EmptyU, the letter is consumed inside r⋆; continuation sd-s1
pdi-R : PDInstance sd-s1 'a'
pdi-R = mk-snd-pdi {res-a} {sd} {6} {'a'}
          ( LeftU {ε} {(ε ● ($ 'a' ` 3) ` 4)} {5} EmptyU , flat-[] _ refl) star-sd

-- pdU[ sd-s1 , 'a' ] is exactly the fused pair: one instance, continuation sd-s2
pdi-s1 : PDInstance sd-s1 'a'
pdi-s1 = fuse {sd-s1} {6} {'a'} pdi-L pdi-R

pdu-s1≡ : ( PosixPD.pdU[ sd-s1 , 'a' ] ) ≡ ( pdi-s1 ∷ [] )
pdu-s1≡ = refl

pd-pdi-s1 : Canonic.pd-expr pdi-s1 ≡ sd-s2
pd-pdi-s1 = refl

-- the path instance for the prefix `a` (the star extension of pdU[ r , a ],
-- composed onto the empty path), and the two-step instance for `a a`
path-a : PDInstance* sd ( 'a' ∷ [] )
path-a = compose-pdi-with {sd} {sd} {[]} {'a'} injId injId-sound star-sd

pdi₂ : PDInstance* sd aa
pdi₂ = compose-pdi-with {sd} {sd-s1} { 'a' ∷ [] } {'a'}
         (Canonic.pd*-inj path-a) (Canonic.pd*-ev path-a) pdi-s1

pd-pdi₂ : Canonic.pd*-expr pdi₂ ≡ sd-s2
pd-pdi₂ = refl

pdUMany-sd-aa≡ : ( PosixPD.pdUMany[ sd , aa ] ) ≡ ( pdi₂ ∷ [] )
pdUMany-sd-aa≡ = refl
```

So `Converse.sd-Ambig-from-descendant` applied to `pdi₂` and `pd-pdi₂` has a
non-vacuous instance; what remains for the completeness direction at this
example is exactly its last hypothesis — injectivity of `pd*-inj pdi₂` —
which §6 discharges by running §3 along the builders of §5.

## 6. Injectivity of the named instances

Case analysis along the constructed instances.  The only place where §3's
non-local side condition (`mkfuseInj-inj`'s range disjointness, §4.1) has to
be faced is the fusion `pdi-s1 = fuse pdi-L pdi-R`; there it is discharged by
the *constructor heads* of the two branch images: the left branch consumes its
letter inside `res-a`, so its image re-enters `res-a` through the `a`-summand
(`RightU (PairU EmptyU (LetterU 'a'))` as first component), while the right
branch carries `res-a`'s empty parse tree through the `ε`-summand
(`LeftU EmptyU`).  The two heads are different constructors of
`U res-a` (`RightU≢LeftU`), so no image can be shared — this is the instance
of Antimirov disjointness that this example needs, proved by inspection rather
than by the general lemma §4.1 leaves open.

```agda
-- U ε has one element
ε-unique : ∀ ( u v : U ε ) → u ≡ v
ε-unique EmptyU EmptyU = refl

-- the fused one-step instance of r = a + a · a (head of the computed o₅):
-- its pd is res-a, its map sends LeftU to the letter of a, RightU to the
-- pair of two letters inside a · a
o₅head : PDInstance sd-body 'a'
o₅head = head-or star-fallback o₅

o₅-LL : ( u v : U ε ) → pd1-inj o₅head (LeftU u) ≡ pd1-inj o₅head (LeftU v) → u ≡ v
o₅-LL u v eq = ε-unique u v

o₅-LR : ( u : U ε ) ( v : U (ε ● ($ 'a' ` 3) ` 4) )
  → pd1-inj o₅head (LeftU u) ≡ pd1-inj o₅head (RightU v) → ⊥
o₅-LR u v eq = ⊥-elim (LeftU≢RightU _ _ eq)

o₅-RL : ( u : U ε ) ( v : U (ε ● ($ 'a' ` 3) ` 4) )
  → pd1-inj o₅head (RightU v) ≡ pd1-inj o₅head (LeftU u) → ⊥
o₅-RL u v eq = ⊥-elim (LeftU≢RightU _ _ (sym eq))

o₅-RR : ( v w : U (ε ● ($ 'a' ` 3) ` 4) )
  → pd1-inj o₅head (RightU v) ≡ pd1-inj o₅head (RightU w) → v ≡ w
o₅-RR (PairU a vs) (PairU b ws) eq =
  cong₂ (PairU {l = ε} {($ 'a' ` 3)} {4}) (ε-unique a b)
        (proj₂ (inv-pairU {l = ($ 'a' ` 2)} {($ 'a' ` 3)} {4} _ _ _ _
                  (inv-rightU {l = ($ 'a' ` 1)} {(($ 'a' ` 2) ● ($ 'a' ` 3) ` 4)} {5} _ _ eq)))

o₅head-inj : Inj₁ o₅head
o₅head-inj u v eq with u | v
...   | LeftU  x | LeftU  y = cong LeftU (o₅-LL x y eq)
...   | LeftU  x | RightU y = ⊥-elim (o₅-LR x y eq)
...   | RightU x | LeftU  y = ⊥-elim (o₅-RL y x eq)
...   | RightU x | RightU y = cong RightU (o₅-RR x y eq)

-- the star extension r⋆ = sd: injective along mkinjList
star-inj : Inj₁ star-sd
star-inj = mkinjList-inj (pd1-inj o₅head) o₅head-inj

-- both branches of pdU[ sd-s1 , 'a' ]: the first-factor branch (r-res has
-- only the empty tree of ε as domain) and the star-extension branch
r-res-inj : Inj₁ r-res
r-res-inj u v eq with u | v
...   | EmptyU | EmptyU = refl

pdi-L-inj : Inj₁ pdi-L
pdi-L-inj = mkinjFst-inj (pd1-inj r-res) r-res-inj

pdi-R-inj : Inj₁ pdi-R
pdi-R-inj = mkinjSnd-inj (pd1-inj star-sd) star-inj

-- range disjointness of the fusion, by the argument above
s1-disj : ( u : U sd-x ) ( v : U sd-s1 ) → ¬ ( pd1-inj pdi-L u ≡ pd1-inj pdi-R v )
s1-disj (PairU a t) (PairU b t′) eq =
  ⊥-elim (RightU≢LeftU _ _ (proj₁ (inv-pairU {l = res-a} {r = sd} {loc = 6} _ _ _ _ eq)))

pdi-s1-inj : Inj₁ pdi-s1
pdi-s1-inj = mkfuseInj-inj {pˡ = sd-x} {pʳ = sd-s1} {r = sd-s1} {loc = 6}
               (pd1-inj pdi-L) (pd1-inj pdi-R) pdi-L-inj pdi-R-inj s1-disj

-- the path instance for `a` composes the identity path map with star-sd, and
-- pdi₂ chains pdi-s1 behind it: §2's composition lemma closes the chain
patha-inj : ∀ ( u v : U (Canonic.pd*-expr path-a) )
  → Canonic.pd*-inj path-a u ≡ Canonic.pd*-inj path-a v → u ≡ v
patha-inj = comp-inj (injId) (pd1-inj star-sd) star-inj injId-inj

pdi₂-inj : PInj pdi₂
pdi₂-inj = comp-inj (Canonic.pd*-inj path-a) (pd1-inj pdi-s1) pdi-s1-inj patha-inj
```

## 7. `Ambig sd` from A1 at the state

With the instance of §5 and its injectivity from §6,
`Converse.sd-Ambig-from-descendant` — the state-level criterion (`A1` at
`sd-s2`, `Converse.sd-s2-A1`) lifted along a transition map — applies:

```agda
sd-Ambig-from-A1-at-state : Ambig sd
sd-Ambig-from-A1-at-state = Converse.sd-Ambig-from-descendant pdi₂ pd-pdi₂ pdi₂-inj
```

This is one direction of the paper's proposition, for this example: a
criterion that fires at a reached state is a *genuine* ambiguity of `r`.  The
witness is the pair of distinct trees of `sd-s2` that `A1→Ambig` extracts
from A1 there (§1's `Collapsed` witness is what the `lift-Ambig` inside
`pd*-A1→Ambig` consumes); `pdi₂-inj` (§6) is what makes their images in
`U sd` distinct — without injectivity the state witness could collapse to one
tree of `r`.  *Which ambiguity pairs arise this way* — the reverse direction,
the completeness direction proper — is the goal stated in §8.

## 8. The goal: the completeness direction, stated

Both readings separated at the top of `cgp.ambig.Converse` —

> `Ambig r` ⇒ there is a state at which A1, A2 or the `Idemp` duplicate fires

— stated once, here, with an unchecked body, before going further.  Two
levels, since the general one needs machinery this project does not have.

**The general statement** (the paper's proposition, section 6): given an
ambiguity of `r` — two distinct parse trees for one word — the word has a
prefix whose pd-states include one at which a criterion fires.  The third
disjunct is the `Idemp`/A3 *pattern* (a sum with `≈₀`-equal members under a
hole context — the shape `Canonic.Ctx-dup→Ambig` consumes); A3 proper is not
formalized (`AmbigCheck` §4).

```agda
completeness : ∀ { r : RE }
  → ( u v : U r )
  → proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) → ¬ ( u ≡ v )
  → ∃[ w′ ] ∃[ w″ ]
      ( ( proj₁ (flat {r} u) ≡ w′ ++ w″ )
      × ∃[ p ]
          ( Any ( λ s → s ≡ p ) (Canonic.pd*-Desc r w′)
          × ( AmbigCheck.AmbigA1 p
            ⊎ AmbigCheck.AmbigA2 p
            ⊎ Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
                  ( ( AmbigCheck.plug ctx ( l + s ` loc ) ≡ p )
                  × ( Canonic._≈₀_ l s ) ) ) ) )
completeness u v w≡ u≢v = _
```

To fill this for an *arbitrary* pair `( u , v )` one has to *find* the
prefix `w′` — the paper's `AllParseFST` argument over parse trees of the
word.  It is not formalized here (like the realizable-states / FST side of
the paper), and this is the actual research gap of the program, beyond §4.1.

**The reading tied to a given pair, for this `r`** (what §5–§6 built the
machinery for): every ambiguity pair of `sd` for the word `aa` is the image,
under the transition map of the single instance of `pdUMany[ sd , aa ]`, of a
pair of distinct trees of the state that word reaches — and A1 fires there
(`sd-s2-A1`, with `pdUMany-sd-aa≡` naming the instance and `pd-pdi₂` its
continuation, §5).  Given `u ≢ v` the pair `( u′ , v′ )` is automatically
distinct (a function sends distinct outputs to distinct inputs); §6's
`pdi₂-inj` gives the converse, and both together say the ambiguity *is* the
state's A1 witness, not an artifact of the map.

```agda
sd-completeness-at-the-state :
    ( u v : U sd )
  → proj₁ (flat {sd} u) ≡ aa → proj₁ (flat {sd} v) ≡ aa → ¬ ( u ≡ v )
  → ∃[ u′ ] ∃[ v′ ]
      ( ( Canonic.pd*-inj pdi₂ u′ ≡ u ) × ( Canonic.pd*-inj pdi₂ v′ ≡ v )
      × ¬ ( u′ ≡ v′ ) )
sd-completeness-at-the-state u v w≡ w′≡ u≢v = _
```

Its input pieces all exist: `pdU-complete`/`pdUMany-complete`
(`cgp.posix.PartialDerivative`) put every tree with word `aa` in the image of
*some* instance of `pdUMany[ sd , aa ]`; `pdUMany-sd-aa≡` says that instance
is `pdi₂`; extracting the field of `Recons*` gives `u′ , v′`
(`cgp.Recons`: `recons*` is literally an equation `inj (unflat w∈⟦p⟧) ≡ u`).
Deriving `flat u′ ≡ []` and `flat v′ ≡ []` from the soundness evidence makes
them the empty trees A1 counts.  So unlike the general statement, this one is
a proof exercise, not a research gap — left as a hole until the statement is
agreed.

## 9. Toward the general proof: the base case of the descent

The general `completeness` above is proved by following the two trees through
their common word letter by letter (the paper's `AllParseFST` argument).  Its
base case — the word is consumed, what remains are two distinct *empty* parse
trees of the state reached — forces A1 *at that state*, for every expression.
Formalized here, for arbitrary `r`:

```agda
-- a list with two distinct members has length ≥ 2
two-distinct-members→len≥2 : ∀ {A : Set} {x y : A} ( xs : List A )
  → Any ( λ z → x ≡ z ) xs → Any ( λ z → y ≡ z ) xs → ¬ ( x ≡ y )
  → suc (suc zero) ≤ length xs
two-distinct-members→len≥2 (x ∷ x₁ ∷ xs) _ _ _ = s≤s (s≤s z≤n)
two-distinct-members→len≥2 (x ∷ []) (here refl) (here refl) x≢y = ⊥-elim (x≢y refl)
two-distinct-members→len≥2 (x ∷ []) (here p) (there ()) _
two-distinct-members→len≥2 (x ∷ []) (there ()) _ _
two-distinct-members→len≥2 [] () _ _

-- two distinct parse trees of r for the empty word ⇒ A1 fires at r
base-A1-at-root : ( r : RE ) ( u v : U r )
  → proj₁ (flat {r} u) ≡ [] → proj₁ (flat {r} v) ≡ [] → ¬ ( u ≡ v )
  → AmbigCheck.AmbigA1 r
base-A1-at-root r u v u≡[] v≡[] u≢v = ( ε∈r , two-distinct-members→len≥2 list u∈ v∈ u≢v )
  where
    ε∈r : ε∈ r
    ε∈r = Word.[]∈⟦r⟧→ε∈r (subst ( λ w → w ∈⟦ r ⟧) u≡[] (proj₂ (flat {r} u)))
    list = mkAllEmptyU {r} ε∈r
    u∈ : Any ( λ z → u ≡ z ) list
    u∈ = mkAllEmptyU-complete ε∈r u (flat-[] u u≡[])
    v∈ : Any ( λ z → v ≡ z ) list
    v∈ = mkAllEmptyU-complete ε∈r v (flat-[] v v≡[])
```

(`u ∈ mkAllEmptyU` is `Any (u ≡_)` by definition of `List._∈_` — the
membership `mkAllEmptyU-complete` produces is used directly.)

The step case of the descent — given a pair at word `c ++ cs`, move both
trees across the letter `c` and recurse on `cs` — is where the Antimirov
nondeterminism bites: the two trees may cross `c` through *different*
instances of `pdU[ r , c ]`, into *different* continuation states, so the
recursion has to run on a pair of states as in the paper's `AllParseFST`;
the criteria then have to be found from a pair-derivation whose two sides
eventually merge or split (the merge = A1 by the base case just proved; a
split at a sum or a duplicated subterm = A2 / the `Idemp` pattern).  That
machinery is what remains to build; the base case above is already exactly
its stopping rule.

## 10. Walking pd paths (the descent's plumbing)

The letter step of the descent reads an IH that lives at a *continuation
state* and must be heard from the *whole expression*: if the word `pref`
reaches the instance `pdi` of `r` (`pdi ∈ pdUMany[ r , pref ]`) and from
`pdi` the suffix `suff` reaches the state `p`, then `p` is a pd-descendant of
`r` for the concatenated word —

> `pdi ∈ pdUMany[ r , pref ]` and `p ∈ Canonic.pd*-Desc (pd r pref) suff`
> together imply `p ∈ Canonic.pd*-Desc r (pref ++ suff)` .

Formally: a chain of advances `chain*` from a single instance — the same
recursion as `pdUMany-aux` but started from one instance — lands inside the
member list of any advancement run containing that instance (`any-aux`), and
membership of the chain's `pd` fields transfers to `pd*-Desc` of the
concatenation (`chain-in-aux`, induction on `pref`; the `pref = []` base uses
the same `rewrite (++-identityʳ …)` device as `pdUMany-aux-complete`'s base
case in `cgp.posix.PartialDerivative`).  The index plumbing needs the
`++-identityʳ` equation added as a rewrite rule next to the project-wide
`∷ʳ-++`; both are used exactly as `pdUMany-aux` itself uses them.

```agda
-- concatMap f distributes over ++
concatMap-++ : ∀ {A B : Set} (f : A → List B) (xs ys : List A)
  → concatMap f (xs ++ ys) ≡ concatMap f xs ++ concatMap f ys
concatMap-++ f [] ys = refl
concatMap-++ f (x ∷ xs) ys = trans
  ( cong (f x ++_) (concatMap-++ f xs ys) )
  ( sym (++-assoc (f x) (concatMap f xs) (concatMap f ys)) )

-- pointwise equal maps, under one concatMap
concatMap-cong-λ : ∀ {A B : Set} (zs : List A) (f g : A → List B)
  → ( ∀ x → f x ≡ g x ) → concatMap f zs ≡ concatMap g zs
concatMap-cong-λ [] f g f≡g = refl
concatMap-cong-λ (z ∷ zs) f g f≡g = cong₂ _++_ (f≡g z) (concatMap-cong-λ zs f g f≡g)

concatMap-compose : ∀ {A B C : Set} (f : B → List C) (g : A → List B) (zs : List A)
  → concatMap f (concatMap g zs) ≡ concatMap (λ z → concatMap f (g z)) zs
concatMap-compose f g [] = refl
concatMap-compose f g (z ∷ zs) = trans
  ( concatMap-++ f (g z) (concatMap g zs) )
  ( cong (concatMap f (g z) ++_) (concatMap-compose f g zs) )

-- concatMap of singletons is the identity
concatMap-∷[]-id : ∀ {A : Set} (ys : List A)
  → concatMap (λ x → x ∷ []) ys ≡ ys
concatMap-∷[]-id [] = refl
concatMap-∷[]-id (y ∷ ys) = cong (y ∷_) (concatMap-∷[]-id ys)

-- membership in a concatenated list, from membership in either part
any-mid : ∀ {A : Set} {P : A → Set} {ys zs : List A} (xs : List A)
  → Any P (ys ++ zs) → Any P (xs ++ (ys ++ zs))
any-mid {ys = ys} {zs = zs} [] p = p
any-mid {ys = ys} {zs = zs} (x ∷ xs) p = there (any-mid {ys = ys} {zs = zs} xs p)

any++₁ : ∀ {A : Set} {P : A → Set} {xs ys : List A}
  → Any P xs → Any P (xs ++ ys)
any++₁ {xs = x ∷ xs} {ys = ys} (here p) = here p
any++₁ {xs = x ∷ xs} {ys = ys} (there p) = there (any++₁ {xs = xs} {ys = ys} p)

map-Any : ∀ {A B : Set} (f : A → B) {P : A → Set} {Q : B → Set}
  → (∀ x → P x → Q (f x)) → {xs : List A} → Any P xs → Any Q (map f xs)
map-Any f P→Q (here p) = here (P→Q _ p)
map-Any f P→Q (there p) = there (map-Any f P→Q p)

-- a member splits its list around it
∈-split : ∀ {A : Set} (ys : List A) (x : A) → x ∈ ys
  → ∃[ xs ] ∃[ zs ] ( xs ++ (x ∷ zs) ≡ ys )
∈-split [] x ()
∈-split (y ∷ ys) x (here refl) = ([] , ys , refl)
∈-split (y ∷ ys) x (there m) with ∈-split ys x m
... | ( xs , zs , eq ) = (y ∷ xs , zs , cong (y ∷_) eq)

-- advancing runs respect concatenation of instance lists, concatMaps and conses
aux-++ : ∀ {r : RE} {pref : List Char} (suff : List Char)
  → (xs ys : List (PDI.PDInstance* r pref))
  → PosixPD.pdUMany-aux {r} {pref} suff (xs ++ ys)
    ≡ PosixPD.pdUMany-aux {r} {pref} suff xs ++ PosixPD.pdUMany-aux {r} {pref} suff ys
aux-++ {r} {pref} [] xs ys rewrite ++-identityʳ pref = refl
aux-++ {r} {pref} (c ∷ cs) xs ys = trans
  ( cong (λ l → PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs l)
         (concatMap-++ (PosixPD.advance-pdi*-with-c {r} {pref} {c}) xs ys) )
  ( aux-++ {r} {pref ∷ʳ c} cs
      (concatMap (PosixPD.advance-pdi*-with-c {r} {pref} {c}) xs)
      (concatMap (PosixPD.advance-pdi*-with-c {r} {pref} {c}) ys) )

aux-concatMap : ∀ {r : RE} {pref : List Char} (suff : List Char)
  → {A : Set} (g : A → List (PDI.PDInstance* r pref)) (zs : List A)
  → PosixPD.pdUMany-aux {r} {pref} suff (concatMap g zs)
    ≡ concatMap (λ z → PosixPD.pdUMany-aux {r} {pref} suff (g z)) zs
aux-concatMap {r} {pref} [] g zs rewrite ++-identityʳ pref = refl
aux-concatMap {r} {pref} (c ∷ cs) g zs = trans
  ( cong (λ l → PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs l)
         (concatMap-compose (PosixPD.advance-pdi*-with-c {r} {pref} {c}) g zs) )
  ( trans ( aux-concatMap {r} {pref ∷ʳ c} cs
              (λ z → concatMap (PosixPD.advance-pdi*-with-c {r} {pref} {c}) (g z)) zs )
          ( concatMap-cong-λ zs
              (λ z → PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs
                       (concatMap (PosixPD.advance-pdi*-with-c {r} {pref} {c}) (g z)))
              (λ z → PosixPD.pdUMany-aux {r} {pref} (c ∷ cs) (g z))
              (λ z → refl) ) )

aux-cons : ∀ {r : RE} {pref : List Char} (suff : List Char)
  → (pdi : PDI.PDInstance* r pref) (zs : List (PDI.PDInstance* r pref))
  → PosixPD.pdUMany-aux {r} {pref} suff (pdi ∷ zs)
    ≡ PosixPD.pdUMany-aux {r} {pref} suff (pdi ∷ [])
      ++ PosixPD.pdUMany-aux {r} {pref} suff zs
aux-cons {r} {pref} [] pdi zs rewrite ++-identityʳ pref = refl
aux-cons {r} {pref} (c ∷ cs) pdi zs = trans
  ( aux-++ {r} {pref ∷ʳ c} cs
      (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi)
      (concatMap (PosixPD.advance-pdi*-with-c {r} {pref} {c}) zs) )
  ( trans
      ( cong (λ u → PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs
                     (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi) ++ u)
             refl' )
      ( cong (λ u → u ++ PosixPD.pdUMany-aux {r} {pref} (c ∷ cs) zs) e1 ) )
  where
    e1 : PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs
           (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi)
         ≡ PosixPD.pdUMany-aux {r} {pref} (c ∷ cs) (pdi ∷ [])
    e1 = refl
    refl' : PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs
              (concatMap (PosixPD.advance-pdi*-with-c {r} {pref} {c}) zs)
            ≡ PosixPD.pdUMany-aux {r} {pref} (c ∷ cs) zs
    refl' = refl

-- chain* : advances of a single instance, mirroring pdUMany-aux's recursion;
-- chain-aux : it is exactly pdUMany-aux run on the singleton list
chain* : ∀ {r : RE} {pref : List Char}
  → ( pdi : PDI.PDInstance* r pref ) → ( suff : List Char )
  → List (PDI.PDInstance* r (pref ++ suff))
chain* {r} {pref} pdi [] = pdi ∷ []
chain* {r} {pref} pdi (c ∷ cs)
  = concatMap (λ x → chain* {r} {pref ∷ʳ c} x cs)
              (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi)

chain-aux : ∀ {r : RE} {pref : List Char} ( pdi : PDI.PDInstance* r pref ) ( suff : List Char )
  → chain* {r} {pref} pdi suff
    ≡ PosixPD.pdUMany-aux {r} {pref} suff (pdi ∷ [])
chain-aux {r} {pref} pdi [] rewrite ++-identityʳ pref = refl
chain-aux {r} {pref} pdi (c ∷ cs) = trans
  ( concatMap-cong-λ (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi)
      (λ x → chain* {r} {pref ∷ʳ c} x cs)
      (λ x → PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs (x ∷ []))
      (λ x → chain-aux {r} {pref ∷ʳ c} x cs) )
  ( trans
      ( sym ( aux-concatMap {r} {pref ∷ʳ c} cs (λ x → x ∷ [])
                       (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi) ) )
      ( cong (λ l → PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs l)
             (concatMap-∷[]-id (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi)) ) )

-- a chain from a member of ys continues inside the advancement run of ys
any-aux : ∀ {r : RE} {pref : List Char} ( suff : List Char )
  → ( ys : List (PDI.PDInstance* r pref ) ) ( pdi : PDI.PDInstance* r pref ) ( p : RE )
  → pdi ∈ ys
  → Any ( λ e → Canonic.pd*-expr e ≡ p ) (chain* pdi suff)
  → Any ( λ e → Canonic.pd*-expr e ≡ p ) (PosixPD.pdUMany-aux {r} {pref} suff ys)
any-aux {r} {pref} suff ys pdi p m anychain =
  subst (λ w → Any ( λ e → Canonic.pd*-expr e ≡ p ) (PosixPD.pdUMany-aux {r} {pref} suff w)) eq
    ( subst (λ L → Any ( λ e → Canonic.pd*-expr e ≡ p ) L) (sym e2)
      ( any-mid {ys = PosixPD.pdUMany-aux {r} {pref} suff (pdi ∷ [])}
                 {zs = PosixPD.pdUMany-aux {r} {pref} suff zs}
                 (PosixPD.pdUMany-aux {r} {pref} suff xs)
        ( any++₁ {ys = PosixPD.pdUMany-aux {r} {pref} suff zs}
          ( subst (λ L → Any ( λ e → Canonic.pd*-expr e ≡ p ) L)
              (chain-aux {r} {pref} pdi suff) anychain ) ) ) )
  where
    eq∃ = ∈-split ys pdi m
    xs  = proj₁ eq∃
    zs  = proj₁ (proj₂ eq∃)
    eq  = proj₂ (proj₂ eq∃)
    e2  = trans (aux-++ {r} {pref} suff xs (pdi ∷ zs))
                (cong (λ u → PosixPD.pdUMany-aux {r} {pref} suff xs ++ u)
                      (aux-cons {r} {pref} suff pdi zs))

-- the composition lemma: a suffix chain from a reachable instance of r
-- reaches, in r's descendant list, for the concatenated word
chain-in-aux : ∀ {r : RE} {q : List Char} (pref suff : List Char)
  → ( xs : List (PDI.PDInstance* r q) ) ( pd : PDI.PDInstance* r (q ++ pref) ) ( p : RE )
  → pd ∈ PosixPD.pdUMany-aux {r} {q} pref xs
  → Any ( λ e → Canonic.pd*-expr e ≡ p ) (chain* {r} {q ++ pref} pd suff)
  → Any ( λ qe → qe ≡ p ) (map Canonic.pd*-expr
                             (PosixPD.pdUMany-aux {r} {q} (pref ++ suff) xs))
chain-in-aux {r} {q} [] suff xs pd p m anychain rewrite ++-identityʳ q =
  map-Any Canonic.pd*-expr (λ x eq → eq)
    (any-aux {r} {q} suff xs pd p m anychain)
chain-in-aux {r} {q} (c ∷ pref) suff xs pd p m anychain =
  chain-in-aux {r} {q ∷ʳ c} pref suff
    (concatMap (PosixPD.advance-pdi*-with-c {r} {q} {c}) xs) pd p m anychain

chain-in-pd*-Desc : ( r : RE ) ( pref suff : List Char ) ( p : RE )
    ( pdi : PDI.PDInstance* r pref )
  → pdi ∈ PosixPD.pdUMany[ r , pref ]
  → Any ( λ e → Canonic.pd*-expr e ≡ p ) (chain* pdi suff)
  → Any ( λ qe → qe ≡ p ) (Canonic.pd*-Desc r (pref ++ suff))
chain-in-pd*-Desc r pref suff p pdi pdi∈ anychain =
  chain-in-aux {r} {[]} pref suff
    [ pdinstance* {r} {r} {[]} injId injId-sound ] pdi p pdi∈ anychain
```

`chain-in-pd*-Desc` is the transfer the letter step of the descent needs:
once both trees have crossed the same letter through the same instance
`pdi`, whatever the induction hypothesis produces at `pd pdi` — a state
reachable by `chain* pdi suff` — is a pd-descendant of `r` for the whole
word.  Note the plumbing lemmas never evaluate `pdUMany-aux` at the empty
word with a variable accumulated index directly; as in `pdUMany-aux-complete`
in `cgp.posix.PartialDerivative`, those cases go through
`rewrite (++-identityʳ …)`, which is why the equation is registered as a
rewrite rule above.

## 11. The descent's instance side: composition and transport

A letter instance of `pdU[ r , c ]` is the same thing as a prefix instance
for the one-letter word (`pdinstance-letter`), and a path of instances can
be built by composition: `pdni∘` composes a prefix instance `pdi` with any
instance whose *target* is `pdi`'s continuation — that equation is an
argument, and `with`-refinement makes it reduce at constructor forms (the
type-level route `PDInstance* (pd*-expr pdi) pre` stays stuck on the
variable `pdi`, the same stuck-list phenomenon as §10's remarks).
Composition is invisible to pd-fields (`pd*-expr-∘`) and preserves
membership pointwise (`∘-pres-∈`).

Below induction depth the composition equalities are hypotheses, not
definitions, so instances and their `pdU` memberships must be *moved*
between equal targets: `pdtransport`, `pdtransport*` and
`pdU-transport-∈` do that, each defined by `with eq | refl` so the
transport is the identity where the equality is — every concrete call of
the descent, once the pair of trees forces the states, is such a case.

```agda
-- a one-letter instance is a prefix instance for the one-letter word
pdinstance-letter : ∀ { r : RE } { c : Char } → PDInstance r c → PDInstance* r (c ∷ [])
pdinstance-letter {c = c} (pdinstance {p} {r} inj ev) = pdinstance* {p} {r} {c ∷ []} inj ev

-- composing a prefix instance with an instance of its continuation
pdni∘ : ∀ { r d : RE } { pref pre : List Char }
  ( pdi : PDInstance* r pref ) ( pe : PDInstance* d pre )
  → Canonic.pd*-expr pdi ≡ d
  → PDInstance* r (pref ++ pre)
pdni∘ {pref = pref} {pre = pre} pdi pe eq with pdi | pe | eq
... | pdinstance* {p} {r} pref→r ev-pref | pdinstance* {q} pre→p ev-pre | refl =
  pdinstance* {q} {r} (pref→r ∘ pre→p)
    (λ u → trans (ev-pref (pre→p u))
                 (trans (cong (pref ++_) (ev-pre u)) (sym (++-assoc pref pre (proj₁ (flat {q} u))))))

-- composition is invisible to pd-fields (holds after refinement by with)
pd*-expr-∘ : ∀ { r d : RE } { pref pre : List Char }
  ( pdi : PDInstance* r pref ) ( pe : PDInstance* d pre )
  ( eq : Canonic.pd*-expr pdi ≡ d )
  → Canonic.pd*-expr (pdni∘ pdi pe eq) ≡ Canonic.pd*-expr pe
pd*-expr-∘ {pref = pref} {pre = pre} pdi pe eq with pdi | pe | eq
... | pdinstance* {p} {r} pref→r ev-pref | pdinstance* {q} pre→p ev-pre | refl = refl

-- pointwise composition preserves membership in instance lists
∘-pres-∈ : ∀ { r d : RE } { pref pre : List Char }
  ( pdi : PDInstance* r pref ) ( eq : Canonic.pd*-expr pdi ≡ d )
  ( pds : List (PDInstance* d pre) ) ( pe : PDInstance* d pre )
  → pe ∈ pds → pdni∘ pdi pe eq ∈ map (λ x → pdni∘ pdi x eq) pds
∘-pres-∈ pdi eq (pe ∷ pds) pe (here refl) = here refl
∘-pres-∈ pdi eq (x ∷ pds) pe (there m)   = there (∘-pres-∈ pdi eq pds pe m)

-- ─── transport of instances along RE-equalities of their targets ────────
U-transport : ∀ { r r′ : RE } → r ≡ r′ → U r → U r′
U-transport eq = subst (λ x → U x) eq

-- transport preserves the yield word (J: reduces at refl)
flat-transport : ∀ { r r′ : RE } ( eq : r ≡ r′ ) ( t : U r )
  → proj₁ (flat {r′} (U-transport eq t)) ≡ proj₁ (flat {r} t)
flat-transport refl t = refl

pdtransport : ∀ { c : Char } { d d′ : RE } ( z : PDInstance d c ) ( eq : d ≡ d′ )
  → PDInstance d′ c
pdtransport z eq with eq
... | refl = z

pdtransport-pd : ∀ { c : Char } { d d′ : RE } ( z : PDInstance d c ) ( eq : d ≡ d′ )
  → Canonic.pd-expr (pdtransport z eq) ≡ Canonic.pd-expr z
pdtransport-pd z refl = refl

pdtransport* : ∀ { d d′ : RE } { pre : List Char } ( x : PDInstance* d pre ) ( eq : d ≡ d′ )
  → PDInstance* d′ pre
pdtransport* x eq with eq
... | refl = x

pdtransport*-pd : ∀ { d d′ : RE } { pre : List Char } ( x : PDInstance* d pre ) ( eq : d ≡ d′ )
  → Canonic.pd*-expr (pdtransport* x eq) ≡ Canonic.pd*-expr x
pdtransport*-pd x refl = refl

-- membership in a pdU list moves with the index
pdU-transport-∈ : ∀ { c : Char } { d d′ : RE } ( eq : d ≡ d′ )
  ( z : PDInstance d c )
  → z ∈ PosixPD.pdU[ d , c ] → pdtransport z eq ∈ PosixPD.pdU[ d′ , c ]
pdU-transport-∈ refl z m = m

-- the pd-field of a composed letter instance is the letter's continuation
compose-letter-pd : ∀ { r d : RE } { pref : List Char } { c : Char }
  ( d→r : U d → U r )
  ( ev : ∀ v → proj₁ (flat {r} (d→r v)) ≡ pref ++ proj₁ (flat {d} v) )
  ( z : PDInstance d c )
  → Canonic.pd*-expr (compose-pdi-with {r} {d} {pref} {c} d→r ev z) ≡ Canonic.pd-expr z
compose-letter-pd d→r ev z with z
... | pdinstance {p} {_} {_} _ _ = refl
```

With these two sections the letter step of the descent is fully equipped on
the *chain* side: the trees' common instance `pdi`, the IH's state `p` and
the continuation `suff` assemble through `chain-in-pd*-Desc` (§10) once the
IH's witness is a chain from `pdi`.  Making the IH's `pd*-Desc p suff`
membership into such a chain — the *reverse* direction — hits the deeper
obstacle this module's probes established: below depth the hypothesis is a
membership in a `pdUMany-aux` call whose instance lists are neutral
(`pdU[ d , c ]`, `map`/`concatMap` over neutral arguments), and those lists
cannot be case-split at all.  The reverse transfer therefore has to run
like the paper's `AllParseFST` argument — along the structural recursion of
`pdU` on the expression — which is the remaining step (B3b).

## 12. The split case: pair descent and context-stable criteria

The paper's proposition justifies its criteria by enumerating the *only
three situations in which the parse-tree construction can branch*: more
than one empty tree at a final state (A1), an injection through a nullable
concatenation whose left side has more than one empty tree (A2), and the
`Idemp` merge of similar alternatives when building canonical
representatives (A3 — here: the duplicate sum under a context).  The split
case of the descent — two trees crossing a letter through *different*
instances, i.e. a `LeftU` in one branch and a `RightU` in the other at
some sum — is where the third situation lives.  What closes the argument
is a *pair theorem*: two trees of a common word, one in each of two
expressions, either diagnose a criterion at their sum or find one below
one of the two along a common word prefix.  This section names the
criteria, proves what is provable without touching neutral lists — the
pair's base (`split-+-A1`) and the syntactic transfer of criteria through
contexts (`A2-Ctx`, `dup-Ctx`) — and states the pair theorem as the goal
of B3b.

```agda
-- the diagnosis disjunction of §8, named
crit : RE → Set
crit p = AmbigCheck.AmbigA1 p
       ⊎ AmbigCheck.AmbigA2 p
       ⊎ Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
             ( ( AmbigCheck.plug ctx ( l + s ` loc ) ≡ p )
             × ( Canonic._≈₀_ l s ) )

-- composition of hole contexts
Ctx∘Ctx : AmbigCheck.Ctx → AmbigCheck.Ctx → AmbigCheck.Ctx
Ctx∘Ctx AmbigCheck.𝟘 c₂ = c₂
Ctx∘Ctx (AmbigCheck.Ctx●R c₁ r loc) c₂ = AmbigCheck.Ctx●R (Ctx∘Ctx c₁ c₂) r loc
Ctx∘Ctx (AmbigCheck.L●Ctx l c₁ loc) c₂ = AmbigCheck.L●Ctx l (Ctx∘Ctx c₁ c₂) loc
Ctx∘Ctx (AmbigCheck.Ctx+R c₁ r loc) c₂ = AmbigCheck.Ctx+R (Ctx∘Ctx c₁ c₂) r loc
Ctx∘Ctx (AmbigCheck.L+Ctx l c₁ loc) c₂ = AmbigCheck.L+Ctx l (Ctx∘Ctx c₁ c₂) loc

plug-Ctx∘ : ( c₁ c₂ : AmbigCheck.Ctx ) ( t : RE )
  → AmbigCheck.plug (Ctx∘Ctx c₁ c₂) t ≡ AmbigCheck.plug c₁ (AmbigCheck.plug c₂ t)
plug-Ctx∘ AmbigCheck.𝟘 c₂ t = refl
plug-Ctx∘ (AmbigCheck.Ctx●R c₁ r loc) c₂ t = cong (λ x → x ● r ` loc) (plug-Ctx∘ c₁ c₂ t)
plug-Ctx∘ (AmbigCheck.L●Ctx l c₁ loc) c₂ t = cong (λ x → l ● x ` loc) (plug-Ctx∘ c₁ c₂ t)
plug-Ctx∘ (AmbigCheck.Ctx+R c₁ r loc) c₂ t = cong (λ x → x + r ` loc) (plug-Ctx∘ c₁ c₂ t)
plug-Ctx∘ (AmbigCheck.L+Ctx l c₁ loc) c₂ t = cong (λ x → l + x ` loc) (plug-Ctx∘ c₁ c₂ t)

-- A2 and the duplicate pattern transfer through any hole context
-- (A1 does not: filling a ●-context needs the sibling to be nullable)
A2-Ctx : ( ctx : AmbigCheck.Ctx ) { p : RE }
  → AmbigCheck.AmbigA2 p → AmbigCheck.AmbigA2 (AmbigCheck.plug ctx p)
A2-Ctx ctx ( ctx₂ , l , t , loc , ( plug-eq , ε∈l , len ) ) =
  ( Ctx∘Ctx ctx ctx₂ , l , t , loc ,
    ( trans (plug-Ctx∘ ctx ctx₂ ( l ● t ` loc )) (cong (AmbigCheck.plug ctx) plug-eq)
    , ε∈l , len ) )

dup-Ctx : ( ctx : AmbigCheck.Ctx ) { p : RE }
  → ( Σ[ ctx₂ ∈ AmbigCheck.Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
        ( ( AmbigCheck.plug ctx₂ ( l + s ` loc ) ≡ p ) × ( Canonic._≈₀_ l s ) ) )
  → ( Σ[ ctx′ ∈ AmbigCheck.Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
        ( ( AmbigCheck.plug ctx′ ( l + s ` loc ) ≡ AmbigCheck.plug ctx p )
        × ( Canonic._≈₀_ l s ) ) )
dup-Ctx ctx ( ctx₂ , l , s , loc , ( plug-eq , ≈₀ls ) ) =
  ( Ctx∘Ctx ctx ctx₂ , l , s , loc ,
    ( trans (plug-Ctx∘ ctx ctx₂ ( l + s ` loc )) (cong (AmbigCheck.plug ctx) plug-eq)
    , ≈₀ls ) )

-- the pair's base: one empty tree in each branch of a sum fires A1 at the
-- sum itself — the two injected trees are always distinct (LeftU ≠ RightU)
split-+-A1 : ( l s : RE ) ( loc : ℕ ) ( u : U l ) ( v : U s )
  → proj₁ (flat {l} u) ≡ [] → proj₁ (flat {s} v) ≡ []
  → AmbigCheck.AmbigA1 (l + s ` loc)
split-+-A1 l s loc u v u≡[] v≡[] = ( ε∈l+s , two-distinct-members→len≥2 list u∈ v∈ u≢v )
  where
    ε∈l : RE.ε∈ l
    ε∈l = Word.[]∈⟦r⟧→ε∈r (subst ( λ w → w ∈⟦ l ⟧) u≡[] (proj₂ (flat {l} u)))
    ε∈s : RE.ε∈ s
    ε∈s = Word.[]∈⟦r⟧→ε∈r (subst ( λ w → w ∈⟦ s ⟧) v≡[] (proj₂ (flat {s} v)))
    ε∈l+s : RE.ε∈ (l + s ` loc)
    ε∈l+s = RE.ε∈_+_ ε∈l ε∈s
    list = mkAllEmptyU {l + s ` loc} ε∈l+s
    u∈ : Any ( λ z → LeftU {l} {s} {loc} u ≡ z ) list
    u∈ = mkAllEmptyU-complete ε∈l+s (LeftU u) (flat-[] (LeftU u) u≡[])
    v∈ : Any ( λ z → RightU {l} {s} {loc} v ≡ z ) list
    v∈ = mkAllEmptyU-complete ε∈l+s (RightU v) (flat-[] (RightU v) v≡[])
    u≢v : ¬ ( LeftU {l} {s} {loc} u ≡ RightU {l} {s} {loc} v )
    u≢v = LeftU≢RightU u v
```

(`proj₁ (flat (LeftU u)) ≡ proj₁ (flat u)` definitionally, so the words
transfer by assumption.)

A criterion found *below* a branch of a sum is heard *at* the sum.  A2 and
the duplicate pattern travel through the one-hole contexts `_ + s \` loc`
and `l + _ \` loc` by `A2-Ctx`/`dup-Ctx`; A1 is reconstructed at the sum:
the decision `RE.ε∈? s` turns the nullable half into an `ε∈` proof whose
shape makes `mkAllEmptyU` unfold — through its `<+`/`+>` forms to
`map LeftU (mkAllEmptyU {l} …)` (or the right-hand mirror) alone, and
through its `+` form to `map LeftU … ++ map RightU …` — and the length
witness moves along `length-map`/`length-++` (one summand embeds by
`m≤m+n`/`m≤n+m`).

```agda
A1-+< : ( l s : RE ) ( loc : ℕ )
  → AmbigCheck.AmbigA1 l → AmbigCheck.AmbigA1 ( l + s ` loc )
A1-+< l s loc ( ε∈l , len ) with RE.ε∈? s
... | yes ε∈s =
  ( RE.ε∈_+_ ε∈l ε∈s
  , subst ( λ n → suc (suc zero) ≤ n ) (sym e-++-len)
      (≤-trans len (m≤m+n (length (mkAllEmptyU {l} ε∈l)) _)) )
  where
    f : U l → U ( l + s ` loc )
    f v = LeftU {l} {s} {loc} v
    g : U s → U ( l + s ` loc )
    g v = RightU {l} {s} {loc} v
    e-++-len : length (map f (mkAllEmptyU {l} ε∈l) ++ map g (mkAllEmptyU {s} ε∈s))
                 ≡ length (mkAllEmptyU {l} ε∈l) + length (map g (mkAllEmptyU {s} ε∈s))
    e-++-len = trans (length-++ (map f (mkAllEmptyU {l} ε∈l)) {map g (mkAllEmptyU {s} ε∈s)})
                     (cong (λ m → m + length (map g (mkAllEmptyU {s} ε∈s)))
                           (length-map f (mkAllEmptyU {l} ε∈l)))
... | no ¬ε∈s =
  ( RE.ε∈_<+_ ε∈l (RE.¬ε∈r→ε∉r ¬ε∈s)
  , subst ( λ n → suc (suc zero) ≤ n ) (sym (length-map f (mkAllEmptyU {l} ε∈l))) len )
  where
    f : U l → U ( l + s ` loc )
    f v = LeftU {l} {s} {loc} v

A1-+> : ( l s : RE ) ( loc : ℕ )
  → AmbigCheck.AmbigA1 s → AmbigCheck.AmbigA1 ( l + s ` loc )
A1-+> l s loc ( ε∈s , len ) with RE.ε∈? l
... | yes ε∈l =
  ( RE.ε∈_+_ ε∈l ε∈s
  , subst ( λ n → suc (suc zero) ≤ n ) (sym e-++-len)
      (≤-trans len (m≤n+m (length (mkAllEmptyU {s} ε∈s)) _)) )
  where
    f : U l → U ( l + s ` loc )
    f v = LeftU {l} {s} {loc} v
    g : U s → U ( l + s ` loc )
    g v = RightU {l} {s} {loc} v
    e-++-len : length (map f (mkAllEmptyU {l} ε∈l) ++ map g (mkAllEmptyU {s} ε∈s))
                 ≡ length (map f (mkAllEmptyU {l} ε∈l)) + length (mkAllEmptyU {s} ε∈s)
    e-++-len = trans (length-++ (map f (mkAllEmptyU {l} ε∈l)) {map g (mkAllEmptyU {s} ε∈s)})
                     (cong (λ n → length (map f (mkAllEmptyU {l} ε∈l)) + n)
                           (length-map g (mkAllEmptyU {s} ε∈s)))
... | no ¬ε∈l =
  ( RE.ε∈_+>_ (RE.¬ε∈r→ε∉r ¬ε∈l) ε∈s
  , subst ( λ n → suc (suc zero) ≤ n ) (sym (length-map f (mkAllEmptyU {s} ε∈s))) len )
  where
    f : U s → U ( l + s ` loc )
    f v = RightU {l} {s} {loc} v

-- a criterion found below a branch is a criterion at the sum
crit-+< : ( l s : RE ) ( loc : ℕ ) → crit l → crit ( l + s ` loc )
crit-+< l s loc (inj₁ a1)        = inj₁ (A1-+< l s loc a1)
crit-+< l s loc (inj₂ (inj₁ a2)) = inj₂ (inj₁ (A2-Ctx (AmbigCheck.Ctx+R AmbigCheck.𝟘 s loc) a2))
crit-+< l s loc (inj₂ (inj₂ d))  = inj₂ (inj₂ (dup-Ctx (AmbigCheck.Ctx+R AmbigCheck.𝟘 s loc) d))

crit-+> : ( l s : RE ) ( loc : ℕ ) → crit s → crit ( l + s ` loc )
crit-+> l s loc (inj₁ a1)        = inj₁ (A1-+> l s loc a1)
crit-+> l s loc (inj₂ (inj₁ a2)) = inj₂ (inj₁ (A2-Ctx (AmbigCheck.L+Ctx l AmbigCheck.𝟘 loc) a2))
crit-+> l s loc (inj₂ (inj₂ d))  = inj₂ (inj₂ (dup-Ctx (AmbigCheck.L+Ctx l AmbigCheck.𝟘 loc) d))
```

What the recursion must hand back from below a pair step is not a bare
`pd*-Desc` membership but a witness of *how the state was reached*: a
chain of letter instances carrying their `pdU` memberships as fields.
That is the `Path` structure below — it sidesteps the §10–§11 stuck-list
obstacle entirely, since every transfer along a path is by construction
and no membership is ever case-split.  One structural fact shapes how
paths may enter a sum: `pdU[ l + s \` loc , c ]` is *not*
`map pdinstance-left … ++ map pdinstance-right …` but
`pdinstance-oplus` of the two lists, and when both sides derive by `c`
the lists **fuse** — every member pairs a left and a right instance
(PartialDerivative 362–368) — so a path below one branch does *not*
extend through the sum head in general; the singleton equations of
`pdinstance-oplus` (one side deriving nowhere) are the only clean
embeddings.  The pair descent therefore runs its two chains *inside* the
two branches, which is what the statement below asks for.

```agda
-- a descent path: each step names its letter instance and carries its
-- pdU membership as a field (never to be case-split)
data Path : ( r : RE ) → ( w : List Char ) → Set where
  pnil  : ∀ { r } → Path r []
  pcons : ∀ { r c ws } ( z : PDInstance r c )
    → z ∈ PosixPD.pdU[ r , c ]
    → Path (Canonic.pd-expr z) ws
    → Path r (c ∷ ws)

-- the state a path ends in
pdend : ∀ { r w } → Path r w → RE
pdend {r} pnil          = r
pdend (pcons z m q) = pdend q

-- membership in a map, from membership in the source (constructing the
-- result, so the neutral `map f xs` never has to be case-split)
map-Any-∈ : ∀ { A B : Set } ( f : A → B ) { xs : List A } { x : A }
  → x ∈ xs → f x ∈ map f xs
map-Any-∈ f (here p) = here (cong f p)
map-Any-∈ f (there m) = there (map-Any-∈ f m)

-- the run-lift bridge in path form (the B3a reverse direction): a path
-- from r is a run of r for its word, so its end state appears in
-- pd*-Desc r w.  Composing the steps into one `PDInstance* r w` goes
-- through `pdni∘` (§11); showing it a member of `pdUMany[ r , w ]` is a
-- construction over the path's fields, not a case split.  Stated with
-- a hole:
pdesc : ∀ { r w } ( π : Path r w )
  → Any ( λ x → x ≡ pdend π ) (Canonic.pd*-Desc r w)
pdesc π = _
```

The pair theorem proper recurses on the *two trees* (each step shrinks one
of them, and the shared word shrinks at `LetterU` pairs): its base is the
`split-+-A1` situation above; the `LeftU`/`LeftU`-style steps re-enter the
recursion in one branch and lift the outcome through the sum with
`crit-+<`/`crit-+>`; and the findings below a branch are handed back as
paths, whose membership content `pdesc` supplies.  Stated as the goal of
B3b:

```agda
pair-complete : ∀ { l s : RE } ( loc : ℕ ) ( w : List Char )
  ( u : U l ) ( v : U s )
  → proj₁ (flat {l} u) ≡ w → proj₁ (flat {s} v) ≡ w
  → crit ( l + s ` loc )
  ⊎ ( ∃[ w′ ] ∃[ w″ ] ( ( w ≡ w′ ++ w″ )
        × ( ( Σ[ π ∈ Path l w′ ] crit (pdend π) )
          ⊎ ( Σ[ π ∈ Path s w′ ] crit (pdend π) ) ) ) )
pair-complete {l} {s} loc w u v u≡ v≡ = _
```

From `pair-complete`, the split case of the §8 descent composes as follows:
the two trees reach the sum state `l + s \` loc` through the common prefix
`w′` (a chain instance, §10–§11); the pair theorem either fires `crit` at
the sum — then `chain-in-pd*-Desc` (§10) puts the sum in
`pd*-Desc r (w′)` — or hands back a path below one branch ending in a
`crit` state; `pdesc` turns the path into a `pd*-Desc l w′` membership,
and the prefix decomposition `w ≡ w′ ++ w″` transports it to a
pd-descendant of `r` for the whole word (§10's composition lemma read in
reverse).  Filling the pair hole is the paper's three-situations argument
run structurally on the tree pair: the word boundary at a `LetterU` pair
is where `split-+-A1` fires, the branch steps lift with `crit-+<`/
`crit-+>`, and the `PairU`/`ListU` word-splitting steps are where A2 and
the duplicate pattern surface.
