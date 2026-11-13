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
  fires) — with the statement here and its proof given in §23–§24, and its
  reading tied to the ambiguity pair of `sd` proved (`Recons*-at-singleton`, `sd-recons*-at-pdi₂`,
  `sd-completeness-at-the-state`: every tree of `aa` is the image under
  `pd*-inj pdi₂` of a tree of `sd-s2`, and distinctness reflects).
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
  their run-lift (`pdesc`: `path-chain` composes the steps with
  `compose-pdi-with`, as `advance-pdi*-with-c` does) is proved; the pair
  theorem `pair-complete` — the structural-recursion core of the paper's
  ambiguity-criteria argument — is proved with paths anchored at the sum
  (a branch-anchored version is refuted by the `($a`1 + ε) + $a`2`
  counterexample, whose witness is the fused derivative `ε + ε`);
  `ε∈→emptyU` and `A1-⊕` fire A1 at any sum of two nullable
  expressions, which closes the first clauses of the pair recursion:
  pairs with an empty tree on one side (`crit-ε+`, `crit-+ε`) and pairs
  of literal trees (`crit-$$`, the duplicate pattern with `ctx = 𝟘`);
  criteria also lift through the concatenation contexts (`A1-●<`,
  `A1-●>`, `crit-●<`, `crit-●>`), via a length-counting toolkit
  (`len-++≥`/`len-++≥ˡ`/`len-++≥₁`, `len∈concatMap`, `length-concatMap≥`,
  `mkAllEmptyU-nonempty`).
* §13 is the one letter step of that recursion: a member of an instance
  list with its witness (`pick-Any` — the list must be a parameter, since
  at the call sites it is the stuck `pdU[ r , c ]`), the residual tree of
  a reconstruction and its forced word (`Recons-residual`, read off the
  instance's own soundness evidence, no `flat∘unflat`), membership of the
  instance pair in the sum's list (`∈-concatMap`, `∈-oplus-fuse`,
  `pdU∈-⊕`) and the continuation equation of that pair
  (`pd-expr-fuse-⊕`: `fuse`'s continuation *is* the sum of the two
  continuations, which is where the recursive call stands), with
  `Path-rescue` carrying a found path across that equation.
* §14 composes the two: `split-completeness` is §8's conclusion for the pair
  that splits at a sum — `pair-complete` read through `pdesc`, the path
  disjunct being exactly a `pd*-Desc` membership and the sum itself the
  pd-descendant of the empty prefix.  This is the one shape of the general
  `completeness` that is closed; the rest of that statement needs the descent
  through `●` and `⋆` and the split-word pairs (A2's shape), §14's last
  paragraph.
* §15 lifts a criterion across a state extension.  Two paths of one word, one
  per branch, fuse into one path at the sum (`Path-⊕`, `pdend-subst`,
  `pdend-Path-⊕`, built from §13's `pdU∈-⊕`), so a criterion below *one*
  branch at a word the sibling also derives is a criterion at a `pd*-Desc`
  state of the sum (`Desc-⊕-crit`, with `pdesc` and `crit-+<`);
  `pd-expr-star`/`crit-*<` do the same for the star continuation, which ends at
  `p ● r ⋆ \` loc` — a nullable-right concatenation, so `crit-●<` applies.  The
  lift that is *not* covered is the one-sided one, where a symbolic `pdU` list
  must be seen to be empty: §4's obstacle, probed and recorded, so the general
  descent cannot be assembled by lifting paths upward.
* §16 states what is left as one named hypothesis.  `Desc-complete` is the
  single-expression form of the descent (two trees of one `r`, pick-only,
  never asking whether a list is empty), `desc-concl` its conclusion; its base
  is §9's `base-A1-at-root` (`desc-base`), its one-instance step is proved
  (`desc-step`, extending the path by `pcons`) together with the fact that a
  *shared* instance carries a distinct pair to a distinct pair of residuals
  (`Recons-residual-2`).  `completeness-from-desc` then derives §8's statement
  from `Desc-complete` through `pdesc`, so the whole completeness direction is
  reduced to one case split — the case where `pdU-complete` yields *different*
  instances for the two trees.
* §17 examines that case on a checked example: a sum whose left branch
  re-appears inside its right branch.  A literal's derivative is its own
  singleton (`pdU-$a1≡`), a sum of two literals has the one fused member
  (`pdU-⊕-lit≡`), and the duplicated sum's single member `dup-pdi` — the fusion
  of the branch instance with the right branch's member, membership from
  `pdU∈-⊕` with no emptiness decision — reconstructs the *same* tree as the
  plain branch injection does (`dup-u-recon`, `dup-u-recon₂`): one letter, one
  member, two derivations.  Nothing is nullable and there is no concatenation
  *before* reading, so no A1/A2 holds at the state; the state carries the
  `Idemp`/duplicate pattern (`≈₀`-similar branches under a context) and A1
  recurs only at the fusion's nullable continuation.  Hence the classification
  §16 needs is a statement about *canonical* expressions (`≈₀`), not about
  `pdU` multiplicity — the paper's third situation is genuinely one of the three.
* §18 writes that third-criterion witness down for the example and runs the
  descent to it: the duplicate sum is `dup-s1` itself in no context
  (`dup-s1-dup`, via `≈₀-$`), it moves under the outer sum's left context by
  `dup-Ctx` (`dup-r-lit-crit`), and the one-letter path through `dup-pdi`
  ends in a `pd*-Desc` state (`pdesc`) which computes, by `refl`, to the sum
  `( ε + ( ε + ε \` 3 ) \` 0 )` of two similar empty alternatives — where the
  third disjunct fires again (`pdend-π-dup-crit`) — so `desc-step` gives
  `desc-concl` for the example word (`dup-desc`).  `Canonic`'s mechanical test
  fires too: `pd-Idemp?` on the example's instance list computes to `true`
  (`dup-Idemp-fires`), and these witnesses are the reflection instance its
  caveat asks for.
* §19 takes stock and closes what can be closed: `Cross-instance→crit` names
  the single missing rule (the two `pdU-complete` picks differ ⇒ a criterion at
  the state), and `desc-picks` assembles the full recursion from that rule and
  a decision of instance identity — base `desc-base`, shared-pick case
  `Recons-residual-2` + `desc-step`, cross case by hypothesis — giving
  `Desc-complete-picks` and `completeness-picks`, the §8 statement modulo its
  two parameters.  Instance identity is intensional here (function fields): the
  decision is classical or needs a quotient of instances by pattern (the
  `Cast`/`≈₀` machinery), and that quotient is also where §17 says the
  classification belongs.  `crit-●-2ε` adds the paper's second situation as a
  rule: two distinct empty trees of a nullable left factor are A2 at the
  concatenation.
* §20 makes the pick test computable up to one rule.  `RE` equality is decidable
  (`RE-≟`, via `ε∉-≟` for the Kleene argument), the residual tree of a
  reconstruction and its word are named terms (`residual`, `residual-word`), and
  `desc-picks-dec` decides record identity (`dec`, §19's intensional equality),
  recurses through a shared record, and otherwise stops at one of two named
  configurations: different continuations (`pick-diff-state`, the surviving
  parameter) or distinct records with one continuation — which
  `pick-diff-record-prf` closes *by computation*, the §22 A3 test via
  `Canonic.pd-Idemp?-members`.  `Desc-complete-dec` and `completeness-dec` give
  §8's statement from the one rule; the test evaluates on the §17–§18 example
  (`dup-cont-differ`), whose pair is descended end to end with neither
  configuration reached (`dup-desc-dec`).
 * §21 locates the second configuration exactly.  `recon-uniq`: two
   reconstructions through the *same* member with the same residual rebuild the
   same tree — a `pick-diff-record` stop for a distinct pair always has two
   *distinct* members with one continuation (dropping that premise fails
   exactly where the two members' transition maps differ).  The configuration
   is realized by `Canonic` §8.1's verbatim-A3 example: two members with
   `≈₀`-similar continuations (`pd-a3-continuations`), `Idemp` firing by
   computation (`pd-a3-Idemp-applied`), an ambiguous expression
   (`pd-a3-ambiguous`) — and the criterion sits at the *merged derivative*
   state (`pd-a3-Desc`), where `crit-sum-≈₀` fires (`pd-a3-crit`), not at the
   state carrying the transition.
 * §22 shows that the last step is smaller than it looks, because it is the
   criterion that was stated wrong.  The paper's A3 is a test on a *transition*
   out of a state ("A1 is always connected to a final state whereas A2 and A3
   are always connected to transitions"), and `Canonic.pd-Idemp?` is exactly
   that test on the partial-derivative list: it becomes `crit`'s fourth
   disjunct, in the same hole-context shape as the third, and `A3-Ctx` gives it
   the same stability, so §12's four lifting lemmas (`crit-+<`, `crit-+>`,
   `crit-●<`, `crit-●>`) carry it too.  It fires at the states themselves —
   `dup-r-lit-crit-A3`, and `pd-a3-crit-A3` at `pd-a3-target`, an expression
   that contains no duplicate at all (`pd-a3-canonic-flag`) — and
   `pd-a3-pair-complete` settles §8's goal for that ambiguity pair at the empty
   prefix, with no descent and no `derivᵖ` re-gluing.  Stating the same
   criterion over *members* ("two members of `pdU[ p , c ]` with similar
   continuations") is the wrong shape, and the reason is structural: the sum
   clause of `pdU` fuses the branch instances, so the duplicate survives only as
   a `+`-spine inside one continuation, and the one clause that does keep
   several members is the nullable concatenation, which is A2's own
   configuration.  §20's record rule, finally, was *false* without the record
   distinctness §21 proves it has; §20 is restated with that premise and with
   §19's decision of instance identity — the record case becomes the theorem
   `pick-diff-record-prf` — and `pick-diff-state`, the paper's enumeration, is
   all that is left.
 * §23 closes the goal: in this formalization *all members of `pdU[ r , c ]`
   continue at one expression* (`pdU-const`, by induction over the `pdU`
   clauses — each maps its sublists through constructor maps that respect
   continuations (`pd-expr-resp∘*`) or fuses them pairwise
   (`fuse-pair-const`), and the POSIX `pdinstance-oplus` only ever joins
   constant lists (`oplus-const`)).  So `pick-diff-state` never applies
   (`cstate-⊥`), and §20's descent runs on with only the record decision left:
   `pdinstance` stores its transition as a function, so that decision, as
   §19's `dec`, has no decision procedure as stated.
 * §24 closes the goal with no postulate: the descent never needs record
   identity — what its two branches use it for is choosing between continuing
   through one shared transition and firing the criterion, and that choice is
   decidable on the *residual trees*: both residuals sit at one expression
   (`pdU-const`'s equation, `flat-resp` moves words with the transport), and
   tree identity there is `ParseTree._⊢_≟_`.  Different residuals: continue
   through one member; equal residuals: the records cannot have been equal
   (`Recons-residual-2`, as `diff-records-≟`), which is the A3 configuration
   closed by §22's `pick-diff-record-prf`.  `desc-picks-≟` is
   `Desc-complete-≟`, and §16's `completeness-from-desc` proves §8's
   `completeness`.

```agda
-- `data Path` is strictly positive by inspection (`pcons` carries it only in
-- argument position), but Agda 2.7.0.1's positivity checker false-positives on
-- it through the `subst` motive in `Path-rescue`'s type once §24 instantiates
-- the descent (agda/agda#7669, fixed in 2.8.0), so the check is off here
{-# OPTIONS --rewriting --no-positivity-check #-}
module cgp.ambig.Complete where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉ ; ε∈ ; ε∉$ ; ε∉fst ; ε∉snd ; ε∉_+_)

import cgp.ParseTree as ParseTree
open ParseTree using ( U ; EmptyU ; LetterU ; LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unListU
                     ; flat-Uε≡[] ; inv-leftU ; inv-rightU ; inv-pairU
                     ; LeftU≢RightU ; RightU≢LeftU )

import cgp.Word as Word
open Word using (_∈⟦_⟧ ; _+L_ ; $_)

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance*
               ; mkinjList ; mkinjFst ; mkinjSnd ; compose-pdi-with
               ; pdinstance-left ; pdinstance-right ; pdinstance-fst ; pdinstance-star ; mk-snd-pdi )

import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( flat-[] ; mkAllEmptyU ; mkAllEmptyU-complete )

import cgp.posix.PartialDerivative as PosixPD
open PosixPD using ( mkfuseInj ; fuse ; pdinstance-oplus ; injId ; injId-sound ; pdU-complete ; pdUMany-complete )

import cgp.Utils as Utils
open Utils using ( ∷-inj )

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using ( Ambig )

import cgp.ambig.Canonic as Canonic

import cgp.ambig.Converse as Converse
open Converse using ( sd ; sd-body ; sd-ε∉ ; sd-s1 ; sd-s2 ; sd-x ; aa ; res-a ; sd-s2-A1 ; sd-Desc₂ )

import cgp.Recons as Recons
open Recons using ( Recons ; recons ; Recons* ; recons* )

open import Data.Char using (Char)
import Data.Char as Char
open import Data.Nat using (ℕ; _≟_ ; suc ; zero ; _≤_ ; _+_ ; s≤s ; z≤n)
import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-refl ; ≤-reflexive ; ≤-trans ; m≤m+n ; m≤n+m ; n≤1+n )
open import Data.List using (List; _∷_; _∷ʳ_; []; _++_; map; concat; concatMap; [_]; length)
open import Data.List.Properties using (++-cancelˡ ; ++-identityʳ ; ++-assoc ; length-map ; length-++ )
{-# REWRITE ++-identityʳ #-}
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_×_; _,_; Σ ; proj₁ ; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong₂ ; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec ; yes ; no)
open import Data.Bool using (true)
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
prefix whose pd-states include one at which a criterion fires.  The diagnosis
disjunction is named once, here, since every later section states its result in
terms of it: the first two disjuncts are the paper's A1 and A2
(`cgp.ambig.AmbigCheck` §3, §4), the third is the `Idemp` *pattern* (a sum with
`≈₀`-equal members under a hole context — the shape `Canonic.Ctx-dup→Ambig`
consumes), the fourth is A3 proper: the `Idemp` *test* firing on a transition out
of a state, again read under a hole context, since the paper's criteria range
over descendants `s ∈ Desc(r)` and a hole context is what this project has of
that (`cgp.ambig.Canonic`'s `pd-Idemp?`; why that is the right shape, and what
it fires on, is §22).  All four are stable under plugging a context: §12's
`A2-Ctx`, `dup-Ctx`, `A3-Ctx`.

```agda
crit : RE → Set
crit p = AmbigCheck.AmbigA1 p
       ⊎ AmbigCheck.AmbigA2 p
       ⊎ Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
             ( ( AmbigCheck.plug ctx ( l + s ` loc ) ≡ p )
             × ( Canonic._≈₀_ l s ) )
       ⊎ Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ q ∈ RE ] Σ[ c ∈ Char ]
             ( ( AmbigCheck.plug ctx q ≡ p )
             × ( Canonic.pd-Idemp? (PosixPD.pdU[ q , c ]) ≡ true ) )

completeness : ∀ { r : RE }
  → ( u v : U r )
  → proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) → ¬ ( u ≡ v )
  → ∃[ w′ ] ∃[ w″ ]
      ( ( proj₁ (flat {r} u) ≡ w′ ++ w″ )
      × ∃[ p ]
          ( Any ( λ s → s ≡ p ) (Canonic.pd*-Desc r w′)
          × crit p ) )

-- (the body of `completeness` is §24's: the statement stays here, but its
-- proof needs `Desc-complete` (§16) and the descent `desc-picks-≟` (§24),
-- defined below)
```

The fourth disjunct is worth naming outright at the empty context, since it is a
decidable test on the transition out of the state and needs no descent to be
applied at the state itself:

```agda
crit-A3-test : ∀ ( r : RE ) ( c : Char )
  → Canonic.pd-Idemp? (PosixPD.pdU[ r , c ]) ≡ true
  → crit r
crit-A3-test r c p≡true = inj₂ (inj₂ (inj₂ ( AmbigCheck.𝟘 , r , c , ( refl , p≡true ) )))
```

To fill this for an *arbitrary* pair `( u , v )` one has to *find* the
prefix `w′` — the paper's `AllParseFST` argument over parse trees of the
word.  It is not formalized here (like the realizable-states / FST side of
the paper), and this is the actual research gap of the program, beyond §4.1.
One shape of it is discharged in §14 (`split-completeness`): the pair that
splits at a sum, which is `pair-complete` (§13) read through `pdesc`.  The
general body is exactly what §16's `completeness-from-desc` computes once the
single named hypothesis `Desc-complete` (§16) is supplied: its two cases are
`pdesc pnil` at the state itself and `pdesc` of the path the descent returns,
so nothing else stands between that hypothesis and this statement.  §19 goes
one step further and assembles `Desc-complete` — hence this statement, via
`completeness-picks` — from two named parameters: the recognition rule
`Cross-instance→crit` (the paper's enumeration as one rule) and a decision of
instance identity; everything except those two parameters now checks.  §23
discharges the recognition rule — it is vacuous once `pdU-const` shows every
transition continues at a single expression — and §24 replaces the record
decision by a decidable question on residuals (`ParseTree._⊢_≟_`): the
assembled body of `completeness` is at the end of §24.

**The reading tied to a given pair, for this `r`** (what §5–§6 built the
machinery for): every ambiguity pair of `sd` for the word `aa` is the image,
under the transition map of the single instance of `pdUMany[ sd , aa ]`, of a
pair of distinct trees of the state that word reaches — and A1 fires there
(`sd-s2-A1`, with `pdUMany-sd-aa≡` naming the instance and `pd-pdi₂` its
continuation, §5).  Given `u ≢ v` the pair `( u′ , v′ )` is automatically
distinct (a function sends distinct outputs to distinct inputs); §6's
`pdi₂-inj` gives the converse, and both together say the ambiguity *is* the
state's A1 witness, not an artifact of the map.

Two lemmas do the extraction.  At a *singleton* run list the instance and its
membership can only be matched *inside* the lemma — at the call site the list
is the computed `pdUMany[ sd , aa ]`, the stuck form of §4 — and §5's
`pdUMany-sd-aa≡` is what makes the singleton equation apply.

```agda
-- at a singleton run list, every tree of the word is in the image of that
-- instance's transition map
Recons*-at-singleton : ∀ { r : RE } { w : List Char } ( u : U r )
  ( pdi : PDInstance* r w )
  → Any (Recons* {r} {w} u) (pdi ∷ [])
  → Σ[ x ∈ U (Canonic.pd*-expr pdi) ] ( Canonic.pd*-inj pdi x ≡ u )
Recons*-at-singleton u (pdinstance* {p} inj ev) (here (recons* _ ( w∈ , eq ))) = ( unflat w∈ , eq )
Recons*-at-singleton u pdi (there ())

-- for `sd` and the word `aa` the run list *is* `[ pdi₂ ]` (§5)
sd-recons*-at-pdi₂ : ( u : U sd ) → ( proj₁ (flat {sd} u) ≡ aa )
  → Σ[ x ∈ U (Canonic.pd*-expr pdi₂) ] ( Canonic.pd*-inj pdi₂ x ≡ u )
sd-recons*-at-pdi₂ u w≡ =
  Recons*-at-singleton u pdi₂
    ( subst ( λ L → Any (Recons* {sd} {aa} u) L ) pdUMany-sd-aa≡
      ( subst ( λ w → Any (Recons* {sd} {w} u) (PosixPD.pdUMany[ sd , w ]) ) w≡
          (PosixPD.pdUMany-complete {sd} u) ) )

sd-completeness-at-the-state :
    ( u v : U sd )
  → proj₁ (flat {sd} u) ≡ aa → proj₁ (flat {sd} v) ≡ aa → ¬ ( u ≡ v )
  → ∃[ u′ ] ∃[ v′ ]
      ( ( Canonic.pd*-inj pdi₂ u′ ≡ u ) × ( Canonic.pd*-inj pdi₂ v′ ≡ v )
      × ¬ ( u′ ≡ v′ ) )
sd-completeness-at-the-state u v w≡ w′≡ u≢v
  with sd-recons*-at-pdi₂ u w≡ | sd-recons*-at-pdi₂ v w′≡
... | ( u′ , u′≡ ) | ( v′ , v′≡ ) =
  ( u′ , v′ , u′≡ , v′≡
  , λ u′≡v′ → u≢v (trans (sym u′≡) (trans (cong (Canonic.pd*-inj pdi₂) u′≡v′) v′≡)) )
```

The residuals are read off the two `Recons*` witnesses, and their
distinctness is `u ≢ v` read back through the very same equations — no
injectivity is needed in this direction.  §6's `pdi₂-inj` is the converse
direction, that distinct trees of the state have distinct images in `U sd`;
together the two say the ambiguity of `sd` *is* the A1 witness of the state
`sd-s2` and not an artifact of the transition map (`sd-Ambig-from-A1-at-state`,
§7, does the lifting).  That `flat u′ ≡ []` and `flat v′ ≡ []` — the two
empty trees A1 counts — follows from `Canonic.pd*-ev` and the word equation
`aa ≡ aa ++ proj₁ (flat u′)`.  Unlike the general statement, this one was a
proof exercise rather than a research gap.

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
representatives (A3 — here: the duplicate sum under a context, or the `Idemp`
test on a transition out of a state under a context).  The split
case of the descent — two trees crossing a letter through *different*
instances, i.e. a `LeftU` in one branch and a `RightU` in the other at
some sum — is where the third situation lives.  What closes the argument
is a *pair theorem*: two trees of a common word, one in each of two
expressions, either diagnose a criterion at their sum or find one at a
continuation of that sum along a common word prefix.  This section proves what
is provable without touching neutral lists — the pair's base (`split-+-A1`) and
the syntactic transfer of criteria through contexts (`A2-Ctx`, `dup-Ctx`) — and
states the pair theorem; its proof is the recursion of §13.

```agda
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

-- the fourth disjunct moves the same way: the A3 test is a property of the
-- state *in the hole*, the hole itself only grows
A3-Ctx : ( ctx : AmbigCheck.Ctx ) { q : RE }
  → ( Σ[ ctx₂ ∈ AmbigCheck.Ctx ] Σ[ q′ ∈ RE ] Σ[ c ∈ Char ]
        ( ( AmbigCheck.plug ctx₂ q′ ≡ q )
        × ( Canonic.pd-Idemp? (PosixPD.pdU[ q′ , c ]) ≡ true ) ) )
  → ( Σ[ ctx′ ∈ AmbigCheck.Ctx ] Σ[ q′ ∈ RE ] Σ[ c ∈ Char ]
        ( ( AmbigCheck.plug ctx′ q′ ≡ AmbigCheck.plug ctx q )
        × ( Canonic.pd-Idemp? (PosixPD.pdU[ q′ , c ]) ≡ true ) ) )
A3-Ctx ctx ( ctx₂ , q′ , c , ( plug-eq , test ) ) =
  ( Ctx∘Ctx ctx ctx₂ , q′ , c
  , ( trans (plug-Ctx∘ ctx ctx₂ q′) (cong (AmbigCheck.plug ctx) plug-eq) , test ) )

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

The same situation occurs at any pair of nullable expressions: an `ε∈`
proof constructs an empty tree (the `with`-free recursion mirrors the
`ε∈` constructors), and `split-+-A1` then gives A1 at the sum — the form
in which A1 will keep firing, since the continuation of a sum instance
under `pdinstance-oplus` is a *sum of continuations*, nullable on both
sides whenever the pair of trees reached it.

```agda
ε∈→emptyU : ∀ { r : RE } → ( ε∈r : RE.ε∈ r )
  → Σ[ u ∈ U r ] ( proj₁ (flat {r} u) ≡ [] )
ε∈→emptyU RE.ε∈ε               = ( EmptyU , refl )
ε∈→emptyU ( RE.ε∈_●_ ε∈l ε∈r ) with ε∈→emptyU ε∈l | ε∈→emptyU ε∈r
... | ( u , u≡ ) | ( v , v≡ ) = ( PairU u v , cong₂ _++_ u≡ v≡ )
ε∈→emptyU ( RE.ε∈_+_ ε∈l ε∈r ) with ε∈→emptyU ε∈l
... | ( u , u≡ ) = ( LeftU u , u≡ )
ε∈→emptyU ( RE.ε∈_<+_ ε∈l ε∉r ) with ε∈→emptyU ε∈l
... | ( u , u≡ ) = ( LeftU u , u≡ )
ε∈→emptyU ( RE.ε∈_+>_ ε∉l ε∈r ) with ε∈→emptyU ε∈r
... | ( v , v≡ ) = ( RightU v , v≡ )
ε∈→emptyU RE.ε∈*               = ( ListU [] , refl )

-- A1 at the sum of any two nullable expressions
A1-⊕ : ( l s : RE ) ( loc : ℕ ) ( ε∈l : RE.ε∈ l ) ( ε∈s : RE.ε∈ s )
  → AmbigCheck.AmbigA1 ( l + s ` loc )
A1-⊕ l s loc ε∈l ε∈s with ε∈→emptyU ε∈l | ε∈→emptyU ε∈s
... | ( u , u≡ ) | ( v , v≡ ) = split-+-A1 l s loc u v u≡ v≡
```

For the pair recursion these give the closed first clauses: any pair with
an *empty* tree on one side reaches the first disjunct (the empty tree on
that side and the empty-word tree on the other side are two empty trees
of the sum), and any pair of *literal* trees does too — equal words make
the letters equal, and literals over one letter are `≈₀`-similar, so the
duplicate pattern fires at the sum with the empty context.

```agda
crit-ε+ : ∀ { s : RE } ( loc : ℕ ) ( v : U s )
  → proj₁ (flat {s} v) ≡ [] → crit ( ε + s ` loc )
crit-ε+ {s} loc v v≡
  = inj₁ (A1-⊕ ε s loc RE.ε∈ε
            (Word.[]∈⟦r⟧→ε∈r (subst ( λ w → w ∈⟦ s ⟧) v≡ (proj₂ (flat {s} v)))))

crit-+ε : ∀ { l : RE } ( loc : ℕ ) ( u : U l )
  → proj₁ (flat {l} u) ≡ [] → crit ( l + ε ` loc )
crit-+ε {l} loc u u≡
  = inj₁ (A1-⊕ l ε loc
            (Word.[]∈⟦r⟧→ε∈r (subst ( λ w → w ∈⟦ l ⟧) u≡ (proj₂ (flat {l} u))))
            RE.ε∈ε)

-- two literal trees over the same letter: the duplicate pattern at the sum
crit-$$ : ∀ { c d : Char } { loc₁ loc₂ loc : ℕ }
  → c ≡ d → crit ( ( $ c ` loc₁ ) + ( $ d ` loc₂ ) ` loc )
crit-$$ {c} {d} {loc₁} {loc₂} {loc} c≡d with c≡d
... | refl = inj₂ (inj₂ (inj₁
  ( AmbigCheck.𝟘 , $ c ` loc₁ , $ d ` loc₂ , loc
  , ( refl , Canonic.≈₀-$ c loc₁ loc₂ ) ) ))
```

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
crit-+< l s loc (inj₂ (inj₂ (inj₁ d)))  = inj₂ (inj₂ (inj₁ (dup-Ctx (AmbigCheck.Ctx+R AmbigCheck.𝟘 s loc) d)))
crit-+< l s loc (inj₂ (inj₂ (inj₂ a3))) = inj₂ (inj₂ (inj₂ (A3-Ctx (AmbigCheck.Ctx+R AmbigCheck.𝟘 s loc) a3)))

crit-+> : ( l s : RE ) ( loc : ℕ ) → crit s → crit ( l + s ` loc )
crit-+> l s loc (inj₁ a1)        = inj₁ (A1-+> l s loc a1)
crit-+> l s loc (inj₂ (inj₁ a2)) = inj₂ (inj₁ (A2-Ctx (AmbigCheck.L+Ctx l AmbigCheck.𝟘 loc) a2))
crit-+> l s loc (inj₂ (inj₂ (inj₁ d)))  = inj₂ (inj₂ (inj₁ (dup-Ctx (AmbigCheck.L+Ctx l AmbigCheck.𝟘 loc) d)))
crit-+> l s loc (inj₂ (inj₂ (inj₂ a3))) = inj₂ (inj₂ (inj₂ (A3-Ctx (AmbigCheck.L+Ctx l AmbigCheck.𝟘 loc) a3)))
```

A criterion found at a *concatenation* position must be liftable the same
way — A2 and the duplicate pattern again travel by context composition
(`Ctx●R`/`L●Ctx`).  A1 has no decision to branch on here: an
concatenation is nullable only when *both* factors are, so the sibling's
`ε∈` is taken as a hypothesis (the pair recursion always has one — the
reached trees restrict to it).  `mkAllEmptyU` at `ε∈_●_` enumerates the
full product: `concatMap (map PairU) ` of the two factors' lists.  The
counting never needs the product's *value*, only lower bounds, and those
are proved by induction on the list whose `_++_`/`length` *do* unfold —
never by transporting along `length-++`, which cannot work here: this
stdlib's `length` is a `foldr`, stuck on a neutral `_++_`, so
`length u + length v` is not a reduct of `length (u ++ v)`.

```agda
-- Counting toolkit.  Concatenation is length-monotone in both factors,
-- and strictly so in the right factor when the left is non-empty: proved
-- by induction on the left factor, where `_++_` and `length` *do* unfold.
-- (Transport along `length-++` is used nowhere and could not work: this
-- stdlib's `length` is a `foldr`, stuck on a neutral `_++_`, so
-- `length u + length v` is not a reduct of `length (u ++ v)`.  In
-- `len-++≥` the step goes through `n≤1+n` because `length v` for a
-- neutral `v` does not reduce to a successor, so `s≤s` cannot match it.)
len-++≥ : ∀ {B : Set} ( u v : List B ) → length v ≤ length (u ++ v)
len-++≥ []       v = ≤-refl
len-++≥ (u ∷ us) v = ≤-trans (len-++≥ us v) (n≤1+n (length (us ++ v)))

len-++≥ˡ : ∀ {B : Set} ( u v : List B ) → length u ≤ length (u ++ v)
len-++≥ˡ []       v = z≤n
len-++≥ˡ (u ∷ us) v = s≤s (len-++≥ˡ us v)

len-++≥₁ : ∀ {B : Set} {u v : List B}
  → suc zero ≤ length u → suc (length v) ≤ length (u ++ v)
len-++≥₁ {u = u ∷ us} {v = v} _ = s≤s (len-++≥ us v)

-- a non-empty list has a member, and each block is bounded by its concatMap
1≤len→∈ : ∀ {A : Set} ( xs : List A ) → suc zero ≤ length xs → Σ[ x ∈ A ] ( x ∈ xs )
1≤len→∈ []       ()
1≤len→∈ (x ∷ xs) _ = ( x , here refl )

-- (`xs` is an explicit parameter: with it implicit, `length` of a metavariable
-- has to be inverted against `length (g x)` and the check falls back on
-- foldr inversion)
len∈concatMap : ∀ {A B : Set} ( g : A → List B ) ( xs : List A ) { x : A }
  → x ∈ xs → length (g x) ≤ length (concatMap g xs)
len∈concatMap g []       ()
len∈concatMap g (x ∷ xs) (here refl)  = len-++≥ˡ (g x) (concatMap g xs)
len∈concatMap g (x ∷ xs) (there ∈xs)  =
  ≤-trans (len∈concatMap g xs ∈xs) (len-++≥ (g x) (concatMap g xs))

-- so a concatMap whose blocks all have ≥ 1 element has at least as many
-- elements as there are blocks
length-concatMap≥ : ∀ {A B : Set} ( g : A → List B ) ( xs : List A )
  → ( ∀ x → suc zero ≤ length (g x) ) → length xs ≤ length (concatMap g xs)
length-concatMap≥ g []       _       = z≤n
length-concatMap≥ g (x ∷ xs) g≥1 =
  ≤-trans (s≤s (length-concatMap≥ g xs g≥1))
          (len-++≥₁ {u = g x} {v = concatMap g xs} (g≥1 x))

-- `mkAllEmptyU` enumerates at least one empty tree for every `ε∈` proof
mkAllEmptyU-nonempty : ∀ { r : RE } ( ε∈r : RE.ε∈ r )
  → suc zero ≤ length (mkAllEmptyU {r} ε∈r)
mkAllEmptyU-nonempty RE.ε∈ε = s≤s z≤n
mkAllEmptyU-nonempty {l ● r ` loc} (RE.ε∈_●_ ε∈l ε∈r)
  with 1≤len→∈ (mkAllEmptyU {l} ε∈l) (mkAllEmptyU-nonempty ε∈l)
... | ( u , u∈ ) =
    ≤-trans (subst ( λ n → suc zero ≤ n )
                   (sym (length-map (λ v → PairU {l = l} {r} {loc} u v)
                                    (mkAllEmptyU {r} ε∈r)))
                   (mkAllEmptyU-nonempty ε∈r))
            (len∈concatMap (λ u → map (λ v → PairU {l = l} {r} {loc} u v)
                                      (mkAllEmptyU {r} ε∈r))
                           (mkAllEmptyU {l} ε∈l) u∈)
mkAllEmptyU-nonempty {l + r ` loc} (RE.ε∈_+_ ε∈l ε∈r) =
  ≤-trans (subst ( λ n → suc zero ≤ n )
                 (sym (length-map (λ v → RightU {l = l} {r} {loc} v)
                                  (mkAllEmptyU {r} ε∈r)))
                 (mkAllEmptyU-nonempty ε∈r))
          (len-++≥ (map (λ v → LeftU {l = l} {r} {loc} v) (mkAllEmptyU {l} ε∈l))
                   (map (λ v → RightU {l = l} {r} {loc} v) (mkAllEmptyU {r} ε∈r)))
mkAllEmptyU-nonempty {l + r ` loc} (RE.ε∈_<+_ ε∈l ε∉r) =
  subst ( λ n → suc zero ≤ n )
        (sym (length-map (λ v → LeftU {l = l} {r} {loc} v) (mkAllEmptyU {l} ε∈l)))
        (mkAllEmptyU-nonempty ε∈l)
mkAllEmptyU-nonempty {l + r ` loc} (RE.ε∈_+>_ ε∉l ε∈r) =
  subst ( λ n → suc zero ≤ n )
        (sym (length-map (λ v → RightU {l = l} {r} {loc} v) (mkAllEmptyU {r} ε∈r)))
        (mkAllEmptyU-nonempty ε∈r)
mkAllEmptyU-nonempty RE.ε∈* = s≤s z≤n

-- A1 through the concatenation contexts: the ambiguous factor's trees are
-- paired with every empty tree of the sibling (a nullable expression has
-- at least one), which is exactly the shape `mkAllEmptyU` enumerates at
-- `ε∈_●_`
A1-●< : ( l s : RE ) ( loc : ℕ ) ( ε∈s : RE.ε∈ s )
  → AmbigCheck.AmbigA1 l → AmbigCheck.AmbigA1 ( l ● s ` loc )
A1-●< l s loc ε∈s ( ε∈l , len ) =
  ( RE.ε∈_●_ ε∈l ε∈s
  , ≤-trans len (length-concatMap≥ f (mkAllEmptyU {l} ε∈l) block) )
  where
    f : U l → List (U ( l ● s ` loc ))
    f u = map (λ v → PairU {l = l} {s} {loc} u v) (mkAllEmptyU {s} ε∈s)
    block : ∀ u → suc zero ≤ length (f u)
    block u = subst ( λ n → suc zero ≤ n )
                    (sym (length-map (λ v → PairU {l = l} {s} {loc} u v)
                                     (mkAllEmptyU {s} ε∈s)))
                    (mkAllEmptyU-nonempty ε∈s)

A1-●> : ( l s : RE ) ( loc : ℕ ) ( ε∈l : RE.ε∈ l )
  → AmbigCheck.AmbigA1 s → AmbigCheck.AmbigA1 ( l ● s ` loc )
A1-●> l s loc ε∈l ( ε∈s , len )
  with 1≤len→∈ (mkAllEmptyU {l} ε∈l) (mkAllEmptyU-nonempty ε∈l)
... | ( u , u∈ ) =
  ( RE.ε∈_●_ ε∈l ε∈s
  , ≤-trans (subst ( λ n → suc (suc zero) ≤ n )
                   (sym (length-map (λ v → PairU {l = l} {s} {loc} u v)
                                    (mkAllEmptyU {s} ε∈s)))
                   len)
            (len∈concatMap f (mkAllEmptyU {l} ε∈l) u∈) )
  where
    f : U l → List (U ( l ● s ` loc ))
    f u = map (λ v → PairU {l = l} {s} {loc} u v) (mkAllEmptyU {s} ε∈s)

-- a criterion found at a concatenation position is a criterion at the
-- enclosing concatenation (the sibling's nullability is carried along)
crit-●< : ( l s : RE ) ( loc : ℕ ) ( ε∈s : RE.ε∈ s ) → crit l → crit ( l ● s ` loc )
crit-●< l s loc ε∈s (inj₁ a1)        = inj₁ (A1-●< l s loc ε∈s a1)
crit-●< l s loc ε∈s (inj₂ (inj₁ a2)) = inj₂ (inj₁ (A2-Ctx (AmbigCheck.Ctx●R AmbigCheck.𝟘 s loc) a2))
crit-●< l s loc ε∈s (inj₂ (inj₂ (inj₁ d)))  = inj₂ (inj₂ (inj₁ (dup-Ctx (AmbigCheck.Ctx●R AmbigCheck.𝟘 s loc) d)))
crit-●< l s loc ε∈s (inj₂ (inj₂ (inj₂ a3))) = inj₂ (inj₂ (inj₂ (A3-Ctx (AmbigCheck.Ctx●R AmbigCheck.𝟘 s loc) a3)))

crit-●> : ( l s : RE ) ( loc : ℕ ) ( ε∈l : RE.ε∈ l ) → crit s → crit ( l ● s ` loc )
crit-●> l s loc ε∈l (inj₁ a1)        = inj₁ (A1-●> l s loc ε∈l a1)
crit-●> l s loc ε∈l (inj₂ (inj₁ a2)) = inj₂ (inj₁ (A2-Ctx (AmbigCheck.L●Ctx l AmbigCheck.𝟘 loc) a2))
crit-●> l s loc ε∈l (inj₂ (inj₂ (inj₁ d)))  = inj₂ (inj₂ (inj₁ (dup-Ctx (AmbigCheck.L●Ctx l AmbigCheck.𝟘 loc) d)))
crit-●> l s loc ε∈l (inj₂ (inj₂ (inj₂ a3))) = inj₂ (inj₂ (inj₂ (A3-Ctx (AmbigCheck.L●Ctx l AmbigCheck.𝟘 loc) a3)))
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
embeddings.  A path is therefore never threaded *through* a sum head: it
is anchored at the state the descent stands in — which for the pair
theorem means the sum itself, as the counterexample below shows.

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

-- membership injection into a concatenation, from the right part
any-++₂ : ∀ { A : Set } { P : A → Set } ( xs : List A ) { ys : List A }
  → Any P ys → Any P (xs ++ ys)
any-++₂ [] p = p
any-++₂ (x ∷ xs) p = there (any-++₂ xs p)

-- membership in a concatenated list, from membership in the parts
any-concatMap : ∀ { A B : Set } ( g : A → List B ) { xs : List A } { P : B → Set }
  → Any ( λ x → Any P (g x) ) xs → Any P (concatMap g xs)
any-concatMap g {xs = x ∷ xs} (here p) = any++₁ {ys = concatMap g xs} p
any-concatMap g {xs = x ∷ xs} (there m) =
  any-++₂ (g x) {ys = concatMap g xs} (any-concatMap g m)

-- the run instance of a path: steps are composed with `compose-pdi-with`,
-- exactly as `advance-pdi*-with-c` composes a head instance with a `pdU`
-- step, so each constructed step *heads* the concatMap that `chain*`
-- unfolds to, and membership follows by construction.  (The constructors
-- are matched directly in the left-hand sides, not through `with`: the
-- Path field's type mentions `pd*-expr hd` and must reduce through the
-- matched constructor — a `with`-abstraction leaves `z : PDInstance
-- (pd*-expr hd) c` stuck on the un-reduced projection.)
path-chain : ∀ { r pref ws } ( hd : PDInstance* r pref )
  → Path (Canonic.pd*-expr hd) ws
  → PDInstance* r (pref ++ ws)
path-chain {r} {pref} hd pnil = hd
path-chain {r} {pref} (pdinstance* {d} d→r ev)
               (pcons {c = c} {ws = ws} z@(pdinstance {p} p→d evz) m q) =
  path-chain {r} {pref = pref ∷ʳ c} (compose-pdi-with {r} {d} {pref} {c} d→r ev z) q

path-chain∈ : ∀ { r pref ws } ( hd : PDInstance* r pref )
  ( π : Path (Canonic.pd*-expr hd) ws )
  → path-chain hd π ∈ chain* {r} {pref} hd ws
path-chain∈ hd pnil = here refl
path-chain∈ {r} {pref} (pdinstance* {d} d→r ev)
                     (pcons {c = c} {ws = ws} z@(pdinstance {p} p→d evz) m q) =
  any-concatMap ( λ x → chain* {r} {pref ∷ʳ c} x ws )
    ( map-Any (compose-pdi-with {r} {d} {pref} {c} d→r ev)
        ( λ a eq → subst ( λ h → path-chain (compose-pdi-with {r} {d} {pref} {c} d→r ev z) q
                              ∈ chain* {r} {pref ∷ʳ c} h ws )
                         ( cong (compose-pdi-with {r} {d} {pref} {c} d→r ev) eq )
                         ( path-chain∈ (compose-pdi-with {r} {d} {pref} {c} d→r ev z) q ) )
        m )

path-chain-pd : ∀ { r pref ws } ( hd : PDInstance* r pref )
  ( π : Path (Canonic.pd*-expr hd) ws )
  → Canonic.pd*-expr (path-chain hd π) ≡ pdend π
path-chain-pd hd pnil = refl
path-chain-pd {r} {pref} (pdinstance* {d} d→r ev)
                       (pcons {c = c} {ws = ws} z@(pdinstance {p} p→d evz) m q) =
  path-chain-pd (compose-pdi-with {r} {d} {pref} {c} d→r ev z) q

-- the run-lift bridge in path form (the B3a reverse direction): a path
-- from r is a run of r for its word, so its end state appears in
-- pd*-Desc r w: the path instance is a member of `chain* hd₀ w` through
-- `path-chain∈`, and `chain-aux` (§10) identifies that singleton run
-- with `pdUMany[ r , w ]` itself.  (The §11 route `pdni∘` composes
-- *after* a run and would first need the syntactic identity
-- `pdni∘ hd id ≡ hd`, which its soundness-evidence plumbing does not
-- give; `compose-pdi-with` builds the instance in the very shape of the
-- list that contains it.)
pdesc : ∀ { r w } ( π : Path r w )
  → Any ( λ x → x ≡ pdend π ) (Canonic.pd*-Desc r w)
pdesc pnil = here refl
pdesc {r} π@(pcons {c = c} {ws = ws} z m q) =
  map-Any Canonic.pd*-expr
    ( λ a eq → trans ( cong Canonic.pd*-expr ( sym eq ) ) ( path-chain-pd hd₀ π ) )
    ( subst ( λ L → path-chain hd₀ π ∈ L ) ( chain-aux hd₀ (c ∷ ws) )
        ( path-chain∈ hd₀ π ) )
  where
    hd₀ : PDInstance* r []
    hd₀ = pdinstance* {r} {r} {[]} injId injId-sound
```

## 13. One letter of the pair: reconstruction and fusion

Both trees of the pair consume the same first letter, so `pdU-complete`
turns each of them into a member of *its own* expression's instance list
together with a reconstruction witness.  Four small facts turn that pair
of members into **one** step of the sum state, and together with
`split-+-A1` (§12) they are the whole of the pair descent: the pick out of
a list, the residual tree and its forced word, the membership of the pair
in the sum's list, and the equation saying where that step lands.

```agda
-- a member of an instance list, with its witness.  The list is a
-- parameter and not the stuck term `pdU[ r , c ]` of the call sites: the
-- case-split has to happen once, here.
pick-Any : ∀ { A : Set } { P : A → Set } { xs : List A }
  → Any P xs
  → Σ[ y ∈ A ] ( P y × y ∈ xs )
pick-Any (here {x = y} {xs = xs} p) = ( y , p , here refl )
pick-Any (there {xs = xs} p) with pick-Any p
... | ( y , q , m ) = ( y , q , there m )

-- the residual of a reconstruction: its word is *forced* to be the tail,
-- because the instance's soundness evidence prefixes the same letter on
-- both sides.  No `flat∘unflat` is needed — the equation is read off the
-- instance's own evidence.
Recons-residual : ∀ { r : RE } { c : Char } { pdi : PDInstance r c } { u : U r } { ws : List Char }
  → Recons {r} {c} u pdi
  → proj₁ (flat {r} u) ≡ c ∷ ws
  → Σ[ x ∈ U (Canonic.pd-expr pdi) ] ( proj₁ (flat {Canonic.pd-expr pdi} x) ≡ ws )
Recons-residual {pdi = pdinstance {p} inj ev} (recons _ ( w∈ , eq )) u≡cw =
  ( unflat w∈
  , proj₂ (∷-inj (trans (sym (ev (unflat w∈))) (trans (cong ( λ z → proj₁ (flat z) ) eq) u≡cw))) )

-- membership in a concatenation, from membership in one of the parts
∈-concatMap : ∀ { A B : Set } ( f : A → List B ) ( xs : List A ) { x : A }
  → x ∈ xs → { y : B } → y ∈ f x → y ∈ concatMap f xs
∈-concatMap f [] () q
∈-concatMap f (x ∷ xs) (here refl) q = any++₁ {ys = concatMap f xs} q
∈-concatMap f (x ∷ xs) (there p) q =
  any-++₂ (f x) {ys = concatMap f xs} (∈-concatMap f xs p q)

-- `⊕` of two *non-empty* instance lists: every member pair gives one
-- member, through `fuse` — the sum's derivative really is pairwise.
∈-oplus-fuse : ∀ { r : RE } { loc : ℕ } { c : Char } { zl zr : PDInstance r c }
  ( xl xr : List (PDInstance r c) )
  → zl ∈ xl → zr ∈ xr
  → fuse {r} {loc} {c} zl zr ∈ pdinstance-oplus {r} {loc} {c} xl xr
∈-oplus-fuse [] xr () q
∈-oplus-fuse (x ∷ xs) [] p ()
∈-oplus-fuse {r} {loc} {c} {zl} {zr} (x ∷ xs) (y ∷ ys) p q
  = ∈-concatMap (λ pdiˡ → map (fuse {r} {loc} {c} pdiˡ) (y ∷ ys)) (x ∷ xs) p
      (map-Any (fuse {r} {loc} {c} zl) (λ w eq → cong (fuse {r} {loc} {c} zl) eq) q)

-- the instance pair of a letter step at a sum, in the shape `pdU` puts in
-- its own list (PartialDerivative 396–399)
fuse-⊕ : ∀ { l s : RE } { loc : ℕ } { c : Char }
  → PDInstance l c → PDInstance s c → PDInstance ( l + s ` loc ) c
fuse-⊕ {l} {s} {loc} {c} zl zr = fuse {l + s ` loc} {loc} {c} (pdinstance-left {l} {s} {loc} {c} zl)
                                                  (pdinstance-right {l} {s} {loc} {c} zr)

-- the pair of instances *is* an instance of the sum, and its continuation
-- is the sum of the two continuations — which is exactly the state the
-- recursive call of the pair theorem stands in.
pdU∈-⊕ : ∀ { l s : RE } { loc : ℕ } { c : Char }
  ( zl : PDInstance l c ) ( zr : PDInstance s c )
  → zl ∈ PosixPD.pdU[ l , c ] → zr ∈ PosixPD.pdU[ s , c ]
  → fuse-⊕ {l} {s} {loc} {c} zl zr ∈ PosixPD.pdU[ l + s ` loc , c ]
pdU∈-⊕ {l} {s} {loc} {c} zl zr zl∈ zr∈
  = ∈-oplus-fuse {l + s ` loc} {loc} {c}
      (map (pdinstance-left {l} {s} {loc} {c}) (PosixPD.pdU[ l , c ]))
      (map (pdinstance-right {l} {s} {loc} {c}) (PosixPD.pdU[ s , c ]))
      (map-Any (pdinstance-left {l} {s} {loc} {c}) (λ a eq → cong (pdinstance-left {l} {s} {loc} {c}) eq) zl∈)
      (map-Any (pdinstance-right {l} {s} {loc} {c}) (λ a eq → cong (pdinstance-right {l} {s} {loc} {c}) eq) zr∈)

pd-expr-fuse-⊕ : ∀ { l s : RE } { loc : ℕ } { c : Char }
  ( zl : PDInstance l c ) ( zr : PDInstance s c )
  → Canonic.pd-expr (fuse-⊕ {l} {s} {loc} {c} zl zr)
    ≡ (Canonic.pd-expr zl) + (Canonic.pd-expr zr) ` loc
pd-expr-fuse-⊕ (pdinstance {p} inj ev) (pdinstance {p₂} g ev₂) = refl

-- carrying a whole found path across such a continuation equation (the
-- `crit (pdend π)` component moves with it, which a path-only transport
-- could not say)
Path-rescue : ( r r′ : RE ) ( w : List Char ) → r ≡ r′
  → ( Σ[ π ∈ Path r w ] crit (pdend π) ) → ( Σ[ π ∈ Path r′ w ] crit (pdend π) )
Path-rescue r r′ w eq = subst ( λ e → Σ[ π ∈ Path e w ] crit (pdend π) ) eq
```

The pair theorem proper recurses on the *two trees*.  The first form one
tries for it anchors the path disjunct *below* one of the two branches —
a path in `l` or in `s`.  That form is **false**: take
`u = LeftU (LetterU a) : U ( $ a \` 1 + ε )` and `v = LetterU a :
U ( $ a \` 2 )`, both with word `[ a ]`.  No criterion holds at the sum
`( $ a \` 1 + ε ) + $ a \` 2` — it has exactly one empty tree (via the
inner right branch), no concatenation subterm, and its two branch
expressions are `≈₀`-apart — and no criterion is reachable below either
branch: the only path below `l` for `[ a ]` and the only path below `s`
both end at `ε`, where no criterion ever holds.  What happens instead:
`pdU[ ( $ a \` 1 + ε ) + $ a \` 2 , a ]` has exactly *one* member — the
`fuse` pairing of the two branch instances (the fusion remark above) —
and that member's continuation is `ε + ε`, precisely the state where
`split-+-A1` fires A1.  The witness of a branching pair lives at the
*fused derivative*, not below either branch.  Since the pair's own letter
steps are instances of the sum (the fused ones), the path disjunct must
be anchored at the sum itself:

```agda
-- the recursion is on the word `w`; Agda's structural check cannot see it
-- through the three nested `with` abstractions and the index-transporting
-- `Path-rescue`, and reports the (pre-existing, previously unchecked) call
-- graph as non-positive
pair-complete : ∀ { l s : RE } ( loc : ℕ ) ( w : List Char )
  ( u : U l ) ( v : U s )
  → proj₁ (flat {l} u) ≡ w → proj₁ (flat {s} v) ≡ w
  → crit ( l + s ` loc )
  ⊎ ( ∃[ w′ ] ∃[ w″ ] ( ( w ≡ w′ ++ w″ )
        × ( Σ[ π ∈ Path ( l + s ` loc ) w′ ] crit (pdend π) ) ) )
pair-complete {l} {s} loc [] u v u≡ v≡ = inj₁ (inj₁ (split-+-A1 l s loc u v u≡ v≡))
pair-complete {l} {s} loc (c ∷ w) u v u≡ v≡
  with pick-Any (pdU-complete {l} {c} u u≡) | pick-Any (pdU-complete {s} {c} v v≡)
... | ( zl , rec-l , zl∈ ) | ( zr , rec-r , zr∈ )
    with Recons-residual rec-l u≡ | Recons-residual rec-r v≡
...   | ( x , x≡ ) | ( y , y≡ )
      with pair-complete {l = Canonic.pd-expr zl} {s = Canonic.pd-expr zr} loc w x y x≡ y≡
...     | inj₁ cr = inj₂ ( [ c ] , w , refl
                          , ( pcons (fuse-⊕ {l} {s} {loc} {c} zl zr)
                              (pdU∈-⊕ {l} {s} {loc} {c} zl zr zl∈ zr∈) pnil
                            , subst crit (sym (pd-expr-fuse-⊕ {l} {s} {loc} {c} zl zr)) cr ) )
...     | inj₂ ( w′ , w″ , w≡w′++w″ , π )
          = inj₂ ( ( c ∷ w′ ) , w″ , cong (c ∷_) w≡w′++w″
                  , let ( π′ , cr′ ) = Path-rescue (Canonic.pd-expr zl + Canonic.pd-expr zr ` loc)
                                                   (Canonic.pd-expr (fuse-⊕ {l} {s} {loc} {c} zl zr)) w′
                                                   (sym (pd-expr-fuse-⊕ {l} {s} {loc} {c} zl zr)) π
                    in ( pcons (fuse-⊕ {l} {s} {loc} {c} zl zr)
                           (pdU∈-⊕ {l} {s} {loc} {c} zl zr zl∈ zr∈) π′ , cr′ ) )
```

The recursion is on the word and it is uniform: `pdU-complete` supplies a
reconstructing instance of each tree's *own* expression,
`Recons-residual` reads off the residual tree together with the fact that
its word is the tail (both sides share that tail), and `pdU∈-⊕` shows
that the two instances — mapped through `pdinstance-left`/`pdinstance-right`
and paired by `fuse` — form **one** member of the sum's own list, whose
continuation is `pd-expr zl + pd-expr zr \` loc` (`pd-expr-fuse-⊕`).  One
recursive call at that continuation plus one `pcons` step is therefore a
step at the sum; when the recursive call stops *at* the continuation the
same single step ends the path there, with `w′ = [ c ]`.  The empty-word
case needs no recursion at all: `split-+-A1` fires A1 at the sum for *any*
pair of empty trees — that is the content of `crit-ε+`/`crit-+ε` — and a
pair of literal trees is the other closed form (`crit-$$`: equal words make
the letters equal, so the two branches are `≈₀`-similar and the duplicate
pattern fires with `ctx = 𝟘`).  Those three lemmas are not clauses of the
recursion — the uniform step covers their pairs too — they are the closed
forms the paper enumerates, kept as such.

(A counting refinement sharpens the recursion: `pdU[ r , c ]` has more than
one member only below a nullable concatenation, where
`concatmap-pdinstance-snd` enumerates one instance per empty tree of the
left factor — the paper's "these are the only situations" in counting
form.)

## 14. The split case of `completeness`

With the path form of the descent (§12) and the pair theorem (§13), the split
case of the §8 statement needs no further machinery: a path *is* a
pd-descendant membership (`pdesc`), and the sum itself is the pd-descendant of
the empty prefix (`pdesc pnil`).

```agda
-- §8's conclusion for a pair that splits at a sum: the left-injection tree
-- and the right-injection tree of `l + s \` loc` have one word, and the
-- criterion the pair theorem finds sits at a pd-descendant state of the sum.
split-completeness : ∀ { l s : RE } ( loc : ℕ ) ( w : List Char )
  ( u : U l ) ( v : U s )
  → proj₁ (flat {l} u) ≡ w → proj₁ (flat {s} v) ≡ w
  → ∃[ w′ ] ∃[ w″ ]
      ( ( w ≡ w′ ++ w″ )
      × ∃[ p ]
          ( Any ( λ t → t ≡ p ) (Canonic.pd*-Desc ( l + s ` loc ) w′)
          × crit p ) )
split-completeness {l} {s} loc w u v u≡ v≡ with pair-complete loc w u v u≡ v≡
... | inj₁ cr = ( [] , w , refl , ( l + s ` loc , pdesc pnil , cr ) )
... | inj₂ ( w′ , w″ , w≡w′++w″ , ( path , cr ) )
    = ( w′ , w″ , w≡w′++w″ , ( pdend path , pdesc path , cr ) )
```

That is the one shape of the general `completeness` which is closed: the two
trees disagree *between the branches of a sum*.  What the general statement
still asks for is the descent through the remaining constructors — a path
below `l` lifted to `l + s \` loc`, `l ● s \` loc` (through
`pdinstance-fst` and `concatmap-pdinstance-snd`, the second together with the
empty-tree split of §12's counting lemmas) and `r ⋆` through
`pdinstance-star`; and the pairs that disagree *inside* one branch, where the
two trees no longer share a word but split it — precisely the situation A2's
nullable-left condition is about.

## 15. Lifting across a state extension

Each step of that descent needs two things: a path at the parent expression,
and a criterion that survives the state extension the step performs.  The
case in which **both** sides of a sum derive the word needs no decision about
computed lists at all — `pdinstance-oplus` pairs them, and §13 already has the
membership, so the two paths simply fuse:

```agda
-- two paths of one word, one per branch, fuse into one path at the sum
-- two paths of one word, one per branch, fuse into one path at the sum.
-- (The word shape is pinned in the head patterns: matching `pcons` against a
-- rigid index `w` only elaborates when the clause names the shape itself.)
Path-⊕ : ∀ { l s : RE } ( loc : ℕ ) { w : List Char }
  → Path l w → Path s w → Path ( l + s ` loc ) w
Path-⊕ {l} {s} loc {w = []} pnil pnil = pnil
Path-⊕ {l} {s} loc {w = c ∷ ws} (pcons z m π) (pcons z′ m′ π′) =
  pcons (fuse-⊕ {l} {s} {loc} {c} z z′) (pdU∈-⊕ {l} {s} {loc} {c} z z′ m m′)
        ( subst ( λ e → Path e ws )
            ( sym (pd-expr-fuse-⊕ {l} {s} {loc} {c} z z′) )
            ( Path-⊕ {l = Canonic.pd-expr z} {s = Canonic.pd-expr z′} loc π π′ ) )

-- transporting a path does not move its end state
pdend-subst : ∀ { r r′ : RE } { w : List Char } ( eq : r ≡ r′ ) ( π : Path r w )
  → pdend ( subst ( λ e → Path e w ) eq π ) ≡ pdend π
pdend-subst refl π = refl

-- and it ends where the two branches end, summed
pdend-Path-⊕ : ∀ { l s : RE } ( loc : ℕ ) { w : List Char }
  ( π : Path l w ) ( π′ : Path s w )
  → pdend (Path-⊕ {l} {s} loc π π′) ≡ pdend π + pdend π′ ` loc
pdend-Path-⊕ {l} {s} loc {w = []} pnil pnil = refl
pdend-Path-⊕ {l} {s} loc {w = c ∷ ws} (pcons z m π) (pcons z′ m′ π′) =
  trans (pdend-subst
           (sym (pd-expr-fuse-⊕ {l} {s} {loc} {c} z z′))
           (Path-⊕ {l = Canonic.pd-expr z} {s = Canonic.pd-expr z′} loc π π′))
        (pdend-Path-⊕ {l = Canonic.pd-expr z} {s = Canonic.pd-expr z′} loc π π′)
```

The star is the dual situation: `pdU[ r * ε∉r \` loc , c ]` is `pdU[ r , c ]`
*through* `pdinstance-star`, so no fusion happens — but every state below `r`
becomes the concatenation `(p ● r ⋆ \` loc)`, a concatenation whose right
factor is nullable.  That is the shape §12's `crit-●<` consumes, with the
sibling's `ε∈` supplied by `RE.ε∈*`:

```agda
pd-expr-star : ∀ { r : RE } { ε∉r : RE.ε∉ r } { loc : ℕ } { c : Char }
  ( pdi : PDInstance r c )
  → Canonic.pd-expr (pdinstance-star {r} {ε∉r} {loc} {c} pdi)
      ≡ (Canonic.pd-expr pdi) ● ( r * ε∉r ` loc ) ` loc
pd-expr-star (pdinstance {p} f s-ev) = refl

crit-*< : ∀ { r : RE } ( ε∉r : RE.ε∉ r ) ( loc : ℕ ) ( p : RE )
  → crit p → crit ( p ● ( r * ε∉r ` loc ) ` loc )
crit-*< {r} ε∉r loc p cr = crit-●< p ( r * ε∉r ` loc ) loc RE.ε∈* cr
```

Composing the fused paths with `pdesc` (§12) and `crit-+<` (§12) yields the
first piece of the general §8 conclusion: a criterion at a state reached below
*one* branch of a sum, at a word the other branch derives as well, is a
criterion at a pd-descendant state **of the sum**.

```agda
Desc-⊕-crit : ∀ { l s : RE } ( loc : ℕ ) { w : List Char }
  ( π : Path l w ) ( π′ : Path s w )
  → crit (pdend π)
  → ∃[ p ]
      ( Any ( λ t → t ≡ p ) (Canonic.pd*-Desc ( l + s ` loc ) w)
      × crit p )
Desc-⊕-crit {l} {s} loc π π′ cr =
  ( pdend (Path-⊕ loc π π′) , pdesc (Path-⊕ loc π π′)
  , subst crit (sym (pdend-Path-⊕ loc π π′))
      (crit-+< (pdend π) (pdend π′) loc cr) )
```

What is *not* covered by these two lemmas is exactly the decision the fusion
postpones: when only one side derives the word, `pdinstance-oplus`'s singleton
equations put the one path through unchanged and no state extension happens.
That case cannot be lifted symbolically at all — it is §4's obstacle, now with
its reason.  `pdU[ l ● s \` loc , c ]` branches on `RE.ε∈? l`, and for a
symbolic `l` that decision never reduces, so which list the membership lives in
is not observable; splitting `l`'s head constructor does not help, because
`ε∈?` recurses into `l`'s sub-expressions, which are still variables, and
`pdinstance-fst pdi ∈ pdU[ l ● s \` loc , c ]` is unprovable there.  (`⊕` is the
opposite case: `pdinstance-oplus` needs nothing about either side beyond the two
members, so fusion *is* available symbolically — that is `pdU∈-⊕`.)  The
general statement therefore cannot be assembled by lifting paths from a
subexpression to its parent.  Either the derivative is redefined symbolically,
with one clause per pair of expression shapes so that the branch is taken in the
definition rather than in the proof, or the descent is run the way §13 runs the
pair: never asking whether a list is empty, only taking a member of it out of
`pdU-complete` for the tree in hand — which is why the pair theorem could be
proved at all.  That second way is the one taken in §16.

## 16. The remaining step, stated exactly

`pair-complete` (§13) treats a pair of trees living in **two** expressions —
that is what a sum's branches are, and it is why the split case closed.  The
general `completeness` is the case where both trees live in **one** expression
`r`, so the descent has to stay inside `r`'s own states.  Stating that case as
its own goal is what is left of the paper's proposition — and the §8 statement
is reducible to it.

```agda
-- what the descent produces at a state for a word
desc-concl : ( r : RE ) → ( w : List Char ) → Set
desc-concl r w = crit r
             ⊎ ( ∃[ w′ ] ∃[ w″ ] ( ( w ≡ w′ ++ w″ )
                   × ( Σ[ π ∈ Path r w′ ] crit (pdend π) ) ) )

-- THE GOAL, as a type: two distinct trees of one expression and one word —
-- a prefix of that word reaches a state at which a criterion fires.
Desc-complete : Set
Desc-complete = ∀ ( r : RE ) ( w : List Char ) ( u v : U r )
  → proj₁ (flat {r} u) ≡ w → proj₁ (flat {r} v) ≡ w → ¬ ( u ≡ v )
  → desc-concl r w
```

`Desc-complete` is a recursion on the word, and both halves of that recursion
are proved here; what is missing is one case inside the step, not the shape of
the proof.

```agda
-- the base: two distinct empty trees of `r` *are* A1 at `r` (§9)
desc-base : ∀ { r : RE } ( u v : U r )
  → proj₁ (flat {r} u) ≡ [] → proj₁ (flat {r} v) ≡ [] → ¬ ( u ≡ v )
  → desc-concl r []
desc-base u v u≡[] v≡[] u≢v = inj₁ (inj₁ (base-A1-at-root _ u v u≡[] v≡[] u≢v))

-- the step: one letter through *one* instance carries a conclusion of the
-- continuation back to the state — the path is extended by `pcons`, the word
-- split by one letter.  Note that it constructs no instance of the
-- continuation and examines no list.
desc-step : ∀ { r : RE } { c : Char } { ws : List Char }
  ( z : PDInstance r c ) → z ∈ PosixPD.pdU[ r , c ]
  → desc-concl (Canonic.pd-expr z) ws → desc-concl r (c ∷ ws)
desc-step {r} {c} {ws} z z∈ (inj₁ cr) =
  inj₂ ( [ c ] , ws , refl , ( pcons z z∈ pnil , cr ) )
desc-step {r} {c} {ws} z z∈ (inj₂ ( w′ , w″ , w≡w′++w″ , path , cr )) =
  inj₂ ( ( c ∷ w′ ) , w″ , cong (c ∷_) w≡w′++w″
        , ( pcons z z∈ path , cr ) )

-- and a shared instance really does carry the pair down: reconstructed through
-- one and the same instance, the residuals have the same word and *remain*
-- distinct, since the instance's transition map sends them to distinct trees
Recons-residual-2 : ∀ { r : RE } { c : Char } { ws : List Char } { z : PDInstance r c } { u v : U r }
  → Recons {r} {c} u z → Recons {r} {c} v z
  → proj₁ (flat {r} u) ≡ c ∷ ws → proj₁ (flat {r} v) ≡ c ∷ ws → ¬ ( u ≡ v )
  → Σ[ x ∈ U (Canonic.pd-expr z) ] Σ[ y ∈ U (Canonic.pd-expr z) ]
      ( proj₁ (flat {Canonic.pd-expr z} x) ≡ ws
      × proj₁ (flat {Canonic.pd-expr z} y) ≡ ws
      × ¬ ( x ≡ y ) )
Recons-residual-2 {z = pdinstance {p} inj ev} (recons _ ( w∈u , eq-u )) (recons _ ( w∈v , eq-v )) u≡ v≡ u≢v =
  ( unflat w∈u , unflat w∈v
  , proj₂ (∷-inj (trans (sym (ev (unflat w∈u))) (trans (cong ( λ t → proj₁ (flat t) ) eq-u) u≡)))
  , proj₂ (∷-inj (trans (sym (ev (unflat w∈v))) (trans (cong ( λ t → proj₁ (flat t) ) eq-v) v≡)))
  , λ x≡y → u≢v (trans (sym eq-u) (trans (cong inj x≡y) eq-v)) )
```

The gap is inside the step and it is a single case.  `pdU-complete` gives *an*
instance for `u` and *an* instance for `v`: when those coincide,
`Recons-residual-2` supplies the residuals and `desc-step` closes the step.
When they do not, the residuals live at different states and need not be
distinct at all, so the step cannot continue by recursion; what closes that
case is a diagnosis *at the state* — the paper's enumeration of the only
situations in which the transition-tree construction branches.  A first guess
would be the counting form: two members of `pdU[ r , c ]` arise only where `pdU`
duplicates instances, below a nullable concatenation through
`concatmap-pdinstance-snd`, one instance per empty tree of the left factor.
§17 shows that guess is wrong as stated — a *sum* whose left branch reappears in
its right branch derives the *same* tree through the branch injection and through
the fused member `pdU` computes, with no concatenation in the expression at all
— and it also shows what saves the argument: the two derivations differ by an
injection through a sum of `≈₀`-similar alternatives, which is exactly the
`Idemp`/A3 situation, the duplicate pattern this project states (`crit`'s third
disjunct) and proves sound but does not test; §18 exhibits that witness at the
example and runs the descent to it.  So the classification has to be made on the *canonical*
expression, where such alternatives have been merged, and that is the content of
the completeness direction; §12's counting toolkit (`mkAllEmptyU-nonempty`,
`length-concatMap≥`) is the half of it that is here.

What is proved is the reduction: the §8 goal is a corollary of `Desc-complete`,
because a path is a `pd*-Desc` membership (`pdesc`) and the state itself is the
pd-descendant of the empty prefix.

```agda
completeness-from-desc : ( dc : Desc-complete )
  → ( r : RE ) ( u v : U r )
  → proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) → ¬ ( u ≡ v )
  → ∃[ w′ ] ∃[ w″ ]
      ( ( proj₁ (flat {r} u) ≡ w′ ++ w″ )
      × ∃[ p ] ( Any ( λ s → s ≡ p ) (Canonic.pd*-Desc r w′) × crit p ) )
completeness-from-desc dc r u v w≡ u≢v with dc r (proj₁ (flat {r} u)) u v refl (sym w≡) u≢v
... | inj₁ cr = ( [] , proj₁ (flat {r} u) , refl , ( r , pdesc pnil , cr ) )
... | inj₂ ( w′ , w″ , w≡w′++w″ , ( path , cr ) )
    = ( w′ , w″ , w≡w′++w″ , ( pdend path , pdesc path , cr ) )
```

## 17. The cross-instance case, and what it really needs

§16's missing case is the one where `pdU-complete` hands the two trees *different*
instances.  A concrete example, checked here, says what that case is — and it is
not what a first reading of the paper suggests.

```agda
ca : Char
ca = 'a'

dup-l1 : RE
dup-l1 = ( $ 'a' ` 1)

dup-l2 : RE
dup-l2 = ( $ 'a' ` 2)

-- the instances of the two literals, in the exact shape `pdU` writes into its
-- list (the soundness evidence is `pdU`'s own reasoning block, so these *are*
-- the members `pdU` computes)
dup-id1 : PDInstance dup-l1 ca
dup-id1 = ( pdinstance {ε} {dup-l1} {ca}
                      (λ u → LetterU {loc = 1} ca)
                      (λ EmptyU →
                         begin
                           [ ca ]
                         ≡⟨⟩
                           ca ∷ []
                         ≡⟨ cong ( λ x → ( ca ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                           ca ∷ (proj₁ (flat EmptyU))
                         ∎) )

dup-id2 : PDInstance dup-l2 ca
dup-id2 = ( pdinstance {ε} {dup-l2} {ca}
                      (λ u → LetterU {loc = 2} ca)
                      (λ EmptyU →
                         begin
                           [ ca ]
                         ≡⟨⟩
                           ca ∷ []
                         ≡⟨ cong ( λ x → ( ca ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                           ca ∷ (proj₁ (flat EmptyU))
                         ∎) )

-- a literal derives to exactly its own singleton instance, and a sum of two
-- literals that both derive has exactly *one* member: the fusion
pdU-$a1≡ : PosixPD.pdU[ dup-l1 , ca ] ≡ ( dup-id1 ∷ [] )
pdU-$a1≡ = refl

dup-s1 : RE
dup-s1 = ( dup-l1 + dup-l2 ` 3 )

pdU-⊕-lit≡ : PosixPD.pdU[ dup-s1 , ca ]
  ≡ ( fuse {dup-s1} {3} {ca}
           (pdinstance-left {dup-l1} {dup-l2} {3} {ca} dup-id1)
           (pdinstance-right {dup-l1} {dup-l2} {3} {ca} dup-id2) ∷ [] )
pdU-⊕-lit≡ = refl

-- now the duplicated sum ( ($a`1) + dup-s1 ` 0 ): one letter `a` reaches a
-- member built from the branch instance *and* a member fusing it with the right
-- branch's instance — membership needs no emptiness decision, it is §13's
-- `pdU∈-⊕`
dup-s1-ca : PDInstance dup-s1 ca
dup-s1-ca = fuse {dup-s1} {3} {ca}
                 (pdinstance-left {dup-l1} {dup-l2} {3} {ca} dup-id1)
                 (pdinstance-right {dup-l1} {dup-l2} {3} {ca} dup-id2)

dup-s1-ca∈ : dup-s1-ca ∈ PosixPD.pdU[ dup-s1 , ca ]
dup-s1-ca∈ = here refl

dup-r-lit : RE
dup-r-lit = ( ($ 'a' ` 1) + dup-s1 ` 0 )

dup-pdi : PDInstance dup-r-lit ca
dup-pdi = fuse-⊕ {($ 'a' ` 1)} {dup-s1} {0} {ca} dup-id1 dup-s1-ca

dup-pdi∈ : dup-pdi ∈ PosixPD.pdU[ dup-r-lit , ca ]
dup-pdi∈ = pdU∈-⊕ {($ 'a' ` 1)} {dup-s1} {0} {ca} dup-id1 dup-s1-ca
                 (here refl) dup-s1-ca∈

-- and the *same* tree reconstructs through the plain branch instance: it is
-- derived twice, once directly and once inside the fusion
dup-u : U dup-r-lit
dup-u = LeftU (LetterU {loc = 1} ca)

dup-u-pdi : PDInstance dup-r-lit ca
dup-u-pdi = (pdinstance-left {dup-l1} {dup-s1} {0} {ca})
              ( pdinstance {ε} {dup-l1} {ca}
                     (λ u → LetterU {loc = 1} ca)
                     (λ EmptyU →
                        begin
                          [ ca ]
                        ≡⟨⟩
                          ca ∷ []
                        ≡⟨ cong ( λ x → ( ca ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                          ca ∷ (proj₁ (flat EmptyU))
                        ∎) )

dup-u-recon : Recons { dup-r-lit } { ca } dup-u dup-u-pdi
dup-u-recon = recons dup-u ( Word.ε , refl )

-- and *through the fused member as well*: the same tree, derived a second
-- time, reconstructed through the member `pdU` actually computes.  The word
-- evidence lives in the language of that member's continuation, which *does*
-- reduce (`pd-expr-fuse-⊕`): the sum of the two branch continuations
dup-u-recon₂ : Recons { dup-r-lit } { ca } dup-u dup-pdi
dup-u-recon₂ = recons dup-u
                 ( Word._+L_ { ε } { [] } { 0 } ( ε + ε ` 3 ) Word.ε , refl )
```

The example carries its own diagnosis.  `dup-r-lit` is ambiguous — `[ a ]` has
the two trees `LeftU (LetterU a)` and `RightU (LeftU (LetterU a))` — and the
first of them is derived *twice*: through the branch injection `dup-u-pdi`
(which is *not* a member of `pdU[ dup-r-lit , a ]`) and through `dup-pdi`, the
one member that list does contain.  One letter, one member, two reconstructions:
the branching is not in the list, it is in the `⊕`-fusion of two alternatives of
the same letter.

No A1 or A2 holds at the expression or its subexpressions — there is no
concatenation anywhere, and every branch is a literal, so no state *before*
reading the letter is nullable.  The fusion's continuation, however, is
`( ε + ( ε + ε \` 3 ) \` 0 )` by `pd-expr-fuse-⊕` — nullable — and A1 *does*
fire at the pd-descendant this word reaches (the sum has the two empty trees
`LeftU EmptyU` and `RightU (LeftU EmptyU)`).  What the state itself carries is
the paper's third situation: the sum `( ($a`1) + ($a`2) \` 3 )` inside the right
branch has `≈₀`-similar branches — the `Idemp` pattern — under the context
`dup-l1 + · \` 0`, so the duplicate-pattern criterion is the one that fires at
the state, *before* reading; this project states it (`crit`'s third disjunct) and
proves it sound (`Canonic.pd*-Ctx-dup→Ambig`) but does not implement it as a
test (`AmbigCheck` §4).  §18 writes that witness and the descent to it.

That is what §16's step has to find in general.  The two derivations of the same
tree are a branch instance and a fusion of that instance with the sibling's — a
pair related by `⊕` over `≈₀`-similar alternatives — and the diagnosis holding
*at the state* is the duplicate pattern, not a counting statement about `pdU`
lists: the classification has to be made on the canonical expression, where
`≈₀`-similar alternatives have been merged, and A1 reappears only at the
nullable continuation the fusion produces.

## 18. The A3 witness for the example, and the descent that reaches it

§17 identified the §16 cross-instance case with the duplicate pattern; here that
diagnosis is *written down* for the example and connected to §16's descent type
`desc-concl`.  The pattern is already in the expression: `dup-s1`'s two branches
are the literals `($ a \` 1)` and `($ a \` 2)`, which are `≈₀`-similar
(`≈₀-$`), so the third disjunct of `crit` fires at `dup-s1` with the empty
context, and `dup-Ctx` (§12) moves it under the outer sum's left context.

```agda
-- the duplicate pattern at `dup-s1`: the sum of two similar literals, in place
dup-s1-dup : Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
    ( ( AmbigCheck.plug ctx ( l + s ` loc ) ≡ dup-s1 ) × ( Canonic._≈₀_ l s ) )
dup-s1-dup = ( AmbigCheck.𝟘 , dup-l1 , dup-l2 , 3 , ( refl , Canonic.≈₀-$ ca 1 2 ) )

dup-s1-crit : crit dup-s1
dup-s1-crit = inj₂ (inj₂ (inj₁ dup-s1-dup))

-- and at the example state itself, under the context `dup-l1 + · ` 0`
dup-r-lit-dup : Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
    ( ( AmbigCheck.plug ctx ( l + s ` loc ) ≡ dup-r-lit ) × ( Canonic._≈₀_ l s ) )
dup-r-lit-dup = dup-Ctx (AmbigCheck.L+Ctx dup-l1 AmbigCheck.𝟘 0) dup-s1-dup

dup-r-lit-crit : crit dup-r-lit
dup-r-lit-crit = inj₂ (inj₂ (inj₁ dup-r-lit-dup))
```

So the empty prefix of the ambiguity word already settles `desc-concl` at the
state (`inj₁ dup-r-lit-crit`).  The non-trivial half is that the *one-letter*
descent — the step §16 could not close when `pdU-complete` hands out the fused
member — reaches a state that carries a criterion too, and it is the same
pattern one level down: the fusion's continuation is a sum of two `ε`
alternatives.

```agda
-- the one-letter descent through the member `pdU` computes: a `Path` step
-- asks for nothing but the membership
π-dup : Path dup-r-lit ( ca ∷ [] )
π-dup = pcons dup-pdi dup-pdi∈ pnil

-- its end state *is* a pd-descendant of the example state (§12's `pdesc`)
π-dup-Desc : Any ( λ t → t ≡ pdend π-dup )
               (Canonic.pd*-Desc dup-r-lit ( ca ∷ [] ))
π-dup-Desc = pdesc π-dup

-- and the state is the sum of the two branch continuations — both `ε`, by the
-- `pdU-$a1≡`/`pdU-⊕-lit≡` computations of §17, so `pd-expr` unfolds through
-- the whole fusion
pdend-π-dup≡ : pdend π-dup ≡ ( ε + ( ε + ε ` 3 ) ` 0 )
pdend-π-dup≡ = refl

-- the third criterion fires there as well: under the context `ε + · ` 0` a sum
-- of two similar empty alternatives
pdend-π-dup-crit : crit (pdend π-dup)
pdend-π-dup-crit = subst crit pdend-π-dup≡
  ( inj₂ (inj₂ (inj₁ ( AmbigCheck.L+Ctx ε AmbigCheck.𝟘 0
               , ε , ε , 3 , ( refl , Canonic.≈₀-ε ) ) )) )

-- the §16 step, instantiated: the fused member carries the conclusion of its
-- own continuation back up to the example state and the word `a`
dup-desc : desc-concl dup-r-lit ( ca ∷ [] )
dup-desc = desc-step dup-pdi dup-pdi∈ (inj₁ pdend-π-dup-crit)
```

(A1 *also* fires at the reached state — `A1-⊕ ε ( ε + ε \` 3 ) 0 RE.ε∈ε` with the
right factor's `ε∈` from `RE.ε∈_+_ RE.ε∈ε RE.ε∈ε` — so the descendant is
diagnosable by the first criterion as well; what is *not* available anywhere
before reading the letter is A1 or A2, and the only criterion the state itself
carries is the third.)

The mechanical A3 test of `cgp.ambig.Canonic` §6.2 fires on this same
expression — its `pd-Idemp?` reads the sum-spine of the member continuations,
which is exactly what `pdend-π-dup≡` computed:

```agda
dup-Idemp-fires : Canonic.pd-Idemp? (PosixPD.pdU[ dup-r-lit , ca ]) ≡ true
dup-Idemp-fires = refl
```

Canonic's caveat there says that turning `A3? r c ≡ true` into `Ambig r` needs
a reflection of the test into a concrete `Ctx`/`plug` duplicate witness;
`dup-s1-dup`, `dup-r-lit-dup` and `pdend-π-dup-crit` are that reflection
instance for this `r` and `c`.

Two things follow for §16.  First, the missing case of `desc-step` — where
`pdU-complete` gives the two trees *different* instances — is here exactly a
branch instance and its `⊕`-fusion with the sibling's instance, and the
diagnosis that closes it is `crit`'s third disjunct, so a general
`Desc-complete` needs the duplicate-pattern recognition, not only the nullable
concatenation counting.  Second, the recognition can *name* its state:
`pdend-π-dup≡` shows the reached state computes to a literal sum of similar
alternatives, and `pdesc` puts it in `pd*-Desc` — the shape
`Desc-⊕-crit` (§15) produces symbolically for a pair of paths, exhibited here
at a concrete instance.

## 19. The completeness proof: what is missing, named, and assembled

Where the program stands: §8's `completeness` is derived by §16's
`completeness-from-desc` from the single recursion `Desc-complete`; that
recursion's base is `desc-base` (§16, from §9) and its shared-instance step is
`desc-step` with `Recons-residual-2` (§16); §17 exhibited the remaining case —
the two picks of `pdU-complete` *differ* — and §18 gave its diagnosis on the
example.  What is left is therefore exactly one rule, and naming it makes the
whole assembly checkable: the two parameters below *are* the gap, nothing else
is missing.

```agda
-- the paper's "three situations" as one rule: when the two picks differ, the
-- diagnosis comes from the state
Cross-instance→crit : Set
Cross-instance→crit = ∀ { r : RE } { c : Char } { ws : List Char }
  ( z z′ : PDInstance r c )
  → z ∈ PosixPD.pdU[ r , c ] → z′ ∈ PosixPD.pdU[ r , c ]
  → ( u v : U r ) → Recons {r} {c} u z → Recons {r} {c} v z′
  → proj₁ (flat {r} u) ≡ c ∷ ws → proj₁ (flat {r} v) ≡ c ∷ ws
  → ¬ ( z ≡ z′ )
  → crit r

-- the induction, assembled: the base is `desc-base`; the step splits on whether
-- the two picks coincide — if they do, `Recons-residual-2` transports the pair
-- through the shared instance and the recursion continues, if not, `cross`
-- closes with `inj₁`
desc-picks : ( cross : Cross-instance→crit )
  → ( dec : ∀ { r : RE } { c : Char } ( z z′ : PDInstance r c ) → Dec ( z ≡ z′ ) )
  → ( r : RE ) → ( w : List Char )
  → ( u v : U r )
  → proj₁ (flat {r} u) ≡ w → proj₁ (flat {r} v) ≡ w → ¬ ( u ≡ v )
  → desc-concl r w
desc-picks cross dec r [] u v u≡[] v≡[] u≢v = desc-base u v u≡[] v≡[] u≢v
desc-picks cross dec r (c ∷ ws) u v u≡ v≡ u≢v
  with pick-Any (PosixPD.pdU-complete {r} {c} u u≡)
... | ( z , u∈ , z∈ ) with pick-Any (PosixPD.pdU-complete {r} {c} v v≡)
...   | ( z′ , v∈ , z′∈ ) with dec z z′
...     | yes z≡z′ = desc-step z z∈
          (desc-picks cross dec (Canonic.pd-expr z) ws x y x≡ y≡ x≢y)
      where
        rr : Σ[ a ∈ U (Canonic.pd-expr z) ] Σ[ b ∈ U (Canonic.pd-expr z) ]
              ( proj₁ (flat {Canonic.pd-expr z} a) ≡ ws
              × proj₁ (flat {Canonic.pd-expr z} b) ≡ ws
              × ¬ ( a ≡ b ) )
        rr = Recons-residual-2 u∈
               (subst ( λ q → Recons {r} {c} v q ) (sym z≡z′) v∈) u≡ v≡ u≢v
        x    = proj₁ rr
        y    = proj₁ (proj₂ rr)
        x≡   = proj₁ (proj₂ (proj₂ rr))
        y≡   = proj₁ (proj₂ (proj₂ (proj₂ rr)))
        x≢y  = proj₂ (proj₂ (proj₂ (proj₂ rr)))
...     | no z≢z′ = inj₁ (cross z z′ z∈ z′∈ u v u∈ v∈ u≡ v≡ z≢z′)

Desc-complete-picks : ( cross : Cross-instance→crit )
  → ( dec : ∀ { r : RE } { c : Char } ( z z′ : PDInstance r c ) → Dec ( z ≡ z′ ) )
  → Desc-complete
Desc-complete-picks cross dec = desc-picks cross dec

-- and the §8 statement itself — this is the full proof, modulo its two parameters
completeness-picks : ( cross : Cross-instance→crit )
  → ( dec : ∀ { r : RE } { c : Char } ( z z′ : PDInstance r c ) → Dec ( z ≡ z′ ) )
  → ∀ { r : RE } ( u v : U r )
  → proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) → ¬ ( u ≡ v )
  → ∃[ w′ ] ∃[ w″ ]
      ( ( proj₁ (flat {r} u) ≡ w′ ++ w″ )
      × ∃[ p ]
          ( Any ( λ s → s ≡ p ) (Canonic.pd*-Desc r w′)
          × crit p ) )
completeness-picks cross dec {r} u v w≡ u≢v =
  completeness-from-desc (Desc-complete-picks cross dec) r u v w≡ u≢v
```

The first parameter is the research content; the second is a formalism fact
worth recording: `PDInstance` equality is *intensional* here — instances carry
function fields (`inj : U p → U r`) — so `dec` is not definable in general.  It
*is* definable at expressions in literal constructor form, where `pdU` computes
as in §17–§18 (finite lists of concrete records); for arbitrary states this
parameter was the open point — §23 first granted it as an assumption, and §24
showed the descent never has to ask the question: an equivalent of it on
residual trees *is* decidable (`ParseTree._⊢_≟_`).  A quotient of instances —
equality of patterns plus transport along `Canonic.Cast`/`≈₀`, the canonical
machinery of §2–§3 — remains the natural candidate for a genuine `dec`, and
would make the induction run on canonical states, which §17 showed is where
the classification belongs anyway.

The two rules that any `cross` must ultimately reduce into *are* both here in
their state-local direction: the nullable-sum case is `A1-⊕` / `split-+-A1`
(§12) and the duplicate case is `dup-Ctx`/`crit-+<` (§12, with §18's
`dup-s1-dup` as the pattern instance); what was missing was the second of the
paper's three situations stated as a rule —

```agda
-- paper situation 2 as a rule: an injection through a concatenation whose left
-- factor is nullable and has two distinct empty trees *is* A2 at the
-- concatenation itself
crit-●-2ε : ( l s : RE ) ( loc : ℕ ) ( ε∈l : RE.ε∈ l )
  ( e f : U l )
  → proj₁ (flat {l} e) ≡ [] → proj₁ (flat {l} f) ≡ [] → ¬ ( e ≡ f )
  → crit ( l ● s ` loc )
crit-●-2ε l s loc ε∈l e f e≡[] f≡[] e≢f =
  inj₂ (inj₁ ( AmbigCheck.𝟘 , l , s , loc
             , ( refl , ε∈l
               , two-distinct-members→len≥2 (mkAllEmptyU {l} ε∈l) e∈ f∈ e≢f ) ) )
  where
    e∈ : Any ( λ z → e ≡ z ) (mkAllEmptyU {l} ε∈l)
    e∈ = mkAllEmptyU-complete ε∈l e (flat-[] e e≡[])
    f∈ : Any ( λ z → f ≡ z ) (mkAllEmptyU {l} ε∈l)
    f∈ = mkAllEmptyU-complete ε∈l f (flat-[] f f≡[])
```

— and the remaining reduction, *cross-instance picks ⇒ one of the three
shapes*, is the paper's enumeration argument: it needs the derivative to be
read *symmetrically* from the pair of trees rather than from the list
(§15's obstacle was exactly reading it from the list), and by §17 the shapes
must be recognized on canonical patterns.  That reduction, plus a decision of
pick-identity (classical or quotient, above), is the whole of what stands
between this file and `completeness`; §20 replaces the second of those by a
computable test on states and residuals.

## 20. The pick test, made computable

§19's second parameter decides identity of *instances*, which is not a computable
property here (`inj : U p → U r` is a function field).  The recursion cannot do
without that decision — but with §8's fourth disjunct in place, only that
decision has to stay a parameter: once the two picks are known *distinct
records*, everything else the step needs is computed.  It decides record identity
(`dec`, non-definability as §19 noted) and, in the distinct case, equality of
continuations (`RE-≟` below, structural).  The two stopping configurations are
the two in which a pair provably forks at the state: the continuations differ
(`pick-diff-state`, the surviving parameter) or two *distinct* records continue
at one continuation — which now provably fires the fourth disjunct
(`pick-diff-record-prf`, via `Canonic.pd-Idemp?-members`: the member list then
holds two entries with one continuation, exactly what §22's test reads).  The
tree comparison (`ParseTree._⊢_≟_`) this section used to stop the recursion with
is not needed in the record case: with record distinctness the conclusion does
not speak of residuals.

```agda
-- the two readings of a concatenation's non-emptiness are different proofs
ε∉-fst≢snd : ∀ { l r : RE } { loc : ℕ } ( p : ε∉ l ) ( q : ε∉ r )
  → ¬ ( ε∉fst {l} {r} {loc} p ≡ ε∉snd {l} {r} {loc} q )
ε∉-fst≢snd p q ()

-- equalities under a constructor of non-emptiness evidence
ε∉-fst-inj : ∀ { l r : RE } { loc : ℕ } ( p q : ε∉ l )
  → ε∉fst {l} {r} {loc} p ≡ ε∉fst {l} {r} {loc} q → p ≡ q
ε∉-fst-inj p .p refl = refl

ε∉-snd-inj : ∀ { l r : RE } { loc : ℕ } ( p q : ε∉ r )
  → ε∉snd {l} {r} {loc} p ≡ ε∉snd {l} {r} {loc} q → p ≡ q
ε∉-snd-inj p .p refl = refl

ε∉-+ˡ-inj : ∀ { l r : RE } { loc : ℕ } ( p q : ε∉ l ) ( p′ q′ : ε∉ r )
  → ε∉_+_ {l} {r} {loc} p p′ ≡ ε∉_+_ {l} {r} {loc} q q′ → p ≡ q
ε∉-+ˡ-inj p .p p′ .p′ refl = refl

ε∉-+ʳ-inj : ∀ { l r : RE } { loc : ℕ } ( p q : ε∉ l ) ( p′ q′ : ε∉ r )
  → ε∉_+_ {l} {r} {loc} p p′ ≡ ε∉_+_ {l} {r} {loc} q q′ → p′ ≡ q′
ε∉-+ʳ-inj p .p p′ .p′ refl = refl

-- non-emptiness evidence at a fixed expression has decidable equality
ε∉-≟ : ∀ { r : RE } ( p q : ε∉ r ) → Dec ( p ≡ q )
ε∉-≟ ε∉$ ε∉$ = yes refl
ε∉-≟ (ε∉fst p) (ε∉fst q) with ε∉-≟ p q
... | yes eq = yes (cong ε∉fst eq)
... | no ¬eq = no ( λ e → ¬eq (ε∉-fst-inj p q e))
ε∉-≟ (ε∉fst p) (ε∉snd q) = no (ε∉-fst≢snd p q)
ε∉-≟ (ε∉snd p) (ε∉fst q) = no ( λ e → ε∉-fst≢snd q p (sym e))
ε∉-≟ (ε∉snd p) (ε∉snd q) with ε∉-≟ p q
... | yes eq = yes (cong ε∉snd eq)
... | no ¬eq = no ( λ e → ¬eq (ε∉-snd-inj p q e))
ε∉-≟ (ε∉_+_ p₁ p₂) (ε∉_+_ q₁ q₂) with ε∉-≟ p₁ q₁ | ε∉-≟ p₂ q₂
... | yes e₁ | yes e₂ = yes (cong₂ ε∉_+_ e₁ e₂)
... | no ¬e₁ | _ = no ( λ e → ¬e₁ (ε∉-+ˡ-inj p₁ q₁ p₂ q₂ e))
... | _ | no ¬e₂ = no ( λ e → ¬e₂ (ε∉-+ʳ-inj p₁ q₁ p₂ q₂ e))

-- an equality of first components plus an equality of the transported second
-- components is an equality of dependent pairs
,≡→≡ : ∀ { A : Set } { B : A → Set } { x y : Σ[ a ∈ A ] B a } ( p : proj₁ x ≡ proj₁ y )
  → subst B p (proj₂ x) ≡ proj₂ y → x ≡ y
,≡→≡ {x = a , b} refl eq = cong ( λ z → a , z ) eq

-- the parts of a compound expression: a failed comparison of the parts pulls
-- back along these congruences
re-left : RE → RE
re-left ( l ● r ` loc) = l
re-left ( l + r ` loc) = l
re-left ( r * ε∉r ` loc) = r
re-left _ = ε

re-right : RE → RE
re-right ( l ● r ` loc) = r
re-right ( l + r ` loc) = r
re-right _ = ε

re-loc : RE → ℕ
re-loc ( $ _ ` loc) = loc
re-loc ( _ ● _ ` loc) = loc
re-loc ( _ + _ ` loc) = loc
re-loc ( _ * _ ` loc) = loc
re-loc _ = zero

re-char : RE → Char
re-char ( $ c ` loc) = c
re-char _ = 'a'

-- two Kleene expressions with equal bases are equal exactly when their
-- non-emptiness proofs are; with unequal bases the pullback is a projection
star-irr : ∀ { r : RE } { loc₁ loc₂ : ℕ } ( p q : ε∉ r )
  → r * p ` loc₁ ≡ r * q ` loc₂ → p ≡ q
star-irr p .p refl = refl

star-irr-subst : ∀ { r₁ r₂ : RE } ( r₁≡r₂ : r₁ ≡ r₂ ) ( ε∉₁ : ε∉ r₁ ) ( ε∉₂ : ε∉ r₂ )
  { loc : ℕ } → r₁ * ε∉₁ ` loc ≡ r₂ * ε∉₂ ` loc
  → subst ( λ q → ε∉ q) r₁≡r₂ ε∉₁ ≡ ε∉₂
star-irr-subst refl ε∉₁ .ε∉₁ refl = refl

-- RE equality is decidable: characters, locations and non-emptiness proofs are
RE-≟ : ( r s : RE ) → Dec ( r ≡ s )
RE-≟ ε ε = yes refl
RE-≟ ε ($ c ` loc) = no λ ()
RE-≟ ε (l ● r ` loc) = no λ ()
RE-≟ ε (l + r ` loc) = no λ ()
RE-≟ ε (r * ε∉r ` loc) = no λ ()
RE-≟ ($ c₁ ` loc₁) ε = no λ ()
RE-≟ ($ c₁ ` loc₁) ($ c₂ ` loc₂) with Char._≟_ c₁ c₂ | loc₁ ≟ loc₂
...   | yes refl | yes refl = yes refl
...   | no ¬c | _ = no ( λ e → ¬c (cong re-char e))
...   | _ | no ¬loc = no ( λ e → ¬loc (cong re-loc e))
RE-≟ ($ c₁ ` loc₁) (l ● r ` loc₂) = no λ ()
RE-≟ ($ c₁ ` loc₁) (l + r ` loc₂) = no λ ()
RE-≟ ($ c₁ ` loc₁) (r * ε∉r ` loc₂) = no λ ()
RE-≟ (l₁ ● r₁ ` loc₁) ε = no λ ()
RE-≟ (l₁ ● r₁ ` loc₁) ($ c ` loc₂) = no λ ()
RE-≟ (l₁ ● r₁ ` loc₁) (l₂ ● r₂ ` loc₂) with RE-≟ l₁ l₂ | RE-≟ r₁ r₂ | loc₁ ≟ loc₂
...   | yes refl | yes refl | yes refl = yes refl
...   | no ¬l | _ | _ = no ( λ e → ¬l (cong re-left e))
...   | _ | no ¬r | _ = no ( λ e → ¬r (cong re-right e))
...   | _ | _ | no ¬loc = no ( λ e → ¬loc (cong re-loc e))
RE-≟ (l₁ ● r₁ ` loc₁) (l₂ + r₂ ` loc₂) = no λ ()
RE-≟ (l₁ ● r₁ ` loc₁) (r₂ * ε∉₂ ` loc₂) = no λ ()
RE-≟ (l₁ + r₁ ` loc₁) ε = no λ ()
RE-≟ (l₁ + r₁ ` loc₁) ($ c ` loc₂) = no λ ()
RE-≟ (l₁ + r₁ ` loc₁) (l₂ ● r₂ ` loc₂) = no λ ()
RE-≟ (l₁ + r₁ ` loc₁) (l₂ + r₂ ` loc₂) with RE-≟ l₁ l₂ | RE-≟ r₁ r₂ | loc₁ ≟ loc₂
...   | yes refl | yes refl | yes refl = yes refl
...   | no ¬l | _ | _ = no ( λ e → ¬l (cong re-left e))
...   | _ | no ¬r | _ = no ( λ e → ¬r (cong re-right e))
...   | _ | _ | no ¬loc = no ( λ e → ¬loc (cong re-loc e))
RE-≟ (l₁ + r₁ ` loc₁) (r₂ * ε∉₂ ` loc₂) = no λ ()
RE-≟ (r₁ * ε∉₁ ` loc₁) ε = no λ ()
RE-≟ (r₁ * ε∉₁ ` loc₁) ($ c ` loc₂) = no λ ()
RE-≟ (r₁ * ε∉₁ ` loc₁) (l ● r ` loc₂) = no λ ()
RE-≟ (r₁ * ε∉₁ ` loc₁) (l + r ` loc₂) = no λ ()
RE-≟ (r₁ * ε∉₁ ` loc₁) (r₂ * ε∉₂ ` loc₂) with RE-≟ r₁ r₂ | loc₁ ≟ loc₂
...   | no ¬r | _ = no ( λ e → ¬r (cong re-left e))
...   | _ | no ¬loc = no ( λ e → ¬loc (cong re-loc e))
...   | yes r₁≡r₂ | yes refl with ε∉-≟ (subst ( λ q → ε∉ q) r₁≡r₂ ε∉₁) ε∉₂
...     | yes eq =
        yes (cong ( λ ( x , ε∉x) → x * ε∉x ` loc₂) (,≡→≡ r₁≡r₂ eq))
...     | no ¬eq = no ( λ e → ¬eq (star-irr-subst r₁≡r₂ ε∉₁ ε∉₂ e))

-- the residual tree of a reconstruction and its word, as named terms
-- (§13's `Recons-residual`, split in two so §21 can use them)
residual : ∀ { r : RE } { c : Char } { ws : List Char } { z : PDInstance r c } { u : U r }
  → Recons {r} {c} u z → proj₁ (flat {r} u) ≡ c ∷ ws → U (Canonic.pd-expr z)
residual u∈ u≡ = proj₁ (Recons-residual u∈ u≡)

residual-word : ∀ { r : RE } { c : Char } { ws : List Char } { z : PDInstance r c } { u : U r }
  ( u∈ : Recons {r} {c} u z ) ( u≡ : proj₁ (flat {r} u) ≡ c ∷ ws )
  → proj₁ (flat {Canonic.pd-expr z} (residual u∈ u≡)) ≡ ws
residual-word u∈ u≡ = proj₂ (Recons-residual u∈ u≡)
```

The step of the descent reads the record decision first.  A `yes` sends the pair
through the shared record — `Recons-residual-2` (§16) moves both reconstructions
to one state and `desc-step` lifts whatever the recursion finds there.  A `no`
reaches one of the two configurations.  Different continuations
(`pick-diff-state`) is the one rule the descent still takes as a parameter.
Equal continuations at *distinct* records is the fourth disjunct: the member
list has two entries whose `+`-spine alternates repeat, which is what
`Canonic.pd-Idemp?-members` turns into the §22 test firing.

```agda
-- the two stopping configurations
pick-diff-state : Set
pick-diff-state = ∀ { r : RE } { c : Char } { ws : List Char }
  ( z z′ : PDInstance r c )
  → z ∈ PosixPD.pdU[ r , c ] → z′ ∈ PosixPD.pdU[ r , c ]
  → ¬ ( z ≡ z′ )
  → ( u v : U r ) → Recons {r} {c} u z → Recons {r} {c} v z′
  → proj₁ (flat {r} u) ≡ c ∷ ws → proj₁ (flat {r} v) ≡ c ∷ ws
  → ¬ ( Canonic.pd-expr z ≡ Canonic.pd-expr z′ )
  → crit r

-- §19's rule implies the first configuration; §22's A3 disjunct is what makes
-- the record premise available where the descent needs it
pick-diff-state-from-cross : Cross-instance→crit → pick-diff-state
pick-diff-state-from-cross cross z z′ z∈ z′∈ z≢z′ u v u∈ v∈ u≡ v≡ ¬pd =
  cross z z′ z∈ z′∈ u v u∈ v∈ u≡ v≡ z≢z′

-- the record rule, with the distinctness premise its use in the descent
-- supplies (§19's `dec`), is provable — it is the A3 test on the transition
pick-diff-record-prf : ∀ { r : RE } { c : Char }
  ( z z′ : PDInstance r c )
  → z ∈ PosixPD.pdU[ r , c ] → z′ ∈ PosixPD.pdU[ r , c ]
  → ¬ ( z ≡ z′ )
  → Canonic.pd-expr z ≡ Canonic.pd-expr z′
  → crit r
pick-diff-record-prf {r} {c} z z′ z∈ z′∈ z≢z′ eq =
  crit-A3-test r c
    (Canonic.pd-Idemp?-members (PosixPD.pdU[ r , c ]) z z′ z∈ z′∈ z≢z′ eq)

-- the whole recursion: `dec` on the records is the parameter of §19, the
-- continuation test is computed, and the record case closes by §22's test
desc-picks-dec : ( cstate : pick-diff-state )
  → ( dec : ∀ { r : RE } { c : Char } ( z z′ : PDInstance r c ) → Dec ( z ≡ z′ ) )
  → ( r : RE ) → ( w : List Char )
  → ( u v : U r )
  → proj₁ (flat {r} u) ≡ w → proj₁ (flat {r} v) ≡ w → ¬ ( u ≡ v )
  → desc-concl r w
desc-picks-dec cstate dec r [] u v u≡[] v≡[] u≢v = desc-base u v u≡[] v≡[] u≢v
desc-picks-dec cstate dec r (c ∷ ws) u v u≡ v≡ u≢v
  with pick-Any (PosixPD.pdU-complete {r} {c} u u≡)
... | ( z , u∈ , z∈ ) with pick-Any (PosixPD.pdU-complete {r} {c} v v≡)
...   | ( z′ , v∈ , z′∈ ) with dec z z′
...     | yes z≡z′ =
          desc-step z z∈
            (desc-picks-dec cstate dec (Canonic.pd-expr z) ws x y x≡ y≡ x≢y)
        where
          rr : Σ[ a ∈ U (Canonic.pd-expr z) ] Σ[ b ∈ U (Canonic.pd-expr z) ]
                ( proj₁ (flat {Canonic.pd-expr z} a) ≡ ws
                × proj₁ (flat {Canonic.pd-expr z} b) ≡ ws
                × ¬ ( a ≡ b ) )
          rr = Recons-residual-2 u∈
                 (subst ( λ q → Recons {r} {c} v q ) (sym z≡z′) v∈) u≡ v≡ u≢v
          x    = proj₁ rr
          y    = proj₁ (proj₂ rr)
          x≡   = proj₁ (proj₂ (proj₂ rr))
          y≡   = proj₁ (proj₂ (proj₂ (proj₂ rr)))
          x≢y  = proj₂ (proj₂ (proj₂ (proj₂ rr)))
...     | no z≢z′ with RE-≟ (Canonic.pd-expr z) (Canonic.pd-expr z′)
...       | no ¬pd = inj₁ (cstate z z′ z∈ z′∈ z≢z′ u v u∈ v∈ u≡ v≡ ¬pd)
...       | yes eq = inj₁ (pick-diff-record-prf z z′ z∈ z′∈ z≢z′ eq)

Desc-complete-dec : ( cstate : pick-diff-state )
  → ( dec : ∀ { r : RE } { c : Char } ( z z′ : PDInstance r c ) → Dec ( z ≡ z′ ) )
  → Desc-complete
Desc-complete-dec cstate dec = desc-picks-dec cstate dec

-- the test is not vacuous: it evaluates on the §17–§18 instances.  The branch
-- injection `dup-u-pdi` and the fused member `dup-pdi` — the two derivations of
-- the *same* tree `dup-u` — continue at different expressions, and the test sees
-- that by computation.  (The ambiguity *pair* of §17–§18 is not in that
-- configuration: `pdU[ dup-r-lit , ca ]` is the singleton `dup-pdi ∷ []`
-- (`pdU-⊕-lit≡`), so the recursion takes its recursing branch there — which is
-- §18's `dup-desc`.  What the example exhibits instead is a double derivation
-- through two *records*, one level of the recursion away from the state that
-- carries the criterion: the configuration `pick-diff-record-prf` now closes by
-- computation, no parameter.)
dup-cont-differ : ¬ ( Canonic.pd-expr dup-pdi ≡ Canonic.pd-expr dup-u-pdi )
dup-cont-differ with RE-≟ (Canonic.pd-expr dup-pdi) (Canonic.pd-expr dup-u-pdi)
... | no ¬eq = ¬eq

-- the second tree of the §17 example, and the fact that the pair is distinct
dup-u₂ : U dup-r-lit
dup-u₂ = RightU (LeftU (LetterU {loc = 1} ca))

dup-u≢u₂ : ¬ ( dup-u ≡ dup-u₂ )
dup-u≢u₂ ()

-- the example pair, descended by the recursion: the member list is a singleton,
-- so the two picks coincide, the residuals at the reached state are distinct
-- trees, the recursion continues, and at the empty word §9's base fires A1 —
-- neither stopping configuration is reached here
dup-desc-dec : ( cstate : pick-diff-state )
  → ( dec : ∀ { r : RE } { c : Char } ( z z′ : PDInstance r c ) → Dec ( z ≡ z′ ) )
  → desc-concl dup-r-lit ( ca ∷ [] )
dup-desc-dec cstate dec =
  desc-picks-dec cstate dec dup-r-lit ( ca ∷ [] ) dup-u dup-u₂ refl refl dup-u≢u₂

-- §8's statement, from the decidable recursion
completeness-dec : ( cstate : pick-diff-state )
  → ( dec : ∀ { r : RE } { c : Char } ( z z′ : PDInstance r c ) → Dec ( z ≡ z′ ) )
  → ∀ { r : RE } ( u v : U r )
  → proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) → ¬ ( u ≡ v )
  → ∃[ w′ ] ∃[ w″ ]
      ( ( proj₁ (flat {r} u) ≡ w′ ++ w″ )
      × ∃[ p ]
          ( Any ( λ s → s ≡ p ) (Canonic.pd*-Desc r w′)
          × crit p ) )
completeness-dec cstate dec {r} u v w≡ u≢v =
  completeness-from-desc (Desc-complete-dec cstate dec) r u v w≡ u≢v

```

The record case is §17's "one letter, two members, one continuation" made
precise — and it is a theorem now, not a rule: two *distinct* members continuing
at one expression leave a repeated alternative in the flattened continuations
(`Canonic.pd-Idemp?-members`, `cgp.ambig.Canonic` §6.3), which is exactly what
`Idemp` would merge, and the §22 test fires at *this* transition.  So the
descent is computable up to a single rule, `pick-diff-state` — the configuration
where the two picks continue at genuinely different expressions — plus the
intensional record decision `dec`.  Reducing that one rule to the paper's other
two situations is the enumeration argument §19 pointed at, and it is a statement
about canonical patterns, which is where §17 said the classification belongs.

## 21. Reconstruction uniqueness: where the second rule is needed

§20 closed with the suspicion that its second stopping configuration might be
mere formalism.  It was rather *false* as stated (§22 records the
counterexample), and this section locates exactly the configuration its premises
were arranging.  Trying to
close the `yes` branch of the residual test by "equal continuations + equal
residuals ⇒ equal trees" fails at a point that is mathematical, not technical:
after the two reconstruction equations `inj (unflat w∈) ≡ u` are exposed, the
two members are two *different* `pdinstance`s, and equal continuation
*expressions* do not identify their transition maps — different maps apply one
residual tree to different trees.  What *is* true is uniqueness per record, and
it sharpens the configuration: the stop requires *two distinct records with one
continuation*.  That is precisely the `Idemp` configuration the canonical form
removes, `Canonic.pd-Idemp?` is the computation that detects it, and the
duplicate pattern is the criterion that names it.  The second rule is not a gap
in the recursion; it is the place where the duplicate pattern enters the
completeness proof.

```agda
-- reconstruction uniqueness for one record: two reconstructions through the
-- *same* member with the same residual tree rebuild the same tree.  The `with`
-- ladder first matches the member equality (so both reconstructions live at one
-- member, one injection), then destructs the reconstructions to expose their
-- equations `inj (unflat w∈) ≡ u` and assembles the chain
recon-uniq : ∀ { r : RE } { c : Char } { ws : List Char }
  { z z′ : PDInstance r c } { u v : U r }
  ( z≡z′ : z ≡ z′ )
  ( u∈ : Recons {r} {c} u z ) ( v∈ : Recons {r} {c} v z′ )
  ( u≡ : proj₁ (flat {r} u) ≡ c ∷ ws ) ( v≡ : proj₁ (flat {r} v) ≡ c ∷ ws )
  → residual u∈ u≡
    ≡ U-transport (sym (cong Canonic.pd-expr z≡z′)) (residual v∈ v≡)
  → u ≡ v
recon-uniq {z = z} {z′ = z′} {u = u₁} {v = v₁} z≡z′ u∈ v∈ u≡ v≡ res
  with z≡z′
... | refl with u∈ | v∈
...   | recons .u₁ ( p₁ , q₁ ) | recons .v₁ ( p₂ , q₂ ) =
        trans (sym q₁) (trans (cong (Canonic.pd-inj z refl) res) q₂)
```

The attempted strengthening — dropping `z≡z′` and taking the continuation
equation `eq` as the hypothesis instead — does not type-check, and the failure
is the point: with both reconstructions destructed, Agda reports `inj != inj₃`,
two distinct transition maps.  No replacement for §20's `desc-picks-dec` (both
rules) comes out of this section; what comes out is the *characterization*:
`pick-diff-record` fires only at a state whose member list holds two distinct
records continuing at one expression.

The stop is not vacuous.  The configuration "`pdU` holds two distinct members
continuing at `≈₀`-similar expressions" is realized, and this repository
already carries the example — `Canonic` §8.1, built when A3 was stated
verbatim: `pd-a3-target` derives the letter `a` through two members whose
continuations are `≈₀` (the list is *computed*, `pd-a3-continuations`),
`Idemp` fires on it (`pd-a3-Idemp-applied`, `pd-a3-A3?-fires`), the expression
is ambiguous (`pd-a3-ambiguous`), and `pd-a3-Desc` exhibits the merged
derivative state — `derivᵖ` re-glues the member continuations into one sum,
which is the paper's `Desc` — as a descendant of the target.  At such a state
the recursion stops or continues by the computed residual test; the criterion
that witnesses the ambiguity, however, is at the *derivative* state, where the
duplicate pattern is syntactic (`l + s` with `l ≈₀ s`):

```agda
-- the duplicate pattern of a sum state fires `crit`'s third disjunct directly
crit-sum-≈₀ : ∀ ( l s : RE ) ( loc : ℕ )
  → Canonic._≈₀_ l s
  → crit ( l + s ` loc )
crit-sum-≈₀ l s loc ≈₀ls = inj₂ (inj₂ (inj₁ ( AmbigCheck.𝟘 , l , s , loc , ( refl , ≈₀ls ) )))

-- the merged derivative state of the A3 example carries the criterion
pd-a3-crit : crit Canonic.pd-a3-state
pd-a3-crit =
  crit-sum-≈₀ ( ε ● ( $ 'c' ` 4 ) ` 5 ) ( ε ● ( $ 'c' ` 7 ) ` 8 ) zero
              ( Canonic.≈₀-● Canonic.≈₀-ε ( Canonic.≈₀-$ 'c' 4 7 ) )
```

Two corrections come out of this section, and both are load-bearing for the
completeness proof:

* `recon-uniq`: a `pick-diff-record` stop for a *distinct* pair always has two
  **distinct** members with one continuation and one residual — a genuine
  double record, never one record twice.  The duplicate-record configuration is
  exactly what `Canonic.pd-Idemp?` detects on a member list; the rule is where
  the duplicate pattern enters the recursion.

* the witness of a duplicate-record configuration is a criterion at the
  **derivative** state (`pd-a3-crit` at `pd-a3-Desc`), not at the state that
  carries the transition.  §20's two rules conclude `crit r` at the state
  itself; making the descent's conclusion the paper's — a *pd-descendant* (in
  the `derivᵖ`/`∈Desc` sense, which `pd*-Desc` per-path lists do not give) at
  which a criterion fires — and matching `pick-diff-state` against the paper's
  remaining two situations is the enumeration argument: §22.

## 22. A3 proper is a test on the *transition*, and it needs no descent

§21 left the impression that the duplicate situation can only be diagnosed at the
*merged* derivative state, and that §8's conclusion therefore has to be
re-targeted from path descendants to `derivᵖ`.  It does not: the paper's own A3
is a test on a transition *out of* the state, not on the state that the
transition reaches —

> criteria **A1** is always connected to a final state whereas criteria **A2**
> and **A3** are always connected to transitions (section 7)

and A3 is "`lang(canonic(deriv s x)) ≠ {}` and `deriv s x` simplifies to
`canonic(deriv s x)` with rule **Idemp** applied".  `Canonic.pd-Idemp?` is that
test on the partial-derivative list in place of the derivative expression
(`cgp.ambig.Canonic` §6.2, §9's `A3-list?`): `pd-alts` takes the `+`-spine of
each member continuation, which is what `Idemp` would merge, and `dups-≈₀` asks
whether two of the merged alternatives are similar.  The paper's side condition
`lang(…) ≠ {}` (its "realizable state" clause) is automatic in this formalism —
`ParseTree.r-∃u` inhabits `U q` for every `q`, the same fact `Canonic` §8 uses
when it drops the realizability clause from `_∈Desc_`.  So the test is the
missing criterion verbatim, and it is now `crit`'s fourth disjunct (§8).

Like the third disjunct, it is written quantified over a hole context: the paper
states its criteria for a *realizable* `s ∈ Desc(r)`, and a context with a hole
is what this project has instead of quantifying over descendants (§7).
`crit-A3-test` is the empty-context instance, stated in §8 next to `crit`; the
stability is `A3-Ctx` (§12), proved exactly as `dup-Ctx` is — the test speaks of
the state in the hole, the hole only grows around it. With that, the four
context-lifting lemmas of §12 (`crit-+<`, `crit-+>`, `crit-●<`, `crit-●>`) carry
the new disjunct as they carried the old three, and nothing else in the file had
to change: no earlier proof *destructs* the diagnosis sum except those four.

A member-level statement of the same thing — "there are two members of
`pdU[ p , c ]` with similar continuations" — was tried first and rejected, and
the reason is worth recording, because it is the same structural fact §18 found
by computation.  Its non-emptiness conjunct is vacuous here (`r-∃u`), and
`pdU` does not keep two unfused members with similar continuations in the first
place: the sum clause fuses the branch instances into one member whose
continuation is the *sum* of theirs (`pdinstance-oplus`, §16's fusion remark), so
the duplicate survives as a `+`-spine inside one continuation — exactly what
`pd-alts`/`sum-spine` reads and what the third disjunct sees one step later
(§18's `pdend-π-dup≡`, §21's `pd-a3-crit`).  The only clause of `pdU` that does
produce several members is the nullable concatenation, and there the members come
one per empty tree of the left factor, continuing at one and the same
expression — which is the second criterion's own configuration.  Stated as a
test on the whole member list, the criterion is instead *decidable* (the paper's
"easy to verify") and it fires on the states where the paper says A3 fires.

```agda
-- the two states this repository already computes `pd-Idemp?` on now carry the
-- diagnosis *at themselves*, for the letter they duplicate on.  §18's
-- `dup-r-lit` — whose duplicate pattern §18 wrote down by hand (`dup-r-lit-crit`
-- above, the third disjunct) — is diagnosed a second, independent way by the
-- test on its `a` transition (`dup-Idemp-fires`): the two readings agree.
dup-r-lit-crit-A3 : crit dup-r-lit
dup-r-lit-crit-A3 = crit-A3-test dup-r-lit ca dup-Idemp-fires

-- `Canonic` §6.2's `pd-a3-target` is the case the pattern *cannot* reach: no
-- duplicate is present in the expression (`pd-a3-canonic-flag` says `canonic`
-- applies no `Idemp` to it), the duplicate is created by the transition on `a`;
-- the test sees it (`pd-a3-Idemp-applied`) and §21's `pd-a3-crit` needed the
-- merged derivative state for the same conclusion.
pd-a3-crit-A3 : crit Canonic.pd-a3-target
pd-a3-crit-A3 = crit-A3-test Canonic.pd-a3-target 'a' Canonic.pd-a3-Idemp-applied

-- so §8's goal for that pair (the two trees of `pd-a3-ambiguous`) is settled at
-- the *empty* prefix, at the state itself, with no descent and no `derivᵖ`:
pd-a3-pair-complete : ∃[ w′ ] ∃[ w″ ]
    ( ( proj₁ (flat {Canonic.pd-a3-target} (proj₁ Canonic.pd-a3-ambiguous))
        ≡ w′ ++ w″ )
    × ∃[ p ] ( Any ( λ s → s ≡ p )
                  (Canonic.pd*-Desc Canonic.pd-a3-target w′)
              × crit p ) )
pd-a3-pair-complete =
  ( [] , proj₁ (flat {Canonic.pd-a3-target} (proj₁ Canonic.pd-a3-ambiguous))
  , refl , ( Canonic.pd-a3-target , pdesc pnil , pd-a3-crit-A3 ) )
```

Soundness of the new disjunct is exactly the reflection lemma `Canonic` §8
records as missing there ("to make `A3? r x ≡ true → Ambig r` itself a theorem,
`canonic`'s rewrite trace would have to be reflected into a concrete `Ctx`/`plug`
+ pair witness"): `pd-a3-ambiguous` and §18's `dup-s1-dup`/`dup-r-lit-dup` are
that reflection for these two states.  Adding a disjunct to `crit` touches every
place that *builds* one (each witness of the third disjunct moves one level
deeper, one more `inj₁`) and every place that *destructs* one, which in this
file is exactly the four context-lifting lemmas of §12 — they gained the clause
written there (`A3-Ctx`).  No other proof reads a `crit`, and no earlier witness
changed summand.

What the new disjunct does change is §20's two stopping rules, and it exposes a
gap in one of them.  Its record rule said: two picks `z`, `z′` with *equal*
continuations, reconstructed trees, equal residuals ⇒ `crit r`.  With A3 present
that conclusion is the fourth disjunct — but the rule as stated was *false*, for
want of one premise: take ``r = $ 'a' ` 1``, its single record and single tree;
every premise holds (`z ≡ z′`, `eq = refl`, one residual compared with itself),
and no disjunct fires at ``$ 'a' ` 1``.  What the rule needs, and what the
descent has in the branch that calls it, is that the two picks are *distinct
records*: then the member list holds two entries with equal — hence
`≈₀`-similar — continuations, and the A3 test fires on that list.  §19's descent
had exactly that decision, as the parameter `dec`; §20 had traded it away for the
expression test `RE-≟`.  The restatement is carried out in §20: the descent takes
`dec` back, and in its negative branch the step tests the continuations with
`RE-≟` — different ones leave `pick-diff-state` (the surviving parameter, now
carrying exactly the record-distinctness premise the descent supplies), equal
ones are closed by `pick-diff-record-prf`, which computes the diagnosis because
`Canonic.pd-Idemp?-members` (§6.3) turns two distinct members with one
continuation into the test firing on the member list.  The residual comparison of
the old rule — and with it the tree test — is gone from the descent: the record
case does not speak of residuals.  What survives that restatement is
`pick-diff-state`, and that is the paper's enumeration argument, not a
formalism gap.  §23 settles it: the configuration is unreachable.

## 23. One continuation per transition

Everything §17–§22 turns on a single property of this project's derivative
list.  The POSIX merging (`pdinstance-oplus`, applied in the sum clause and in
the nullable-concatenation clause of `pdU`) makes `pdU[ r , c ]` behave like the
paper's single derivative expression `deriv s x`: the list has several members
only when the transition leaves `l ● s` with nullable `l` — one member per empty
tree of the left factor, which is the second criterion's own configuration, as
§22 observed — and *all members of `pdU[ r , c ]` continue at one and the same
expression*.  Two picks therefore never continue at *different* expressions:
`pick-diff-state` is discharged by absurdity, and the descent of §20 runs with
only the record decision left.  That decision, §19's `dec`, is what this
section cannot supply — `pdinstance` stores a function field — and §24 shows
the descent does not need it: an equivalent question on residual trees is
decidable.  With it the §8 statement follows through §16's
`completeness-from-desc`.

The result also places this file precisely against the paper's diagnosis.  The
proof walks the pair to the state reached by the *whole* word, and there
§9's `desc-base` reads the two empty trees as A1: a criterion does fire, at the
latest possible state.  The A2/A3 machinery of §17–§22 is what finds a criterion
*earlier* — at the transition where the pair first separates, which is what the
paper's enumeration is for; it sharpens the diagnosis, and the completeness
direction itself does not depend on it.

```agda
-- every element of a `map`/`concatMap` comes from an element of the argument
∈-map⁻ : {A B : Set} ( f : A → B ) ( xs : List A ) ( y : B )
  → y ∈ map f xs → Σ[ x ∈ A ] ( x ∈ xs × f x ≡ y )
∈-map⁻ f [] y ()
∈-map⁻ f (x ∷ xs) y (here p) = ( x , here refl , sym p )
∈-map⁻ f (x ∷ xs) y (there w) with ∈-map⁻ f xs y w
...   | ( x₂ , x∈ , eq ) = ( x₂ , there x∈ , eq )

-- membership destructors: an append and a `concat` (whose element lists must
-- be matched in constructor form, hence the `[] ∷ `_`_` patterns)
∈-++-dest : {A : Set} ( xs ys : List A ) ( y : A )
  → y ∈ xs ++ ys → ( y ∈ xs ) ⊎ ( y ∈ ys )
∈-++-dest [] ys y w = inj₂ w
∈-++-dest (x ∷ xs) ys y (here q) = inj₁ (here q)
∈-++-dest (x ∷ xs) ys y (there w) with ∈-++-dest xs ys y w
...   | inj₁ u = inj₁ (there u)
...   | inj₂ v = inj₂ v

∈-concat-dest : {A : Set} ( xss : List ( List A ) ) ( y : A )
  → y ∈ concat xss → Σ[ xs ∈ List A ] ( xs ∈ xss × y ∈ xs )
∈-concat-dest [] y ()
∈-concat-dest ([] ∷ xss) y z∈ with ∈-concat-dest xss y z∈
...   | ( xs₂ , xs∈ , q ) = ( xs₂ , there xs∈ , q )
∈-concat-dest ((x ∷ xs) ∷ xss) y (here q) = ( x ∷ xs , here refl , here q )
∈-concat-dest ((x ∷ xs) ∷ xss) y (there w) with ∈-++-dest xs (concat xss) y w
...   | inj₁ u = ( x ∷ xs , here refl , there u )
...   | inj₂ v with ∈-concat-dest xss y v
...     | ( xs₂ , xs∈ , q ) = ( xs₂ , there xs∈ , q )

-- a list whose members all continue at one expression
PdConst : ( r : RE ) ( c : Char ) → List ( PDInstance r c ) → Set
PdConst r c xs = ∀ ( z z′ : PDInstance r c )
  → z ∈ xs → z′ ∈ xs → Canonic.pd-expr z ≡ Canonic.pd-expr z′

-- constancy is preserved by maps that send equal continuations to equal
-- continuations — which is what the `pdinstance-*` constructors do, each one
-- wrapping the pattern field in a fixed RE context (`pd-expr-resp∘*` below)
map-const : ( r s : RE ) ( c : Char ) ( f : PDInstance r c → PDInstance s c )
  → ( resp : ( x x₂ : PDInstance r c )
        → Canonic.pd-expr x ≡ Canonic.pd-expr x₂
        → Canonic.pd-expr (f x) ≡ Canonic.pd-expr (f x₂) )
  → ( xs : List ( PDInstance r c ) ) → PdConst r c xs → PdConst s c (map f xs)
map-const r s c f resp xs u z z′ z∈ z′∈
  with ∈-map⁻ f xs z z∈ | ∈-map⁻ f xs z′ z′∈
...   | ( x , x∈ , eq ) | ( x₂ , x₂∈ , eq₂ ) =
    trans (sym (cong Canonic.pd-expr eq))
      (trans (resp x x₂ (u x x₂ x∈ x₂∈)) (cong Canonic.pd-expr eq₂))

-- `concatMap` of a list whose images are pairwise constant at one expression
concat-const : ( s : RE ) ( c : Char )
  → ( xss : List ( List ( PDInstance s c ) ) )
  → (∀ ( xs xs′ : List ( PDInstance s c ) ) → xs ∈ xss → xs′ ∈ xss
       → ( z z′ : PDInstance s c ) → z ∈ xs → z′ ∈ xs′
       → Canonic.pd-expr z ≡ Canonic.pd-expr z′)
  → PdConst s c (concat xss)
concat-const s c xss hyp z z′ z∈ z′∈ with ∈-concat-dest xss z z∈ | ∈-concat-dest xss z′ z′∈
...   | ( xs , x∈ , q ) | ( xs′ , x′∈ , q′ ) = hyp xs xs′ x∈ x′∈ z z′ q q′

concatMap-hyp : { A : Set } ( s : RE ) ( c : Char )
  → ( f : A → List ( PDInstance s c ) ) → ( xs : List A )
  → (∀ ( x x′ : A ) → x ∈ xs → x′ ∈ xs → ( y y′ : PDInstance s c )
        → y ∈ f x → y′ ∈ f x′ → Canonic.pd-expr y ≡ Canonic.pd-expr y′)
  → ( xs₁ xs₂ : List ( PDInstance s c ) )
  → xs₁ ∈ map f xs → xs₂ ∈ map f xs
  → ( z z′ : PDInstance s c ) → z ∈ xs₁ → z′ ∈ xs₂
  → Canonic.pd-expr z ≡ Canonic.pd-expr z′
concatMap-hyp s c f xs hyp xs₁ xs₂ m₁ m₂ z z′ q q′
  with ∈-map⁻ f xs xs₁ m₁ | ∈-map⁻ f xs xs₂ m₂
...   | ( x , x∈ , eq ) | ( x₂ , x₂∈ , eq₂ ) =
    hyp x x₂ x∈ x₂∈ z z′
      (subst ( λ L → z ∈ L ) (sym eq) q)
      (subst ( λ L → z′ ∈ L ) (sym eq₂) q′)

concatMap-const : ( s : RE ) ( c : Char ) { A : Set }
  → ( f : A → List ( PDInstance s c ) ) → ( xs : List A )
  → (∀ ( x x′ : A ) → x ∈ xs → x′ ∈ xs → ( y y′ : PDInstance s c )
        → y ∈ f x → y′ ∈ f x′ → Canonic.pd-expr y ≡ Canonic.pd-expr y′)
  → PdConst s c (concatMap f xs)
concatMap-const s c f xs hyp =
  concat-const s c (map f xs)
    (λ xs₁ xs₂ m₁ m₂ z z′ q q′ →
       concatMap-hyp s c f xs hyp xs₁ xs₂ m₁ m₂ z z′ q q′)

-- continuations of the constructed records, in terms of their inputs
pd-expr∘fuse : ( r : RE ) ( c : Char ) ( loc : ℕ )
  ( x y : PDInstance r c )
  → Canonic.pd-expr (fuse {r} {loc} {c} x y)
    ≡ Canonic.pd-expr x + Canonic.pd-expr y ` loc
pd-expr∘fuse r c loc (pdinstance {pˡ} injˡ evˡ) (pdinstance {pʳ} injʳ evʳ) = refl

pd-expr∘snd : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( ex : Σ[ e ∈ U l ] ( AllEmpty.Flat-[] l e ) ) ( y : PDInstance r c )
  → Canonic.pd-expr (mk-snd-pdi {l} {r} {loc} {c} ex y) ≡ Canonic.pd-expr y
pd-expr∘snd ( e , flat-[] .e eq ) (pdinstance {p} inj ev) = refl

-- the four constructor maps of the `pdU` clauses respect continuations: each
-- computes the new pattern field from the old one, definitionally after the
-- record is destructured (`left`/`right` keep it; `fst`/`star` put it into a
-- fixed concatenation)
pd-expr-resp∘left : ∀ { l r : RE } { loc : ℕ } { c : Char }
  ( z z′ : PDInstance l c ) → Canonic.pd-expr z ≡ Canonic.pd-expr z′
  → Canonic.pd-expr (pdinstance-left {l} {r} {loc} {c} z)
    ≡ Canonic.pd-expr (pdinstance-left {l} {r} {loc} {c} z′)
pd-expr-resp∘left (pdinstance {p} inj ev) (pdinstance {p₂} inj′ ev′) eq = eq

pd-expr-resp∘right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  ( z z′ : PDInstance r c ) → Canonic.pd-expr z ≡ Canonic.pd-expr z′
  → Canonic.pd-expr (pdinstance-right {l} {r} {loc} {c} z)
    ≡ Canonic.pd-expr (pdinstance-right {l} {r} {loc} {c} z′)
pd-expr-resp∘right (pdinstance {p} inj ev) (pdinstance {p₂} inj′ ev′) eq = eq

pd-expr-resp∘fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  ( z z′ : PDInstance l c ) → Canonic.pd-expr z ≡ Canonic.pd-expr z′
  → Canonic.pd-expr (pdinstance-fst {l} {r} {loc} {c} z)
    ≡ Canonic.pd-expr (pdinstance-fst {l} {r} {loc} {c} z′)
pd-expr-resp∘fst {l} {r} {loc} {c}
  (pdinstance {p} inj ev) (pdinstance {p₂} inj′ ev′) eq =
    cong ( λ q → q ● r ` loc ) eq

pd-expr-resp∘star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  ( z z′ : PDInstance r c ) → Canonic.pd-expr z ≡ Canonic.pd-expr z′
  → Canonic.pd-expr (pdinstance-star {r} {ε∉r} {loc} {c} z)
    ≡ Canonic.pd-expr (pdinstance-star {r} {ε∉r} {loc} {c} z′)
pd-expr-resp∘star {r} {ε∉r} {loc} {c}
  (pdinstance {p} inj ev) (pdinstance {p₂} inj′ ev′) eq =
    cong ( λ q → q ● (r * ε∉r ` loc) ` loc ) eq

-- two members built by `fuse` from one right side and continuations that agree
fuse-pair-const : ( r : RE ) ( c : Char ) ( loc : ℕ )
  → ( ys : List ( PDInstance r c ) ) → PdConst r c ys
  → ( x₁ x₂ : PDInstance r c ) → Canonic.pd-expr x₁ ≡ Canonic.pd-expr x₂
  → ( z z′ : PDInstance r c )
  → z ∈ map (fuse {r} {loc} {c} x₁) ys → z′ ∈ map (fuse {r} {loc} {c} x₂) ys
  → Canonic.pd-expr z ≡ Canonic.pd-expr z′
fuse-pair-const r c loc ys uy x₁ x₂ x₁≡x₂ z z′ q q₂
  with ∈-map⁻ (fuse {r} {loc} {c} x₁) ys z q | ∈-map⁻ (fuse {r} {loc} {c} x₂) ys z′ q₂
...   | ( w , w∈ , eq ) | ( w₂ , w₂∈ , eq₂ ) =
    trans (sym (cong Canonic.pd-expr eq))
      (trans (pd-expr∘fuse r c loc x₁ w)
        (trans (cong₂ ( λ a b → a + b ` loc ) x₁≡x₂ (uy w w₂ w∈ w₂∈))
               (trans (sym (pd-expr∘fuse r c loc x₂ w₂))
                      (cong Canonic.pd-expr eq₂))))

-- `pdinstance-oplus` of two constant lists is constant: its members are the
-- pairwise fusions, and each one continues at the sum of one pair of
-- continuations
oplus-const : ( r : RE ) ( c : Char ) ( loc : ℕ )
  → ( xs ys : List ( PDInstance r c ) )
  → PdConst r c xs → PdConst r c ys
  → PdConst r c (pdinstance-oplus {r} {loc} {c} xs ys)
oplus-const r c loc []       ys ux uy z z′ z∈ z′∈ = uy z z′ z∈ z′∈
oplus-const r c loc (x ∷ xs) []  ux uy z z′ z∈ z′∈ = ux z z′ z∈ z′∈
oplus-const r c loc (x ∷ xs) (y ∷ ys) ux uy =
  concatMap-const r c ( λ x₁ → map (fuse {r} {loc} {c} x₁) (y ∷ ys) ) (x ∷ xs)
    ( λ x₁ x₂ x₁∈ x₂∈ → fuse-pair-const r c loc (y ∷ ys) uy x₁ x₂ (ux x₁ x₂ x₁∈ x₂∈) )

-- the continuation of a `pdinstance-snd` member list: one member per empty
-- tree of the left factor, all continuing at the right factor's continuation
snd-pair-const : ∀ { l s : RE } { loc : ℕ } { c : Char }
  → ( ex ex′ : Σ[ e ∈ U l ] ( AllEmpty.Flat-[] l e ) )
  → PdConst s c (PosixPD.pdU[ s , c ])
  → ( y y′ : PDInstance ( l ● s ` loc ) c )
  → y ∈ PDI.pdinstance-snd {l} {s} {loc} {c} ex (PosixPD.pdU[ s , c ])
  → y′ ∈ PDI.pdinstance-snd {l} {s} {loc} {c} ex′ (PosixPD.pdU[ s , c ])
  → Canonic.pd-expr y ≡ Canonic.pd-expr y′
snd-pair-const {l} {s} {loc} {c} ex ex′ u y y′ q q₂
  with ∈-map⁻ (mk-snd-pdi {l} {s} {loc} {c} ex) (PosixPD.pdU[ s , c ]) y q
    | ∈-map⁻ (mk-snd-pdi {l} {s} {loc} {c} ex′) (PosixPD.pdU[ s , c ]) y′ q₂
...   | ( w , w∈ , eq ) | ( w₂ , w₂∈ , eq₂ ) =
    trans (sym (cong Canonic.pd-expr eq))
      (trans (pd-expr∘snd ex w)
        (trans (u w w₂ w∈ w₂∈)
          (trans (sym (pd-expr∘snd ex′ w₂)) (cong Canonic.pd-expr eq₂))))

snd-list-const : ∀ { l s : RE } { ε∈l : RE.ε∈ l } { loc : ℕ } { c : Char }
  → PdConst s c (PosixPD.pdU[ s , c ])
  → PdConst ( l ● s ` loc ) c
      (PDI.concatmap-pdinstance-snd {l} {s} {ε∈l} {loc} {c} (PosixPD.pdU[ s , c ]))
snd-list-const {l} {s} {ε∈l} {loc} {c} u =
  concatMap-const ( l ● s ` loc ) c
    ( λ ex → PDI.pdinstance-snd {l} {s} {loc} {c} ex (PosixPD.pdU[ s , c ]) )
    ( PDI.zip-es-flat-[]-es {l} {ε∈l} (mkAllEmptyU {l} ε∈l)
        (AllEmpty.mkAllEmptyU-sound {l} ε∈l) )
    ( λ ex ex′ ex∈ ex′∈ → snd-pair-const {l} {s} {loc} {c} ex ex′ u )

-- one continuation per transition: the members of `pdU[ r , c ]` all continue
-- at the same expression.  Induction on `r`; every clause either maps a
-- constant list or oplus's two constant lists, which is constant by
-- `oplus-const`
pdU-const : ( r : RE ) ( c : Char ) ( z z′ : PDInstance r c )
  → z ∈ PosixPD.pdU[ r , c ] → z′ ∈ PosixPD.pdU[ r , c ]
  → Canonic.pd-expr z ≡ Canonic.pd-expr z′
pdU-const ε c z z′ ()
pdU-const ( $ c₀ ` loc ) c z z′ z∈ z′∈ with c₀ Char.≟ c | z∈ | z′∈
...   | yes refl | here p | here q = cong Canonic.pd-expr (trans p (sym q))
...   | yes refl | here p | there ()
...   | yes refl | there () | _
...   | no ¬c | () | _
pdU-const ( l + s ` loc ) c z z′ z∈ z′∈ =
  oplus-const ( l + s ` loc ) c loc
    ( map (pdinstance-left {l} {s} {loc} {c}) (PosixPD.pdU[ l , c ]) )
    ( map (pdinstance-right {l} {s} {loc} {c}) (PosixPD.pdU[ s , c ]) )
    ( map-const l ( l + s ` loc ) c (pdinstance-left {l} {s} {loc} {c})
        (pd-expr-resp∘left {l} {s} {loc} {c})
        (PosixPD.pdU[ l , c ]) (pdU-const l c) )
    ( map-const s ( l + s ` loc ) c (pdinstance-right {l} {s} {loc} {c})
        (pd-expr-resp∘right {l} {s} {loc} {c})
        (PosixPD.pdU[ s , c ]) (pdU-const s c) )
    z z′ z∈ z′∈
pdU-const ( r * ε∉r ` loc ) c z z′ z∈ z′∈ =
  map-const r ( r * ε∉r ` loc ) c (pdinstance-star {r} {ε∉r} {loc} {c})
    (pd-expr-resp∘star {r} {ε∉r} {loc} {c})
    (PosixPD.pdU[ r , c ]) (pdU-const r c) z z′ z∈ z′∈
pdU-const ( l ● s ` loc ) c z z′ z∈ z′∈ with RE.ε∈? l
...   | no ¬ε∈l =
      map-const l ( l ● s ` loc ) c (pdinstance-fst {l} {s} {loc} {c})
        (pd-expr-resp∘fst {l} {s} {loc} {c})
        (PosixPD.pdU[ l , c ]) (pdU-const l c) z z′ z∈ z′∈
...   | yes ε∈l =
      oplus-const ( l ● s ` loc ) c loc
        ( map (pdinstance-fst {l} {s} {loc} {c}) (PosixPD.pdU[ l , c ]) )
        ( PDI.concatmap-pdinstance-snd {l} {s} {ε∈l} {loc} {c}
            (PosixPD.pdU[ s , c ]) )
        ( map-const l ( l ● s ` loc ) c (pdinstance-fst {l} {s} {loc} {c})
            (pd-expr-resp∘fst {l} {s} {loc} {c})
            (PosixPD.pdU[ l , c ]) (pdU-const l c) )
        ( snd-list-const {l} {s} {ε∈l} {loc} {c} (pdU-const s c) )
        z z′ z∈ z′∈

-- §20's first stopping configuration is unreachable: distinct records of one
-- pd list never continue at distinct expressions
cstate-⊥ : pick-diff-state
cstate-⊥ {r} {c} z z′ z∈ z′∈ z≢z′ u v u∈ v∈ u≡ v≡ ¬pd =
  ⊥-elim (¬pd (pdU-const r c z z′ z∈ z′∈))

-- what remains of §20's descent after this: the record decision.  §23 stops
-- here because `PDInstance` equality is intensional (the constructor stores a
-- function field), so §19's `dec` has no decision procedure *as stated* —
-- §24 shows the descent does not need it
```

## 24. The record decision, computed: the completeness direction, closed

The one question §23 leaves is whether the two picks are *one record*.  As
stated that question has no decision procedure — `pdinstance` stores a function
(`U p → U r`), so record identity is intensional (§19) — and this is where the
paper's enumeration would have to quotient instances by pattern.  But the
descent never uses record identity *as such*: it uses it to choose between
continuing through one shared transition and firing the criterion.  That choice
has an equivalent form on the other side of the reconstruction, where it is
decidable: the two **residual trees**.  By `pdU-const` both residuals, after
transport along one equation, live at the same expression, and tree identity at
one expression is decidable (`ParseTree._⊢_≟_`).

- *different residuals*: the descent continues — at the single reached state,
  through the single member `z`, exactly as §20's shared-record branch does;
- *equal residuals*: the two records cannot have been one: a single record maps
  distinct trees to distinct residuals (`Recons-residual-2`), so equal
  residuals mean *two distinct members with one continuation* — the A3
  configuration, closed by §22's `pick-diff-record-prf`.

In `diff-records-≟` the claim's two transports cancel in a single clause: the
record equation and the continuation equation are case-split, which identifies
the two records and dissolves the transport — constructor injectivity does all
the work, no postulate and no transport coherence.

```agda
-- transporting a tree across an equation of expressions does not move its word
flat-resp : ∀ { r r′ : RE } ( eq : r ≡ r′ ) ( u : U r )
  → proj₁ (flat {r′} (subst ( λ e → U e ) eq u)) ≡ proj₁ (flat {r} u)
flat-resp refl u = refl

-- equal residuals ⇒ distinct records: were the picks one record,
-- `Recons-residual-2`'s computation (`cong inj` under one transition map)
-- would separate the residuals.  Splitting the record equation identifies the
-- two records, and with it the continuation equation dissolves
diff-records-≟ : ∀ { r : RE } { c : Char } { ws : List Char } { u v : U r }
  ( z z′ : PDInstance r c )
  ( rec-l : Recons {r} {c} u z ) ( rec-r : Recons {r} {c} v z′ )
  ( u≡ : proj₁ (flat {r} u) ≡ c ∷ ws ) ( v≡ : proj₁ (flat {r} v) ≡ c ∷ ws )
  ( q : Canonic.pd-expr z′ ≡ Canonic.pd-expr z )
  → residual rec-l u≡ ≡ subst ( λ e → U e ) q ( residual rec-r v≡ )
  → ¬ ( u ≡ v )
  → ¬ ( z ≡ z′ )
diff-records-≟ z z′ (recons {inj = inj} uˡ ( w∈ˡ , eqˡ ))
                  (recons {inj = inj′} vʳ ( w∈ʳ , eqʳ ))
  u≡ v≡ q eq u≢v ρ with q | ρ
...   | refl | refl = u≢v (trans (sym eqˡ) (trans (cong inj eq) eqʳ))

-- the completeness descent, with the decidable test in place of the record
-- decision: pick both members, place the second residual at the first
-- member's continuation (`pdU-const`), and decide the residuals
desc-picks-≟ : ( r : RE ) → ( w : List Char )
  → ( u v : U r )
  → proj₁ (flat {r} u) ≡ w → proj₁ (flat {r} v) ≡ w → ¬ ( u ≡ v )
  → desc-concl r w
desc-picks-≟ r [] u v u≡[] v≡[] u≢v = desc-base u v u≡[] v≡[] u≢v
desc-picks-≟ r (c ∷ ws) u v u≡ v≡ u≢v
  with pick-Any (PosixPD.pdU-complete {r} {c} u u≡)
... | ( z , rec-l , z∈ ) with pick-Any (PosixPD.pdU-complete {r} {c} v v≡)
...   | ( z′ , rec-r , z′∈ )
      with (ParseTree._⊢_≟_ (Canonic.pd-expr z) (residual rec-l u≡)
             ( subst ( λ e → U e ) (sym (pdU-const r c z z′ z∈ z′∈))
               (residual rec-r v≡) ))
...     | yes eq =
          inj₁ (pick-diff-record-prf z z′ z∈ z′∈
                  (diff-records-≟ z z′ rec-l rec-r u≡ v≡
                     (sym (pdU-const r c z z′ z∈ z′∈)) eq u≢v)
                  (pdU-const r c z z′ z∈ z′∈))
...     | no x≢y =
          desc-step z z∈
            (desc-picks-≟ (Canonic.pd-expr z) ws x y x≡ y≡ x≢y)
        where
          q  = sym (pdU-const r c z z′ z∈ z′∈)
          x  = residual rec-l u≡
          x≡ = residual-word rec-l u≡
          y  = subst ( λ e → U e ) q ( residual rec-r v≡ )
          y≡ = trans (flat-resp q (residual rec-r v≡)) (residual-word rec-r v≡)

-- the completeness direction, closed with no postulate at all: §23's
-- `pdU-const` supplies the shared continuation, the residual test replaces the
-- record decision, and §16 turns the descent into the statement about the pair
Desc-complete-≟ : Desc-complete
Desc-complete-≟ r w u v = desc-picks-≟ r w u v

-- and §8's `completeness` (signature stated there, proved here)
completeness {r} u v w≡ u≢v = completeness-from-desc Desc-complete-≟ r u v w≡ u≢v
```

