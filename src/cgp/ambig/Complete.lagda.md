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
* §4 records what still stands between this and a proof of the completeness
  direction for a concrete `r`: uniqueness of the reconstructing instance
  (Antimirov disjointness, absent from the project), and an Agda-level
  obstacle — a *computed* instance such as `pdUMany[ sd , a a ]` cannot be
  named, so §2–§3 cannot be pointed at it.  The checks behind that claim are
  in §4.

```agda
{-# OPTIONS --rewriting #-}
module cgp.ambig.Complete where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉)

import cgp.ParseTree as ParseTree
open ParseTree using ( U ; EmptyU ; LetterU ; LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unListU
                     ; inv-leftU ; inv-rightU ; inv-pairU )

import cgp.Word as Word
open Word using (_∈⟦_⟧)

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance*
               ; mkinjList ; compose-pdi-with )

import cgp.posix.PartialDerivative as PosixPD
open PosixPD using ( mkfuseInj ; injId )

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using ( Ambig )

import cgp.ambig.Canonic as Canonic

import cgp.ambig.Converse as Converse
open Converse using ( sd ; sd-s1 ; sd-s2 ; aa ; res-a ; sd-s2-A1 ; sd-Desc₂ )

import cgp.Recons as Recons
open Recons using ( Recons ; Recons* )

open import Data.Char using (Char)
open import Data.Nat using (ℕ)
open import Data.List using (List; _∷_; []; _++_)
open import Data.List.Properties using (++-cancelˡ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁ ; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_)
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

```agda
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
pairL-inj : ∀ { l r : RE } { loc : ℕ } { t : U r }
  → ( f : U l → U l )
  → ( ∀ ( u v : U l ) → f u ≡ f v → u ≡ v )
  → ∀ ( u v : U l ) → PairU {l} {r} {loc} (f u) t ≡ PairU (f v) t → u ≡ v
pairL-inj {l} {r} {loc} {t} f f-inj u v eq
  with inv-pairU {l = l} {r} {loc} (f u) t (f v) t eq
...   | fu≡fv , _ = f-inj u v fu≡fv

pairR-inj : ∀ { l r : RE } { loc : ℕ } { t : U l }
  → ( f : U r → U r )
  → ( ∀ ( u v : U r ) → f u ≡ f v → u ≡ v )
  → ∀ ( u v : U r ) → PairU {l} {r} {loc} t (f u) ≡ PairU t (f v) → u ≡ v
pairR-inj {l} {r} {loc} {t} f f-inj u v eq
  with inv-pairU {l = l} {r} {loc} t (f u) t (f v) eq
...   | _ , fu≡fv = f-inj u v fu≡fv

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

**4.2 A computed instance cannot be named.**  The injectivity proofs of §3 are
about maps; to use one for a transition map of `pdU` the instance has to be a
term.  It is not: matching on the computed list leaves unrefutable cases,

The definitions

    pdUMany-sd-aa-named : PDInstance* sd aa
    pdUMany-sd-aa-named with PosixPD.pdUMany[ sd , aa ]
    ...   | pdi ∷ [] = pdi

    pdU-sd-s1-a-named : PDInstance sd-s1 'a'
    pdU-sd-s1-a-named with PosixPD.pdU[ sd-s1 , 'a' ]
    ...   | pdi ∷ [] = pdi

are rejected with `Missing cases: [] / x ∷ x₁ ∷ w`: nothing in the type of
those lists rules the other shapes out (being a singleton is a computational
fact, not a typing fact), so the case split cannot be closed.

and the parametric substitute does not work either: given `pdis ≡ pdU[ … ]` and
`pdis ≡ pdi ∷ []` for *variables*, the goal `pd-expr pdi ≡ sd-s2` is not `refl`
— an equation about a list cannot rewrite the field of an abstract instance.
What *is* computational is the list as a whole:

```agda
-- the state after `a a`, as a computed list (Converse.sd-Desc₂)
sd-aa-state : Canonic.pd*-Desc sd aa ≡ ( sd-s2 ∷ [] )
sd-aa-state = refl

-- and A1 holds at it: the state is nullable twice over (Converse.sd-s2-A1)
sd-aa-A1 : AmbigCheck.AmbigA1 sd-s2
sd-aa-A1 = sd-s2-A1
```

Closing 4.2 means either building the instance by hand out of the constructors
(`pdinstance-left`/`-right`/`-fst`/`-snd`/`-star`, `fuse`) and proving the
computed list equal to the singleton containing it — a mechanical replay of the
`any-recons-*` lemmas — or a cardinality lemma for `pdU`/`pdUMany`.  With that
instance in hand, §3 gives injectivity of its map once §4.1 discharges the
range-disjointness of its `+` node (`mkfuseInj-inj` is the only step that is
not local), §1 plus `sd-s2-A1` give `Ambig sd`, and the criterion that fires
is `A1`, as computed by `Converse.sd-s2-criteria`.
