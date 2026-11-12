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
  checked `Ambig sd`: the completeness direction for this example.

```agda
{-# OPTIONS --rewriting #-}
module cgp.ambig.Complete where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉)

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
open AllEmpty using ( flat-[] )

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
open import Data.Nat using (ℕ; _≟_)
open import Data.List using (List; _∷_; []; _++_; map; [_])
open import Data.List.Properties using (++-cancelˡ)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Product using (_×_; _,_; proj₁ ; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong₂)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)
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

This is the completeness direction *for this example*, in the form the paper
proves in general: the ambiguity witness is the pair of distinct trees of the
state `sd-s2` that `Canonic.pd*-A1→Ambig` extracts from A1 there (§1's
`Collapsed` witness is what `lift-Ambig` inside it consumes), transported back
along the *injective* map of the unique instance of `pdUMany[ sd , a a ]`.
What the general statement would still need is §4.1 — that every word
reaches *some* injective-instance state — which stays open.
