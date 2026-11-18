# Ambiguity Diagnosis (Ambiguity Detection)

This module implements and proves the properties of the ambiguity detection criteria
from section 6 "Ambiguity Diagnosis" of

> Martin Sulzmann and Kenny Zhuo Ming Lu.
> Derivative-Based Diagnosis of Regular Expression Ambiguity. CIAA 2016.
> (`/home/luzm/assembla/regexp/trunk/ambig-check/finalCIAA2016.tex`)

based on the existing formalism of this project
(`cgp.RE`, `cgp.ParseTree`, `cgp.Word`, `cgp.empty.AllEmptyParseTree`).

## Correspondence with the paper

The Ambiguity Criteria proposition (paper section 6) states, for a non-problematic
expression r: r is ambiguous iff there exists a *realizable* state s ∈ Desc(r) and a
symbol x such that one of

* **A1** `| allEps s | > 1`, or
* **A2** `s = R[t1 ● t2]` where `| allEps s | > 1` (R[] is a hole context, no hole under a star), or
* **A3** `L(canonic(deriv s x)) ≠ {}` and the `Idemp` similarity rule is applied when
  building the canonical representative `canonic(deriv s x)`.

Notes on the correspondence:

1. In this project every `RE` is non-problematic *by construction* (the star
   constructor `_*)_` carries the evidence `ε∉ r`), and no expression denotes the
   empty language (see `ParseTree.r-∃u`). Hence the side conditions "non-problematic"
   and "realizable" of the paper are discharged automatically for top-level
   expressions.
2. What is formalized here is the **soundness direction** of the criteria for the
   top-level expression (the FST initial state):
   * `AmbigA1 → Ambig` (the paper's A1, using `mkAllEmptyU` as `allEps`),
   * `AmbigA2 → Ambig` (the paper's A2, with the hole contexts R[] of the paper's
     Definition `Ctxt` / `Hole Expressions`),
   * plus the lemma `NoDup-mkAllEmptyU` which certifies that the syntactic test
     `length (mkAllEmptyU ε∈r) > 1` faithfully reflects `| allEps r | > 1`
     (distinct list positions give distinct parse trees).
3. **A3 is not formalized**: it refers to canonical representatives under the
   similarity relation `≈` (paper Definitions `canonical representative` and
   `Similarity with Parse Tree Transformation`), which has no counterpart in the
   current partial-derivative based formalism (the only expression rewriting
   formalized in the project is `assoc` in `cgp.PDInstance`). To justify that a
   criterion like A3 is *required*, we exhibit a concrete ambiguous expression that
   satisfies neither A1 nor A2 (`ambiguousSum`, `notA1Sum`, `notA2Sum`). This is
   exactly the situation the paper catches with the `Idemp` rule (A3).

The full equivalence (the "only if" direction, quantifying over realizable states
`Desc(r)` and transitions) requires the FST construction of paper section 4, which
is future work.

```agda
{-# OPTIONS --rewriting #-}
module cgp.ambig.AmbigCheck where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉; ε∈; ε∈?; ε∈ε; ε∈_●_; ε∈_+_ ; ε∈_<+_ ; ε∈_+>_ ; ε∈* ; ε∉$ ; ε∉_+_ ; ε∉r→¬ε∈r )

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU; LetterU; LeftU; RightU; PairU; ListU ; unListU ; flat ; r-∃u ; inv-leftU ; inv-rightU ; inv-pairU ; LeftU≢RightU ; RightU≢LeftU ; _⊢_≟_ )

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; pdinstance-left ; pdinstance-right ; pdinstance-fst ; PDInstance* ; pdinstance* )

import cgp.posix.PartialDerivative as PosixPD

import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; Flat-[] ; flat-[] ; mkAllEmptyU-sound )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; length)

open import Data.List.Properties using (++-assoc ; ∷-injectiveˡ ; ∷-injectiveʳ ; length-map ; length-++ ; ∷-injective ; ++-identityʳ)

import Data.Bool.Base as Bool
open Bool using (Bool; true; false; _∨_)

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using ( ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ; ≤-refl ; ≤-trans ; m≤n⇒m≤1+n )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; cong₂)

import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map)

import Data.List.Relation.Unary.Any as AnyMod
open AnyMod using (Any; here; there)
import Data.List.Membership.Propositional
open Data.List.Membership.Propositional using (_∈_)
import Data.List.Membership.Propositional.Properties as ListMem
-- ListMem.∈-++⁻ : ∀ xs {ys} → v ∈ xs ++ ys → (v ∈ xs) ⊎ (v ∈ ys)
-- ListMem.∈-map⁻ : y ∈ map f xs → ∃[ x ] ( x ∈ xs × y ≡ f x )

import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )

import Data.Maybe as Maybe
open Maybe using ( Maybe ; just ; nothing )
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Relation.Nullary as Nullary
open Nullary using (¬_)

import Data.Empty as Empty
open Empty using (⊥ ; ⊥-elim)

import Relation.Nullary.Decidable as Decidable
open Decidable using (Dec; yes; no; ⌊_⌋)

import cgp.Utils as Utils
open Utils using ( NoDup ; nd[] ; nd∷ ; lookup-All ; nd-++ ; nd-map ; ∈-concatMap⁻
  ; Dec→true ; ∨-true ; ∈-++-inv ; ∈-++ˡ ; ∈-++ʳ ; ∈-∷-++ʳ ; ∈-map⁻ )

```

## 1. (Ambiguous / unambiguous) expressions  (paper section 2)

Paper Definition "Ambiguous Regular Expressions": r is ambiguous iff there exist two
distinct parse trees `v₁` and `v₂` for r with `| v₁ | = | v₂ |`.

```agda
Ambig : RE → Set
Ambig r = Σ[ u ∈ U r ] Σ[ v ∈ U r ]
            ( (proj₁ (flat {r} u) ≡ proj₁ (flat {r} v)) × (¬ (u ≡ v)) )

UnAmbig : RE → Set
UnAmbig r = ∀ ( u v : U r ) → proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) → u ≡ v

UnAmbig→¬Ambig : ∀ ( r : RE ) → UnAmbig r → ¬ Ambig r
UnAmbig→¬Ambig r unambig (u , v , w≡ , u≢v) = u≢v (unambig u v w≡)

-- the converse direction uses the decidability of parse tree equality (ParseTree._⊢_≟_)
¬Ambig→UnAmbig : ∀ ( r : RE ) → ¬ Ambig r → UnAmbig r
¬Ambig→UnAmbig r ¬amb u v w≡ with r ⊢ u ≟ v
...   | yes u≡v = u≡v
...   | no ¬u≡v = ⊥-elim (¬amb (u , v , w≡ , ¬u≡v))

```

## 2. Criterion A1 (paper section 6, condition A1)

A1 concerns a nullable state s (a final FST state): `| allEps s | > 1`.
In this project `allEps` is formalized by `AllEmpty.mkAllEmptyU`.

```agda
AmbigA1 : RE → Set
AmbigA1 r = Σ[ ε∈r ∈ ε∈ r ]
              ( suc (suc zero) ≤ length (mkAllEmptyU {r} ε∈r) )

```

### 2.1. `mkAllEmptyU` has no duplicates

To make sure the syntactic length test is faithful we prove that all parse trees
generated by `mkAllEmptyU` are pairwise distinct.

The generic list lemmas flagged here (`NoDup`/`nd-++`/`nd-map`/`lookup-All`/
`∈-concatMap⁻`) now live in `cgp.Utils`; `∈-++-inv`, `∈-map⁻`, `Dec→true` and
`∨-true` were checked against the standard library and kept as thin wrappers
there (see the note in `cgp.Utils`).  What remains below is `RE` / `U RE` specific.

```agda
-- cartesian product of two duplicate free lists (the ● case of mkAllEmptyU)
nd-cart : ∀ { l r : RE } { loc : ℕ } { us : List (U l) } { vs : List (U r) }
  → NoDup {U l} us
  → NoDup {U r} vs
  → NoDup {U (l ● r ` loc)} (List.concatMap (λ u → List.map (λ v → PairU {l} {r} {loc} u v) vs) us)
nd-cart {l} {r} {loc} nd[] ndvs = nd[]
nd-cart {l} {r} {loc} {vs = vs} (nd∷ {x = a} {xs = us} a∉ ndus) ndvs =
  nd-++ (nd-map (λ v → PairU {l} {r} {loc} a v) (λ {v₁} {v₂} eq → proj₂ (inv-pairU {l} {r} {loc} a v₁ a v₂ eq)) ndvs)
        disj-blocks
        (nd-cart ndus ndvs)
  where
    disj-blocks : ∀ { x y }
      → x ∈ List.map (λ v → PairU {l} {r} {loc} a v) vs
      → y ∈ List.concatMap (λ u → List.map (λ v → PairU {l} {r} {loc} u v) vs) us
      → ¬ (x ≡ y)
    disj-blocks {x} {y} x∈ y∈ eq with ListMem.∈-map⁻ (λ v → PairU {l} {r} {loc} a v) x∈ | ∈-concatMap⁻ (λ u → List.map (λ v → PairU {l} {r} {loc} u v) vs) us y y∈
    ...   | v , v∈vs , x≡Pair-a-v | u′ , u′∈us , y∈block with ListMem.∈-map⁻ (λ v → PairU {l} {r} {loc} u′ v) y∈block
    ...   | v′ , v′∈vs , y≡Pair-u′-v′ =
        a∉ (AnyMod.map (λ eq′ → trans (proj₁ (inv-pairU {l} {r} {loc} a v u′ v′ (trans (trans (sym x≡Pair-a-v) eq) y≡Pair-u′-v′))) eq′) u′∈us)

-- elements produced by LeftU and by RightU are always distinct
⊥-L-R-∈ : ∀ { l r : RE } { loc : ℕ } { us : List (U l) } { vs : List (U r) } { x y : U (l + r ` loc) }
  → x ∈ List.map (λ u → LeftU {l} {r} {loc} u) us
  → y ∈ List.map (λ v → RightU {l} {r} {loc} v) vs
  → x ≡ y
  → ⊥
⊥-L-R-∈ {l = l} {r = r} {loc = loc} {x} {y} x∈ y∈ eq with ListMem.∈-map⁻ (λ u → LeftU {l} {r} {loc} u) x∈ | ListMem.∈-map⁻ (λ v → RightU {l} {r} {loc} v) y∈
...   | u , u∈us , x≡LeftU-u | v , v∈vs , y≡RightU-v = LeftU≢RightU u v (trans (trans (sym x≡LeftU-u) eq) y≡RightU-v)

NoDup-mkAllEmptyU : ∀ { r : RE } ( ε∈r : ε∈ r )
  → NoDup {U r} (mkAllEmptyU {r} ε∈r)
NoDup-mkAllEmptyU ε∈ε = nd∷ (λ()) nd[]
NoDup-mkAllEmptyU {l + r ` loc} ε∈l+r with ε∈l+r
...   | ε∈ ε∈l + ε∈r =
          nd-++ (nd-map (λ u → LeftU {l} {r} {loc} u) (λ {u₁} {u₂} eq → inv-leftU {l} {r} {loc} u₁ u₂ eq) (NoDup-mkAllEmptyU ε∈l))
                (λ {x} {y} x∈ y→∈ eq → ⊥-L-R-∈ x∈ y→∈ eq)
                (nd-map (λ v → RightU {l} {r} {loc} v) (λ {v₁} {v₂} eq → inv-rightU {l} {r} {loc} v₁ v₂ eq) (NoDup-mkAllEmptyU ε∈r))
...   | ε∈ ε∈l <+ ε∉r =
          nd-map (λ u → LeftU {l} {r} {loc} u) (λ {u₁} {u₂} eq → inv-leftU {l} {r} {loc} u₁ u₂ eq) (NoDup-mkAllEmptyU ε∈l)
...   | ε∈ ε∉l +> ε∈r =
          nd-map (λ v → RightU {l} {r} {loc} v) (λ {v₁} {v₂} eq → inv-rightU {l} {r} {loc} v₁ v₂ eq) (NoDup-mkAllEmptyU ε∈r)
NoDup-mkAllEmptyU {l ● r ` loc} (ε∈ ε∈l ● ε∈r) =
  nd-cart (NoDup-mkAllEmptyU ε∈l) (NoDup-mkAllEmptyU ε∈r)
NoDup-mkAllEmptyU {r * ε∉r ` loc} ε∈* = nd∷ (λ()) nd[]

```

### 2.2. From "length > 1" to two distinct empty parse trees

```agda
not-1-le-0 : suc zero ≤ zero → ⊥
not-1-le-0 ()

not-2-le-0 : suc (suc zero) ≤ zero → ⊥
not-2-le-0 ()

not-2-le-1 : suc (suc zero) ≤ suc zero → ⊥
not-2-le-1 (s≤s p) = not-1-le-0 p

length≥2→∃∷∷ : ∀ { a : Set } { xs : List a }
  → suc (suc zero) ≤ List.length xs
  → ∃[ x ] ( ∃[ y ] ( ∃[ xs′ ] ( xs ≡ x ∷ y ∷ xs′ ) ) )
length≥2→∃∷∷ {xs = []} p = ⊥-elim (not-2-le-0 p)
length≥2→∃∷∷ {xs = x ∷ []} p = ⊥-elim (not-2-le-1 p)
length≥2→∃∷∷ {xs = x ∷ y ∷ xs′} p = x , y , xs′ , refl

nd-two-core : ∀ { a : Set } { x y : a } { xs : List a }
  → NoDup {a} (x ∷ y ∷ xs)
  → ∃[ u ] ∃[ v ] ( u ∈ (x ∷ y ∷ xs) × v ∈ (x ∷ y ∷ xs) × ¬ (u ≡ v) )
nd-two-core {x = x} {y = y} (nd∷ x∉ _) = x , y , ( here refl , there (here refl) , λ x≡y → x∉ (here x≡y) )

A1→∃two : ∀ { r : RE } ( ε∈r : ε∈ r )
  → suc (suc zero) ≤ List.length (mkAllEmptyU {r} ε∈r)
  → ∃[ u ] ∃[ v ] ( u ∈ mkAllEmptyU {r} ε∈r × v ∈ mkAllEmptyU {r} ε∈r × ¬ (u ≡ v) )
A1→∃two {r} ε∈r p≤ with length≥2→∃∷∷ {xs = mkAllEmptyU {r} ε∈r} p≤
...   | x , y , xs′ , xs≡ with nd-two-core {xs = xs′} (subst (λ l → NoDup {U r} l) xs≡ (NoDup-mkAllEmptyU ε∈r))
...   | u , v , u∈ , v∈ , u≢v = u , v , ( subst (λ l → u ∈ l) (sym xs≡) u∈ , subst (λ l → v ∈ l) (sym xs≡) v∈ , u≢v )

```

### 2.3. Soundness of A1:  A1 r implies r is ambiguous

Both empty parse trees flatten to `[]` (`mkAllEmptyU-sound`) and they are distinct
(`NoDup-mkAllEmptyU`). (Paper: "If we encounter multiple empty parse trees for a
nullable descendant (accepting state) then ... the initial expression is ambiguous.")

```agda
A1→Ambig : ∀ ( r : RE ) → AmbigA1 r → Ambig r
A1→Ambig r (ε∈r , len≥2) with A1→∃two ε∈r len≥2
...   | u , v , u∈ , v∈ , u≢v with lookup-All (mkAllEmptyU-sound ε∈r) u∈ | lookup-All (mkAllEmptyU-sound ε∈r) v∈
...   | flat-[] .u eq₁ | flat-[] .v eq₂ = u , v , ( trans eq₁ (sym eq₂) , u≢v )

```

## 3. Criterion A2 (paper section 6, condition A2)

A2 concerns a transition: it fires when a (reachable) expression contains a
subterm `t₁ ● t₂` whose left component `t₁` has multiple empty parse trees
(the `Right v₂` case of the paper's `injs` injection applies `allEps t₁`).

We formalize the paper's hole expressions (Definition `Similarity`, rule
`Hole Expressions`: `R[] ::= [] | R[] ● s | s ● R[] | R[] + s | s + R[]`;
there is no hole inside a Kleene star).

```agda
data Ctx : Set where
  𝟘 : Ctx
  Ctx●R : Ctx → RE → ℕ → Ctx
  L●Ctx : RE → Ctx → ℕ → Ctx
  Ctx+R : Ctx → RE → ℕ → Ctx
  L+Ctx : RE → Ctx → ℕ → Ctx

plug : Ctx → RE → RE
plug 𝟘 t = t
plug (Ctx●R ctx s loc) t = plug ctx t ● s ` loc
plug (L●Ctx s ctx loc) t = s ● plug ctx t ` loc
plug (Ctx+R ctx s loc) t = plug ctx t + s ` loc
plug (L+Ctx s ctx loc) t = s + plug ctx t ` loc

AmbigA2 : RE → Set
AmbigA2 r = Σ[ ctx ∈ Ctx ] Σ[ l ∈ RE ] Σ[ t ∈ RE ] Σ[ loc ∈ ℕ ]
              ( (plug ctx (l ● t ` loc) ≡ r)
              × Σ[ ε∈l ∈ ε∈ l ] ( suc (suc zero) ≤ length (mkAllEmptyU {l} ε∈l) ) )

```

### 3.1. Filling a context with a parse tree

`CtxT ctx u` embeds a parse tree `u` of the hole expression into a parse tree of
`plug ctx _`; sibling subtrees are arbitrary inhabitants (`ParseTree.r-∃u`).

```agda
CtxT : ∀ ( ctx : Ctx ) { p : RE } → U p → U (plug ctx p)
CtxT 𝟘 u = u
CtxT (Ctx●R ctx s loc) u = PairU (CtxT ctx u) (proj₁ (r-∃u s))
CtxT (L●Ctx s ctx loc) u = PairU (proj₁ (r-∃u s)) (CtxT ctx u)
CtxT (Ctx+R ctx s loc) u = LeftU (CtxT ctx u)
CtxT (L+Ctx s ctx loc) u = RightU (CtxT ctx u)

-- filling a context preserves equality of flattened words
CtxT-pres-flat : ∀ ( ctx : Ctx ) { p : RE } { u v : U p }
  → proj₁ (flat {p} u) ≡ proj₁ (flat {p} v)
  ------------------------------------------------------------
  → proj₁ (flat {plug ctx p} (CtxT ctx u)) ≡ proj₁ (flat {plug ctx p} (CtxT ctx v))
CtxT-pres-flat 𝟘 eq = eq
CtxT-pres-flat (Ctx●R ctx s loc) eq = cong₂ _++_ (CtxT-pres-flat ctx eq) refl
CtxT-pres-flat (L●Ctx s ctx loc) eq = cong₂ _++_ refl (CtxT-pres-flat ctx eq)
CtxT-pres-flat (Ctx+R ctx s loc) eq = CtxT-pres-flat ctx eq
CtxT-pres-flat (L+Ctx s ctx loc) eq = CtxT-pres-flat ctx eq

-- filling a context is injective
CtxT-injective : ∀ ( ctx : Ctx ) { p : RE } { u v : U p }
  → CtxT ctx u ≡ CtxT ctx v
  → u ≡ v
CtxT-injective 𝟘 eq = eq
CtxT-injective (Ctx●R ctx s loc) {p = p} {u} {v} eq = CtxT-injective ctx (proj₁ (inv-pairU {plug ctx p} {s} {loc} (CtxT ctx u) (proj₁ (r-∃u s)) (CtxT ctx v) (proj₁ (r-∃u s)) eq))
CtxT-injective (L●Ctx s ctx loc) {p = p} {u} {v} eq = CtxT-injective ctx (proj₂ (inv-pairU {s} {plug ctx p} {loc} (proj₁ (r-∃u s)) (CtxT ctx u) (proj₁ (r-∃u s)) (CtxT ctx v) eq))
CtxT-injective (Ctx+R ctx s loc) {p = p} {u} {v} eq = CtxT-injective ctx (inv-leftU {plug ctx p} {s} {loc} (CtxT ctx u) (CtxT ctx v) eq)
CtxT-injective (L+Ctx s ctx loc) {p = p} {u} {v} eq = CtxT-injective ctx (inv-rightU {s} {plug ctx p} {loc} (CtxT ctx u) (CtxT ctx v) eq)

```

### 3.2. Soundness of A2:  A2 r implies r is ambiguous

(Paper: this happens "if we apply the derivative operation on some subterm
`t₁ ● t₂` where `t₁` is a nullable expression with multiple empty parse trees".
Since every parse tree inhabits its expression in this formalism (`r-∃u`), the
top-level instance of A2 is unconditionally sound.)

```agda
A2→Ambig : ∀ ( r : RE ) → AmbigA2 r → Ambig r
A2→Ambig r (ctx , l , t , loc , (eq , (ε∈l , len≥2))) rewrite sym eq with A1→∃two ε∈l len≥2
...   | u₁ , u₂ , u₁∈ , u₂∈ , u₁≢u₂ with lookup-All (mkAllEmptyU-sound ε∈l) u₁∈ | lookup-All (mkAllEmptyU-sound ε∈l) u₂∈
...   | flat-[] .u₁ eq₁ | flat-[] .u₂ eq₂ =
    let wt = proj₁ (r-∃u t) in
    ( CtxT ctx (PairU {l} {t} {loc} u₁ wt)
    , CtxT ctx (PairU {l} {t} {loc} u₂ wt)
    , CtxT-pres-flat ctx (cong₂ _++_ (trans eq₁ (sym eq₂)) refl)
    , λ trees≡ → u₁≢u₂ (proj₁ (inv-pairU {l} {t} {loc} u₁ wt u₂ wt (CtxT-injective ctx trees≡))) )

```

## 4. Criterion A3 and why A1 ∨ A2 is not enough

A3 of the paper fires when building the canonical representative of a derivative
applies the similarity rule `Idemp` (merging duplicated alternatives).  The
project's partial-derivative construction (e.g. `cgp.lne.PartialDerivative.pdU`)
does not merge alternatives, i.e. the `Idemp` rule and `canonic` have no
counterpart here; hence A3 cannot be stated for an arbitrary expression yet.

The following example (the simplest instance of the paper's A3 situation:
`deriv (x + x) x = (ε + φ) + (ε + φ)` requires `Idemp`) shows that A1 and A2
alone do *not* detect all ambiguity: the expression `a + a` is ambiguous
(witnessed by `LeftU` versus `RightU`) but it is not nullable (¬ A1) and it has no
concatenation subterm (¬ A2).

```agda
ambiguousSum : Ambig (($ 'a' ` 1) + ($ 'a' ` 2) ` 3)
ambiguousSum = ( LeftU (LetterU 'a') , RightU (LetterU 'a') , refl , λ() )

notA1Sum : ¬ AmbigA1 (($ 'a' ` 1) + ($ 'a' ` 2) ` 3)
notA1Sum (ε∈l+r , _) = ε∉r→¬ε∈r (ε∉ ε∉$ + ε∉$) ε∈l+r

inv-+-left : ∀ { l₁ r₁ l₂ r₂ : RE } { loc₁ loc₂ : ℕ }
  → RE._+_`_ l₁ r₁ loc₁ ≡ RE._+_`_ l₂ r₂ loc₂ → l₁ ≡ l₂
inv-+-left refl = refl

inv-+-right : ∀ { l₁ r₁ l₂ r₂ : RE } { loc₁ loc₂ : ℕ }
  → RE._+_`_ l₁ r₁ loc₁ ≡ RE._+_`_ l₂ r₂ loc₂ → r₁ ≡ r₂
inv-+-right refl = refl

plug-●-≢-letter : ∀ ( ctx : Ctx ) ( l t : RE ) ( loc loc₁ : ℕ )
  → plug ctx (l ● t ` loc) ≡ RE.$_`_ 'a' loc₁ → ⊥
plug-●-≢-letter 𝟘 l t loc loc₁ ()
plug-●-≢-letter (Ctx●R ctx s loc₁) l t loc loc₂ ()
plug-●-≢-letter (L●Ctx s ctx loc₁) l t loc loc₂ ()
plug-●-≢-letter (Ctx+R ctx s loc₁) l t loc loc₂ ()
plug-●-≢-letter (L+Ctx s ctx loc₁) l t loc loc₂ ()

notA2Sum-ctx : ∀ ( ctx : Ctx ) ( l t : RE ) ( loc : ℕ )
  → plug ctx (l ● t ` loc) ≡ RE._+_`_ (RE.$_`_ 'a' 1) (RE.$_`_ 'a' 2) 3 → ⊥
notA2Sum-ctx 𝟘 l t loc ()
notA2Sum-ctx (Ctx●R ctx s loc₁) l t loc ()
notA2Sum-ctx (L●Ctx s ctx loc₁) l t loc ()
notA2Sum-ctx (Ctx+R ctx s loc₁) l t loc eq = plug-●-≢-letter ctx l t loc 1 (inv-+-left eq)
notA2Sum-ctx (L+Ctx s ctx loc₁) l t loc eq = plug-●-≢-letter ctx l t loc 2 (inv-+-right eq)

notA2Sum : ¬ AmbigA2 (($ 'a' ` 1) + ($ 'a' ` 2) ` 3)
notA2Sum (ctx , l , t , loc , (eq , _)) = notA2Sum-ctx ctx l t loc eq

```

## 5. Computing examples

The example `(a*)2 + (a*)4` (cf. `AllEmptyParseTree.u`) witnesses A1, and
`((a*)4 + (a*)6)7 ● b8` is detected by A2 (the left component of its top level
concatenation has two empty parse trees); both conclusions produce actual
ambiguity witnesses.

```agda
a1-witness : AmbigA1 ((($ 'a' ` 1) * ε∉$ ` 2) + (($ 'a' ` 3) * ε∉$ ` 4) ` 5)
a1-witness = ( ε∈ ε∈* + ε∈* , ≤-reflexive refl )

a1-ambiguous : Ambig ((($ 'a' ` 1) * ε∉$ ` 2) + (($ 'a' ` 3) * ε∉$ ` 4) ` 5)
a1-ambiguous = A1→Ambig _ a1-witness

a2-target : RE
a2-target = ((($ 'a' ` 4) * ε∉$ ` 5) + (($ 'a' ` 6) * ε∉$ ` 7) ` 8) ● ( $ 'b' ` 9 ) ` 10

a2-witness : AmbigA2 a2-target
a2-witness = ( 𝟘 , (($ 'a' ` 4) * ε∉$ ` 5) + (($ 'a' ` 6) * ε∉$ ` 7) ` 8 , ( $ 'b' ` 9 ) , 10
             , ( refl , ( ε∈ ε∈* + ε∈* , ≤-reflexive refl ) ) )

a2-ambiguous : Ambig a2-target
a2-ambiguous = A2→Ambig _ a2-witness

```


# Canonical Representatives (Idemp) — the A3 mechanism

The sections below implement the *similarity* machinery of section 5 of

> Martin Sulzmann and Kenny Zhuo Ming Lu.
> Derivative-Based Diagnosis of Regular Expression Ambiguity. CIAA 2016.
> (`/home/luzm/assembla/regexp/trunk/ambig-check/finalCIAA2016.tex`)

needed for criterion **A3** of the Ambiguity Criteria proposition (paper section 6):

* **A3** `lang(canonic(deriv s x)) ≠ {}` and `deriv s x →fs canonic(deriv s x)`
  with rule **Idemp** applied.

## What is formalized here

1. Structural congruence `_≈₀_`: equality of expressions modulo the AST
   location annotations of this project (two occurrences of the same
   alternative in a source expression always carry *different* AST locations,
   so the paper's `Idemp  r + r ≈ r` must be implemented with a location
   insensitive equality).
2. `canonic : RE → RE × Bool` — the canonical representative of paper
   Definition `Canonical Representative`:
   (1) alternatives in right-associative normal form (`Assoc`),
   (2) duplicates removed (`Idemp`, keeping the first occurrence —
   "alternatives keep their relative position"),
   the second component records whether rule `Idemp` was applied.
   Following the paper's `Hole Expressions` there is no rewriting inside a
   Kleene star.
3. `Cast` — the parse tree transformation of paper Definition
   `Similarity with Parse Tree Transformation` for the congruence cases:
   `u ∈ 𝓣 r` is transported to `𝓣 s` for `r ≈₀ s`, preserving `| u |`.
4. The *statements* the A3 soundness needs: `pd-expr`, `pd-alts`, the
   `Idemp` transition test `pd-Idemp?`, the positioned duplicate witness
   (`dups-≈₀-dups`) and the member classification (§4.2) — and the
   `crit` disjunction of the criteria (§8).  The soundness closure
   itself — `dup-sum→Ambig` / `Ctx-dup→Ambig` (Soundness §1), the
   `a + a` example (Soundness §2), and the full `pdU`-clause chain
   Soundness §7–§11 ending in
   `pd-Idemp : pd-Idemp? (pdU[ q , c ]) ≡ true → Ambig q` — lives in
   `cgp.ambig.Soundness`; the converse direction lives in
   `cgp.ambig.Completeness`.  Together with `cgp.ambig.AmbigCheck`
   (`ambiguousSum`, `notA1Sum`, `notA2Sum`) the example shows the A3
   criterion genuinely adds detection power: `a + a` is missed by A1
   and A2 but caught there.
5. Section 10: the *general* form of the criteria — one master lift
   `lift-Ambig` (an injective path tree map with the soundness evidence of
   a `PDInstance*` transports `Ambig p → Ambig r`), from which the
   pd-state corollaries `pd*-A1→Ambig`, `pd*-A2→Ambig` factor
   (`AmbigCheck.A1→Ambig` etc.
   are the `w = []`, `inj = id` instances); the Ctx-dup versions
   `lift-Ctx-dup→Ambig` / `pd*-Ctx-dup→Ambig` travel with
   `Ctx-dup→Ambig` in `cgp.ambig.Soundness` §6.
6. Section 11: the paper's `Desc(r)` *as a single expression* via the
   `oplus` trick — `derivᵖ r w` re-glues the partial-derivative
   continuations of `pdUMany[ r , w ]` into one state expression, `_∈Desc_`
   states the paper's quantification over realizable states, and `A3?` is
   the paper's A3 test as a computable boolean (verified `true` on the
   §4.1 example).  This form exists only to state the paper's
   `canonic(deriv s x)` verbatim; for the tests §7's list form is used.
7. Section 12: the pd-native states — `pd*-Desc r w` is the Antimirov state
   itself (the list of partial-derivative continuations of `pdUMany[ r , w ]`,
   no re-gluing, no `Maybe`) and `A3-state? r w c` applies the A3 test to
   that list; §5's corollaries then apply to *any* member of the list.

## Why the full A3 condition is not stated

A3 quantifies over `deriv s x` for descendants `s ∈ Desc(r)` of the paper's
FST (section 4).  The current formalism cannot express that:

* the project's `RE` has **no empty-language constructor** (`data RE` in
  `cgp.RE` is `ε | $_`_ | _●_`_ | _+_`_ | _*_`_`), so the Brzozowski
  derivative is not a total operation on `RE` (e.g. `deriv ($ c ` loc) x`
  for `x ≠ c` would have to be `∅`);
* there is no FST / `Desc(r)` construction in the project (the partial
  derivative `pdU` works directly on parse trees, not on expressions);
* the non-emptiness side condition `lang(…) ≠ {}` holds of every project
  `RE` automatically (`ParseTree.r-∃u`).

Hence the top-level instance ("`Idemp` applies to `r` ⇒ `r` ambiguous") is
formalized, which is exactly the situation the paper's A3 detects, minus the
derivative construction.

**However** (section 4 below) the derivative can be *mimicked by partial
derivatives*: `pdU[ r , x ]` (in `cgp.posix.PartialDerivative`, the same
route as the old `cgp.posix.Related`, now `cgp.relatedwork.RelatedWorkOkuiSuzuki`)
yields the partial derivatives whose sum denotes `deriv r x`, and each comes
with its injection `U p → U r` (the paper's transition tree maps).
So A3's "Idemp applied when canonicalizing `deriv s x`" becomes: the
continuations produced by `pdU` (flattened over their `+` spines) contain
two `≈₀`-equal members, which is decidable, and the pair of injections
builds the two parse trees directly.


## 6. Similarity: structural equality modulo AST location (`≈₀`)

The paper's rules `Idemp`, `Comm`, `Assoc` compare expressions up to the
AC-theory of `+`.  For duplicate *detection* we use the location-insensitive
structural congruence: two alternatives are duplicates when they have the
same shape (the `Idemp` side condition `r + r`).

```agda
data _≈₀_ : RE → RE → Set where
  ≈₀-ε : ε ≈₀ ε
  ≈₀-$ : ∀ ( c : Char ) ( loc₁ loc₂ : ℕ )
    → ($ c ` loc₁) ≈₀ ($ c ` loc₂)
  ≈₀-● : ∀ { l₁ s₁ l₂ s₂ : RE } { loc₁ loc₂ : ℕ }
    → l₁ ≈₀ l₂ → s₁ ≈₀ s₂ → (l₁ ● s₁ ` loc₁) ≈₀ (l₂ ● s₂ ` loc₂)
  ≈₀-+ : ∀ { l₁ s₁ l₂ s₂ : RE } { loc₁ loc₂ : ℕ }
    → l₁ ≈₀ l₂ → s₁ ≈₀ s₂ → (l₁ + s₁ ` loc₁) ≈₀ (l₂ + s₂ ` loc₂)
  ≈₀-* : ∀ { r s : RE } { nεr : ε∉ r } { nεs : ε∉ s } { loc₁ loc₂ : ℕ }
    → r ≈₀ s → (r * nεr ` loc₁) ≈₀ (s * nεs ` loc₂)

≈₀-refl : ∀ ( r : RE ) → r ≈₀ r
≈₀-refl ε = ≈₀-ε
≈₀-refl ($ c ` loc) = ≈₀-$ c loc loc
≈₀-refl (l ● s ` loc) = ≈₀-● (≈₀-refl l) (≈₀-refl s)
≈₀-refl (l + s ` loc) = ≈₀-+ (≈₀-refl l) (≈₀-refl s)
≈₀-refl (r * nε ` loc) = ≈₀-* (≈₀-refl r)

-- (purpose): `_≈₀_` is symmetric
-- (used in): `pdU-+-location` below — the §9.2 split carries the pair
--   as `later ≈₀ earlier` (a positional convention), while
--   `pd-cross-positions→Ambig` reads `≈₀` left-to-right along the
--   two branches of the sum
-- (proof idea): induction on the derivation
≈₀-sym : ∀ { r s : RE } → s ≈₀ r → r ≈₀ s
≈₀-sym ≈₀-ε = ≈₀-ε
≈₀-sym (≈₀-$ c loc₁ loc₂) = ≈₀-$ c loc₂ loc₁
≈₀-sym (≈₀-● p q) = ≈₀-● (≈₀-sym p) (≈₀-sym q)
≈₀-sym (≈₀-+ p q) = ≈₀-+ (≈₀-sym p) (≈₀-sym q)
≈₀-sym (≈₀-* p) = ≈₀-* (≈₀-sym p)

_≟₀_ : ( r s : RE ) → Dec ( r ≈₀ s )
ε ≟₀ ε = yes ≈₀-ε
ε ≟₀ ($ d ` loc₂) = no λ()
ε ≟₀ (l₂ ● s₂ ` loc₂) = no λ()
ε ≟₀ (l₂ + s₂ ` loc₂) = no λ()
ε ≟₀ (r₂ * nε₂ ` loc₂) = no λ()
($ c ` loc₁) ≟₀ ε = no λ()
($ c ` loc₁) ≟₀ ($ d ` loc₂) with c Char.≟ d
...   | yes refl = yes (≈₀-$ c loc₁ loc₂)
...   | no c≢d = no λ{(≈₀-$ .c .loc₁ .loc₂) → c≢d refl}
($ c ` loc₁) ≟₀ (l₂ ● s₂ ` loc₂) = no λ()
($ c ` loc₁) ≟₀ (l₂ + s₂ ` loc₂) = no λ()
($ c ` loc₁) ≟₀ (r₂ * nε₂ ` loc₂) = no λ()
(l₁ ● s₁ ` loc₁) ≟₀ ε = no λ()
(l₁ ● s₁ ` loc₁) ≟₀ ($ d ` loc₂) = no λ()
(l₁ ● s₁ ` loc₁) ≟₀ (l₂ ● s₂ ` loc₂) with l₁ ≟₀ l₂ | s₁ ≟₀ s₂
...   | yes p | yes q = yes (≈₀-● p q)
...   | no ¬p | _ = no λ{(≈₀-● p q) → ¬p p}
...   | _ | no ¬q = no λ{(≈₀-● p q) → ¬q q}
(l₁ ● s₁ ` loc₁) ≟₀ (l₂ + s₂ ` loc₂) = no λ()
(l₁ ● s₁ ` loc₁) ≟₀ (r₂ * nε₂ ` loc₂) = no λ()
(l₁ + s₁ ` loc₁) ≟₀ ε = no λ()
(l₁ + s₁ ` loc₁) ≟₀ ($ d ` loc₂) = no λ()
(l₁ + s₁ ` loc₁) ≟₀ (l₂ ● s₂ ` loc₂) = no λ()
(l₁ + s₁ ` loc₁) ≟₀ (l₂ + s₂ ` loc₂) with l₁ ≟₀ l₂ | s₁ ≟₀ s₂
...   | yes p | yes q = yes (≈₀-+ p q)
...   | no ¬p | _ = no λ{(≈₀-+ p q) → ¬p p}
...   | _ | no ¬q = no λ{(≈₀-+ p q) → ¬q q}
(l₁ + s₁ ` loc₁) ≟₀ (r₂ * nε₂ ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟₀ ε = no λ()
(r₁ * nε₁ ` loc₁) ≟₀ ($ d ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟₀ (l₂ ● s₂ ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟₀ (l₂ + s₂ ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟₀ (r₂ * nε₂ ` loc₂) with r₁ ≟₀ r₂
...   | yes p = yes (≈₀-* p)
...   | no ¬p = no λ{(≈₀-* p) → ¬p p}

-- list membership via the location insensitive equality
any-≈₀ : ( r : RE ) → ( rs : List RE ) → Bool
any-≈₀ r rs = List.any ( λ s → ⌊ r ≟₀ s ⌋) rs

```

## 7. Parse tree transport along `≈₀` (paper's `Idemp` tree transformation)

For `r ≈₀ s` every parse tree of `r` is a parse tree of `s` (the congruence
rules of Definition `Similarity with Parse Tree Transformation` act as the
identity on the tree structure), and flattening is preserved.

```agda
Cast : ∀ { r s : RE } → r ≈₀ s → U r → U s
Cast ≈₀-ε EmptyU = EmptyU
Cast (≈₀-$ c loc₁ loc₂) (LetterU .c) = LetterU c
Cast (≈₀-● pq ps) (PairU u v) = PairU (Cast pq u) (Cast ps v)
Cast (≈₀-+ pq ps) (LeftU u) = LeftU (Cast pq u)
Cast (≈₀-+ pq ps) (RightU v) = RightU (Cast ps v)
Cast (≈₀-* p) (ListU us) = ListU (List.map ( λ u → Cast p u) us)

Cast-pres-flat : ∀ { r s : RE } ( p : r ≈₀ s ) ( u : U r )
  → proj₁ (flat (Cast p u)) ≡ proj₁ (flat u)
Cast-pres-flat ≈₀-ε EmptyU = refl
Cast-pres-flat (≈₀-$ c loc₁ loc₂) (LetterU .c) = refl
Cast-pres-flat (≈₀-● pq ps) (PairU u v) = cong₂ _++_ (Cast-pres-flat pq u) (Cast-pres-flat ps v)
Cast-pres-flat (≈₀-+ pq ps) (LeftU u) = Cast-pres-flat pq u
Cast-pres-flat (≈₀-+ pq ps) (RightU v) = Cast-pres-flat ps v
Cast-pres-flat (≈₀-* p) (ListU []) = refl
Cast-pres-flat (≈₀-* p) (ListU (u ∷ us)) = cong₂ _++_ (Cast-pres-flat p u) (Cast-pres-flat (≈₀-* p) (ListU us))

```

## 8. `canonic`: right associative normal form + duplicate removal

Paper Definition `Canonical Representative`:
(1) flatten all `+` to right-associative form (`Assoc`),
(2) remove duplicates (`Idemp`; the *first* occurrence is kept so that
"alternatives keep their relative position"),
(3) no rewriting inside a Kleene star (`Hole Expressions`).

The second component of the result records whether rule `Idemp` was applied
(the A3 side condition).

```agda
-- the + spine of an expression as a list of alternatives
sum-spine : RE → List RE
sum-spine (l + s ` loc) = sum-spine l ++ sum-spine s
sum-spine r = r ∷ []

-- the [] case never happens (a spine is never empty; the project has no ∅)
sum-build : List RE → ℕ → RE
sum-build [] loc = ε
sum-build (r ∷ []) loc = r
sum-build (r ∷ rs) loc = r + sum-build rs loc ` loc

-- remove later duplicates, keep the first occurrences in order
dedup : List RE → List RE × Bool
dedup xs = go [] xs
  where
    go : List RE → List RE → List RE × Bool
    go kept [] = kept , false
    go kept (r ∷ rs) with any-≈₀ r kept
    ...   | true = proj₁ (go kept rs) , true
    ...   | false = go (kept ++ (r ∷ [])) rs

canonic : RE → RE × Bool
canonic ε = ε , false
canonic ($ c ` loc) = ($ c ` loc) , false
canonic (l ● s ` loc) with canonic l | canonic s
...   | l₁ , fl | s₁ , fs = (l₁ ● s₁ ` loc) , fl ∨ fs
canonic (r * nε ` loc) = (r * nε ` loc) , false
canonic (l + s ` loc) with canonic l | canonic s
...   | l₁ , fl | s₁ , fs with dedup (sum-spine l₁ ++ sum-spine s₁)
...   | m , fd = sum-build m loc , fl ∨ fs ∨ fd

```

## 9. A3 by mimicking the derivative with partial derivatives

The paper's `deriv s x` is a single expression; this project computes
*partial* derivatives instead (`cgp.posix.PartialDerivative.pdU`).
A partial derivative instance `PDInstance r c` carries

* its continuation expression `p` (`pdinstance {p} inj ev`), and
* the injection `inj : U p → U r` with the soundness evidence
  `| inj u | = c ∷ | u |` — this is exactly the paper's transition
  parse-tree map (Definition `Injection`).

Since Brzozowski's derivative distributes over `+`, the union of the
continuations of `pdU[ r , x ]` (summed) denotes `deriv r x`; the
`posix` variant even *merges* two instances into one with a sum
continuation (`pdinstance-oplus`/`fuse`, needed for POSIX order).
Note `fuse` itself is the actualization of the *distributivity of the
derivative*, not of `Idemp` — it merges continuations without an
equality test.  `Idemp` fires exactly when the continuations combined
by `fuse` happen to be `≈₀`-equal, i.e. when the fused continuation
contains a duplicated alternative; detecting that is the job of
`pd-Idemp?` below.  So the A3 test becomes: *after flattening the `+`
spines of all continuations, do two `≈₀`-equal members exist?*  The
non-emptiness condition `lang(canonic(deriv s x)) ≠ {}` holds
automatically (`r-∃u`).

```agda
-- the continuation expression of one pd path
pd-expr : ∀ { r : RE } { c : Char } → PDInstance r c → RE
pd-expr (pdinstance {p} inj ev) = p

-- the transition map of one pd path, read off at a named continuation
pd-inj : ∀ { r p : RE } { c : Char } → ( pdi : PDInstance r c )
  → pd-expr pdi ≡ p → (U p → U r)
pd-inj (pdinstance {p} inj ev) refl = inj

pd*-expr : ∀ { r : RE } { pref : List Char } → PDInstance* r pref → RE
pd*-expr (pdinstance* {p} inj ev) = p

-- all alternatives of the (distributed) derivative deriv r x
pd-alts : ∀ { r : RE } { c : Char } → List (PDInstance r c) → List RE
pd-alts pdis = concatMap ( λ pdi → sum-spine (pd-expr pdi) ) pdis

-- does canonicalizing the sum of the continuations require the Idemp rule?
-- (`dups-≈₀-go` is the scan, hoisted out of a `where` clause so §9.2 can
-- reason about it; the equations are the ones `dups-≈₀` had)
dups-≈₀-go : List RE → List RE → Bool
dups-≈₀-go kept [] = false
dups-≈₀-go kept (r ∷ rs) with any-≈₀ r kept
...   | true = true
...   | false = dups-≈₀-go (kept ++ (r ∷ [])) rs

dups-≈₀ : List RE → Bool
dups-≈₀ xs = dups-≈₀-go [] xs

pd-Idemp? : ∀ { r : RE } { c : Char } → List (PDInstance r c) → Bool
pd-Idemp? pdis = dups-≈₀ (pd-alts pdis)

```

### 9.1. Example: the duplicate is *created by the derivative*

`((a + b) ● c) + (a ● c)` has no duplicate alternatives itself —
`canonic` reports `Idemp` was **not** applied (the first component below);
its structure is also not caught by A1/A2 (neither nullable nor a
concatenation with a duplicated empty component).  But its derivative on
`'a` has two equal continuations `ε ● c` (from the `a` inside `a + b` and
from the second `a`), so `pd-Idemp?` fires and `pd-pairs→Ambig` proves the
expression ambiguous.  This is precisely the situation the paper reserves
for **A3**.

```agda
pd-a3-target : RE
pd-a3-target = ( (($ 'a' ` 1) + ($ 'b' ` 2) ` 3) ● ($ 'c' ` 4) ` 5 )
               + ( ($ 'a' ` 6) ● ($ 'c' ` 7) ` 8 ) ` 9

-- the top-level Idemp test does NOT fire (unlike Soundness §2):
pd-a3-canonic-flag : proj₂ (canonic pd-a3-target) ≡ false
pd-a3-canonic-flag = refl

-- but computing the partial derivatives on 'a and flattening the
-- continuations ε ● ($ 'c' ` 4) ` 5  and  ε ● ($ 'c' ` 7) ` 8
-- finds the duplicate: the continuations of the partial derivatives of
-- pd-a3-target on 'a' are exactly the two equal terms ε ● ($ 'c' ` 4) ` 5
-- and ε ● ($ 'c' ` 7) ` 8 (the posix pd fuses them into one instance,
-- their + spine is recovered by sum-spine):
pd-a3-continuations : pd-alts (PosixPD.pdU[ pd-a3-target , 'a' ]) ≡ ((ε ● ($ 'c' ` 4) ` 5) ∷ (ε ● ($ 'c' ` 7) ` 8) ∷ [])
pd-a3-continuations = refl

pd-a3-Idemp-applied : pd-Idemp? (PosixPD.pdU[ pd-a3-target , 'a' ]) ≡ true
pd-a3-Idemp-applied = refl

-- the two pd instances (before the posix fusion), at the continuation

```

### 9.2. The test finds the duplicate when there is one

`pd-Idemp?` is defined as a scan, so none of the above says the scan *finds* a
duplicate that is there.  The instance `cgp.ambig.Completeness` §7's `pick-diff-record-prf` needs is the one
where `pdU[ r , c ]` holds two **distinct members** continuing at **one**
expression: flattening then puts the same alternative in the list twice, and the
scan has to answer `true`.  The two structural facts that make that go —
scanning more list never loses a `true`, and a value already in the scan's window
that occurs again in the rest fires it — are worth having in general.

The generic lemmas in this section were checked against the standard library
(2.1): `∈-++-inv` is its `∈-++⁻` with explicit arguments and `Dec→true` is its
`dec-true` spelled with `⌊_⌋` — both kept as thin wrappers, with `∨-true` and
`∈-concatMap⁻`, in `cgp.Utils` (see the note there).  They are imported from
there; `++-idʳ` is not kept at all: `Data.List.Properties.++-identityʳ` is used

```agda
≈₀-refl-≡ : ∀ { r s : RE } → r ≡ s → r ≈₀ s
≈₀-refl-≡ {r} refl = ≈₀-refl r


any-≈₀-witness : ( r : RE ) ( rs : List RE )
  → Any ( λ s → r ≈₀ s ) rs
  → any-≈₀ r rs ≡ true
any-≈₀-witness r (x ∷ rs) (here ≈₀xs) =
  trans (cong ( λ b → b ∨ any-≈₀ r rs ) (Dec→true (r ≟₀ x) ≈₀xs)) refl
any-≈₀-witness r (x ∷ rs) (there w) =
  trans (cong ( λ b → ⌊ r ≟₀ x ⌋ ∨ b ) (any-≈₀-witness r rs w))
        (∨-true ⌊ r ≟₀ x ⌋)

-- scanning `a` and then `b` from a window, or scanning `b` from the window
-- `kept ++ a`: the scan of the split version is what the joint scan reaches
-- anyway, so a `true` found there is found by the joint scan
dups-≈₀-go-++ : ( kept a b : List RE )
  → dups-≈₀-go (kept ++ a) b ≡ true
  → dups-≈₀-go kept (a ++ b) ≡ true
dups-≈₀-go-++ kept [] b h =
  subst ( λ q → dups-≈₀-go q b ≡ true ) (++-identityʳ kept) h
dups-≈₀-go-++ kept (x ∷ a) b h with any-≈₀ x kept
...   | true = refl
...   | false = dups-≈₀-go-++ (kept ++ (x ∷ [])) a b h



-- the test fires as soon as the head of the rest is `≈₀`-equal to the window
dups-≈₀-go-head : ( kept : List RE ) ( r : RE ) ( rs : List RE )
  → any-≈₀ r kept ≡ true
  → dups-≈₀-go kept (r ∷ rs) ≡ true
dups-≈₀-go-head kept r rs eq with any-≈₀ r kept | eq
...   | true  | refl = refl
...   | false | ()

-- membership of `h` in a list, transported along `y ≡ h`, gives an
-- `≈₀`-witness for `y`
∈-≈₀ : ( kept : List RE ) { y h : RE }
  → y ≡ h
  → h ∈ kept
  → Any ( λ s → y ≈₀ s ) kept
∈-≈₀ [] q ()
∈-≈₀ (z ∷ kept) q (here p) = here (≈₀-refl-≡ (trans q p))
∈-≈₀ (z ∷ kept) q (there w) = there (∈-≈₀ kept q w)

-- the window holds `h` and the rest contains `h` again: the test fires
dups-≈₀-go-repeat : ( kept ys : List RE ) ( h : RE )
  → h ∈ kept
  → h ∈ ys
  → dups-≈₀-go kept ys ≡ true
dups-≈₀-go-repeat kept [] h h∈ ()
dups-≈₀-go-repeat kept (y ∷ ys) h h∈ (here q) =
  dups-≈₀-go-head kept y ys
    (any-≈₀-witness y kept (∈-≈₀ kept (sym q) h∈))
dups-≈₀-go-repeat kept (y ∷ ys) h h∈ (there w) =
  dups-≈₀-go-++ kept (y ∷ []) ys
    (dups-≈₀-go-repeat (kept ++ (y ∷ [])) ys h (∈-++ˡ kept (y ∷ []) h h∈) w)


dups-≈₀-∷-repeat : ( kept : List RE ) ( h : RE ) ( t ys : List RE )
  → h ∈ ys
  → dups-≈₀-go kept (h ∷ (t ++ ys)) ≡ true
dups-≈₀-∷-repeat kept h t ys h∈ =
  dups-≈₀-go-++ kept (h ∷ []) (t ++ ys)
    (dups-≈₀-go-repeat (kept ++ (h ∷ [])) (t ++ ys) h
       (∈-∷-++ʳ kept h) (∈-++ʳ t ys h h∈))

-- a `+`-spine is never empty
sum-spine∷ : ( p : RE ) → Σ[ h ∈ RE ] Σ[ t ∈ List RE ] ( sum-spine p ≡ h ∷ t )
sum-spine∷ (l + s ` loc) with sum-spine∷ l | sum-spine∷ s
...   | ( h , t , eq₁ ) | ( h₂ , t₂ , eq₂ ) =
    ( h , t ++ ( h₂ ∷ t₂ )
    , trans (cong ( λ x → x ++ sum-spine s ) eq₁)
            (cong ( λ y → ( h ∷ t ) ++ y ) eq₂) )
sum-spine∷ ε = ( ε , [] , refl )
sum-spine∷ ( $ c ` loc ) = ( $ c ` loc , [] , refl )
sum-spine∷ ( l ● s ` loc ) = ( l ● s ` loc , [] , refl )
sum-spine∷ ( l * n ` loc ) = ( l * n ` loc , [] , refl )

-- an alternative of a member is an alternative of the state
pd-alts∈ : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) )
  ( z : PDInstance r c ) ( h : RE )
  → z ∈ pdis
  → h ∈ sum-spine (pd-expr z)
  → h ∈ pd-alts pdis
pd-alts∈ [] z h ()
pd-alts∈ (x ∷ pdis) z h (here p) h∈ with p | sum-spine∷ (pd-expr x)
...   | refl | ( h₀ , t , sp ) =
      let eq₂ = trans (cong ( λ q → q ++ pd-alts pdis ) (sym sp)) refl
      in  subst ( λ L → h ∈ L ) eq₂
            (∈-++ˡ (h₀ ∷ t) (pd-alts pdis) h (subst ( λ K → h ∈ K ) sp h∈))
pd-alts∈ (x ∷ pdis) z h (there z∈) h∈ with sum-spine∷ (pd-expr x)
...   | ( h₀ , t , sp ) =
      subst ( λ L → h ∈ L )
            (cong ( λ q → q ++ pd-alts pdis ) (sym sp))
            (∈-++ʳ (h₀ ∷ t) (pd-alts pdis) h (pd-alts∈ pdis z h z∈ h∈))

dups-≈₀-alts-head : ∀ { r : RE } { c : Char }
  ( kept : List RE ) ( x z′ : PDInstance r c ) ( pdis : List (PDInstance r c) )
  → pd-expr x ≡ pd-expr z′
  → z′ ∈ pdis
  → dups-≈₀-go kept (sum-spine (pd-expr x) ++ pd-alts pdis) ≡ true
dups-≈₀-alts-head {r} {c} kept x z′ pdis eq z′∈ with sum-spine∷ (pd-expr z′)
...   | ( h , t , sp ) =
      subst ( λ q → dups-≈₀-go kept (q ++ pd-alts pdis) ≡ true )
            (sym (trans (cong sum-spine eq) sp))
            (dups-≈₀-∷-repeat kept h t (pd-alts pdis)
               (pd-alts∈ pdis z′ h z′∈
                  (subst ( λ K → h ∈ K ) (sym sp) (here refl))))

pd-Idemp?-members-go : ∀ { r : RE } { c : Char } ( kept : List RE )
  ( pdis : List (PDInstance r c) ) ( z z′ : PDInstance r c )
  → z ∈ pdis
  → z′ ∈ pdis
  → ¬ ( z ≡ z′ )
  → pd-expr z ≡ pd-expr z′
  → dups-≈₀-go kept (pd-alts pdis) ≡ true
pd-Idemp?-members-go kept [] z z′ ()
pd-Idemp?-members-go kept (x ∷ pdis) z z′ (here p) (here q) z≢z′ eq with p | q
...   | refl | refl = ⊥-elim (z≢z′ refl)
pd-Idemp?-members-go kept (x ∷ pdis) z z′ (here p) (there z′∈) z≢z′ eq =
  dups-≈₀-alts-head kept x z′ pdis (trans (cong pd-expr (sym p)) eq) z′∈
pd-Idemp?-members-go kept (x ∷ pdis) z z′ (there z∈) (here q) z≢z′ eq =
  dups-≈₀-alts-head kept x z pdis (trans (sym (cong pd-expr q)) (sym eq)) z∈
pd-Idemp?-members-go kept (x ∷ pdis) z z′ (there z∈) (there z′∈) z≢z′ eq =
  dups-≈₀-go-++ kept (sum-spine (pd-expr x)) (pd-alts pdis)
    (pd-Idemp?-members-go (kept ++ sum-spine (pd-expr x)) pdis z z′ z∈ z′∈ z≢z′ eq)

-- the test of §9 fires on a member list that holds two distinct records with
-- one continuation
pd-Idemp?-members : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) )
  ( z z′ : PDInstance r c )
  → z ∈ pdis
  → z′ ∈ pdis
  → ¬ ( z ≡ z′ )
  → pd-expr z ≡ pd-expr z′
  → pd-Idemp? pdis ≡ true
pd-Idemp?-members pdis z z′ z∈ z′∈ z≢z′ eq =
  pd-Idemp?-members-go [] pdis z z′ z∈ z′∈ z≢z′ eq

-- (purpose): the reflection of the decision procedure — a `true` of the
--   boolean test `any-≈₀` always comes from the proposition `Any (≈₀)`
-- (used in): `dups-≈₀-go-wp` below (the head-match branch)
-- (proof idea): case-split the decision `r ≟₀ y` against the hypothesis;
--   `true` can only come from a `yes` cell, whose position is the witness
any-≈₀-true : ( r : RE ) ( ys : List RE )
  → any-≈₀ r ys ≡ true
  → Any ( λ s → r ≈₀ s ) ys
any-≈₀-true r [] ()
any-≈₀-true r (y ∷ ys) eq with r ≟₀ y | eq
...   | yes r≈₀y | _ = here r≈₀y
...   | no ¬r≈₀y | h = there (any-≈₀-true r ys h)

-- (purpose): the scan step inverts — a `true` of `dups-≈₀-go` came
--   either from the head matching the window or from the tail
-- (used in): `dups-≈₀-go-wp` below (the positioned reflection)
-- (proof idea): case-split on the window decision.  Returning the
--   disjunction, rather than splitting the goal on it, avoids the
--   with-abstraction blocking on the non-datatype goal
dups-≈₀-go-inv-step : ( kept xs : List RE ) ( x : RE )
  → dups-≈₀-go kept (x ∷ xs) ≡ true
  → Sum._⊎_ (any-≈₀ x kept ≡ true)
            (dups-≈₀-go (kept ++ (x ∷ [])) xs ≡ true)
dups-≈₀-go-inv-step kept xs x eq with any-≈₀ x kept | eq
...   | true  | h = Sum.inj₁ refl
...   | false | h = Sum.inj₂ h


-- (purpose): the inverse of `pd-alts∈` — an alternative of the state
--   belongs to a member: it names a record `z` of the list with the
--   alternative inside `z`'s `sum-spine`
-- (used in): `pd-alts-Dups-w-classify` below (the member-level placement
--   of the positioned pair)
-- (proof idea): induction on the record list, splitting each membership
--   in the concatenation with `∈-++-inv`
pd-alts∈-inv : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) )
  ( h : RE )
  → h ∈ pd-alts pdis
  → Σ[ z ∈ PDInstance r c ] ( z ∈ pdis × h ∈ sum-spine (pd-expr z) )
pd-alts∈-inv [] h ()
pd-alts∈-inv (x ∷ pdis) h h∈
  with ∈-++-inv (sum-spine (pd-expr x)) (pd-alts pdis) h∈
...   | Sum.inj₁ h∈₁ = ( x , here refl , h∈₁ )
...   | Sum.inj₂ h∈₂ with pd-alts∈-inv pdis h h∈₂
...   | ( z , z∈ , h∈₃ ) = ( z , there z∈ , h∈₃ )

-- a *positioned* duplicate pair inside a list: two occurrences, the
-- earlier one in a window between `pre` and `post`, the later one after
-- it.  This keeps the occurrence identity the scan is built on — two
-- distinct positions, one value pair — where a bare Σ of values would not.
-- (form: an inductive with the positions as constructor arguments.  A
--   Σ-alias `Dups-w xs = Σ[...]` does *not* unfold when `xs` is neutral,
--   and pair construction against the stuck alias fails; the datatype is
--   rigid and elaborates directly)
data Dups-w : List RE → Set where
  dups-at : ∀ { xs : List RE }
              { pre mid post : List RE } { earlier later : RE }
    → pre ++ (earlier ∷ (mid ++ (later ∷ post))) ≡ xs
    → later ≈₀ earlier
    → Dups-w xs

-- the positioned pair is transportable along list equations
Dups-w-transp : ( xs ys : List RE ) → xs ≡ ys → Dups-w xs → Dups-w ys
Dups-w-transp xs .xs refl w = w

-- cast a scan hypothesis along a window equation (the boolean test does
-- not see how the window list is written)
dups-≈₀-go-cast : ( kept₁ kept₂ : List RE ) ( xs : List RE )
  → kept₁ ≡ kept₂ → dups-≈₀-go kept₁ xs ≡ true → dups-≈₀-go kept₂ xs ≡ true
dups-≈₀-go-cast .k₂ k₂ xs refl h = h

-- a window match located: an `Any` witness names the matched element and
-- the window split around it.
-- (purpose): the head branch of `dups-≈₀-go-wp`
-- (used in): `dups-≈₀-go-wp` below, via `any-≈₀-true`
-- (proof idea): recursion on the witness; the split is returned as
--   *equation data* (matching a Σ inside a with would block it)
any-≈₀-wloc : ( y : RE ) ( kept′ : List RE )
  → Any ( λ r → y ≈₀ r ) kept′
  → Σ[ r ∈ RE ] Σ[ pre ∈ List RE ] Σ[ post ∈ List RE ]
      ( kept′ ≡ pre ++ (r ∷ post) × y ≈₀ r )
any-≈₀-wloc y [] ()
any-≈₀-wloc y (z ∷ kept′) (here y≈₀z) = ( z , [] , kept′ , refl , y≈₀z )
any-≈₀-wloc y (z ∷ kept′) (there p) with any-≈₀-wloc y kept′ p
...   | ( r , pre , post , eq , y≈₀r ) =
          ( r , z ∷ pre , post , cong (_∷_ z) eq , y≈₀r )

-- The pair positions in one scanned step.  The window equation
-- `x ∷ kept ≡ pre ++ (r ∷ post)` from `any-≈₀-wloc` splits the *whole*
-- window around the matched element `r`; then in the scanned list
-- `(x ∷ kept) ++ (y ∷ xs)` the earlier occurrence `r` has prefix `pre`,
-- middle `post` (the window tail), and after the later occurrence `y`
-- the remainder `xs`.  The one reassociation needed
-- (`(pre ++ r ∷ post) ++ y ∷ xs ≡ pre ++ r ∷ (post ++ y ∷ xs)`) has
-- rigid endpoints on both sides — the direct layouts with a cons in the
-- transport context are NOT definitionally checkable, which is what the
-- first attempts kept tripping on.
dups-wp-head : ( x : RE ) ( kept xs : List RE ) ( y : RE )
  → ( w : Σ[ r ∈ RE ] Σ[ pre ∈ List RE ] Σ[ post ∈ List RE ]
          ( (x ∷ kept) ≡ pre ++ (r ∷ post) × y ≈₀ r ) )
  → Dups-w ((x ∷ kept) ++ (y ∷ xs))
dups-wp-head x kept xs y w =
    subst Dups-w (sym (cong ( λ K → K ++ (y ∷ xs) ) eqw))
      (dups-at {xs = (pre ++ (r ∷ post)) ++ (y ∷ xs)}
         {pre = pre} {mid = post} {post = xs} {earlier = r} {later = y}
         (sym (++-assoc pre (r ∷ post) (y ∷ xs))) y≈₀r)
  where
    r      = proj₁ w
    pre    = proj₁ (proj₂ w)
    post   = proj₁ (proj₂ (proj₂ w))
    eqw    = proj₁ (proj₂ (proj₂ (proj₂ w)))
    y≈₀r   = proj₂ (proj₂ (proj₂ (proj₂ w)))

dups-≈₀-go-wp : ( x : RE ) ( kept xs : List RE )
  → dups-≈₀-go (x ∷ kept) xs ≡ true
  → Dups-w ((x ∷ kept) ++ xs)
dups-≈₀-go-wp x kept [] ()
dups-≈₀-go-wp x kept (y ∷ xs) h
  with dups-≈₀-go-inv-step (x ∷ kept) xs y h
...   | Sum.inj₁ h₁ =
          dups-wp-head x kept xs y
            (any-≈₀-wloc y (x ∷ kept) (any-≈₀-true y (x ∷ kept) h₁))
...   | Sum.inj₂ h₂ =
      -- the scan appends the head to the window: `(x ∷ kept) ++ [y]`
      -- *is* `x ∷ (kept ++ [y])` definitionally, so the recursion keeps
      -- the one-cons window form; the remainder layouts differ by
      -- `++-assoc` only
      Dups-w-transp (x ∷ ((kept ++ (y ∷ [])) ++ xs)) ((x ∷ kept) ++ (y ∷ xs))
        (trans (cong ( λ K → x ∷ K ) (++-assoc kept (y ∷ []) xs)) refl)
        (dups-≈₀-go-wp x (kept ++ (y ∷ [])) xs
           (dups-≈₀-go-cast ((x ∷ kept) ++ (y ∷ [])) (x ∷ (kept ++ (y ∷ [])))
              xs refl h₂))

-- (purpose): the scan's output read back as positioned occurrences — a
--   fired `dups-≈₀` names the two positions of the duplicate pair
-- (used in): the §11.1 `pd-Idemp` hypothesis unpacking; the member-level
--   classification of the pair relative to `pd-alts` (design note below)
--   is the step that consumes it
-- (proof idea): through the general-window form `dups-≈₀-go-wp`: the
--   whole list is the one-element window `[x]` followed by the rest
dups-≈₀-dups : ( xs : List RE )
  → dups-≈₀ xs ≡ true
  → Dups-w xs
dups-≈₀-dups [] ()
dups-≈₀-dups (x ∷ xs) eq = dups-≈₀-go-wp x [] xs eq

-- the reflection instantiates on a concrete fired scan (the scan on a
-- two-element list of `≈₀`-equal letters answers `true` by `refl`)
dups-w-test : Dups-w (($ 'a' ` 1) ∷ ($ 'a' ` 2) ∷ [])
dups-w-test = dups-≈₀-dups _ refl

-- two splices of one equation: the longer prefix extends the shorter,
-- the overlap is the shared middle.  (used by the cut-split below;
-- proof idea: induction peeling both prefixes, the overlap equation
-- carried through cons contexts in cong-normal form)
compare-++ : ( as bs cs ds : List RE )
  → as ++ bs ≡ cs ++ ds
  → Sum._⊎_ (Σ[ u ∈ List RE ] ( (cs ≡ as ++ u) × (bs ≡ u ++ ds) ))
            (Σ[ u ∈ List RE ] ( (as ≡ cs ++ u) × (ds ≡ u ++ bs) ))
compare-++ []       bs []       ds eq = Sum.inj₁ ( [] , refl , eq )
compare-++ []       bs (c ∷ cs) ds eq = Sum.inj₁ ( c ∷ cs , refl , eq )
compare-++ (a ∷ as) bs []       ds eq = Sum.inj₂ ( a ∷ as , refl , sym eq )
compare-++ (a ∷ as) bs (c ∷ cs) ds eq
  with compare-++ as bs cs ds (∷-injectiveʳ eq)
...   | Sum.inj₁ ( u , cs≡ , bs≡ ) =
          Sum.inj₁ ( u , ( trans (cong ( _∷_ c ) cs≡)
                               (cong ( λ z → z ∷ (as ++ u) )
                                     (sym (∷-injectiveˡ eq)))
                       , bs≡ ) )
...   | Sum.inj₂ ( u , as≡ , ds≡ ) =
          Sum.inj₂ ( u , ( trans (cong ( _∷_ a ) as≡)
                               (cong ( λ z → z ∷ (cs ++ u) )
                                     (∷-injectiveˡ eq))
                       , ds≡ ) )

-- the pair straddles the cut: earlier occurrence in the left part at
-- position `pre`, later occurrence in the right part at position `mid₂`
Dups-w-cross : ( xs ys : List RE ) → Set
Dups-w-cross xs ys =
    Σ[ pre ∈ List RE ] Σ[ mid₁ ∈ List RE ] Σ[ mid₂ ∈ List RE ]
    Σ[ post ∈ List RE ] Σ[ earlier ∈ RE ] Σ[ later ∈ RE ]
      ( (xs ≡ pre ++ (earlier ∷ mid₁))
      × (ys ≡ mid₂ ++ (later ∷ post))
      × (later ≈₀ earlier) )

-- (purpose): a positioned duplicate pair in a concatenation either has
--   both occurrences on one side of the cut or one on each side — the
--   case split that localises a fired test's pair relative to a list
--   structure
-- (used in): the member-level classification of the pair of a fired
--   `pd-Idemp?` against the `pd-alts` cuts (§11.1)
-- (proof idea): compare the layout prefix `pre` against the left part
--   `xs` with `compare-++`; in the overlap branch a second comparison
--   of `mid` against the overlap decides which side holds the later
--   occurrence.  (Clauses are ordered so each nested `with` comes last:
--   an outer with-function gets no clauses after an inner one is opened)
Dups-w-++-split : ( xs ys : List RE )
  → Dups-w (xs ++ ys)
  → Sum._⊎_ (Dups-w xs) (Sum._⊎_ (Dups-w-cross xs ys) (Dups-w ys))
Dups-w-++-split xs ys (dups-at {xs = .(xs ++ ys)} {pre = pre} {mid = mid}
                     {post = post} {earlier = e} {later = l} eq l≈₀e)
  with compare-++ pre (e ∷ (mid ++ (l ∷ post))) xs ys eq
...   | Sum.inj₂ ( u , pre≡ , ys≡ ) = Sum.inj₂ (Sum.inj₂ (dups-at {xs = ys}
          {pre = u} {mid = mid} {post = post}
          {earlier = e} {later = l} (sym ys≡) l≈₀e))
...   | Sum.inj₁ ( u , xs≡ , eq2 ) with u
...       | [] = Sum.inj₂ (Sum.inj₂ (dups-at {xs = [] ++ ys} {pre = []}
            {mid = mid} {post = post} {earlier = e} {later = l} eq2 l≈₀e))
...       | ( z ∷ us) with compare-++ mid (l ∷ post) us ys (∷-injectiveʳ eq2)
...           | Sum.inj₂ ( v , mid≡ , ys≡ ) = Sum.inj₂ (Sum.inj₁
                     ( pre , us , v , post , e , l
                     , ( trans xs≡
                           (sym (cong ( λ K → pre ++ (K ∷ us) )
                                      (∷-injectiveˡ eq2)))
                     , ys≡ , l≈₀e ) ))
...           | Sum.inj₁ ( v , us≡ , eq3 ) with v
...               | [] = Sum.inj₂ (Sum.inj₁
                       ( pre , us , [] , post , e , l
                       , ( trans xs≡
                             (sym (cong ( λ K → pre ++ (K ∷ us) )
                                        (∷-injectiveˡ eq2)))
                       , sym eq3 , l≈₀e ) ))
...               | ( w ∷ vs) = Sum.inj₁ (dups-at {xs = xs}
                    {pre = pre} {mid = mid} {post = vs}
                    {earlier = e} {later = l} eqGoal l≈₀e)
                 where
                   eqGoal : pre ++ (e ∷ (mid ++ (l ∷ vs))) ≡ xs
                   eqGoal =
                     trans (cong ( λ K → pre ++ (e ∷ K) )
                           (trans (cong ( λ z → mid ++ (z ∷ vs) )
                                        (∷-injectiveˡ eq3))
                                  (sym us≡)))
                           (trans (cong ( λ K → pre ++ (K ∷ us) )
                                        (∷-injectiveˡ eq2))
                                  (sym xs≡))

-- the split instantiates on the output of a concrete fired scan with a
-- cut between the two occurrences
dups-w-split-test : Sum._⊎_ (Dups-w (($ 'a' ` 1) ∷ []))
    (Sum._⊎_ (Dups-w-cross (($ 'a' ` 1) ∷ []) (($ 'a' ` 2) ∷ []))
             (Dups-w (($ 'a' ` 2) ∷ [])))
dups-w-split-test = Dups-w-++-split _ _ (dups-≈₀-dups _ refl)

-- (purpose): an inhabitant of a list forces its length to be at least 1
-- (used in): the crossing branch of `pd-alts-Dups-w-classify` below
-- (proof idea): induction on the membership witness; `here` reads the
--   cons cell, `there` weakens the bound along `_≤_`
x∈xs→1≤length : ∀ { a : Set } { xs : List a } { x : a }
  → x ∈ xs → suc zero ≤ length xs
x∈xs→1≤length (here refl) = s≤s z≤n
x∈xs→1≤length (there xs∈) = m≤n⇒m≤1+n (x∈xs→1≤length xs∈)

-- (purpose): the empty list carries no positioned duplicate pair
-- (used in): the nil case of `pd-alts-Dups-w-classify` below
-- (proof idea): the `dups-at` layout always has two cons cells, so its
--   layout equation against `[]` is impossible for either shape of `pre`
Dups-w-[] : Dups-w [] → ⊥
Dups-w-[] (dups-at {xs = []} {pre = []} () l≈₀e)
Dups-w-[] (dups-at {xs = []} {pre = z ∷ zs} () l≈₀e)

-- (purpose): the member-level classification — a positioned duplicate
--   pair of the flattened alternative list `pd-alts pdis` either sits at
--   two positions of *one* member's `sum-spine`, or has its earlier
--   occurrence in one member's spine and its later occurrence in
--   another member's spine
-- (used in): the §11.1 statement of `pd-Idemp` — the classification step of
--   its hypothesis unpacking; the left branch is the material of
--   configurations (a)/(b), the right branch of configuration (c)
-- (proof idea): induction on the member list, cutting
--   `pd-alts (z ∷ zs) ≡ sum-spine (pd-expr z) ++ pd-alts zs` with
--   `Dups-w-++-split`: the both-left branch is the goal's left branch
--   at the head member, the crossing branch names the second member
--   through `pd-alts∈-inv`, the both-right branch recurses.  The
--   crossing branch uses a `let`, not a nested `with`: a clause opening
--   a `with` must come last among its siblings, and the recursive
--   branch needs one
pd-alts-Dups-w-classify : ∀ { r : RE } { c : Char }
  ( pdis : List (PDInstance r c) )
  → Dups-w (pd-alts pdis)
  → Sum._⊎_
      (Σ[ z ∈ PDInstance r c ]
        ( (z ∈ pdis) × Dups-w (sum-spine (pd-expr z)) ))
      (Σ[ z ∈ PDInstance r c ] Σ[ z′ ∈ PDInstance r c ]
        Σ[ earlier ∈ RE ] Σ[ later ∈ RE ]
          ( (z ∈ pdis) × (z′ ∈ pdis)
          × (earlier ∈ sum-spine (pd-expr z))
          × (later ∈ sum-spine (pd-expr z′))
          × (later ≈₀ earlier)
          × ( suc (suc zero) ≤ length pdis ) ))
pd-alts-Dups-w-classify [] dw = ⊥-elim (Dups-w-[] dw)
pd-alts-Dups-w-classify (z ∷ zs) dw
  with Dups-w-++-split (sum-spine (pd-expr z)) (pd-alts zs) dw
...   | Sum.inj₁ d = Sum.inj₁ ( z , ( here refl , d ) )
...   | Sum.inj₂ (Sum.inj₁ ( pre , mid₁ , mid₂ , post , earlier , later
                           , ( xs≡ , ys≡ , later≈₀earlier ) )) =
      let ( z′ , z′∈ , later∈′ ) =
            pd-alts∈-inv zs later
              ( subst ( λ L → later ∈ L ) (sym ys≡)
                  ( ∈-++ʳ mid₂ (later ∷ post) later (here refl) ) )
      in  Sum.inj₂ ( z , z′ , earlier , later
                   , ( here refl , there z′∈
                     , ( subst ( λ L → earlier ∈ L ) (sym xs≡)
                           ( ∈-++ʳ pre (earlier ∷ mid₁) earlier
                               (here refl) )
                     , later∈′ , later≈₀earlier
                     , s≤s (x∈xs→1≤length z′∈) ) ) )
...   | Sum.inj₂ (Sum.inj₂ d) with pd-alts-Dups-w-classify zs d
...       | Sum.inj₁ ( z′ , z′∈ , d′ ) = Sum.inj₁ ( z′ , ( there z′∈ , d′ ) )
...       | Sum.inj₂ ( z′ , z″ , earlier , later
                     , ( z′∈ , z″∈ , earlier∈ , later∈ , later≈₀earlier
                       , 2≤len ) ) =
            Sum.inj₂ ( z′ , z″ , earlier , later
                     , ( there z′∈ , there z″∈ , earlier∈ , later∈
                       , later≈₀earlier , m≤n⇒m≤1+n 2≤len ) )

-- The classification instantiated at the §9.1 example: the fired test
-- read position-preservingly (`dups-≈₀-dups`), then classified against
-- the `pdU` member list
pd-alts-classify-a3 : Sum._⊎_
  (Σ[ z ∈ PDInstance pd-a3-target 'a' ]
    ( (z ∈ PosixPD.pdU[ pd-a3-target , 'a' ])
    × Dups-w (sum-spine (pd-expr z)) ))
  (Σ[ z ∈ PDInstance pd-a3-target 'a' ]
    Σ[ z′ ∈ PDInstance pd-a3-target 'a' ]
    Σ[ earlier ∈ RE ] Σ[ later ∈ RE ]
      ( (z ∈ PosixPD.pdU[ pd-a3-target , 'a' ])
      × (z′ ∈ PosixPD.pdU[ pd-a3-target , 'a' ])
      × (earlier ∈ sum-spine (pd-expr z))
      × (later ∈ sum-spine (pd-expr z′))
      × (later ≈₀ earlier)
      × ( suc (suc zero)
        ≤ length (PosixPD.pdU[ pd-a3-target , 'a' ]) ) ))
pd-alts-classify-a3 =
  pd-alts-Dups-w-classify (PosixPD.pdU[ pd-a3-target , 'a' ])
    (dups-≈₀-dups (pd-alts (PosixPD.pdU[ pd-a3-target , 'a' ]))
       pd-a3-Idemp-applied)

-- What remains after the classification is the analysis *inside* the
-- members: for the left branch, what a positioned pair inside one
-- `sum-spine` says about the expression (configurations (a)/(b) of
-- §11.1; Soundness §5's `pd-cross-positions→Ambig` is the tool once the
--   `_◁_`
-- position of the pair is extracted).  The right branch needs no record
-- analysis: its witnesses carry `2 ≤ length pdis` (the two members are
-- at distinct list positions), and Soundness §11's `pdU-2members→Ambig`
--   inverts
-- that length bound through the `pdU` clauses to an A1/A2
-- configuration.

```

Note what is *not* claimed here: the two records may continue at one expression
without that expression being syntactically a sum, which is why this is stated
for members and not read off `dups-≈₀`'s definition.  §9.1's `pd-a3-target` is
exactly that shape — `pdU` fuses the two branch instances, and the flattened
list still contains `ε ● ($ c \` 4) \` 5` twice — and `pd-a3-Idemp-applied` is
the computation that this section's lemmas now justify.

## 10. Lifting a criterion from a reachable state (the full form of the paper's criteria)


`A1→Ambig` / `A2→Ambig` (in `cgp.ambig.AmbigCheck`) and `Ctx-dup→Ambig`
(`cgp.ambig.Soundness` §1) cover only the initial state `s = r`, i.e. a path
of length 0.  The
Ambiguity Criteria proposition of the paper quantifies over *realizable*
`s ∈ Desc(r)`: if a criterion fires at a state reached after consuming a
word `w`, then `r` is ambiguous — the ambiguity witness (two distinct parse
trees of `s` reading the same word) is lifted to parse trees of `r` along
the path, and both read the word `w ++ | u |`.

In this formalism "state `p` reached after `w` together with its path tree
map" is exactly a `PDInstance* r w` (`pdUMany[ r , w ]` produces them): the
continuation is the state `p`, `inj : U p → U r` is the composed transition
map and `ev` states `| inj u | = w ++ | u |`.  All three criteria then share
*one* proof, the master lift below: the criterion supplies `Ambig p`, and
`lift-Ambig` transports the witness.  The paper hides one side condition in
its construction — distinct trees must stay distinct under the lift; here it
becomes the explicit hypothesis `inj-inj` (the transition maps of the paper's
`AllParseFST` are injective by construction; in this project the pd builders
`pdinstance-left/right/fst/snd/star` are injective given an injective
input — the `posix` `mkfuseInj` is the exception, it can identify trees
coming from different branches).

```agda
-- accessors for the data carried by a PDInstance*
pd*-inj : ∀ { r : RE } { pref : List Char } ( pdi : PDInstance* r pref )
  → U (pd*-expr pdi) → U r
pd*-inj (pdinstance* {p} inj ev) = inj

pd*-ev : ∀ { r : RE } { pref : List Char } ( pdi : PDInstance* r pref )
  → ∀ ( u : U (pd*-expr pdi) ) → proj₁ (flat (pd*-inj pdi u)) ≡ pref ++ proj₁ (flat u)
pd*-ev (pdinstance* {p} inj ev) = ev

-- master lift: an ambiguity witness of the state p survives the path lift
lift-Ambig : ∀ { r p : RE } { w : List Char }
  → ( inj : U p → U r )
  → ( ev : ∀ ( u : U p ) → proj₁ (flat {r} (inj u)) ≡ w ++ proj₁ (flat {p} u) )
  → ( inj-inj : ∀ ( u v : U p ) → inj u ≡ inj v → u ≡ v )
  → Ambig p
  → Ambig r
lift-Ambig {r} {p} {w} inj ev inj-inj (u , v , w≡ , u≢v) =
    ( inj u
    , inj v
    , trans (trans (ev u) (cong ( λ z → w ++ z) w≡)) (sym (ev v))
    , λ trees≡ → u≢v (inj-inj u v trees≡) )

-- (purpose): the context lift on its own — an ambiguity of the hole
--   expression transfers to the filled expression
-- (used in): the re-embedding clauses of the pdU clause analysis
--   (`pdU-member-pair→Ambig`, `pdU-2members→Ambig`, Soundness §10);
--   through the latter the §11.1 closer `pd-Idemp` (Soundness §11)
--   composes it, and so does the `soundness` statement (Soundness §12,
--   fourth disjunct); `Ctx-dup→Ambig` (Soundness §1) builds the same
--   witness inline
-- (proof idea): `CtxT` embeds the two trees, `CtxT-pres-flat` keeps the
--   word equation, `CtxT-injective` reflects the disequality
lift-Ctx : ∀ ( ctx : Ctx ) { s : RE } → Ambig s → Ambig (plug ctx s)
lift-Ctx ctx ( u , v , word≡ , u≢v ) =
    ( CtxT ctx u
    , CtxT ctx v
    , CtxT-pres-flat ctx word≡
    , λ trees≡ → u≢v (CtxT-injective ctx trees≡) )

-- the three criteria at a pd-reachable state (pdUMany witnesses)
pd*-Ambig→Ambig : ∀ { r : RE } { pref : List Char }
  → ( pdi : PDInstance* r pref )
  → ( ∀ ( u v : U (pd*-expr pdi) ) → pd*-inj pdi u ≡ pd*-inj pdi v → u ≡ v )
  → Ambig (pd*-expr pdi)
  → Ambig r
pd*-Ambig→Ambig pdi inj-inj = lift-Ambig (pd*-inj pdi) (pd*-ev pdi) inj-inj

pd*-A1→Ambig : ∀ { r : RE } { pref : List Char }
  → ( pdi : PDInstance* r pref )
  → ( ∀ ( u v : U (pd*-expr pdi) ) → pd*-inj pdi u ≡ pd*-inj pdi v → u ≡ v )
  → AmbigA1 (pd*-expr pdi)
  → Ambig r
pd*-A1→Ambig pdi inj-inj a1 = pd*-Ambig→Ambig pdi inj-inj (A1→Ambig (pd*-expr pdi) a1)

pd*-A2→Ambig : ∀ { r : RE } { pref : List Char }
  → ( pdi : PDInstance* r pref )
  → ( ∀ ( u v : U (pd*-expr pdi) ) → pd*-inj pdi u ≡ pd*-inj pdi v → u ≡ v )
  → AmbigA2 (pd*-expr pdi)
  → Ambig r
pd*-A2→Ambig pdi inj-inj a2 = pd*-Ambig→Ambig pdi inj-inj (A2→Ambig (pd*-expr pdi) a2)

```

Notes:

* `A1→Ambig` / `A2→Ambig` / `Ctx-dup→Ambig` are the special cases
  `w = []`, `inj = id` (realizability in the paper's sense is automatic
  here: every project `RE` has a parse tree, `r-∃u`).
* `cgp.ambig.Soundness` §3's `pd-pairs→Ambig` / `pd*-pairs→Ambig`
  is an *already lifted* form of
  A3: the two parse trees are built directly under the injections, so no
  injectivity hypothesis is needed (the pair sits in different sum branches,
  `LeftU≢RightU`).
* The remaining gap towards the paper's full proposition is unchanged:
  proving that `inj-inj` holds for the concrete injections produced by
  `pdUMany` (routine for the `lne`/`greedy` builders, false for
  `mkfuseInj`), and the converse direction
  ("`r` ambiguous ⇒ some realizable state fires A1/A2/A3"), which needs
  the FST / `Desc(r)` construction.  The converse does *not* hold without
  the quantification over `Desc(r)`: for `r = ( a + a · a ) ⋆` the word
  `a a` has two parse trees (`ListU [ a , a ]`, `ListU [ a · a ]`), yet no
  criterion fires at `r` — a star has a single empty parse tree, and the
  paper's hole contexts have no hole under a star.

## 11. `Desc(r)` — the paper's states, built from partial derivatives

The paper's `Desc(r) = { s | r Descendant s }` is defined by the
Brzozowski derivative, which `cgp` lacks.  The `posix` `pdU` already
contains the trick that repairs this: `pdinstance-oplus`/`fuse` merges
sibling alternatives *inside* every pd step, so one fused `pdinstance`
carries one continuation expression — and iterating single-character
steps with `advance-pdi*-with-c`/`pdUMany` composes those continuations
along a word (this is the "encode the derivative via partial
derivatives" construction of the old `cgp.posix.Related` /
`cgp.relatedwork.RelatedWorkOkuiSuzuki`).

Only a residual multi-instance list can remain (from nullable-`●`
products and under stars).  Its sum is the derivative: by Antimirov,
`deriv r w` is denoted by the *sum of all partial derivative
continuations*, so re-gluing them with `sum-build` produces a single
expression (`derivᵖ r w` below) that plays the role of `deriv r w`
(denotes the same language — the project formalizes exactly this
correspondence, `pdUMany` soundness / reconstructability, Lemmas 21–22).
`nothing` is the `∅`-case.  With it the paper's quantification "there
exists a realizable `s ∈ Desc(r)`" becomes the concrete type `_∈Desc_`
below — realizability is automatic (every reachable `RE` is inhabited,
`r-∃u`; the `∅` cases are filtered out by `just`).

```agda
-- alternatives of the (distributed) derivative of a word
pd*-alts : ∀ { r : RE } { w : List Char } → List (PDInstance* r w) → List RE
pd*-alts pdis = concatMap ( λ pdi → sum-spine (pd*-expr pdi) ) pdis

-- the derivative of r w.r.t. w, encoded via partial derivatives
-- (sum-build re-glues the residual instances; the loc zero of the
-- artificial top '+' is irrelevant, ≈₀ and the theorems are loc-agnostic)
derivᵖ : ( r : RE ) → ( w : List Char ) → Maybe RE
derivᵖ r w with PosixPD.pdUMany[ r , w ]
...   | [] = nothing
...   | pdis = just (sum-build (pd*-alts pdis) zero)

-- s ∈Desc r  ⟺  s is a (realizable) descendant state of r
-- (paper: s ∈ Desc(r); the realizable side condition is automatic here)
infix 4 _∈Desc_
_∈Desc_ : RE → RE → Set
s ∈Desc r = Σ[ w ∈ List Char ] ( derivᵖ r w ≡ just s )

```

### 11.1. A3 stated verbatim for the initial state

With `derivᵖ`, the paper's A3 condition for the initial state,
"`lang(canonic(deriv r x)) ≠ {}` and `Idemp` applied", becomes a
computable boolean:

```agda
A3? : ( r : RE ) → ( c : Char ) → Bool
A3? r c with derivᵖ r (c ∷ [])
...   | nothing = false
...   | just s = proj₂ (canonic s)

-- the paper's A3 test fires on the §9.1 example:
-- after consuming 'a' the descendant state
--   (ε ● ($ 'c' ` 4) ` 5) + (ε ● ($ 'c' ` 7) ` 8) ` 0
-- is reached, and its canonical representative applies Idemp:
pd-a3-state : RE
pd-a3-state = (ε ● ($ 'c' ` 4) ` 5) + ((ε ● ($ 'c' ` 7) ` 8)) ` zero

pd-a3-Desc : pd-a3-state ∈Desc pd-a3-target
pd-a3-Desc = ( 'a' ∷ [] , refl )

pd-a3-A3?-fires : A3? pd-a3-target 'a' ≡ true
pd-a3-A3?-fires = refl

-- sanity check: a single letter reaches the state ε, no Idemp fires:
letter-A3?-silent : A3? ($ 'a' ` 1) 'a' ≡ false
letter-A3?-silent = refl

```

Caveats (consistent with §9/§10):

* `derivᵖ r w` is a *witness term* for the derivative (same language),
  not a syntactic replica of Brzozowski's — stars unfold positionally
  (`pdinstance-star` appends `r * ε∉r ` loc`) and `sum-build`
  introduces artificial `+` locations.  The paper's own FST quotients by
  similarity anyway, and `≈₀`/`canonic` are location-insensitive, so
  the A3 *test* is unaffected.
* The soundness of a fired `A3?` is composed in `cgp.ambig.Soundness` §11,
  unconditionally:

  > `pd-Idemp : pd-Idemp? (PosixPD.pdU[ q , c ]) ≡ true → Ambig q`

  Its test hypothesis is fully unpacked (§9.2: the positioned reflection
  `dups-≈₀-dups : dups-≈₀ xs ≡ true → Dups-w xs` reads a fired scan
  back as a *positioned* duplicate pair — two list positions, not just
  two values (the value-only form is too weak: the same value may
  legitimately occur twice in an unambiguous list).  The *classification* is proved
  (`Dups-w-++-split` + `pd-alts-Dups-w-classify`, this module's §9.2,
  instantiated at the example by `pd-alts-classify-a3`): the pair of a fired test either
  sits at two positions of one member's `sum-spine`, or has its earlier
  occurrence in one member's spine and its later occurrence in another's.
  The first branch is closed in full by Soundness §10's
  `pdU-member-pair→Ambig`,
  an induction along the clauses of the `pdU` definition —
  configurations (a) and (b) closed by that same induction (its non-sum
  leaves through Soundness §9's `Dups-w-∷[]-absurd`), the crossings of a `+` clause through Soundness §5's
  `pd-cross-positions→Ambig` and of the nullable-`●` clause through
  Soundness §10's `pd-cross-●→Ambig` (which closes a
  first-factor/empty-first-factor pair by *word* distinctness, `c ∷ _`
  versus `[]` via `flat-[]`, the one place where branch-constructor
  injectivity is unavailable because both records share their input
  expression).  The second branch is closed by Soundness §11's
  `pdU-2members→Ambig`, a second induction along the `pdU` clauses: the
  classification hands over the *length bound* `2 ≤ length (pdU[ q , c ])`
  (the two members sit at distinct positions of the member list), and
  that bound alone suffices — each clause either factors it through a
  branch list (`length-map`, `pdU-oplus-≥2`, `pdU-cms-len`, `×-≥2→`) and
  lifts the resulting ambiguity back through the sum/consumption contexts
  (`lift-Ctx`, `star-Ambig`), or ends at the empty-tree factor of the
  nullable-`●` clause, where `≥ 2` empty parse trees of the left factor
  is exactly the A2 criterion record at the clause's own concatenation
  node (`A2→Ambig`).  No record-distinctness question arises on this
  branch: the ambiguity comes from the clause structure of the member
  list, not from comparing the pair's values.
  The `mkfuseInj` gap of §10 does not arise in (a) — the
  branch maps are only used through different parent branches.

For the *criteria* themselves the single-expression form is not needed: the
states are lists of partial derivatives, see §12.

## 12. `Desc(r)` as a list of partial derivatives (the pd-native form)

An Antimirov state *is* a set of partial derivatives, so the faithful
formalization of `Desc(r)` keeps the list and drops `sum-build`/`Maybe`:

```agda
-- the pd-descendant state of r after w: the list of continuations of the
-- partial derivatives produced by pdUMany (the Antimirov state)
pd*-Desc : ( r : RE ) → ( w : List Char ) → List RE
pd*-Desc r w = List.map pd*-expr (PosixPD.pdUMany[ r , w ])

-- s ∈Descᵖ r  ⟺  s is the (list) state reached after some word
-- (paper: s ∈ Desc(r); 'realizable' is automatic, and the ∅ state is the
-- empty list rather than a Maybe case)
infix 4 _∈Descᵖ_
_∈Descᵖ_ : List RE → RE → Set
ss ∈Descᵖ r = Σ[ w ∈ List Char ] ( pd*-Desc r w ≡ ss )

```

The three criteria are then tests *on the list*, and §10's `lift-Ambig`
applies componentwise — every element of `pd*-Desc r w` is the continuation
of some `pdi : PDInstance* r w`, and `pd*-A1→Ambig` / `pd*-A2→Ambig` /
`pd*-Ctx-dup→Ambig` are universally quantified over such an instance, so a
criterion firing at *any* member of the state list already gives `Ambig r`
(the `pd*-Ctx-dup→Ambig` instance travels with `Ctx-dup→Ambig` in
`cgp.ambig.Soundness` §6).
Only A3 needs an additional list-level test, which is exactly `dups-≈₀` —
no re-glued expression and no artificial `+` locations involved:

```agda
-- the paper's A3 test on the state reached after w then c:
-- does canonicalizing that state apply Idemp?
A3-list? : ( r : RE ) → ( w : List Char ) → ( c : Char ) → Bool
A3-list? r w c = dups-≈₀ (pd*-alts (PosixPD.pdUMany[ r , w ++ (c ∷ []) ]))

-- the §9.1 example, in list form: after 'a the state is the single fused
-- instance whose continuation is the sum of the two equal continuations
-- (the ' + ' carries the location 9 of the source expression, §11's
-- pd-a3-state differs from it only by the artificial location):
pd-a3-Descᵖ : ( (ε ● ($ 'c' ` 4) ` 5) + ((ε ● ($ 'c' ` 7) ` 8)) ` 9 ) ∷ []
              ∈Descᵖ pd-a3-target
pd-a3-Descᵖ = ( 'a' ∷ [] , refl )

pd-a3-A3-list?-fires : A3-list? pd-a3-target [] 'a' ≡ true
pd-a3-A3-list?-fires = refl

-- a two-step word reaches the same situation one level deeper
-- (consume 'a' then 'c': both continuations become ε, so the state
-- contains two copies of ε):
pd-a3-A3-list?-step2 : A3-list? pd-a3-target ( 'a' ∷ [] ) 'c' ≡ true
pd-a3-A3-list?-step2 = refl

-- negative controls: a dead state has no duplicates
letter-A3-list?-silent : A3-list? ($ 'a' ` 1) [] 'a' ≡ false
letter-A3-list?-silent = refl

```

For one step the list form is the same computation as §9's `pd-Idemp?`:
`pdUMany[ r , x ∷ [] ]` is `pdU[ r , x ]` composed with the identity path
map, and `compose-pdi-with` keeps the continuation of its argument
(`pdinstance* {p}` with the same `p`), so `pd*-alts` of the one-step state
coincides with `pd-alts (pdU[ r , x ])`.  The list form is therefore a
*conservative* extension: it runs the same test on the state reached after
an arbitrary prefix, which is the paper's A3 for a descendant `s`, stated
without ever leaving the partial-derivative setting.





## 13. The diagnosis disjunction `crit`

This `crit` defines the ambiguity check criteria. The first two disjuncts
correspond to the A1 and A2 criteria in the CIAA 2016 paper section 6.
The third and the fourth correspond to the A3 criteria with the adjustment to
current project formlation, i.e. no phi, folding oplus over a list partial derivatives.
The third disjunct says that there exists some choice sub expressions whose left and right
alts are similar _≈₀_ (eq modulo AST source locations), i.e. the top level A3.
The fourth disjunct says that there eixsts some sub expression q, whose derivative (pd via oplus)
descendant have two similar spine members, i.e. reverse the folding with oplus back to a list of
partial derivatives, and in the list we find two similar partial derivatives, i.e. it is the
descendant version of the A3.


The completeness half (`cgp.ambig.Completeness`) proves "ambiguous ⇒ some
realizable state fires a criterion"; its diagnosing lemmas and the pd-state
soundness reading (`cgp.ambig.Soundness` §12) share one codomain, the
disjunction of the paper's criteria at a state.  It is stated here, next to
the tests it mentions:

```agda
-- the diagnosis disjunction: one of the paper's criteria fires at `p`
-- (purpose): the single codomain every diagnosing lemma targets
-- (used in): `desc-concl`/`Desc-complete` (Completeness §6), `pick-diff-record-prf`
--   (Completeness §7), the `completeness` statement (Completeness §9), and the
--   `soundness` reading (Soundness §12)
-- (proof idea): definition — A1/A2 from `AmbigCheck`, the duplicate pattern and
-- the transition `Idemp` test read under a hole context
crit : RE → Set
crit p = Sum._⊎_
      (AmbigA1 p)
      (Sum._⊎_
        (AmbigA2 p)
        (Sum._⊎_
          ( Σ[ ctx ∈ Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
              ( ( plug ctx ( l + s ` loc ) ≡ p )
              × ( _≈₀_ l s ) ) )
          ( Σ[ ctx ∈ Ctx ] Σ[ q ∈ RE ] Σ[ c ∈ Char ]
              ( ( plug ctx q ≡ p )
              × ( pd-Idemp? (PosixPD.pdU[ q , c ]) ≡ true ) ) )))

-- The fourth disjunct is worth naming outright at the empty context, since
-- it is a decidable test on the transition out of the state and needs no
-- descent: a positive `Idemp` test on the transition out of `r` is a
-- criterion at `r` itself.
-- (purpose): the fourth disjunct at the empty context
-- (used in): `pick-diff-record-prf` (Completeness §7)
-- (proof idea): by inspection: `𝟘 , r , c` plugs to `r` at `refl`, and the
--   hypothesis is exactly the fourth component
crit-A3-test : ∀ ( r : RE ) ( c : Char )
  → pd-Idemp? (PosixPD.pdU[ r , c ]) ≡ true
  → crit r
crit-A3-test r c p≡true = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ ( 𝟘 , r , c , ( refl , p≡true ) )))
```
