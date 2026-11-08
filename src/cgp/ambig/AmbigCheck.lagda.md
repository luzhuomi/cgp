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
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉; ε∈; ε∈ε; ε∈_●_; ε∈_+_ ; ε∈_<+_ ; ε∈_+>_ ; ε∈* ; ε∉$ ; ε∉_+_ ; ε∉r→¬ε∈r )

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU; LetterU; LeftU; RightU; PairU; ListU; flat; r-∃u ; inv-leftU ; inv-rightU ; inv-pairU ; LeftU≢RightU ; RightU≢LeftU ; _⊢_≟_ )

import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; Flat-[] ; flat-[] ; mkAllEmptyU-sound )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; length)

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using ( ℕ ; zero ; suc ; _≤_ ; s≤s )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive )

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
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Relation.Nullary as Nullary
open Nullary using (¬_)

import Data.Empty as Empty
open Empty using (⊥ ; ⊥-elim)

import Relation.Nullary.Decidable as Decidable
open Decidable using (Dec; yes; no)

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

```agda
data NoDup { a : Set } : List a → Set where
  nd[] : NoDup {a} []
  nd∷ : ∀ { x : a } { xs : List a }
    → ( ¬ ( Any ( _≡_ x ) xs ) )
    → NoDup {a} xs
    → NoDup {a} (x ∷ xs)

-- membership inversion helper for All
lookup-All : ∀ { a : Set } { P : a → Set } { x : a } { xs : List a }
  → All P xs
  → Any ( _≡_ x ) xs
  → P x
lookup-All {P = P} {x} (p ∷ ps) (here eq) = subst P (sym eq) p
lookup-All (p ∷ ps) (there x∈) = lookup-All ps x∈

nd-++ : ∀ { a : Set } { xs ys : List a }
  → NoDup {a} xs
  → (∀ { x y } → x ∈ xs → y ∈ ys → ¬ (x ≡ y))
  → NoDup {a} ys
  → NoDup {a} (xs ++ ys)
nd-++ nd[] disj ndys = ndys
nd-++ {xs = x ∷ xs} {ys = ys} (nd∷ x∉ ndxs) disj ndys = nd∷ (λ x∈xs++ys → ⊥-help x∈xs++ys) (nd-++ ndxs disj′ ndys)
  where
    disj′ : ∀ { z y } → z ∈ xs → y ∈ ys → ¬ (z ≡ y)
    disj′ z∈ y∈ = disj (there z∈) y∈
    ⊥-help : Any ( _≡_ x ) (xs ++ ys) → ⊥
    ⊥-help x∈xs++ys with ListMem.∈-++⁻ xs x∈xs++ys
    ...   | inj₁ x∈xs = x∉ x∈xs
    ...   | inj₂ x∈ys = disj (here refl) x∈ys refl

nd-map : ∀ { a b : Set } ( f : a → b )
  → (∀ { x y } → f x ≡ f y → x ≡ y)
  → ∀ { xs : List a }
  → NoDup {a} xs
  → NoDup {b} (List.map f xs)
nd-map {a} {b} f f-inj nd[] = nd[]
nd-map {a} {b} f f-inj {x ∷ xs} (nd∷ x∉ ndxs) = nd∷ (λ f-x∈map → ⊥-help f-x∈map) (nd-map f f-inj ndxs)
  where
    ⊥-help : Any ( _≡_ (f x)) (List.map f xs) → ⊥
    ⊥-help f-x∈map with ListMem.∈-map⁻ f f-x∈map
    ...   | w , w∈xs , f-x≡f-w = x∉ (AnyMod.map (λ eq → trans (f-inj f-x≡f-w) eq) w∈xs)

-- membership inversion for concatMap (not in the standard library)
∈-concatMap⁻ : ∀ { a b : Set } ( f : a → List b ) { xs : List a } { y : b }
  → y ∈ List.concatMap f xs
  → ∃[ x ] ( x ∈ xs × y ∈ f x )
∈-concatMap⁻ f {xs = []} ()
∈-concatMap⁻ f {xs = x ∷ xs} y∈ with ListMem.∈-++⁻ (f x) y∈
...   | inj₁ y∈fx = x , here refl , y∈fx
...   | inj₂ y∈tail with ∈-concatMap⁻ f y∈tail
...   | x′ , x′∈ , y∈fx′ = x′ , there x′∈ , y∈fx′

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
    disj-blocks {x} {y} x∈ y∈ eq with ListMem.∈-map⁻ (λ v → PairU {l} {r} {loc} a v) x∈ | ∈-concatMap⁻ (λ u → List.map (λ v → PairU {l} {r} {loc} u v) vs) y∈
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
