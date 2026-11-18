# MaxWord: the maximal parse tree of a word (posix side)

This is the `cgp.posix` counterpart of `cgp.lne.MaxWord` / `cgp.greedy.MaxWord`'s
`≥-Max`: the property that a parse tree `u` reading word `w` is maximal among
*all* parse trees of `r` reading `w`.

The posix order (`cgp.posix.Order`, `_⊢_>_`) is strict and total, so the
non-strict comparison `u ≥ v` of the lne/greedy version appears here as
`( r ⊢ u > v ) ⊎ ( u ≡ v )` — the same form `≥-maximal` (Definition 42 of
`cgp.posix.ExtendedOrder`) uses.

The corresponding theorem is the composition that was previously unnamed on
this side: Theorem 43 (`parseAll-is-posix-maximal`: the head of the computed
list `parseAll[ r , w ] = concatMap buildU (pdUMany[ r , w ])` dominates that
list) + `parseAll-complete` (every parse tree of `w` is in that list) yields
`parseAll-head-isMax`: the head tree is `≥-Max` for its word.

```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.MaxWord where

import cgp.RE as RE
open RE using (RE)

import cgp.ParseTree as ParseTree
open ParseTree using ( U ; flat )

import cgp.posix.Order as PosixOrder
open PosixOrder using ( _⊢_>_ )

import cgp.posix.ExtendedOrder as ExtendedOrder
open ExtendedOrder using ( ≥-maximal ; ≥-join ; parseAll-is-posix-maximal )

import cgp.posix.PartialDerivative as PartialDerivative
open PartialDerivative using ( parseAll[_,_] ; parseAll-sound ; parseAll-complete )

import cgp.Utils as Utils
open Utils using ( lookup-All )

import Data.List as List
open List using (List ; _∷_ ; [] ; head)

import Data.Char as Char
open Char using (Char)

import Data.List.Relation.Unary.All as All
open All using (All)

import Data.List.Relation.Unary.Any as Any
open Any using (Any; here; there)

import Data.Maybe as Maybe
open Maybe using ( just )

import Data.Product as Product
open Product using ( Σ-syntax ; _,_ )
open Product using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using ( _⊎_ )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; subst)

```

## 1. `≥-Max`: a tree maximal among all trees of its word

```agda
-- Purpose: define what it means for a parse tree u to be maximal for word w.
--   u is maximal iff flat u = w and for every v with flat v = w,
--   r ⊢ u > v or u ≡ v (the posix order is strict; >-or-equal is its ≥).
-- Used by: (entry point of the maximality story on the posix side; cf. the
--   lne/greedy consumers ≥-Max-PDInstance, parseAll-head-isMax)
-- Proof idea: N/A (data type definition with single constructor ≥-max)
data ≥-Max : ∀ { r : RE } → List Char → U r → Set where
  ≥-max : ∀ { r : RE }
        → ( w : List Char )
        → ( u : U r )
        → proj₁ (flat {r} u) ≡ w
        → ( ( v : U r )
          → proj₁ (flat {r} v) ≡ w
          → ( r ⊢ u > v ) ⊎ ( u ≡ v ) )
        → ≥-Max {r} w u

-- Purpose: extract the word-equality proof from a ≥-Max proof
-- Used by: consumers that need |u| = w from maximality alone
-- Proof idea: the only constructor stores it
≥-max-word : ∀ { r : RE } { w : List Char } { u : U r } → ≥-Max {r} w u → proj₁ (flat {r} u) ≡ w
≥-max-word {r} {w} {u} (≥-max .w u w≡ _) = w≡

```

## 2. The head of `parseAll[ r , w ]` is `≥-Max`

```agda
-- a head equation unpacks the list: head xs = just x forces xs = x ∷ tail
head-just→∷ : ∀ { a : Set } { x : a } ( xs : List a )
  → head xs ≡ just x
  → Σ[ t ∈ List a ] xs ≡ x ∷ t
head-just→∷ [] ()
head-just→∷ (y ∷ xs) refl = xs , refl

-- membership in x ∷ xs is either the head or the tail
∈-∷-inv : ∀ { a : Set } { x y : a } { ys : List a }
  → Any ( _≡_ y ) (x ∷ ys)
  → ( y ≡ x ) ⊎ (Any ( _≡_ y ) ys)
∈-∷-inv (here p) = Sum.inj₁ p
∈-∷-inv (there y∈) = Sum.inj₂ y∈

-- inversion of ≥-maximal (Definition 42) at a non-empty list
≥-maximal-head : ∀ { r : RE } { u : U r } { t : List (U r) }
  → ≥-maximal {r} (u ∷ t)
  → All ( λ x → ( r ⊢ u > x ) ⊎ ( u ≡ x ) ) t
≥-maximal-head {r} {u} {t} (≥-join .u .t a) = a

-- Purpose: main theorem — if parseAll[ r , w ] has a head, that head tree is
--   ≥-Max: it reads w and it dominates *every* parse tree of r reading w.
-- Used by: the posix reading of "the greedy/posix parse produces a maximal
--   tree" (cf. lne/greedy parseAll-head-isMax)
-- Proof idea: head-just→∷ gives parseAll[ r , w ] ≡ u ∷ t; Theorem 43
--   (parseAll-is-posix-maximal) transported along that equation and inverted
--   (≥-maximal-head) dominates t; any v reading w is in parseAll[ r , w ]
--   by parseAll-complete, so it is u or a member of t
parseAll-head-isMax : ∀ ( r : RE ) ( w : List Char ) ( u : U r )
  → head parseAll[ r , w ] ≡ just u
  → ≥-Max {r} w u
parseAll-head-isMax r w u u-is-head with head-just→∷ (parseAll[ r , w ]) u-is-head
...   | ( t , pa≡u∷t ) = ≥-max w u flat-u≡w max-of-v
  where
    u∈ : Any ( _≡_ u ) parseAll[ r , w ]
    u∈ = subst ( λ L → Any ( _≡_ u ) L ) (sym pa≡u∷t) (here refl)

    flat-u≡w : proj₁ (flat {r} u) ≡ w
    flat-u≡w = lookup-All (parseAll-sound {r} {w}) u∈

    maxAll : All ( λ x → ( r ⊢ u > x ) ⊎ ( u ≡ x ) ) t
    maxAll = ≥-maximal-head (subst ( λ L → ≥-maximal {r} L ) pa≡u∷t (parseAll-is-posix-maximal {r} {w}))

    max-of-v : ( v : U r ) → proj₁ (flat {r} v) ≡ w → ( r ⊢ u > v ) ⊎ ( u ≡ v )
    max-of-v v word≡ with ∈-∷-inv (subst ( λ L → Any ( _≡_ v ) L ) pa≡u∷t
        (subst ( λ k → Any ( _≡_ v ) parseAll[ r , k ] ) word≡ (proj₂ (parseAll-complete {r} v))))
    ...   | Sum.inj₁ v≡u = Sum.inj₂ (sym v≡u)
    ...   | Sum.inj₂ v∈t = lookup-All maxAll v∈t

```
