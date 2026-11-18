```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.greedyposix.Robust where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_)

import cgp.ParseTree as ParseTree
open ParseTree using (U; EmptyU; LetterU; LeftU; RightU; PairU; ListU; flat)

import cgp.PDInstance as PDI
open PDI using (PDInstance; pdinstance)

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming (_⊢_>_ to _⊢_>ᵍ_; >→¬≡ to >ᵍ→¬≡; u>v→¬v>u to u>ᵍv→¬v>ᵍu)

import cgp.greedy.PartialDerivative as GreedyPD
open GreedyPD renaming (parseAll[_,_] to parseAllᵍ[_,_])

import cgp.greedy.MaxWord as GreedyMax
open GreedyMax renaming (≥-Max to ≥-Maxᵍ; ≥-max to ≥-maxᵍ)

import cgp.posix.Order as PosixOrder
open PosixOrder renaming (_⊢_>_ to _⊢_>ᵖ_; >→¬≡ to >ᵖ→¬≡)

import cgp.posix.PartialDerivative as PosixPD
open PosixPD renaming (parseAll[_,_] to parseAllᵖ[_,_])

import cgp.posix.MaxWord as PosixMax
open PosixMax renaming (≥-Max to ≥-Maxᵖ; ≥-max to ≥-maxᵖ)

import cgp.Utils as Utils
open Utils using (∷-inj; ¬∷≡[])

import Data.List as List
open List using (List; _∷_; []; _++_; length)

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using (ℕ; suc; zero)

import Data.Product as Product
open Product using (_×_; _,_)
open Product.Σ using (proj₁; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Data.Empty as Empty
open Empty using (⊥-elim; ⊥)

import Relation.Nullary.Negation as Negation
open Negation using (contradiction)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)

import cgp.robust.greedyposix.Iso as Iso
open Iso using (Iso; iso)

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using (Ambig;  UnAmbig) 

```

### Robustness Definition

```agda

data Robust : RE → Set where
  robust : ∀ { r : RE }
              → ( ∀ ( w : List Char )
                → ( v : U r )
                → ( ( ≥-Maxᵍ {r} w v ) → (≥-Maxᵖ {r} w v ) ) × ( ( ≥-Maxᵖ {r} w v ) → (≥-Maxᵍ {r} w v ) )
                )
            -----------------------------------------
            → Robust r


iso→robust : ∀ ( r : RE )
  → Iso r
  → Robust r
iso→robust r (iso iso-ev) = robust {r} ev
  where
    ev : ( w : List Char ) → ( v : U r )
      → ( ≥-Maxᵍ {r} w v → ≥-Maxᵖ {r} w v )
      × ( ≥-Maxᵖ {r} w v → ≥-Maxᵍ {r} w v )
    ev w v = to-ev , from-ev
      where
        to-ev : ≥-Maxᵍ {r} w v → ≥-Maxᵖ {r} w v
        to-ev (GreedyMax.≥-max w' v' flat-v'≡w' max-v') =
          PosixMax.≥-max w' v' flat-v'≡w' max-vᵖ
          where
            max-vᵖ : ( u : U r ) → proj₁ (flat u) ≡ w' → PosixMax._⊢_≥_ r v' u
            max-vᵖ u flat-u≡w' with max-v' u flat-u≡w'
            ... | inj₁ v'>ᵍu = inj₁ (proj₁ (iso-ev v' u) v'>ᵍu)
            ... | inj₂ v'≡u = inj₂ v'≡u

        from-ev : ≥-Maxᵖ {r} w v → ≥-Maxᵍ {r} w v
        from-ev (PosixMax.≥-max w' v' flat-v'≡w' max-v') =
          GreedyMax.≥-max w' v' flat-v'≡w' max-vᵍ
          where
            max-vᵍ : ( u : U r ) → proj₁ (flat u) ≡ w' → GreedyMax._⊢_≥_ r v' u
            max-vᵍ u flat-u≡w' with max-v' u flat-u≡w'
            ... | inj₁ v'>ᵖu = inj₁ (proj₂ (iso-ev v' u) v'>ᵖu)
            ... | inj₂ v'≡u = inj₂ v'≡u



unambig→robust : ∀ { r : RE }
  → UnAmbig r
  → Robust r
unambig→robust {r} unambig = robust {r} ev
  where
    ev : ( w : List Char ) → ( v : U r )
      → ( ≥-Maxᵍ {r} w v → ≥-Maxᵖ {r} w v )
      × ( ≥-Maxᵖ {r} w v → ≥-Maxᵍ {r} w v )
    ev w v = to-ev , from-ev
      where
        -- an unambiguous r has at most one tree per word: any two trees
        -- reading the same word are identical, so the comparison field of
        -- a maximality proof always holds on its equality side
        eq-side : ( v' u : U r ) ( w' : List Char )
          → proj₁ (flat {r} v') ≡ w' → proj₁ (flat {r} u) ≡ w'
          → v' ≡ u
        eq-side v' u w' v'≡w' u≡w' = unambig v' u (trans v'≡w' (sym u≡w'))

        to-ev : ≥-Maxᵍ {r} w v → ≥-Maxᵖ {r} w v
        to-ev (GreedyMax.≥-max w' v' flat-v'≡w' _) =
          PosixMax.≥-max w' v' flat-v'≡w'
            (λ u flat-u≡w' → inj₂ (eq-side v' u w' flat-v'≡w' flat-u≡w'))

        from-ev : ≥-Maxᵖ {r} w v → ≥-Maxᵍ {r} w v
        from-ev (PosixMax.≥-max w' v' flat-v'≡w' _) =
          GreedyMax.≥-max w' v' flat-v'≡w'
            (λ u flat-u≡w' → inj₂ (eq-side v' u w' flat-v'≡w' flat-u≡w'))

```
