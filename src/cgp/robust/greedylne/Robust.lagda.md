```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.greedylne.Robust where

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

import cgp.lne.Order as LNEOrder
open LNEOrder renaming (_⊢_>_ to _⊢_>ˡ_; >→¬≡ to >ˡ→¬≡)

import cgp.lne.PartialDerivative as LNEPD
open LNEPD renaming (parseAll[_,_] to parseAllˡ[_,_])

import cgp.lne.MaxWord as LNEMax
open LNEMax renaming (≥-Max to ≥-Maxˡ; ≥-max to ≥-maxˡ)

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

import cgp.robust.greedylne.Iso as Iso
open Iso using (Iso; iso)

```

### Robustness Definition

```agda

data Robust : RE → Set where
  robust : ∀ { r : RE }
              → ( ∀ ( w : List Char )
                → ( v : U r )
                → ( ( ≥-Maxᵍ {r} w v ) → (≥-Maxˡ {r} w v ) ) × ( ( ≥-Maxˡ {r} w v ) → (≥-Maxᵍ {r} w v ) )
                )
            -----------------------------------------
            → Robust r


iso→robust : ∀ ( r : RE )
  → Iso r
  → Robust r
iso→robust r (iso iso-ev) = robust {r} ev
  where
    ev : ( w : List Char ) → ( v : U r )
      → ( ≥-Maxᵍ {r} w v → ≥-Maxˡ {r} w v )
      × ( ≥-Maxˡ {r} w v → ≥-Maxᵍ {r} w v )
    ev w v = to-ev , from-ev
      where
        to-ev : ≥-Maxᵍ {r} w v → ≥-Maxˡ {r} w v
        to-ev (GreedyMax.≥-max w' v' flat-v'≡w' max-v') =
          LNEMax.≥-max w' v' flat-v'≡w' max-vˡ
          where
            max-vˡ : ( u : U r ) → proj₁ (flat u) ≡ w' → LNEOrder._⊢_≥_ r v' u
            max-vˡ u flat-u≡w' with max-v' u flat-u≡w'
            ... | inj₁ v'>ᵍu = inj₁ (proj₁ (iso-ev v' u) v'>ᵍu)
            ... | inj₂ v'≡u = inj₂ v'≡u

        from-ev : ≥-Maxˡ {r} w v → ≥-Maxᵍ {r} w v
        from-ev (LNEMax.≥-max w' v' flat-v'≡w' max-v') =
          GreedyMax.≥-max w' v' flat-v'≡w' max-vᵍ
          where
            max-vᵍ : ( u : U r ) → proj₁ (flat u) ≡ w' → GreedyMax._⊢_≥_ r v' u
            max-vᵍ u flat-u≡w' with max-v' u flat-u≡w'
            ... | inj₁ v'>ˡu = inj₁ (proj₂ (iso-ev v' u) v'>ˡu)
            ... | inj₂ v'≡u = inj₂ v'≡u

```
