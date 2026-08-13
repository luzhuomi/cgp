```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.greedylne.Iso where

import cgp.robust.greedylne.GreedyLNEUtils as Utils
open Utils public

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉; ε∈; ε∈_+_; ε∈_<+_; ε∈_+>_; ε∈_●_; ε∈*; ε∈ε; ε∉r→¬ε∈r; ¬ε∈r→ε∉r; ε∉fst; ε∉snd; ε∉$; ε∉_+_; ε∉?; ε∈?; first; ε∉r→¬first-r≡[])

import cgp.ParseTree as ParseTree
open ParseTree using (U; EmptyU; LetterU; LeftU; RightU; PairU; ListU; flat; unflat; unflat∘proj₂∘flat; flat∘unflat; inv-flat-pair-fst; inv-flat-pair-snd; inv-flat-star; inv-leftU; inv-rightU; inv-pairU; inv-listU; unListU; listU∘unListU; LeftU≢RightU; RightU≢LeftU; proj₁∘LeftU≢proj₁∘RightU; r-∃u)

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming (_⊢_>_ to _⊢_>ᵍ_; >→¬≡ to >ᵍ→¬≡; u>v→¬v>u to u>ᵍv→¬v>ᵍu)

import cgp.lne.Order as LNEOrder
open LNEOrder renaming (_⊢_>_ to _⊢_>ˡ_; >→¬≡ to >ˡ→¬≡)

import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)
open Product.Σ using (proj₁; proj₂)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst; _≢_)
open Eq.≡-Reasoning using (begin_; step-≡; step-≡-∣; step-≡-⟩; _∎)

```

-- actually this is order isomoprhism, not maximality robustness 
### Isomoprhic definition 

```agda

data Iso : RE → Set where
  iso : ∀ { r : RE } 
              → ( ∀ ( v₁ : U r ) → ( v₂ : U r ) 
                → ( r ⊢ v₁ >ᵍ v₂ → r ⊢ v₁ >ˡ v₂ ) × ( r ⊢ v₁ >ˡ v₂ → r ⊢ v₁ >ᵍ v₂ )
                )
            -----------------------------------------
            → Iso r  
```
