```agda
{-# OPTIONS --rewriting  #-}

module cgp.greedy.MaxWord where

import Agda.Primitive as Prim
open Prim using (Level)

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ¬≡[]→length>0 ; ¬≡0→>0 ; length≡0→[] ; n≡0→¬n>0 ;
  ¬nothing≡just ; just-injective ; head-x∷xs≡just-x ; map-id  ; map-cong ; map-∘-eq ; concatMap-∘-eq ; map-++-distrib ;
  concatMap-map-commute  ; concatMap-cong ; concat-++ ; concatMap-++-distrib ; all-map-∈ 
 )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r ; []∈⟦r⟧→ε∈r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; unListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ; flat-Uε≡[] ; inv-pairU ) 

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; mkAllEmptyU≢[] ; Flat-[] ; flat-[] ; proj₁flat-v≡[]→ε∈r )

import cgp.Recons as Recons
open Recons using ( Recons ; recons )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ; 
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ; mkinjFstSoundEv ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ; mkinjSndSoundEv ; 
  concatmap-pdinstance-snd ; concatmap-pdinstance-snd-[]≡[] ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with 
  ) 


import cgp.greedy.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_]  ; pdU-complete ; 
  advance-pdi*-with-c ; 
  pdUMany[_,_]; pdUMany-aux ;
  parseAll[_,_] ; buildU ;
  pdUMany-complete ; buildU-complete ; buildU-sound 
  ) 

import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional.Properties as MembershipProperties
open MembershipProperties using (∈-concat⁺′ ; ∈-concat⁻′ ; ∈-map⁺ ; ∈-map⁻)

import cgp.greedy.Order as Order
open Order -- TODO: we should only whitelist those are used here 

import cgp.greedy.ExtendedOrder as ExtendedOrder
open ExtendedOrder using (
  pdU-sorted ;
  Ex>-sorted ; ex>-nil ; ex>-cons ;
  Ex>-maybe ; ex>-nothing ; ex>-just ;
  _,_⊢_>_ ; >-pdi )

import Data.Char as Char
open Char using (Char ; toℕ )

import Data.Char.Properties as CharProperties
open CharProperties using (≈⇒≡ ; _≈?_ ; ≈-reflexive)

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _+_ ; _∸_ ; _≤_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; _≟_ ; m+n≤o⇒m≤o∸n ; m≤o∸n⇒m+n≤o ; m+n≤o⇒n≤o ; +-identityʳ ; +-identityˡ ; m≤m+n ; m≤n+m ; +-comm ; m+n≡0⇒m≡0 ; m+n≡0⇒n≡0 ; ≡ᵇ⇒≡ ; ≡⇒≡ᵇ )



import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Function as Function
open Function using (case_of_)

import Data.Product as Product
open Product using (Σ; _,_; ∃; ∃-syntax; _×_)
open Σ using (proj₁ ; proj₂)

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; tail; concatMap ; _∷ʳ_ ; length ; foldr )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ; length-++ ; ++-assoc ; ∷-injective ; ≡-dec )


open import Data.List.Relation.Unary.Any using (Any; here; there ; map)

import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)

import Data.List.Membership.Propositional.Properties as MembershipProperties
open MembershipProperties using (∈-concat⁺′ ; ∈-concat⁻′ ; ∈-map⁺ ; ∈-map⁻ ; ∈-++⁻)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst; inspect)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map ; lookup)
import Data.List.Relation.Unary.All.Properties as AllProperties
open AllProperties using (++⁺)

import Relation.Nullary as Nullary
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Data.Empty using (⊥ ; ⊥-elim)
open Data.Empty

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?; map′)

open import Function using (_∘_ ; flip ; case_of_)


import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )


```


```agda

infix 4 _⊢_≥_

-- type alias
_⊢_≥_ : (r : RE) → U r → U r → Set 
_⊢_≥_ r u v = (r ⊢ u > v) ⊎  ( u ≡ v  )



-- Purpose: Define what it means for a parse tree u to be maximal for word w
-- Used by: ≥-max-word, ≥-max-pair→-≥-max-fst, ≥-max-pres-left-helper, >-wellfounded, ≥-Max-PDInstance, parseAll-head-isMax
-- Proof idea: N/A (data type definition with single constructor ≥-max)
data ≥-Max : ∀ { r : RE } → List Char → U r  → Set where 
  ≥-max : ∀ { r : RE }
        → ( w : List Char )
        → ( u : U r )
        → proj₁ (flat u) ≡ w 
        → ( ( v : U r )
          →  proj₁ (flat v) ≡ w 
          → r ⊢ u ≥ v )
        → ≥-Max {r} w u
```



```agda
-- >-wellfounded: every word w ∈⟦ r ⟧ has a ≥-Max parse tree under the GREEDY order.
-- Proof: enumerate all parse trees with parseAll, take their maximum using the total
-- order, and use parseAll-completeness to show every competitor appears in the list.
>-wellfounded : ∀ { r : RE} { w : List Char }
  → w ∈⟦ r ⟧
  → ∃[ v ] ( ≥-Max {r}  w v )
>-wellfounded {r} {w} w∈r = {!!} 

```
