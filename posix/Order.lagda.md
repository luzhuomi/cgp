```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.Order where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat {- ; ¬≡[]→¬length≡0 ; ¬≡0→>0 ; []→length≡0  ; ¬0>0 -}  )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ) 

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ; proj₁flat-v≡[]→ε∈r )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ) 


{-
import cgp.lne.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; pdUConcat ;
  -- PDInstance ; pdinstance ;
  pdinstance-left ; pdinstance-right;  pdinstance-fst ; mkinjFst ;  pdinstance-snd ; zip-es-flat-[]-es;   mk-snd-pdi ; mkinjSnd ; compose-pdi-with;  advance-pdi*-with-c ; concatmap-pdinstance-snd; pdinstance-star ; mkinjList ; pdinstance-assoc ; mkinjAssoc ; pdUMany[_,_]; pdUMany-aux ) 
-- ;   PDInstance* ; pdinstance*  ) 
-} 

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _>_ )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map)

import Relation.Nullary as Nullary 
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

open import Function using (_∘_ ; flip)

```



### Definition : POSIX ordering among parse trees




```agda
infix 4 _⊢_>_


data _⊢_>_ : ∀ ( r : RE ) → U r → U r → Set where
  seq₁ : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U  l } { v₂ v₂' : U r }
    →   l ⊢ v₁ >  v₁'   
    ------------------------------------------------------------------
    →   l  ● r ` loc ⊢ PairU v₁ v₂ > PairU v₁' v₂'

  seq₂ : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U l } { v₂ v₂' : U r }
    → v₁ ≡ v₁'
    → r ⊢ v₂ > v₂'
    -------------------------------------------------------------------
    →  ( l ● r ` loc) ⊢ (PairU v₁ v₂) > (PairU v₁' v₂')

  choice-lr : ∀ { l r : RE } { loc : ℕ } { v₁ : U l } { v₂ : U r }
    → length (proj₁ (flat v₁)) > length (proj₁ (flat v₂))
    -------------------------------------------------------------------    
    → ( l + r ` loc ) ⊢ (LeftU v₁) > (RightU v₂)


  choice-rl : ∀ { l r : RE } { loc : ℕ } { v₁ : U r } { v₂ : U l }
    → length (proj₁ (flat v₁)) > length (proj₁ (flat v₂))
    -------------------------------------------------------------------    
    → ( l + r ` loc ) ⊢ (RightU v₁) > (LeftU v₂)

  choice-ll : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U l }
    →  l ⊢ v₁ >  v₁'
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (LeftU v₁) > (LeftU v₁')

  choice-rr : ∀ { l r : RE } { loc : ℕ } { v₂ v₂'  : U r }
    →  r ⊢ v₂ >  v₂'
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (RightU v₂) > (RightU v₂')


  star-cons-nil : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v : U r } { vs : List (U r) }
    → ( r * nε ` loc ) ⊢ (ListU (v ∷ vs)) > ( ListU [] )
    

  star-head : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v₁ v₂ : U r } { vs₁ vs₂ : List (U r) }
    → r ⊢ v₁ > v₂
    ----------------------------------------------------------------------
    → ( r * nε ` loc ) ⊢ (ListU (v₁ ∷ vs₁)) > (ListU (v₂ ∷ vs₂))


  star-tail : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v₁ v₂ : U r } { vs₁ vs₂ : List (U r) }
    → v₁ ≡ v₂
    → ( r * nε ` loc ) ⊢ (ListU vs₁) > (ListU vs₂)
    ----------------------------------------------------------------------
    → ( r * nε ` loc ) ⊢ (ListU (v₁ ∷ vs₁)) > (ListU (v₂ ∷ vs₂))


```
