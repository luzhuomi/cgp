```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.RelatedWorkMamouras where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ∷-inj  ;
  w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ ;
  w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ ;
  ¬m>n→n≡m⊎n>m ;
  len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ ; concatmap-λx→[]-xs≡[] ;
  length≡0→[] ; ¬≡[]→¬length≡0)


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;
  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unListU ; listU∘unListU ; 
  unflat∘proj₂∘flat ; flat∘unflat ;
  inv-listU ; inv-listU1 ; inv-pairU ; inv-leftU ; inv-rightU ;
  _⊢_≟_  ; ¬|list-u∷us|≡[] ) 

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ;
  proj₁flat-v≡[]→ε∈r ; flat-[]→flat-[]-left ; flat-[]→flat-[]-right ; mkAllEmptyU≢[]  )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ;
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ;
  concatmap-pdinstance-snd ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with ;
  concatmap-pdinstance-snd-[]≡[] 
  ) 



import cgp.posix.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; -- pdUConcat ;
  pdUMany[_,_]; pdUMany-aux ;
  pdinstance-oplus ; fuse ; mkfuseInj ;  mkfuseInjSoundEv ; 
  advance-pdi*-with-c
  )


import cgp.posix.Order as PosixOrder
open PosixOrder using ( _⊢_>_ ; len-≡ ; len-> ;
  _⊢_>ⁱ_ ; seq₁ ; seq₂ ;
  choice-ll ; choice-rr ;
  choice-lr ;
  choice-rl ; star-head ; star-cons-nil ; star-tail ;
  >→¬≡
  )

import cgp.posix.RelatedWorkCUrban as RelatedWorkCUrban
open RelatedWorkCUrban  using ( _,_⇒_ ; p₁ ; pc ; p+l ; p+r ; ps ; p[] ; p* ; ∈⟦→⇒ ; ∈⟦→⇒*-go ; ∈⟦→⇒●-go ; *-fb ; ∈⟦-+-elim ; ∈⟦-●-elim ; ∈⟦-ε-elim ; ∈⟦-decides ; elim-star ; list≡-decides ; ∈⟦-*-empty-r* ; find-longest-split ; NoShorter ; ∈⟦→⇒-ε ; ∈⟦→⇒-$ ; plus-right-member ; plus-right-∈⟦→⇒ ; ⇒-member ; ⇒→>-max ; >-anti-sym ; >-max→⇒ ; intersect-memberʳ ; >→¬< )

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _>_ ; _≥_ ; _≤_  ; _+_  )

import Data.Nat.Properties as NatProperties
open import Data.Nat using (_<_ ; _≤_ ; zero ; suc ; _+_ ; _∸_ ; s<s ; z<s ; z≤n ; s≤s)
open import Data.Empty using (⊥ ; ⊥-elim)
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; <-cmp ; +-suc ; +-identityʳ )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; tail; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-cancelʳ ; ++-conicalʳ ; ++-conicalˡ ;
  length-++ ; ++-assoc ; ∷-injective
  -- ; length-++-sucʳ -- this is only available after v2.3
  )

open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst; inspect; _≢_)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)

import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)


import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)





```



Mamoura's Definition 1


```agda


infix 4 _,_,_⊨_ 


_!!_ : ∀ {A : Set} →  (List A) → ℕ → Maybe A 
_!!_ {A} []       _       = nothing
_!!_ {A} (x ∷ _)  zero    = just x
_!!_ {A} (x ∷ xs) (suc n) =  xs !! n 

-- the matching relation _,_,_⊨_ from Mamoura's paper definition, we shuffle the order of the parameters
-- r , i , j ⊨ w is a proof of showing the w[i,j] is matched with r.

data _,_,_⊨_ : RE →  ℕ → ℕ → List Char → Set where
  ⊨ε : ∀ ( i : ℕ )
     → ( w : List Char )
     ---------------------
     → ε , i , i ⊨ w 
  ⊨$ : ∀ ( c : Char )
     → ( loc : ℕ )
     → ( i : ℕ )
     → ( w : List Char )
     → w !! i ≡ just c 
     ----------------------
     → ($ c ` loc) , i , (suc i) ⊨ w
  ⊨inl : ∀ ( l r : RE ) ( loc : ℕ )
      → ( i j : ℕ )
      → ( w : List Char )
      → l , i , j ⊨ w
      ---------------------
      → ( l + r ` loc ) , i , j ⊨ w 
     
  ⊨inr : ∀ ( l r : RE ) ( loc : ℕ )
      → ( i j : ℕ )
      → ( w : List Char )
      → r , i , j ⊨ w
      ---------------------
      → ( l + r ` loc ) , i , j ⊨ w 
     

  ⊨● : ∀ ( l r : RE ) ( loc : ℕ )
      → ( i k : ℕ )
      → ( w : List Char )
      → ∃[ j ] ( i Nat.≤ j ) × ( j Nat.≤ k ) × ( l , i , j ⊨ w ) × ( r , j , k ⊨ w )  
      ---------------------
      → ( l ● r ` loc ) , i , k ⊨ w 


  ⊨[] : ∀ ( r : RE ) ( ε∉r : ε∉ r )  -- this ε∉r is not in Maoura's definition
     → ( loc : ℕ )
     → ( w : List Char )
     → ( i : ℕ )
     ----------------------
     → ( r * ε∉r ` loc ) , i , i ⊨ w

  ⊨∷ : ∀ ( r : RE ) ( ε∉r : ε∉ r )  -- this ε∉r is not in Maoura's definition
     → ( loc : ℕ )
     → ( w : List Char )
     → ( i k : ℕ )
     → ∃[ j ] ( i Nat.< j ) × ( j Nat.≤ k ) × ( r , i , j ⊨ w ) × (( r * ε∉r ` loc ) , j , k  ⊨ w )
     ----------------------
     → ( r * ε∉r ` loc ) , i , k ⊨ w 




```

a match set M( w , r ) is a set of pairs ( i , j ) such that there exists an evidence of  r , i , j ⊨ w.

a match set M( w , r , i ) is the set of pairs whose starting index must be i.


In Maoura's Section 2.1 : Disambiguation


> greedy order preference <ʳᵢ  is an order over Match set M(w, r, i), Define 𝑇ᵢ  = {inl[𝑖 , 𝑗] | 𝑤, [𝑖, 𝑗]⊨ 𝑟₁} ∪ {inr[𝑖, 𝑗] | w, [𝑖, 𝑗] ⊨ 𝑟₂ }. The “flattening” function 𝜌𝑖 :𝑇𝑖 → M(w , 𝑟 ) is given by 𝜌𝑖 (inl[𝑖, 𝑗]) = 𝜌𝑖 (inr[𝑖, 𝑗])= [𝑖, 𝑗]. The order 𝑖 on 𝑇𝑖 is generated by the rules:



> Finally, we define [i, j] <ʳᵢ [i, j'] iff min ρ⁻¹ [(i , j)] <ʳᵢ min ρ⁻¹ [(i , j')], where the min operator is
with respect to the linear order i.


So in our implementation  ⊨inl is inl,  ⊨inr is inr 

The <ʳᵢ order is defined over two instances of r , i , j ⊨ w where r, i and w are the same.

In our Agda implementation, we have to include the Tᵢ evidence as part of the <ʳᵢ relation constructor,
so as to construct the min ρ⁻¹ [(i , j)]

```agda


data _,_,_,_,_⊢_<_ : ∀ ( r :  RE ) → ( w : List Char ) → ( i j j' : ℕ ) → ( r , i , j ⊨ w ) → ( r , i , j' ⊨ w ) → Set

data <-Min : ∀ ( r : RE ) → ( w : List Char )  → ( i j : ℕ ) →  ( r , i , j ⊨ w ) → Set


-- is this well-founded, wellfounded is depending on <-Min hahah.. circular definition
data _,_,_,_,_⊢_<_ where
  choice-lr : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j j' : ℕ )
    → ( t₁ : l , i , j  ⊨ w ) -- the evidence of ⊨inl l r loc i j w ∈ Tᵢ 
    → ( t₂ : r , i , j' ⊨ w ) -- the evidence of ⊨inr l r loc i j' w ∈ Tᵢ 
    --------------------------------------------------------- 
    → (l + r ` loc) , w , i , j , j'  ⊢  ( ⊨inl l r loc i j w t₁ ) < ( ⊨inr l r loc i j' w t₂ ) 
  
  choice-ll : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j j' : ℕ )
    → ( t₁ : (l , i , j  ⊨ w) )  
    → ( t₂ : (l , i , j' ⊨ w) )  
    → <-Min l w i j t₁  -- t₁ must be the min
    → <-Min l w i j' t₂ -- t₂ must be the min
    → ( l , w , i , j , j' ⊢ t₁ < t₂ )
    -----------------------------------------------------------------
    → (l + r ` loc) , w , i , j , j' ⊢ ( ⊨inl l r loc i j w t₁ ) < ( ⊨inl l r loc i j' w t₂ ) 


  choice-rr : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j j' : ℕ )
    → ( t₁ : (r , i , j  ⊨ w) )
    → ( t₂ : (r , i , j' ⊨ w ) )
    → <-Min r w i j t₁ 
    → <-Min r w i j' t₂ 
    → ( r , w , i , j , j' ⊢ t₁ < t₂ )
    -----------------------------------------------------------------
    → (l + r ` loc) , w , i , j , j' ⊢ ( ⊨inr l r loc i j w t₁ ) < ( ⊨inr l r loc i j' w t₂ )

  seq₁ : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j j' k k' : ℕ )
    → ( i≤j : i Nat.≤ j )
    → ( j≤k : j Nat.≤ k )
    → ( i≤j' : i Nat.≤ j' )
    → ( j'≤k' : j' Nat.≤ k' )
    → ( t₁ : ( l , i , j ⊨ w ) )
    → ( t₂ : ( r , j , k ⊨ w ) )
    → ( t₁' : ( l , i , j' ⊨ w ) )
    → ( t₂' : ( r , j' , k' ⊨ w ) )
    → <-Min l w i j t₁
    → <-Min l w i j' t₁' 
    → l , w , i , j , j' ⊢ t₁ < t₁' 
    -----------------------------------------------------------------------
    → (l ● r ` loc) , w , i , k , k' ⊢ (⊨● l r loc i k w ( j , i≤j , j≤k , t₁ , t₂ )) < ( ⊨● l r loc i k' w ( j' , i≤j' , j'≤k' , t₁' , t₂' ) )


  seq₂ : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j k k' : ℕ )
    → ( i≤j : i Nat.≤ j )
    → ( j≤k : j Nat.≤ k )
    → ( j≤k' : j Nat.≤ k' )
    → ( t₁ : ( l , i , j ⊨ w ) )
    → ( t₂ : ( r , j , k ⊨ w ) )
    → ( t₂' : ( r , j , k' ⊨ w ) )
    → <-Min r w j k t₂
    → <-Min r w j k' t₂' 
    → r , w , j , k , k' ⊢ t₂ < t₂' 
    -----------------------------------------------------------------------
    → (l ● r ` loc) , w , i , k , k' ⊢ (⊨● l r loc i k w ( j , i≤j , j≤k , t₁ , t₂ )) < ( ⊨● l r loc i k' w ( j , i≤j , j≤k' , t₁ , t₂' ) )


  star-cons-nil : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { w : List Char }
    → ( i j k : ℕ )
    → ( i<j : i Nat.< j )
    → ( j≤k : j Nat.≤ k )
    → ( t₁ : ( r , i , j ⊨ w ) )
    → ( t₂ : ( r * ε∉r ` loc , j , k ⊨ w ) )
    -----------------------------------------------------------------------
    → ( r * ε∉r ` loc ) , w , i , k , i ⊢ (⊨∷ r  ε∉r loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) < (⊨[] r ε∉r loc w i) 

  star-head : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { w : List Char }
    → ( i j j' k k' : ℕ )
    → ( i<j : i < j )
    → ( j≤k : j Nat.≤ k )
    → ( i<j' : i Nat.< j' )
    → ( j'≤k' : j' Nat.≤ k' )
    → ( t₁ : ( r , i , j ⊨ w ) )
    → ( t₂ : ( r * ε∉r ` loc , j , k ⊨ w ) )
    → ( t₁' : ( r , i , j' ⊨ w ) )
    → ( t₂' : ( r * ε∉r ` loc , j' , k' ⊨ w ) )
    → <-Min r w i j t₁
    → <-Min r w i j' t₁' 
    → r , w , i , j , j' ⊢ t₁ < t₁' 
    -----------------------------------------------------------------------
    → ( r * ε∉r ` loc ) , w , i , k , k' ⊢  (⊨∷ r  ε∉r loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) <  (⊨∷ r  ε∉r loc w i k' ( j' , i<j' , j'≤k' , t₁' , t₂' ) )


  star-tail : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { w : List Char }
    → ( i j k k' : ℕ )
    → ( i<j : i < j )
    → ( j≤k : j Nat.≤ k )
    → ( j≤k' : j Nat.≤ k' )
    → ( t₁ : ( r , i , j ⊨ w ) )
    → ( t₂ : ( r * ε∉r ` loc , j , k ⊨ w ) )
    → ( t₂' : ( r * ε∉r ` loc , j , k' ⊨ w ) )
    → <-Min ( r * ε∉r ` loc) w j k t₂
    → <-Min ( r * ε∉r ` loc) w j k' t₂' 
    → ( r * ε∉r ` loc) , w , j , k , k' ⊢ t₂ < t₂' 
    -----------------------------------------------------------------------
    → ( r * ε∉r ` loc ) , w , i , k , k' ⊢  (⊨∷ r  ε∉r loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) <  (⊨∷ r  ε∉r loc w i k' ( j , i<j , j≤k' , t₁ , t₂' ) )



    
data <-Min where
  <-min : ∀ ( r : RE )
    → ( w : List Char )
    → ( i j : ℕ )
    → ( t₁ : (r , i , j  ⊨ w) ) 
    → ( ( t₂ : (r , i , j  ⊨ w) )
      → ( r , w , i , j , j ⊢ t₁ < t₂ ) ⊎ (t₁ ≡ t₂) 
      )
    → <-Min r w i j t₁ 
      


>-wellfounded : ∀ { r : RE} { w : List Char } { i j : ℕ } 
  → r , i , j ⊨ w 
  → ∃[ t ] ( <-Min r w i j t )
>-wellfounded {r} {w} {i} {j} = {!!} 

```



