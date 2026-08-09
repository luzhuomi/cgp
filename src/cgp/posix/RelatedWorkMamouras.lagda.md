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
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; tail; concatMap ; _∷ʳ_ ; length ; take ; drop )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-cancelʳ ; ++-conicalʳ ; ++-conicalˡ ;
  length-++ ; ++-assoc ; ∷-injective
  -- ; length-++-sucʳ -- this is only available after v2.3
  )

open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst; subst₂; inspect; _≢_)

open import Relation.Nullary using (¬_)
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


postulate
  find-<-Min : ∀ ( r : RE ) ( w : List Char ) ( i j : ℕ )
    → r , i , j ⊨ w 
    → ∃[ t ] ( <-Min r w i j t )


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
    → l , w , i , j , j' ⊢ proj₁ ( find-<-Min l w i j t₁ ) < proj₁ ( find-<-Min l w i j' t₂) 
    -----------------------------------------------------------------
    → (l + r ` loc) , w , i , j , j' ⊢ ( ⊨inl l r loc i j w t₁ ) < ( ⊨inl l r loc i j' w t₂ ) 


  choice-rr : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j j' : ℕ )
    → ( t₁ : (r , i , j  ⊨ w) )
    → ( t₂ : (r , i , j' ⊨ w ) )
    → r , w , i , j , j' ⊢ proj₁ ( find-<-Min r w i j t₁ ) < proj₁ ( find-<-Min r w i j' t₂)     
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
    → l , w , i , j , j' ⊢ proj₁ ( find-<-Min l w i j t₁ ) < proj₁ ( find-<-Min l w i j' t₁')     
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
    → r , w , j , k , k' ⊢ proj₁ ( find-<-Min r w j k t₂ ) < proj₁ ( find-<-Min r w j k' t₂')         
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
    → r , w , i , j , j' ⊢ proj₁ ( find-<-Min r w i j t₁ ) < proj₁ ( find-<-Min r w i j' t₁')         
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
    → (r * ε∉r ` loc) , w , j , k , k' ⊢ proj₁ ( find-<-Min (r * ε∉r ` loc) w j k t₂ ) < proj₁ ( find-<-Min (r * ε∉r ` loc) w j k' t₂')         
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



  
-- K is available (no --without-K), so equality proofs are unique.
UIP-≡ : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
UIP-≡ refl refl = refl


-- The current definition of the order makes find-<-Min impossible to define.
-- The counterexample below shows that assuming such a function leads to a contradiction.

-- The lemma find-<-Min is unprovable.  The definition of <-Min requires
-- both sub-terms to be minimal before the order can lift through a plus/seq/star
-- constructor.  This creates incomparable evidences, so a match need not have a
-- <-Min witness.
--
-- Counterexample: r = (a + a) + a over w = [a], i = 0, j = 1.
-- There are three evidences:
--   P1 = left (left a)
--   P2 = left (right a)
--   P3 = right a
-- P1 and P2 are incomparable because comparing two outer-left proofs requires
-- comparing the minima of L1 and L2, both of which are L1, yielding L1 < L1.
-- Hence no evidence is <-Min.

counterexample : (∀ {r : RE} {w : List Char} {i j : ℕ}
                   → (t : r , i , j ⊨ w)
                   → ∃[ t' ] (<-Min r w i j t'))
                 → ⊥
counterexample wellfounded = contradiction (proj₁ (wellfounded P1)) (proj₂ (wellfounded P1))
  where
    a0 : RE
    a0 = $ 'a' ` 0

    a1 : RE
    a1 = $ 'a' ` 1

    a2 : RE
    a2 = $ 'a' ` 3

    l : RE
    l = a0 + a1 ` 2

    r : RE
    r = l + a2 ` 4

    w : List Char
    w = 'a' ∷ []

    i : ℕ
    i = 0

    j : ℕ
    j = 1

    t$0 : a0 , i , j ⊨ w
    t$0 = ⊨$ 'a' 0 i w refl

    L1 : l , i , j ⊨ w
    L1 = ⊨inl a0 a1 2 i j w t$0

    t$1 : a1 , i , j ⊨ w
    t$1 = ⊨$ 'a' 1 i w refl

    L2 : l , i , j ⊨ w
    L2 = ⊨inr a0 a1 2 i j w t$1

    t$2 : a2 , i , j ⊨ w
    t$2 = ⊨$ 'a' 3 i w refl

    P1 : r , i , j ⊨ w
    P1 = ⊨inl l a2 4 i j w L1

    P2 : r , i , j ⊨ w
    P2 = ⊨inl l a2 4 i j w L2

    P3 : r , i , j ⊨ w
    P3 = ⊨inr l a2 4 i j w t$2

    -- uniqueness of atomic evidences
    $-evidence-unique : ∀ {c loc w i j} (t t' : ($ c ` loc) , i , j ⊨ w) → t ≡ t'
    $-evidence-unique (⊨$ c loc i w eq) (⊨$ .c .loc .i .w eq') =
      cong (λ p → ⊨$ c loc i w p) (UIP-≡ eq eq')

    find-<-Min-$-returns-t : ∀ {c loc w i j} (t : ($ c ` loc) , i , j ⊨ w)
      → proj₁ (find-<-Min ($ c ` loc) w i j t) ≡ t
    find-<-Min-$-returns-t {c} {loc} {w} {i} {j} t = $-evidence-unique (proj₁ (find-<-Min ($ c ` loc) w i j t)) t

    t$0-unique : (t : a0 , i , j ⊨ w) → t ≡ t$0
    t$0-unique t = $-evidence-unique t t$0

    t$1-unique : (t : a1 , i , j ⊨ w) → t ≡ t$1
    t$1-unique t = $-evidence-unique t t$1

    t$2-unique : (t : a2 , i , j ⊨ w) → t ≡ t$2
    t$2-unique t = $-evidence-unique t t$2

    -- every evidence of l is either L1 or L2
    l-evidence : (t : l , i , j ⊨ w) → t ≡ L1 ⊎ t ≡ L2
    l-evidence (⊨inl .a0 .a1 .2 .i .j .w t') = inj₁ (cong (λ z → ⊨inl a0 a1 2 i j w z) (t$0-unique t'))
    l-evidence (⊨inr .a0 .a1 .2 .i .j .w t') = inj₂ (cong (λ z → ⊨inr a0 a1 2 i j w z) (t$1-unique t'))

    -- every evidence of r is either P1, P2, or P3
    r-evidence : (t : r , i , j ⊨ w) → t ≡ P1 ⊎ t ≡ P2 ⊎ t ≡ P3
    r-evidence (⊨inl .l .a2 .4 .i .j .w t')
      with l-evidence t'
    ... | inj₁ t'≡L1 = inj₁ (cong (λ z → ⊨inl l a2 4 i j w z) t'≡L1)
    ... | inj₂ t'≡L2 = inj₂ (inj₁ (cong (λ z → ⊨inl l a2 4 i j w z) t'≡L2))
    r-evidence (⊨inr .l .a2 .4 .i .j .w t') = inj₂ (inj₂ (cong (λ z → ⊨inr l a2 4 i j w z) (t$2-unique t')))

    -- no atomic evidence is less than itself
    ¬t$0<t$0 : ¬ (a0 , w , i , j , j ⊢ t$0 < t$0)
    ¬t$0<t$0 ()

    ¬t$1<t$1 : ¬ (a1 , w , i , j , j ⊢ t$1 < t$1)
    ¬t$1<t$1 ()

    -- L2 is not less than L1 (no constructor gives inr < inl)
    ¬L2<L1 : ¬ (l , w , i , j , j ⊢ L2 < L1)
    ¬L2<L1 ()

    -- L1 is not less than itself: any proof would use choice-ll, whose premise
    -- reduces to t$0 < t$0, which is impossible.
    ¬L1<L1 : ¬ (l , w , i , j , j ⊢ L1 < L1)
    ¬L1<L1 (choice-ll i j j .t$0 .t$0 L1<L1-premise)
      rewrite find-<-Min-$-returns-t t$0
      = ¬t$0<t$0 L1<L1-premise

    -- L2 is not less than itself: any proof would use choice-rr, whose premise
    -- reduces to t$1 < t$1, which is impossible.
    ¬L2<L2 : ¬ (l , w , i , j , j ⊢ L2 < L2)
    ¬L2<L2 (choice-rr i j j .t$1 .t$1 L2<L2-premise)
      rewrite find-<-Min-$-returns-t t$1
      = ¬t$1<t$1 L2<L2-premise

    -- find-<-Min on l always returns L1, because L1 is the unique minimal evidence
    find-<-Min-l-returns-L1 : (t : l , i , j ⊨ w)
      → proj₁ (find-<-Min l w i j t) ≡ L1
    find-<-Min-l-returns-L1 t
      with find-<-Min l w i j t
    ... | M , <-min .l .w .i .j .M minM
      with minM L2 | l-evidence M
    ... | inj₁ M<L2 | inj₁ M≡L1 = M≡L1
    ... | inj₁ M<L2 | inj₂ M≡L2 = ⊥-elim (¬L2<L2 (subst₂ (λ x y → l , w , i , j , j ⊢ x < y) M≡L2 (refl {x = L2}) M<L2))
    ... | inj₂ M≡L2 | _ = ⊥-elim (¬L2-min M≡L2 (<-min l w i j M minM))
      where
        L2≢L1 : ¬ (L2 ≡ L1)
        L2≢L1 ()

        ¬L2-min : M ≡ L2 → ¬ (<-Min l w i j M)
        ¬L2-min M≡L2 (<-min .l .w .i .j .M minM')
          with minM' L1
        ... | inj₁ M<L1 = ¬L2<L1 (subst₂ (λ x y → l , w , i , j , j ⊢ x < y) M≡L2 (refl {x = L1}) M<L1)
        ... | inj₂ M≡L1 = L2≢L1 (trans (sym M≡L2) M≡L1)

    -- P1 is not less than P2
    ¬P1<P2 : ¬ (r , w , i , j , j ⊢ P1 < P2)
    ¬P1<P2 (choice-ll i j j .L1 .L2 prem)
      rewrite find-<-Min-l-returns-L1 L1 | find-<-Min-l-returns-L1 L2
      = ¬L1<L1 prem

    -- P2 is not less than P1
    ¬P2<P1 : ¬ (r , w , i , j , j ⊢ P2 < P1)
    ¬P2<P1 (choice-ll i j j .L2 .L1 prem)
      rewrite find-<-Min-l-returns-L1 L2 | find-<-Min-l-returns-L1 L1
      = ¬L1<L1 prem

    -- P3 is not less than P1
    ¬P3<P1 : ¬ (r , w , i , j , j ⊢ P3 < P1)
    ¬P3<P1 ()

    inl-inj : {t₁ t₂ : l , i , j ⊨ w}
            → ⊨inl l a2 4 i j w t₁ ≡ ⊨inl l a2 4 i j w t₂
            → t₁ ≡ t₂
    inl-inj refl = refl

    P1≢P2 : ¬ (P1 ≡ P2)
    P1≢P2 P1≡P2 = L1≢L2 (inl-inj P1≡P2)
      where
        L1≢L2 : ¬ (L1 ≡ L2)
        L1≢L2 ()

    P3≢P1 : ¬ (P3 ≡ P1)
    P3≢P1 ()

    -- no evidence of r is minimal
    ¬Min-P1 : ¬ (<-Min r w i j P1)
    ¬Min-P1 (<-min .r .w .i .j .P1 minP1)
      with minP1 P2
    ... | inj₁ P1<P2 = ¬P1<P2 P1<P2
    ... | inj₂ P1≡P2 = P1≢P2 P1≡P2

    ¬Min-P2 : ¬ (<-Min r w i j P2)
    ¬Min-P2 (<-min .r .w .i .j .P2 minP2)
      with minP2 P1
    ... | inj₁ P2<P1 = ¬P2<P1 P2<P1
    ... | inj₂ P2≡P1 = P1≢P2 (sym P2≡P1)

    ¬Min-P3 : ¬ (<-Min r w i j P3)
    ¬Min-P3 (<-min .r .w .i .j .P3 minP3)
      with minP3 P1
    ... | inj₁ P3<P1 = ¬P3<P1 P3<P1
    ... | inj₂ P3≡P1 = P3≢P1 P3≡P1

    contradiction : (t : r , i , j ⊨ w) → ¬ (<-Min r w i j t)
    contradiction t min
      with r-evidence t
    ... | inj₁ t≡P1 = ¬Min-P1 (subst (<-Min r w i j) t≡P1 min)
    ... | inj₂ (inj₁ t≡P2) = ¬Min-P2 (subst (<-Min r w i j) t≡P2 min)
    ... | inj₂ (inj₂ t≡P3) = ¬Min-P3 (subst (<-Min r w i j) t≡P3 min)

```



