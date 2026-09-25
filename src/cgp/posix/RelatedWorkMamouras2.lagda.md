```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.RelatedWorkMamouras2 where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ∷-inj  ;
  w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ ;
  w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ ;
  ¬m>n→n≡m⊎n>m ;
  len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ ; concatmap-λx→[]-xs≡[] ;
  length≡0→[] ; ¬≡[]→¬length≡0 ;
  dec-elim ; maybe-just-≟ ; n∸0≡n ; dec-∃-range ;
  +-1≡suc ; suc-∸-1 ; ∸-suc-≤ ; ∸-step-≤)


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
open import Data.Nat using (_<_ ; _≤_ ; _≟_ ; _≤?_ ; zero ; suc ; _+_ ; _∸_ ; s<s ; z<s ; z≤n ; s≤s)
open import Data.Empty using (⊥ ; ⊥-elim)
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; <-cmp ; +-suc ; +-identityʳ ;
  ≤-antisym ; m∸n≡0⇒m≤n ; n≤1+n )

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




import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; _×-dec_ )

```



Mamouras's Definition 1


```agda


infix 4 _,_,_⊨_ 


_!!_ : ∀ {A : Set} →  (List A) → ℕ → Maybe A 
_!!_ {A} []       _       = nothing
_!!_ {A} (x ∷ _)  zero    = just x
_!!_ {A} (x ∷ xs) (suc n) =  xs !! n 

-- the matching relation _,_,_⊨_ from Mamoura's paper definition w , [i , j] ⊨ r,
-- we shuffle the order of the parameters to r , i , j ⊨ w
-- is a proof of showing the w[i,j] is matched with r.

-- NOTE: The index bounds in ⊨● (i ≤ j and j ≤ k) and in ⊨∷ (i < j and j ≤ k)
-- are derivable from the sub-match evidences via rij⊨w→i≤j.  They are kept as
-- explicit fields because they are convenient for the proofs below; removing
-- them would require a wider refactor of every ⊨●/⊨∷ pattern match and
-- construction in this file.

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


  ⊨[] : ∀ ( r : RE ) ( ε∉r : ε∉ r )  -- this ε∉r is not in Mamouras's definition
     → ( loc : ℕ )
     → ( w : List Char )
     → ( i : ℕ )
     ----------------------
     → ( r * ε∉r ` loc ) , i , i ⊨ w

  ⊨∷ : ∀ ( r : RE ) ( ε∉r : ε∉ r )  -- this ε∉r is not in Mamouras's definition
     → ( loc : ℕ )
     → ( w : List Char )
     → ( i k : ℕ )
     → ∃[ j ] ( i Nat.< j ) × ( j Nat.≤ k ) × ( r , i , j ⊨ w ) × (( r * ε∉r ` loc ) , j , k  ⊨ w )
     ----------------------
     → ( r * ε∉r ` loc ) , i , k ⊨ w 



-- Decides ( r * nε ` loc ) , i , k ⊨ w by induction on an upper bound d of
-- the span k ∸ i.  The induction hypothesis covers all pairs with span
-- ≤ d - 1, which is exactly what the ⊨∷ rule needs: it keeps the end index
-- k but moves the start index strictly forward.  The decision procedure for
-- the sub-expression r is passed as an argument.
star-dec : ( r : RE ) → ( nε : ε∉ r ) → ( loc : ℕ ) → ( d : ℕ )
  → ( i k : ℕ ) → ( k ∸ i ≤ d ) → ( w : List Char )
  → ( dec-r : ( i j : ℕ ) → Dec ( r , i , j ⊨ w ) )
  → Dec ( ( r * nε ` loc ) , i , k ⊨ w )
star-dec r nε loc zero i k h w dec-r with k ≟ i
... | yes k≡i rewrite k≡i = yes ( ⊨[] r nε loc w i )
... | no  k≢i = no ( no-match )
  where
    no-match : ( r * nε ` loc ) , i , k ⊨ w → ⊥
    no-match ( ⊨[] _ _ _ _ _ ) = k≢i refl
    no-match ( ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤k , _ , _ ) ) =
      <-irrefl refl ( ≤-trans ( ≤-trans i<j j≤k ) ( m∸n≡0⇒m≤n ( ≤-antisym h z≤n ) ) )
star-dec r nε loc ( suc d' ) i k h w dec-r with k ≤? i
... | no  k≰i =
    dec-elim ( dec-∃-range ( suc i ) k ( λ j → ( r , i , j ⊨ w ) × ( ( r * nε ` loc ) , j , k ⊨ w ) ) dec-j )
      ( λ ( j , j≥ , j≤k , ( t₁ , t₂ ) ) → yes ( ⊨∷ r nε loc w i k ( j , j≥ , j≤k , t₁ , t₂ ) ) )
      ( λ n → no ( λ t → no-match n t ) )
    where
      dec-j : ( j : ℕ ) → ( suc i ≤ j ) → ( j ≤ k )
        → Dec ( ( r , i , j ⊨ w ) × ( ( r * nε ` loc ) , j , k ⊨ w ) )
      dec-j j j≥ j≤k with dec-r i j
      ... | no  ¬t₁ = no λ { ( t₁ , _ ) → ¬t₁ t₁ }
      ... | yes t₁ with star-dec r nε loc d' j k ( ∸-step-≤ i j k d' j≥ j≤k h ) w dec-r
      ... | yes t₂ = yes ( t₁ , t₂ )
      ... | no  ¬t₂ = no λ { ( _ , t₂ ) → ¬t₂ t₂ }

      no-match : ( n : ¬ ( ∃[ j ] suc i ≤ j × j ≤ k × ( ( r , i , j ⊨ w ) × ( ( r * nε ` loc ) , j , k ⊨ w ) ) ) )
        → ( ( r * nε ` loc ) , i , k ⊨ w ) → ⊥
      no-match n ( ⊨[] _ _ _ _ _ ) = k≰i ≤-refl
      no-match n ( ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤k , t₁ , t₂ ) ) =
        n ( j , i<j , j≤k , ( t₁ , t₂ ) )
... | yes k≤i with k ≟ i
... | yes k≡i rewrite k≡i = yes ( ⊨[] r nε loc w i )
... | no  k≢i = no ( no-match )
  where
    no-match : ( r * nε ` loc ) , i , k ⊨ w → ⊥
    no-match ( ⊨[] _ _ _ _ _ ) = k≢i refl
    no-match ( ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤k , _ , _ ) ) =
      <-irrefl refl ( ≤-trans ( ≤-trans i<j j≤k ) k≤i )

-- From evidence of ( $ c ` loc ) , i , j ⊨ w extract w !! i ≡ just c.
no-$-eq : ( c : Char ) → ( loc i j : ℕ ) → ( w : List Char )
  → ( w !! i ≡ just c → ⊥ ) → ( ( $ c ` loc ) , i , j ⊨ w ) → ⊥
no-$-eq c loc i j w ¬eq t with t
... | ⊨$ _ _ _ _ eq = ¬eq eq

⊨? : ∀ ( r : RE ) → ( i : ℕ ) → ( j : ℕ ) → ( w : List Char ) → Dec ( r , i , j ⊨ w )
⊨? ε i j w with i ≟ j
... | no  i≢j = no ( no-ε )
  where
    no-ε : ( ε , i , j ⊨ w ) → ⊥
    no-ε t with t
    ... | ⊨ε _ _ = i≢j refl
... | yes i≡j rewrite sym i≡j = yes ( ⊨ε i w )
⊨? ( $ c ` loc ) i j w with j ≟ suc i
... | no  j≢suc-i = no ( no-$ )
  where
    no-$ : ( ( $ c ` loc ) , i , j ⊨ w ) → ⊥
    no-$ t with t
    ... | ⊨$ _ _ _ _ _ = j≢suc-i refl
... | yes j≡suc-i with maybe-just-≟ ( w !! i ) c
... | no  ¬eq = no ( no-$-eq c loc i j w ¬eq )
... | yes eq  = yes ( subst ( λ x → ( $ c ` loc ) , i , x ⊨ w ) ( sym j≡suc-i ) ( ⊨$ c loc i w eq ) )
⊨? ( l + r ` loc ) i j w with ⊨? l i j w
... | yes l⊨w = yes ( ⊨inl l r loc i j w l⊨w )
... | no  ¬l⊨w with ⊨? r i j w
... | yes r⊨w = yes ( ⊨inr l r loc i j w r⊨w )
... | no  ¬r⊨w = no ( no-+ )
  where
    no-+ : ( ( l + r ` loc ) , i , j ⊨ w ) → ⊥
    no-+ t with t
    ... | ⊨inl .l .r .loc .i .j .w t' = ¬l⊨w t'
    ... | ⊨inr .l .r .loc .i .j .w t' = ¬r⊨w t'
⊨? ( l ● r ` loc ) i k w =
  dec-elim ( i ≤? k )
    ( λ i≤k → dec-elim ( dec-∃-range i k ( λ j → ( l , i , j ⊨ w ) × ( r , j , k ⊨ w ) ) dec-j )
        ( λ ( j , i≤j , j≤k , ( t₁ , t₂ ) ) → yes ( ⊨● l r loc i k w ( j , i≤j , j≤k , t₁ , t₂ ) ) )
        ( λ n → no ( λ t → no-match n t ) ) )
    ( λ i≰k → no ( λ t → no-match-i≰k i≰k t ) )
  where
    dec-j : ( j : ℕ ) → ( i ≤ j ) → ( j ≤ k )
      → Dec ( ( l , i , j ⊨ w ) × ( r , j , k ⊨ w ) )
    dec-j j i≤j j≤k with ⊨? l i j w
    ... | no  ¬t₁ = no λ { ( t₁ , _ ) → ¬t₁ t₁ }
    ... | yes t₁ with ⊨? r j k w
    ... | no  ¬t₂ = no λ { ( _ , t₂ ) → ¬t₂ t₂ }
    ... | yes t₂ = yes ( t₁ , t₂ )

    no-match-i≰k : ( i≰k : ¬ ( i ≤ k ) ) → ( l ● r ` loc ) , i , k ⊨ w → ⊥
    no-match-i≰k i≰k ( ⊨● _ _ _ _ _ _ ( j , i≤j , j≤k , _ , _ ) ) = i≰k ( ≤-trans i≤j j≤k )

    no-match : ( n : ¬ ( ∃[ j ] i ≤ j × j ≤ k × ( ( l , i , j ⊨ w ) × ( r , j , k ⊨ w ) ) ) )
      → ( l ● r ` loc ) , i , k ⊨ w → ⊥
    no-match n ( ⊨● _ _ _ _ _ _ ( j , i≤j , j≤k , t₁ , t₂ ) ) = n ( j , i≤j , j≤k , ( t₁ , t₂ ) )
⊨? ( r * nε ` loc ) i k w = star-dec r nε loc ( k ∸ i ) i k ≤-refl w ( λ i' j' → ⊨? r i' j' w )



rij⊨w→i≤j : ∀ { r : RE } { i j : ℕ } { w : List Char }
           → r , i , j ⊨ w
           → i Nat.≤ j
rij⊨w→i≤j ( ⊨ε i w ) = ≤-refl
rij⊨w→i≤j ( ⊨$ c loc i w eq ) = n≤1+n i
rij⊨w→i≤j ( ⊨inl l r loc i j w t ) = rij⊨w→i≤j t
rij⊨w→i≤j ( ⊨inr l r loc i j w t ) = rij⊨w→i≤j t
rij⊨w→i≤j ( ⊨● l r loc i k w ( j , i≤j , j≤k , t₁ , t₂ ) ) = ≤-trans i≤j j≤k
rij⊨w→i≤j ( ⊨[] r ε∉r loc w i ) = ≤-refl
rij⊨w→i≤j ( ⊨∷ r ε∉r loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) = ≤-trans ( <⇒≤ i<j ) j≤k

```





a match set M( w , r ) is a set of pairs ( i , j ) such that there exists an evidence of  r , i , j ⊨ w.

a match set M( w , r , i ) is the set of pairs whose starting index must be i.


In Mamouras's Section 2.1 : Disambiguation


> greedy order preference <ʳᵢ  is an order over Match set M(w, r, i), Define 𝑇ᵢ  = {inl[𝑖 , 𝑗] | 𝑤, [𝑖, 𝑗]⊨ 𝑟₁} ∪ {inr[𝑖, 𝑗] | w, [𝑖, 𝑗] ⊨ 𝑟₂ }. The “flattening” function 𝜌𝑖 :𝑇𝑖 → M(w , 𝑟 ) is given by 𝜌𝑖 (inl[𝑖, 𝑗]) = 𝜌𝑖 (inr[𝑖, 𝑗])= [𝑖, 𝑗]. The order 𝑖 on 𝑇𝑖 is generated by the rules:



> Finally, we define [i, j] <ʳᵢ [i, j'] iff min ρ⁻¹ [(i , j)] <ʳᵢ min ρ⁻¹ [(i , j')], where the min operator is
with respect to the linear order i.


So in our implementation  ⊨inl is inl,  ⊨inr is inr 

The <ʳᵢ order is defined over two instances of r , i , j ⊨ w where r, i and w are the same.

In our Agda implementation, we have to include the Tᵢ evidence as part of the <ʳᵢ relation constructor,
so as to construct the min ρ⁻¹ [(i , j)]


the <-Min and find-<-Min+ (which is min ρ⁻¹ ( . ) function from Marmouras' paper.) has to be divided into
multiple definitions per regex operator, e.g. one for +, another one for ●, another one for *


Their order don't differentiate parse trees, e.g. for r = (a + a) + a, w = 'a'
they treat Left (Left 'a') the sane as Left (Right 'a') w.r.t to the above because both has the same
match set value [0,1].

```agda
-- [i , j] <ᵢʳ [i , j']

-- we do not index this order over ( r , i , j ⊨ w ) and  ( r , i , j' ⊨ w )
infix 4 _,_,_⊢_<_

data _,_,_⊢_<_ : ∀ ( r :  RE ) → ( w : List Char ) → ( i : ℕ ) → ( j : ℕ ) → ( j' : ℕ )  → Set 


infix 4 _,_,_,_,_,_,_⊢⁺_<_

-- we index this order over ( r , i , j ⊨ w ) and  ( r , i , j' ⊨ w ) 
data _,_,_,_,_,_,_⊢⁺_<_ : ∀ ( l r : RE ) → ( loc : ℕ ) → ( w : List Char ) → ( i j j' : ℕ ) →  ( l + r ` loc , i , j ⊨ w ) → ( l + r ` loc , i , j' ⊨ w ) → Set

infix 4 _,_,_,_,_,_,_⊢●_<_

data _,_,_,_,_,_,_⊢●_<_ : ∀ ( l r : RE ) → ( loc : ℕ ) → ( w : List Char ) → ( i k k'  : ℕ ) →  ( l ● r ` loc , i , k ⊨ w ) → ( l ● r ` loc , i , k' ⊨ w ) → Set



data <-Min⁺ : ∀ ( l r : RE ) → ( loc : ℕ ) → ( w : List Char )  → ( i j : ℕ ) →  ( l + r ` loc , i , j ⊨ w ) → Set where 
  <-min-l : ∀ ( l r : RE ) ( loc : ℕ )
    → ( w : List Char )
    → ( i j : ℕ )
    → ( t₁ : ( l , i , j  ⊨ w) )
    → <-Min⁺ l r loc w i j ( ⊨inl l r loc i j  w t₁ )  --  ⊨inl is the min of +
  <-min-r : ∀ ( l r : RE ) ( loc : ℕ )
    → ( w : List Char )
    → ( i j : ℕ )
    → ¬  ( l , i , j ⊨ w )
    → ( t₂ : (r , i , j ⊨ w ) )
    → <-Min⁺ l r loc w i j ( ⊨inr l r loc i j  w t₂ )  --  ⊨inr is the min of +



find-<-Min⁺ : ∀ ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    → l + r ` loc , i , j ⊨ w
    → ∃[ t ] ( <-Min⁺ l r loc  w i j t )

find-<-Min⁺ l r loc w i j ( ⊨inl .l .r .loc .i .j .w lij⊨w ) =  ⊨inl l r loc i j w lij⊨w , <-min-l l r loc w i j lij⊨w 
find-<-Min⁺ l r loc w i j ( ⊨inr .l .r .loc .i .j .w rij⊨w )
  with ⊨? l i j w
... | yes  lij⊨w = ⊨inl l r loc i j w lij⊨w , <-min-l l r loc w i j lij⊨w
... | no  ¬lij⊨w = ⊨inr l r loc i j w rij⊨w , <-min-r l r loc w i j ¬lij⊨w rij⊨w


data <-Min● : ∀ ( l r : RE ) → ( loc : ℕ ) → ( w : List Char ) → ( i k : ℕ ) → ( l ● r ` loc , i , k ⊨ w ) → Set
  where
  <-min-● : ∀ ( l r : RE) ( loc : ℕ )
    → ( w : List Char )
    → ( i j k : ℕ )
    → ( i≤j : i Nat.≤ j )
    → ( j≤k : j Nat.≤ k )
    → ( t₁ : ( l , i , j ⊨ w ) )
    → ( t₂ : ( r , j , k ⊨ w ) )
    → ¬ ( ∃[ j' ] ( l , i , j' ⊨ w ) × ( r , j' , k ⊨ w ) × ( j < j') )
    --------------------------------------------------------------------
    → <-Min● l r loc w i k (⊨● l r loc i k w ( j , rij⊨w→i≤j t₁ , rij⊨w→i≤j t₂ , t₁ , t₂ ))



{-# TERMINATING #-}
find-<-Min●-go : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
  → ( j' : ℕ ) → l , i , j' ⊨ w → r , j' , j ⊨ w
  → ∃[ t ] ( <-Min● l r loc  w i j t )
find-<-Min●-go l r loc w i j j' t₁ t₂
  with dec-∃-range (suc j') j
    (λ j'' → ( l , i , j'' ⊨ w ) × ( r , j'' , j ⊨ w ))
    (λ j'' _ _ → ⊨? l i j'' w ×-dec ⊨? r j'' j w )
... | no ¬longer =
  ⊨● l r loc i j w ( j' , rij⊨w→i≤j t₁ , rij⊨w→i≤j t₂ , t₁ , t₂ ) ,
  <-min-● l r loc w i j' j ( rij⊨w→i≤j t₁ ) ( rij⊨w→i≤j t₂ ) t₁ t₂
    (λ { ( j'' , t₁'' , t₂'' , j'<j'' ) →
      ¬longer ( j'' , j'<j'' , rij⊨w→i≤j t₂'' , t₁'' , t₂'' ) })
... | yes ( j'' , _ , _ , t₁'' , t₂'' ) =
  find-<-Min●-go l r loc w i j j'' t₁'' t₂''

find-<-Min● : ∀ ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    → l ● r ` loc , i , j ⊨ w
    → ∃[ t ] ( <-Min● l r loc  w i j t )
find-<-Min● l r loc w i j ( ⊨● _ _ _ _ _ _ ( j' , i≤j' , j'≤j , t₁ , t₂ ) ) =
  find-<-Min●-go l r loc w i j j' t₁ t₂

-- is this well-founded, wellfounded is depending on <-Min hahah.. circular definition
data _,_,_⊢_<_ where
  choice : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j j' : ℕ )
    → ( t₁ : (l + r ` loc , i , j  ⊨ w) )  
    → ( t₂ : (l + r ` loc , i , j' ⊨ w) )      
    → l , r , loc , w , i , j , j' ⊢⁺  (proj₁ ( find-<-Min⁺ l r loc w i j t₁ )) < (proj₁ ( find-<-Min⁺ l r loc w i j' t₂) )
    --------------------------------------------------------- 
    → (l + r ` loc) , w , i ⊢ j < j'
  seq : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i k k' : ℕ )
    → ( t₁ : ( l ● r ` loc , i , k ⊨ w) )
    → ( t₂ : ( l ● r ` loc , i , k' ⊨ w) )
    → l , r , loc , w , i , k , k' ⊢● ( proj₁ (find-<-Min● l r loc w i k t₁) ) < (proj₁ (find-<-Min● l r loc w i k' t₂) )
    --------------------------------------------------
    → ( l ● r ` loc) , w , i ⊢ k < k' 


data _,_,_,_,_,_,_⊢⁺_<_ where
  inlinr :  ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j j' : ℕ )
    → ( t₁ : l , i , j  ⊨ w ) -- the evidence of ⊨inl l r loc i j w ∈ Tᵢ 
    → ( t₂ : r , i , j' ⊨ w ) -- the evidence of ⊨inr l r loc i j' w ∈ Tᵢ
    ---------------------------------------------------------------------
    → l , r , loc , w , i , j , j' ⊢⁺ ( ⊨inl l r loc i j w t₁ ) < ( ⊨inr l r loc i j' w t₂ ) 

  inlinl : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j j' : ℕ )
    → ( t₁ : l , i , j  ⊨ w ) -- the evidence of ⊨inl l r loc i j w ∈ Tᵢ 
    → ( t₂ : l , i , j' ⊨ w ) -- the evidence of ⊨inl l r loc i j' w ∈ Tᵢ
    → l , w , i ⊢ j < j'
    -----------------------------------------------------------------------
    → l , r , loc , w , i , j , j' ⊢⁺ ( ⊨inl l r loc i j w t₁ ) < ( ⊨inl l r loc i j' w t₂ ) 


  inrinr : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j j' : ℕ )
    → ( t₁ : r , i , j  ⊨ w ) -- the evidence of ⊨inr l r loc i j w ∈ Tᵢ 
    → ( t₂ : r , i , j' ⊨ w ) -- the evidence of ⊨inr l r loc i j' w ∈ Tᵢ
    → l , w , i ⊢ j < j'
    -----------------------------------------------------------------------
    → l , r , loc , w , i , j , j' ⊢⁺ ( ⊨inr l r loc i j w t₁ ) < ( ⊨inr l r loc i j' w t₂ )

data _,_,_,_,_,_,_⊢●_<_ where
  seq₂ : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j k k' : ℕ )
    → ( t₁ : l , i , j ⊨ w )
    → ( t₂ : r , j , k ⊨ w )
    → ( t₂' : r , j , k' ⊨ w )
    -----------------------------------------------------------------------
    → l , r , loc , w , i , k , k' ⊢● ( ⊨● l r loc i k w ( j , rij⊨w→i≤j t₁ , rij⊨w→i≤j t₂ , t₁ , t₂ ) ) < ( ⊨● l r loc i k' w ( j , rij⊨w→i≤j t₁ , rij⊨w→i≤j t₂' , t₁ , t₂' ) ) 


```



