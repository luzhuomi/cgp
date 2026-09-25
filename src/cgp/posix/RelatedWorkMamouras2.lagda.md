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
open import Data.Nat using (_<_ ; _≤_ ; _≟_ ; _≤?_ ; zero ; suc ; _+_ ; _∸_ ; s<s ; z<s ; z≤n ; s≤s)
open import Data.Empty using (⊥ ; ⊥-elim)
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; <-cmp ; +-suc ; +-identityʳ ;
  ≤-antisym ; m∸n≡0⇒m≤n ; m≤n⇒m∸n≡0 ; m+[n∸m]≡n ; [m+n]∸[m+o]≡n∸o ; m+n∸n≡m ; ∸-monoʳ-≤ ; n≤1+n ; m≤n⇒m<n∨m≡n ; m<1+n⇒m<n∨m≡n )

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
  ( Dec; yes; no )

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


-- Eliminate a Dec by providing a handler for each branch.
dec-elim : ∀ { a ℓ } { A : Set a } { B : Set ℓ }
  → ( x : Dec A ) → ( yes : A → B ) → ( no : ¬ A → B ) → B
dec-elim ( yes x ) h-yes _ = h-yes x
dec-elim ( no ¬x ) _ h-no  = h-no ¬x

-- Decidable equality of a (Maybe Char) with ( just c ).
maybe-just-≟ : ( m : Maybe Char ) → ( c : Char ) → Dec ( m ≡ just c )
maybe-just-≟ nothing    c    = no λ ()
maybe-just-≟ ( just c' ) c with c' Char.≟ c
... | no  c'≢c = no λ { refl → c'≢c refl }
... | yes c'≡c = yes ( cong just c'≡c )

-- n ∸ 0 ≡ n
n∸0≡n : ( n : ℕ ) → n ∸ 0 ≡ n
n∸0≡n zero    = refl
n∸0≡n (suc n) = cong suc ( n∸0≡n n )

-- Decide ∃[ j ] ( i ≤ j × j ≤ k × P j ) by recursion on the upper bound k.
dec-∃-range : ( i k : ℕ ) → ( P : ℕ → Set )
  → ( ∀ j → i ≤ j → j ≤ k → Dec ( P j ) )
  → Dec ( ∃[ j ] i ≤ j × j ≤ k × P j )
dec-∃-range i zero P dec with i ≟ zero
... | no  i≢zero = no ( λ ( j , i≤j , j≤zero , _ ) → i≢zero ( trans ( sym ( n∸0≡n i ) ) ( m≤n⇒m∸n≡0 ( ≤-trans i≤j j≤zero ) ) ) )
... | yes i≡zero with dec zero ( subst ( λ x → x ≤ zero ) ( sym i≡zero ) z≤n ) z≤n
... | yes p = yes ( zero , subst ( λ x → x ≤ zero ) ( sym i≡zero ) z≤n , z≤n , p )
... | no  ¬p = no ( λ ( j , _ , j≤zero , p ) → ¬p ( subst ( λ x → P x ) ( trans ( sym ( n∸0≡n j ) ) ( m≤n⇒m∸n≡0 j≤zero ) ) p ) )
dec-∃-range i ( suc k' ) P dec with i ≤? suc k'
... | no  i≰k = no λ { ( _ , i≤j , j≤k , _ ) → i≰k ( ≤-trans i≤j j≤k ) }
... | yes i≤k with dec ( suc k' ) i≤k ≤-refl
... | yes p = yes ( suc k' , i≤k , ≤-refl , p )
... | no  ¬p with dec-∃-range i k' P ( λ j i≤j j≤k' → dec j i≤j ( ≤-trans j≤k' ( n≤1+n k' ) ) )
... | yes ( j , i≤j , j≤k' , p ) = yes ( j , i≤j , ≤-trans j≤k' ( n≤1+n k' ) , p )
... | no  n = no ( λ ( j , i≤j , j≤k , p ) → no-cand j i≤j j≤k p )
  where
    no-cand : ( j : ℕ ) → ( i ≤ j ) → ( j ≤ suc k' ) → ( P j ) → ⊥
    no-cand zero i≤zero _ p = n ( zero , i≤zero , z≤n , p )
    no-cand ( suc j ) i≤j j≤k p with m≤n⇒m<n∨m≡n j≤k
    ... | inj₂ j≡suc-k' = ¬p ( subst ( λ x → P x ) ( j≡suc-k' ) p )
    ... | inj₁ j<suc-k' with m<1+n⇒m<n∨m≡n j<suc-k'
    ... | inj₁ j<k' = n ( suc j , i≤j , <⇒≤ j<k' , p )
    ... | inj₂ j≡k' = n ( suc j , i≤j , subst ( λ x → suc j ≤ x ) ( j≡k' ) ≤-refl , p )

-- m + 1 ≡ suc m
+-1≡suc : ( m : ℕ ) → m + 1 ≡ suc m
+-1≡suc zero    = refl
+-1≡suc (suc m) = cong suc ( +-1≡suc m )

-- suc m ∸ 1 ≡ m
suc-∸-1 : ( m : ℕ ) → suc m ∸ 1 ≡ m
suc-∸-1 zero    = refl
suc-∸-1 ( suc m ) = trans ( cong ( λ x → x ∸ 1 ) ( sym ( +-1≡suc ( suc m ) ) ) ) ( m+n∸n≡m ( suc m ) 1 )

-- m ≤ suc d  ⇒  m ∸ 1 ≤ d
∸-suc-≤ : ( m d : ℕ ) → m ≤ suc d → m ∸ 1 ≤ d
∸-suc-≤ zero    d z≤n         = z≤n
∸-suc-≤ (suc m) d ( s≤s m≤d ) = subst ( λ x → x ≤ d ) ( sym ( suc-∸-1 m ) ) m≤d

-- i < j ≤ k and k ∸ i ≤ suc d  ⇒  k ∸ j ≤ d
∸-step-≤ : ( i j k d : ℕ ) → i < j → j ≤ k → k ∸ i ≤ suc d → k ∸ j ≤ d
∸-step-≤ i j k d i<j j≤k h =
  ≤-trans ( subst ( λ x → k ∸ j ≤ x ) k∸i+1≡k∸i∸1 ( ∸-monoʳ-≤ k ( subst ( λ x → x ≤ j ) ( sym ( +-1≡suc i ) ) i<j ) ) )
          ( ∸-suc-≤ ( k ∸ i ) d h )
  where
    i≤k : i ≤ k
    i≤k = ≤-trans ( <⇒≤ i<j ) j≤k

    k∸i+1≡k∸i∸1 : k ∸ ( i + 1 ) ≡ ( k ∸ i ) ∸ 1
    k∸i+1≡k∸i∸1 = begin
      k ∸ ( i + 1 )                ≡⟨ cong ( λ x → x ∸ ( i + 1 ) ) ( sym ( m+[n∸m]≡n i≤k ) ) ⟩
      ( i + ( k ∸ i ) ) ∸ ( i + 1 ) ≡⟨ [m+n]∸[m+o]≡n∸o i ( k ∸ i ) 1 ⟩
      ( k ∸ i ) ∸ 1                ∎

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


```agda
-- [i , j] <ᵢʳ [i , j']

-- we do not index this order over ( r , i , j ⊨ w ) and  ( r , i , j' ⊨ w )
infix 4 _,_,_⊢_<_

data _,_,_⊢_<_ : ∀ ( r :  RE ) → ( w : List Char ) → ( i : ℕ ) → ( j : ℕ ) → ( j' : ℕ )  → Set 


-- inl[i , j] <ᵢ inl[i , j']
-- inr[i , j] <ᵢ inr[i , j']
-- inl[i , j] <ᵢ inr[i , j']


infix 4 _,_,_,_,_,_,_⊢⁺_<_

-- we index this order over ( r , i , j ⊨ w ) and  ( r , i , j' ⊨ w ) 
data _,_,_,_,_,_,_⊢⁺_<_ : ∀ ( l r : RE ) → ( loc : ℕ ) → ( w : List Char ) → ( i j j' : ℕ ) →  ( l + r ` loc , i , j ⊨ w ) → ( l + r ` loc , i , j' ⊨ w ) → Set



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

-- The current definition of the order makes find-<-Min⁺ impossible to define.
-- The counterexample below shows that assuming such a function leads to a contradiction.

-- The lemma find-<-Min⁺ is unprovable.  <-Min⁺ requires t₁ to be
-- ⊢⁺-less-than-or-equal to every evidence of the same ( i , j ) match, but the
-- ⊢⁺ order leaves two inl evidences incomparable whenever comparing their
-- minima degenerates into a self-comparison (min < min), which is empty.
-- Hence a match need not have a <-Min⁺ witness.

-- postulate
find-<-Min⁺ : ∀ ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    → l + r ` loc , i , j ⊨ w
    → ∃[ t ] ( <-Min⁺ l r loc  w i j t )

find-<-Min⁺ l r loc w i j ( ⊨inl .l .r .loc .i .j .w lij⊨w ) =  ⊨inl l r loc i j w lij⊨w , <-min-l l r loc w i j lij⊨w 
find-<-Min⁺ l r loc w i j ( ⊨inr .l .r .loc .i .j .w rij⊨w )
  with ⊨? l i j w
... | yes  lij⊨w = ⊨inl l r loc i j w lij⊨w , <-min-l l r loc w i j lij⊨w
... | no  ¬lij⊨w = ⊨inr l r loc i j w rij⊨w , <-min-r l r loc w i j ¬lij⊨w rij⊨w

-- is this well-founded, wellfounded is depending on <-Min hahah.. circular definition
data _,_,_⊢_<_ where
  choice : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    → ( i j j' : ℕ )
    → ( t₁ : (l + r ` loc , i , j  ⊨ w) )  
    → ( t₂ : (l + r ` loc , i , j' ⊨ w) )      
    → l , r , loc , w , i , j , j' ⊢⁺  (proj₁ ( find-<-Min⁺ l r loc w i j t₁ )) < (proj₁ ( find-<-Min⁺ l r loc w i j' t₂) )
    --------------------------------------------------------- 
    → (l + r ` loc) , w , i ⊢ j < j' 
  


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

```



-- Counterexample: l = a0 + a1 ` 2, r = a2 over w = [a], i = 0, j = 1.
-- There are three evidences of ( l + a2 ` 4 ) , 0 , 1 ⊨ w :
--   P1 = inl (inl t$0)
--   P2 = inl (inr t$1)
--   P3 = inr t$2
-- P1 and P2 are incomparable: inlinl would require l , w , 0 ⊢ 1 < 1, whose
-- only constructor choice requires ⊢⁺ (L1 < L1) where L1 = inl t$0 is the
-- unique minimum of l's evidences; but ⊢⁺ (L1 < L1) would require
-- a0 , w , 0 ⊢ 1 < 1, which is empty because a0 is a literal, not a plus.
-- Hence no evidence is <-Min⁺.

```agda
{-
-- K is available (no --without-K), so equality proofs are unique.
UIP-≡ : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
UIP-≡ refl refl = refl

counterexample : (∀ ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
                   → ( t : l + r ` loc , i , j ⊨ w )
                   → ∃[ t' ] (<-Min⁺ l r loc w i j t'))
                 → ⊥
counterexample wellfounded = contradiction (proj₁ (wellfounded l a2 4 w i j P1)) (proj₂ (wellfounded l a2 4 w i j P1))
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

    -- a0 is a literal, not a plus, so the flat order on a0 is empty
    ¬a0-flat : (j₁ j₂ : ℕ) → ¬ (a0 , w , i ⊢ j₁ < j₂)
    ¬a0-flat _ _ ()

    -- L1 is not less than itself under ⊢⁺ : only inlinl can give inl < inl,
    -- and its premise a0 , w , i ⊢ j < j is empty
    ¬L1<L1⁺ : ¬ (a0 , a1 , 2 , w , i , j , j ⊢⁺ (⊨inl a0 a1 2 i j w t$0) < (⊨inl a0 a1 2 i j w t$0))
    ¬L1<L1⁺ (inlinl _ _ _ _ _ a0flat) = ¬a0-flat j j a0flat

    -- L2 is not less than itself under ⊢⁺ : only inrinr can give inr < inr,
    -- and its premise a0 , w , i ⊢ j < j is empty
    ¬L2<L2⁺ : ¬ (a0 , a1 , 2 , w , i , j , j ⊢⁺ (⊨inr a0 a1 2 i j w t$1) < (⊨inr a0 a1 2 i j w t$1))
    ¬L2<L2⁺ (inrinr _ _ _ _ _ a0flat) = ¬a0-flat j j a0flat

    -- L2 is not less than L1 (no constructor gives inr < inl)
    ¬L2<L1⁺ : ¬ (a0 , a1 , 2 , w , i , j , j ⊢⁺ (⊨inr a0 a1 2 i j w t$1) < (⊨inl a0 a1 2 i j w t$0))
    ¬L2<L1⁺ ()

    -- find-<-Min⁺ on l always returns L1, because L1 is the unique minimal evidence
    find-<-Min⁺-l-returns-L1 : (t : l , i , j ⊨ w)
      → proj₁ (find-<-Min⁺ a0 a1 2 w i j t) ≡ L1
    find-<-Min⁺-l-returns-L1 t
      with find-<-Min⁺ a0 a1 2 w i j t
    ... | M , <-min⁺ .a0 .a1 .2 .w .i .j .M minM
      with minM L2 | l-evidence M
    ... | inj₁ M<L2 | inj₁ M≡L1 = M≡L1
    ... | inj₁ M<L2 | inj₂ M≡L2 = ⊥-elim (¬L2<L2⁺ (subst (λ x → a0 , a1 , 2 , w , i , j , j ⊢⁺ x < L2) M≡L2 M<L2))
    ... | inj₂ M≡L2 | _ = ⊥-elim (¬L2-min M≡L2 (<-min⁺ a0 a1 2 w i j M minM))
      where
        L2≢L1 : ¬ (L2 ≡ L1)
        L2≢L1 ()

        ¬L2-min : M ≡ L2 → ¬ (<-Min⁺ a0 a1 2 w i j M)
        ¬L2-min M≡L2 (<-min⁺ .a0 .a1 .2 .w .i .j .M minM')
          with minM' L1
        ... | inj₁ M<L1 = ¬L2<L1⁺ (subst (λ x → a0 , a1 , 2 , w , i , j , j ⊢⁺ x < L1) M≡L2 M<L1)
        ... | inj₂ M≡L1 = L2≢L1 (trans (sym M≡L2) M≡L1)

    -- the flat order on l at ( i , j , j ) is empty: its only constructor choice
    -- would require ⊢⁺ (L1 < L1), since find-<-Min⁺ on l always returns L1
    ¬l-flat : ¬ (l , w , i ⊢ j < j)
    ¬l-flat (choice .i .j .j t₁ t₂ ev)
      rewrite find-<-Min⁺-l-returns-L1 t₁ | find-<-Min⁺-l-returns-L1 t₂
      = ¬L1<L1⁺ ev

    -- P1 is not less than P2 under ⊢⁺ : only inlinl can give inl < inl,
    -- and its premise l , w , i ⊢ j < j is empty
    ¬P1<P2⁺ : ¬ (l , a2 , 4 , w , i , j , j ⊢⁺ (⊨inl l a2 4 i j w L1) < (⊨inl l a2 4 i j w L2))
    ¬P1<P2⁺ (inlinl _ _ _ _ _ lflat) = ¬l-flat lflat

    -- P2 is not less than P1 under ⊢⁺
    ¬P2<P1⁺ : ¬ (l , a2 , 4 , w , i , j , j ⊢⁺ (⊨inl l a2 4 i j w L2) < (⊨inl l a2 4 i j w L1))
    ¬P2<P1⁺ (inlinl _ _ _ _ _ lflat) = ¬l-flat lflat

    -- P3 is not less than P1 (no constructor gives inr < inl)
    ¬P3<P1⁺ : ¬ (l , a2 , 4 , w , i , j , j ⊢⁺ (⊨inr l a2 4 i j w t$2) < (⊨inl l a2 4 i j w L1))
    ¬P3<P1⁺ ()

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
    ¬Min-P1 : ¬ (<-Min⁺ l a2 4 w i j P1)
    ¬Min-P1 (<-min⁺ .l .a2 .4 .w .i .j .P1 minP1)
      with minP1 P2
    ... | inj₁ P1<P2 = ¬P1<P2⁺ P1<P2
    ... | inj₂ P1≡P2 = P1≢P2 P1≡P2

    ¬Min-P2 : ¬ (<-Min⁺ l a2 4 w i j P2)
    ¬Min-P2 (<-min⁺ .l .a2 .4 .w .i .j .P2 minP2)
      with minP2 P1
    ... | inj₁ P2<P1 = ¬P2<P1⁺ P2<P1
    ... | inj₂ P2≡P1 = P1≢P2 (sym P2≡P1)

    ¬Min-P3 : ¬ (<-Min⁺ l a2 4 w i j P3)
    ¬Min-P3 (<-min⁺ .l .a2 .4 .w .i .j .P3 minP3)
      with minP3 P1
    ... | inj₁ P3<P1 = ¬P3<P1⁺ P3<P1
    ... | inj₂ P3≡P1 = P3≢P1 P3≡P1

    contradiction : (t : r , i , j ⊨ w) → ¬ (<-Min⁺ l a2 4 w i j t)
    contradiction t min
      with r-evidence t
    ... | inj₁ t≡P1 = ¬Min-P1 (subst (<-Min⁺ l a2 4 w i j) t≡P1 min)
    ... | inj₂ (inj₁ t≡P2) = ¬Min-P2 (subst (<-Min⁺ l a2 4 w i j) t≡P2 min)
    ... | inj₂ (inj₂ t≡P3) = ¬Min-P3 (subst (<-Min⁺ l a2 4 w i j) t≡P3 min)

-} 
