```agda
{-# OPTIONS --rewriting --no-positivity-check #-}
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
  dec-elim ; maybe-just-≟ ; n∸0≡n ; dec-∃-range ; dec-∃-range-Max ;
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
  ≤-antisym ; m∸n≡0⇒m≤n ; n≤1+n ; ≤-step ; m≤n⇒m<n∨m≡n ; ≤-pred )

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
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst; subst₂; inspect; Reveal_·_is_; [_]; _≢_)

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

-- NOTE: The index bounds in ⊨∷ (i < j and j ≤ k) are derivable from the
-- sub-match evidences via rij⊨w→i≤j.  They are kept as explicit fields because
-- they are convenient for the proofs below and staying
-- faithful to Mamoura's definition in the paper ; removing
-- them would require a wider refactor of every ⊨∷ pattern match and
-- construction in this file.  (The ⊨● bounds are handled differently ;
-- see the comment above ⊨●.)

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
     

  -- Why is the split point `j` an explicit field here, instead of an
  -- existentially bundled one ( ∃[ j ] i≤j × j≤k × t₁ × t₂ ) as before ?
  -- The minimality machinery computes with the split : find-<-Min●-go builds
  -- the canonical minimal evidence, and decide-⊢< / trichotomy-● on ●
  -- pattern-match it to bind the split point and the two sub-evidences,
  -- recurse on the left regex ( decide-⊢< l₁ w i min-s min-s' … ), and
  -- rebuild ⊨● terms in the conclusions of seq₁ / seq₂.  Bundling everything
  -- into one Σ field would force all of that through nested projections ;
  -- lifting j , t₁ , t₂ to first-class fields makes the payload of a ●-match
  -- exactly ( j , t₁ , t₂ ).
  --
  -- Why are the bounds .( i ≤ j ) and .( j ≤ k ) irrelevant ( dot ) arguments ?
  -- They are derivable from the sub-evidences ( rij⊨w→i≤j t₁ /
  -- rij⊨w→i≤j t₂ ), so they are side conditions, not data : they must be
  -- supplied and checked at every construction site ( soundness is kept ),
  -- but they are erased from the term and cannot be extracted.  Hence the
  -- term identity of a ●-match depends only on ( j , t₁ , t₂ ).  This erasure
  -- is load-bearing for canonicity : find-<-Min● reconstructs the minimal
  -- evidence from the closed search dec-∃-range-Max ( independent of the
  -- starting evidence T ), so find-<-Min●-canon is refl ; and the subst₂
  -- transports in decide-⊢< / trichotomy-● require that the ⊨● rebuilt from
  -- the pattern-matched sub-evidences be judgmentally equal to the
  -- pattern-matched minimal evidence.  If the bounds were stored — the old Σ,
  -- or even plain implicit { … } fields — the two sides would carry different
  -- proof terms ( the searched i≤a vs the re-derived rij⊨w→i≤j t₁ ) and would
  -- not be judgmentally equal, breaking those transports.
  ⊨● : ∀ ( l r : RE ) ( loc : ℕ )
      → ( i k : ℕ )
      → ( w : List Char )
      → ( j : ℕ )
      → .( i Nat.≤ j )
      → .( j Nat.≤ k )
      → ( l , i , j ⊨ w )
      → ( r , j , k ⊨ w )
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

rij⊨w→i≤j : ∀ { r : RE } { i j : ℕ } { w : List Char }
           → r , i , j ⊨ w
           → i Nat.≤ j
rij⊨w→i≤j ( ⊨ε i w ) = ≤-refl
rij⊨w→i≤j ( ⊨$ c loc i w eq ) = n≤1+n i
rij⊨w→i≤j ( ⊨inl l r loc i j w t ) = rij⊨w→i≤j t
rij⊨w→i≤j ( ⊨inr l r loc i j w t ) = rij⊨w→i≤j t
rij⊨w→i≤j ( ⊨● l r loc i k w j _ _ t₁ t₂ ) = ≤-trans (rij⊨w→i≤j t₁) (rij⊨w→i≤j t₂)
rij⊨w→i≤j ( ⊨[] r ε∉r loc w i ) = ≤-refl
rij⊨w→i≤j ( ⊨∷ r ε∉r loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) = ≤-trans ( <⇒≤ i<j ) j≤k

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
        ( λ ( j , i≤j , j≤k , ( t₁ , t₂ ) ) → yes ( ⊨● l r loc i k w j i≤j j≤k t₁ t₂ ) )
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
    no-match-i≰k i≰k ( ⊨● _ _ _ _ _ _ j _ _ t₁ t₂ ) = i≰k ( ≤-trans ( rij⊨w→i≤j t₁ ) ( rij⊨w→i≤j t₂ ) )

    no-match : ( n : ¬ ( ∃[ j ] i ≤ j × j ≤ k × ( ( l , i , j ⊨ w ) × ( r , j , k ⊨ w ) ) ) )
      → ( l ● r ` loc ) , i , k ⊨ w → ⊥
    no-match n ( ⊨● _ _ _ _ _ _ j _ _ t₁ t₂ ) = n ( j , rij⊨w→i≤j t₁ , rij⊨w→i≤j t₂ , ( t₁ , t₂ ) )
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


the <-Min and find-<-Min+ (which is min ρ⁻¹ ( . ) function from Marmouras' paper.) has to be divided into
multiple definitions per regex operator, e.g. one for +, another one for ●, another one for *


Their order don't differentiate parse trees, e.g. for r = (a + a) + a, w = 'a'
they treat Left (Left 'a') the sane as Left (Right 'a') w.r.t to the above because both has the same
match set value [0,1].

```agda
-- [i , j] <ᵢʳ [i , j']

-- we do not index this order over ( r , i , j ⊨ w ) and  ( r , i , j' ⊨ w )
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


-- The shape (inl / inr) of the minimal evidence of l + r at (i , j) is
-- determined by whether l matches at (i , j) ; it does not depend on which
-- evidence we start from.

Min⁺ : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
  → l + r ` loc , i , j ⊨ w → l + r ` loc , i , j ⊨ w
Min⁺ l r loc w i j t = proj₁ ( find-<-Min⁺ l r loc w i j t )

-- Purpose : when l matches at ( i , j ), the minimal evidence Min⁺ (l + r)
--           at ( i , j ) is the ⊨inl embedding of some l-match ; returns that
--           l-match with a proof that Min⁺ computes to exactly it.
-- Used in : decide-⊢< ( + case : inr/inl and inl/inl branches ).
-- Idea    : case split on the given evidence t : a ⊨inl is done. For ⊨inr,
--           decide ⊨? l i j w : yes → the minimal is ⊨inl and, since both
--           sides run the same closed ⊨? decision, the payloads coincide
--           ( refl ) ; no → contradicts the hypothesis u that l matches.
Min⁺-inl : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
  ( u : l , i , j ⊨ w ) ( t : l + r ` loc , i , j ⊨ w )
  → Σ[ a ∈ l , i , j ⊨ w ] Min⁺ l r loc w i j t ≡ ⊨inl l r loc i j w a
Min⁺-inl l r loc w i j u ( ⊨inl _ _ _ _ _ _ a ) = a , refl
Min⁺-inl l r loc w i j u ( ⊨inr _ _ _ _ _ _ b ) with ⊨? l i j w
... | yes a = a , refl
... | no ¬a = ⊥-elim ( ¬a u )

-- Purpose : dual of Min⁺-inl : when l does NOT match at ( i , j ), the
--           minimal evidence Min⁺ (l + r) at ( i , j ) is the ⊨inr embedding
--           of some r-match ; returns that r-match with a proof.
-- Used in : decide-⊢< ( + case : inr/inl and inr/inr branches ).
-- Idea    : case split on t : a ⊨inl already witnesses l matching,
--           contradicting ¬u. For ⊨inr, decide ⊨? l i j w : yes contradicts
--           ¬u ; no → the minimal keeps its ⊨inr shape and its payload is the
--           very r-match of t ( refl , by canonicity of find-<-Min⁺ ).
Min⁺-inr : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
  ( ¬u : ¬ ( l , i , j ⊨ w ) ) ( t : l + r ` loc , i , j ⊨ w )
  → Σ[ b ∈ r , i , j ⊨ w ] Min⁺ l r loc w i j t ≡ ⊨inr l r loc i j w b
Min⁺-inr l r loc w i j ¬u ( ⊨inl _ _ _ _ _ _ a ) = ⊥-elim ( ¬u a )
Min⁺-inr l r loc w i j ¬u ( ⊨inr _ _ _ _ _ _ b ) with ⊨? l i j w
... | yes a = ⊥-elim ( ¬u a )
... | no ¬a = b , refl

-- Purpose : minimality of an ⊨inr evidence of l + r at ( i , j ) implies that
--           l does not match at ( i , j ).
-- Used in : decide-⊢< ( + case : inr/inl and inr/inr branches ), supplying
--           the ¬( l , i , j ⊨ w ) premise of Min⁺-inr.
-- Idea    : inspection of the <-min-r constructor, whose side condition is
--           exactly ¬( l , i , j ⊨ w ).
<-Min⁺-inr¬ : ∀ { l r loc w i j b }
  → <-Min⁺ l r loc w i j ( ⊨inr l r loc i j w b ) → ¬ ( l , i , j ⊨ w )
<-Min⁺-inr¬ ( <-min-r _ _ _ _ _ _ ¬l _ ) = ¬l



mutual

  infix 4 _∣_∣_⊢_<_
  infix 4 _∣_∣_∣_∣_∣_∣_⊢⁺_<_
  infix 4 _∣_∣_∣_∣_∣_∣_⊢●_<_
  infix 4 _∣_∣_∣_∣_∣_∣_⊢⋆_<_


  data _∣_∣_⊢_<_ : ∀ ( q :  RE ) → ( w : List Char ) → ( i : ℕ ) → ( j : ℕ ) → ( j' : ℕ )  → Set
  data _∣_∣_∣_∣_∣_∣_⊢⁺_<_ : ∀ ( l r : RE ) → ( loc : ℕ ) → ( w : List Char ) → ( i j j' : ℕ ) →  ( l + r ` loc , i , j ⊨ w ) → ( l + r ` loc , i , j' ⊨ w ) → Set
  data _∣_∣_∣_∣_∣_∣_⊢●_<_ : ∀ ( l r : RE ) → ( loc : ℕ ) → ( w : List Char ) → ( i k k'  : ℕ ) →  ( l ● r ` loc , i , k ⊨ w ) → ( l ● r ` loc , i , k' ⊨ w ) → Set
  data _∣_∣_∣_∣_∣_∣_⊢⋆_<_ : ∀ ( r : RE ) → ( nε : ε∉ r ) → ( loc : ℕ ) → ( w : List Char ) → ( i k k' : ℕ ) →  ( r * nε ` loc , i , k ⊨ w ) → ( r * nε ` loc , i , k' ⊨ w ) → Set

  data <-Min● : ∀ ( l r : RE ) → ( loc : ℕ ) → ( w : List Char ) → ( i k : ℕ ) → ( l ● r ` loc , i , k ⊨ w ) → Set

  find-<-Min● : ∀ ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    → l ● r ` loc , i , j ⊨ w
    → ∃[ t ] ( <-Min● l r loc  w i j t )

  data <-Min* : ∀ ( r : RE ) → ( nε : ε∉ r ) → ( loc : ℕ ) → ( w : List Char ) → ( i k : ℕ ) → ( r * nε ` loc , i , k ⊨ w ) → Set

  find-<-Min* : ∀ ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i k : ℕ )
    → ( r * nε ` loc , i , k ⊨ w )
    → ∃[ t ] ( <-Min* r nε loc w i k t )

  data <-Min● where
      <-min-● : ∀ ( l r : RE) ( loc : ℕ )
        → ( w : List Char )
        → ( i j k : ℕ )
        → ( i≤j : i Nat.≤ j )
        → ( j≤k : j Nat.≤ k )
        → ( t₁ : ( l , i , j ⊨ w ) )
        → ( t₂ : ( r , j , k ⊨ w ) )
        → ¬ ( ∃[ j' ] ( l , i , j' ⊨ w ) × ( r , j' , k ⊨ w ) × ( j < j' ) )
        --------------------------------------------------------------------
        → <-Min● l r loc w i k (⊨● l r loc i k w j (rij⊨w→i≤j t₁) (rij⊨w→i≤j t₂) t₁ t₂ )

  data <-Min* where
      <-min-[] : ∀ ( r : RE) ( nε : ε∉ r ) ( loc : ℕ )
        → ( w : List Char ) ( i : ℕ )
        → <-Min* r nε loc w i i ( ⊨[] r nε loc w i )

      <-min-∷ : ∀ ( r : RE) ( nε : ε∉ r ) ( loc : ℕ )
        → ( w : List Char )
        → ( i j k : ℕ )
        → ( i<j : i Nat.< j )
        → ( j≤k : j Nat.≤ k )
        → ( t₁ : ( r , i , j ⊨ w ) )
        → ( t₂ : ( r * nε ` loc , j , k ⊨ w ) )
        → ( <-Min* r nε loc w j k t₂ )
        → ¬ ( ∃[ j' ] ( i Nat.< j' ) × ( j' Nat.≤ k ) × ( r , i , j' ⊨ w ) × ( r * nε ` loc , j' , k ⊨ w ) × ( r ∣ w ∣ i ⊢ j' < j ) )
        --------------------------------------------------------------------
        → <-Min* r nε loc w i k ( ⊨∷ r nε loc w i k ( j , i<j , j≤k , t₁ , t₂ ) )

  -- is this well-founded, wellfounded is depending on <-Min hahah.. circular definition
  data _∣_∣_⊢_<_ where
    choice : ∀ { l r : RE } { loc : ℕ } { w : List Char }
      → ( i j j' : ℕ )
      → ( t₁ : (l + r ` loc , i , j  ⊨ w) )  
      → ( t₂ : (l + r ` loc , i , j' ⊨ w) )      
      → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j' ⊢⁺  (proj₁ ( find-<-Min⁺ l r loc w i j t₁ )) < (proj₁ ( find-<-Min⁺ l r loc w i j' t₂) )
      --------------------------------------------------------- 
      → (l + r ` loc) ∣ w ∣ i ⊢ j < j'
    seq : ∀ { l r : RE } { loc : ℕ } { w : List Char }
      → ( i k k' : ℕ )
      → ( t₁ : ( l ● r ` loc , i , k ⊨ w) )
      → ( t₂ : ( l ● r ` loc , i , k' ⊨ w) )
      → l ∣ r ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢● ( proj₁ (find-<-Min● l r loc w i k t₁) ) < (proj₁ (find-<-Min● l r loc w i k' t₂) )
      --------------------------------------------------
      → ( l ● r ` loc) ∣ w ∣ i ⊢ k < k' 
    star : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char }
      → ( i k k' : ℕ )
      → ( t₁ : ( r * nε ` loc , i , k ⊨ w) )
      → ( t₂ : ( r * nε ` loc , i , k' ⊨ w) )
      → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i k k' ( proj₁ ( find-<-Min* r nε loc w i k t₁ ) ) ( proj₁ ( find-<-Min* r nε loc w i k' t₂ ) )
      --------------------------------------------------
      → ( r * nε ` loc ) ∣ w ∣ i ⊢ k < k'


  data _∣_∣_∣_∣_∣_∣_⊢⁺_<_ where
    inlinr :  ∀ { l r : RE } { loc : ℕ } { w : List Char }
      → ( i j j' : ℕ )
      → ( t₁ : l , i , j  ⊨ w ) -- the evidence of ⊨inl l r loc i j w ∈ Tᵢ 
      → ( t₂ : r , i , j' ⊨ w ) -- the evidence of ⊨inr l r loc i j' w ∈ Tᵢ
      ---------------------------------------------------------------------
      → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j' ⊢⁺ ( ⊨inl l r loc i j w t₁ ) < ( ⊨inr l r loc i j' w t₂ ) 

    inlinl : ∀ { l r : RE } { loc : ℕ } { w : List Char }
      → ( i j j' : ℕ )
      → ( t₁ : l , i , j  ⊨ w ) -- the evidence of ⊨inl l r loc i j w ∈ Tᵢ 
      → ( t₂ : l , i , j' ⊨ w ) -- the evidence of ⊨inl l r loc i j' w ∈ Tᵢ
      → l ∣ w ∣ i ⊢ j < j'
      -----------------------------------------------------------------------
      → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j' ⊢⁺ ( ⊨inl l r loc i j w t₁ ) < ( ⊨inl l r loc i j' w t₂ ) 


    inrinr : ∀ { l r : RE } { loc : ℕ } { w : List Char }
      → ( i j j' : ℕ )
      → ( t₁ : r , i , j  ⊨ w ) -- the evidence of ⊨inr l r loc i j w ∈ Tᵢ 
      → ( t₂ : r , i , j' ⊨ w ) -- the evidence of ⊨inr l r loc i j' w ∈ Tᵢ
      → r ∣ w ∣ i ⊢ j < j'
      -----------------------------------------------------------------------
      → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j' ⊢⁺ ( ⊨inr l r loc i j w t₁ ) < ( ⊨inr l r loc i j' w t₂ )

  data _∣_∣_∣_∣_∣_∣_⊢●_<_ where
    seq₂ : ∀ { l r : RE } { loc : ℕ } { w : List Char }
      → ( i j j' k k' : ℕ )
      → ( t₁ : l , i , j ⊨ w )
      → ( t₂ : r , j , k ⊨ w )
      → ( t₁' : l , i , j' ⊨ w )
      → ( t₂' : r , j' , k' ⊨ w )
      → ( j ≡ j' )
      → r ∣ w ∣ j ⊢ k < k' 
      -----------------------------------------------------------------------
      → l ∣ r ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢● ( ⊨● l r loc i k w j (rij⊨w→i≤j t₁) (rij⊨w→i≤j t₂) t₁ t₂ ) < ( ⊨● l r loc i k' w j' (rij⊨w→i≤j t₁') (rij⊨w→i≤j t₂') t₁' t₂' )

    seq₁ : ∀ { l r : RE }  { loc : ℕ } { w : List Char }
      → ( i j k j' k' : ℕ )
      → ( t₁ : l , i , j ⊨ w )
      → ( t₂ : r , j , k ⊨ w )
      → ( t₁' : l , i , j'  ⊨ w )
      → ( t₂' : r , j' , k' ⊨ w )
      → l ∣ w ∣ i ⊢ j < j'     
      -----------------------------------------------------------------------
      → l ∣ r ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢● ( ⊨● l r loc i k w j (rij⊨w→i≤j t₁) (rij⊨w→i≤j t₂) t₁ t₂ ) < ( ⊨● l r loc i k' w j' (rij⊨w→i≤j t₁') (rij⊨w→i≤j t₂') t₁' t₂' )

  data _∣_∣_∣_∣_∣_∣_⊢⋆_<_ where
    -- a non-empty iteration is strictly better (smaller) than the empty match
    *-cons-nil : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char }
      → ( i j k : ℕ )
      → ( i<j : i Nat.< j ) ( j≤k : j Nat.≤ k )
      → ( t₁ : ( r , i , j ⊨ w ) )
      → ( t₂ : ( r * nε ` loc , j , k ⊨ w ) )
      -----------------------------------------------------------------------
      → r ∣ nε ∣ loc ∣ w ∣ i ∣ k ∣ i ⊢⋆ ( ⊨∷ r nε loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) < ( ⊨[] r nε loc w i )

    -- compare the heads
    *-head : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char }
      → ( i j j' k k' : ℕ )
      → ( i<j : i Nat.< j ) ( j≤k : j Nat.≤ k )
      → ( i<j' : i Nat.< j' ) ( j'≤k' : j' Nat.≤ k' )
      → ( t₁ : ( r , i , j ⊨ w ) )
      → ( t₂ : ( r * nε ` loc , j , k ⊨ w ) )
      → ( t₁' : ( r , i , j' ⊨ w ) )
      → ( t₂' : ( r * nε ` loc , j' , k' ⊨ w ) )
      → r ∣ w ∣ i ⊢ j < j'
      -----------------------------------------------------------------------
      → r ∣ nε ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⋆ ( ⊨∷ r nε loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) < ( ⊨∷ r nε loc w i k' ( j' , i<j' , j'≤k' , t₁' , t₂' ) )

    -- same head, compare the tails
    *-tail : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char }
      → ( i j j' k k' : ℕ )
      → ( i<j : i Nat.< j ) ( j≤k : j Nat.≤ k ) ( i<j' : i Nat.< j' ) ( j'≤k' : j' Nat.≤ k' )
      → ( t₁ : ( r , i , j ⊨ w ) )
      → ( t₂ : ( r * nε ` loc , j , k ⊨ w ) )
      → ( t₁' : ( r , i , j' ⊨ w ) )
      → ( t₂' : ( r * nε ` loc , j' , k' ⊨ w ) )
      → ( j ≡ j' )
      → ( r * nε ` loc ) ∣ w ∣ j ⊢ k < k'
      -----------------------------------------------------------------------
      → r ∣ nε ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⋆ ( ⊨∷ r nε loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) < ( ⊨∷ r nε loc w i k' ( j' , i<j' , j'≤k' , t₁' , t₂' ) )

  -- the order is empty when the head of the left match is the empty iteration
  -- Purpose : ⊨[] is not below itself in ⊢⋆.
  -- Used in : no call sites yet ( kept for the irreflexivity of ⊢⋆ ).
  -- Idea    : ( ) — every ⊢⋆ constructor has a ⊨∷ left-hand side, so a ⊨[]
  --           left-hand side cannot be produced.
  ¬⊢⋆-[]-[] : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char } { i : ℕ }
    → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i i i ( ⊨[] r nε loc w i ) ( ⊨[] r nε loc w i ) → ⊥
  ¬⊢⋆-[]-[] ()

  -- Purpose : ⊨[] is not below any other match t in ⊢⋆ : combined with
  --           *-cons-nil ( every ⊨∷ is below ⊨[] ), this makes ⊨[] the
  --           bottom element of the order.
  -- Used in : decide-⊢< ( * case, the ⊨[] refute helpers ).
  -- Idea    : ( ) — as above, every ⊢⋆ constructor has a ⊨∷ left-hand side.
  ¬⊢⋆-[]-∷ : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char } { i k : ℕ }
    → ( t : ( r * nε ` loc ) , i , k ⊨ w )
    → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i i k ( ⊨[] r nε loc w i ) t → ⊥
  ¬⊢⋆-[]-∷ t ()

  -- Purpose : ⊢⁺ never relates an ⊨inr evidence to an ⊨inl one : ⊨inl
  --           evidence is uniformly smaller than ⊨inr evidence.
  -- Used in : decide-⊢< ( + case : inr/inl branch ).
  -- Idea    : ( ) — the only ⊢⁺ constructor with an ⊨inl right-hand side is
  --           inlinr, whose left-hand side is ⊨inl.
  inr≮inl : ∀ { l r loc w i j j' v u }
    → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j' ⊢⁺ ⊨inr l r loc i j w v < ⊨inl l r loc i j' w u → ⊥
  inr≮inl ()

  -- Purpose : if the base order says ¬( l₁ ∣ w ∣ i ⊢ j' < j ), then ⊢⁺ cannot
  --           relate ⊨inl(·, j') to ⊨inl(·, j).
  -- Used in : decide-⊢< ( + case : inl/inl branch, no-answer ).
  -- Idea    : the only ⊢⁺ constructor relating two ⊨inl evidence is inlinl,
  --           whose premise is exactly the base order — contradiction.
  ¬inl<inl⁺ : ∀ { l₁ l₂ loc i j j' w v u }
    → ¬ ( l₁ ∣ w ∣ i ⊢ j' < j )
    → l₁ ∣ l₂ ∣ loc ∣ w ∣ i ∣ j' ∣ j ⊢⁺ ⊨inl l₁ l₂ loc i j' w v < ⊨inl l₁ l₂ loc i j w u → ⊥
  ¬inl<inl⁺ ¬ord ( inlinl _ _ _ _ _ ord ) = ¬ord ord

  -- Purpose : dual of ¬inl<inl⁺ for ⊨inr evidence, recursing on the right
  --           regex l₂.
  -- Used in : decide-⊢< ( + case : inr/inr branch, no-answer ).
  -- Idea    : the only relevant constructor is inrinr, whose premise is
  --           exactly the base order on l₂ — contradiction.
  ¬inr<inr⁺ : ∀ { l₁ l₂ loc i j j' w v u }
    → ¬ ( l₂ ∣ w ∣ i ⊢ j' < j )
    → l₁ ∣ l₂ ∣ loc ∣ w ∣ i ∣ j' ∣ j ⊢⁺ ⊨inr l₁ l₂ loc i j' w v < ⊨inr l₁ l₂ loc i j w u → ⊥
  ¬inr<inr⁺ ¬ord ( inrinr _ _ _ _ _ ord ) = ¬ord ord

  -- trichotomy of the order on matches with a common start
  -- Purpose : for two matches t₁, t₂ of the same regex l from the same start
  --           i, the base order is total : exactly one of
  --           ( l ∣ w ∣ i ⊢ s₂ < s₁ ) / ( s₁ ≡ s₂ ) / ( l ∣ w ∣ i ⊢ s₁ < s₂ )
  --           holds.
  -- Used in : no external call sites yet ; recurses into itself through the
  --           * / + / ● branches.
  -- Idea    : structural on l. ε / $ : the evidence is unique, so equality.
  --           + : compare the minimal shapes ( inlinr : inl < inr ; same
  --           shape : recurse on the branch ). * : via trichotomy-* — compare
  --           the minimal heads by the base order on r ( *-head / *-tail ),
  --           equal heads → recurse on r*. ● : via trichotomy-● — compare the
  --           minimal splits by the base order on l₁ ( seq₁ ), equal splits →
  --           recurse on l₂ ( seq₂ ).
  trichotomy : ∀ ( l : RE ) ( w : List Char ) ( i s₁ s₂ : ℕ )
    → ( t₁ : l , i , s₁ ⊨ w ) → ( t₂ : l , i , s₂ ⊨ w )
    → ( l ∣ w ∣ i ⊢ s₂ < s₁ ) ⊎ ( s₁ ≡ s₂ ) ⊎ ( l ∣ w ∣ i ⊢ s₁ < s₂ )
  trichotomy ε w i s₁ s₂ ( ⊨ε _ _ ) ( ⊨ε _ _ ) = inj₂ ( inj₁ refl )
  trichotomy ( $ c ` loc ) w i s₁ s₂ ( ⊨$ _ _ _ _ _ ) ( ⊨$ _ _ _ _ _ ) = inj₂ ( inj₁ refl )
  trichotomy ( l₃ * nε ` loc ) w i s₁ s₂ t₁ t₂ = trichotomy-* l₃ nε loc w i s₁ s₂ t₁ t₂
    where
      trichotomy-* : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i s₁ s₂ : ℕ )
        → ( t₁ : ( r * nε ` loc ) , i , s₁ ⊨ w )
        → ( t₂ : ( r * nε ` loc ) , i , s₂ ⊨ w )
        → ( r * nε ` loc ) ∣ w ∣ i ⊢ s₂ < s₁ ⊎ s₁ ≡ s₂ ⊎ ( r * nε ` loc ) ∣ w ∣ i ⊢ s₁ < s₂
      trichotomy-* r nε loc w i s₁ s₂ t₁ t₂
        with find-<-Min* r nε loc w i s₁ t₁ | inspect ( find-<-Min* r nε loc w i s₁ ) t₁
           | find-<-Min* r nε loc w i s₂ t₂ | inspect ( find-<-Min* r nε loc w i s₂ ) t₂
      ... | ( min-t₁ , _ ) | [ eq₁ ] | ( min-t₂ , _ ) | [ eq₂ ]
        with min-t₁ | min-t₂
      ... | ⊨∷ _ _ _ _ _ _ ( j₁ , i<j₁ , j₁≤s₁ , u₁ , v₁ ) | ⊨∷ _ _ _ _ _ _ ( j₂ , i<j₂ , j₂≤s₂ , u₂ , v₂ ) =
        case-⊎ (λ j₁<j₂ →
          inj₂ ( inj₂ ( star i s₁ s₂ t₁ t₂ ( subst₂ (λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ s₁ ∣ s₂ ⊢⋆ x < y) ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₂ ) ) ( *-head i j₁ j₂ s₁ s₂ i<j₁ j₁≤s₁ i<j₂ j₂≤s₂ u₁ v₁ u₂ v₂ j₁<j₂ ) ) ) ))
               (case-⊎ (λ { refl →
                 case-⊎ (λ s₁<s₂ →
                   inj₂ ( inj₂ ( star i s₁ s₂ t₁ t₂ ( subst₂ (λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ s₁ ∣ s₂ ⊢⋆ x < y) ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₂ ) ) ( *-tail i j₁ j₂ s₁ s₂ i<j₁ j₁≤s₁ i<j₂ j₂≤s₂ u₁ v₁ u₂ v₂ refl s₁<s₂ ) ) ) ))
                        (case-⊎ (λ s₂≡s₁ → inj₂ ( inj₁ ( sym s₂≡s₁ ) ))
                                 (λ s₂<s₁ →
                                   inj₁ ( star i s₂ s₁ t₂ t₁ ( subst₂ (λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ s₂ ∣ s₁ ⊢⋆ x < y) ( sym ( cong proj₁ eq₂ ) ) ( sym ( cong proj₁ eq₁ ) ) ( *-tail i j₂ j₁ s₂ s₁ i<j₂ j₂≤s₂ i<j₁ j₁≤s₁ u₂ v₂ u₁ v₁ refl s₂<s₁ ) ) ) ))
                        ( trichotomy ( r * nε ` loc ) w j₁ s₂ s₁ v₂ v₁ ) })
                       (λ j₂<j₁ →
                         inj₁ ( star i s₂ s₁ t₂ t₁ ( subst₂ (λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ s₂ ∣ s₁ ⊢⋆ x < y) ( sym ( cong proj₁ eq₂ ) ) ( sym ( cong proj₁ eq₁ ) ) ( *-head i j₂ j₁ s₂ s₁ i<j₂ j₂≤s₂ i<j₁ j₁≤s₁ u₂ v₂ u₁ v₁ j₂<j₁ ) ) ) ))
               ( trichotomy r w i j₂ j₁ u₂ u₁ )
      ... | ⊨[] _ _ _ _ _ | ⊨∷ _ _ _ _ _ _ ( j₂ , i<j₂ , j₂≤s₂ , u₂ , v₂ ) =
        inj₁ ( star i s₂ s₁ t₂ t₁ ( subst₂ (λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ s₂ ∣ s₁ ⊢⋆ x < y) ( sym ( cong proj₁ eq₂ ) ) ( sym ( cong proj₁ eq₁ ) ) ( *-cons-nil i j₂ s₂ i<j₂ j₂≤s₂ u₂ v₂ ) ) )
      ... | ⊨∷ _ _ _ _ _ _ ( j₁ , i<j₁ , j₁≤s₁ , u₁ , v₁ ) | ⊨[] _ _ _ _ _ =
        inj₂ ( inj₂ ( star i s₁ s₂ t₁ t₂ ( subst₂ (λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ s₁ ∣ s₂ ⊢⋆ x < y) ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₂ ) ) ( *-cons-nil i j₁ s₁ i<j₁ j₁≤s₁ u₁ v₁ ) ) ) )
      ... | ⊨[] _ _ _ _ _ | ⊨[] _ _ _ _ _ = inj₂ ( inj₁ refl )
  trichotomy ( l₃ + l₄ ` loc ) w i s₁ s₂ t₁ t₂
    with find-<-Min⁺ l₃ l₄ loc w i s₂ t₂ | inspect ( find-<-Min⁺ l₃ l₄ loc w i s₂ ) t₂
       | find-<-Min⁺ l₃ l₄ loc w i s₁ t₁ | inspect ( find-<-Min⁺ l₃ l₄ loc w i s₁ ) t₁
  ... | ( min-t₂ , _ ) | [ eq₂ ] | ( min-t₁ , _ ) | [ eq₁ ]
    with min-t₁ | min-t₂
  ... | ⊨inl _ _ _ _ _ _ v₁' | ⊨inl _ _ _ _ _ _ v₂' =
    case-⊎ (λ ord → inj₁ ( choice i s₂ s₁ t₂ t₁ ( subst₂ (λ x y → l₃ ∣ l₄ ∣ loc ∣ w ∣ i ∣ s₂ ∣ s₁ ⊢⁺ x < y) ( sym ( cong proj₁ eq₂ ) ) ( sym ( cong proj₁ eq₁ ) ) ( inlinl i s₂ s₁ v₂' v₁' ord ) ) ))
           (case-⊎ (λ eq → inj₂ ( inj₁ eq ))
                    (λ ord → inj₂ ( inj₂ ( choice i s₁ s₂ t₁ t₂ ( subst₂ (λ x y → l₃ ∣ l₄ ∣ loc ∣ w ∣ i ∣ s₁ ∣ s₂ ⊢⁺ x < y) ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₂ ) ) ( inlinl i s₁ s₂ v₁' v₂' ord ) ) )) ))
           ( trichotomy l₃ w i s₁ s₂ v₁' v₂' )
  ... | ⊨inl _ _ _ _ _ _ v₁' | ⊨inr _ _ _ _ _ _ v₂' = inj₂ ( inj₂ ( choice i s₁ s₂ t₁ t₂ ( subst₂ (λ x y → l₃ ∣ l₄ ∣ loc ∣ w ∣ i ∣ s₁ ∣ s₂ ⊢⁺ x < y) ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₂ ) ) ( inlinr i s₁ s₂ v₁' v₂' ) ) ) )
  ... | ⊨inr _ _ _ _ _ _ v₁' | ⊨inl _ _ _ _ _ _ v₂' = inj₁ ( choice i s₂ s₁ t₂ t₁ ( subst₂ (λ x y → l₃ ∣ l₄ ∣ loc ∣ w ∣ i ∣ s₂ ∣ s₁ ⊢⁺ x < y) ( sym ( cong proj₁ eq₂ ) ) ( sym ( cong proj₁ eq₁ ) ) ( inlinr i s₂ s₁ v₂' v₁' ) ) )
  ... | ⊨inr _ _ _ _ _ _ v₁' | ⊨inr _ _ _ _ _ _ v₂' =
    case-⊎ (λ ord → inj₁ ( choice i s₂ s₁ t₂ t₁ ( subst₂ (λ x y → l₃ ∣ l₄ ∣ loc ∣ w ∣ i ∣ s₂ ∣ s₁ ⊢⁺ x < y) ( sym ( cong proj₁ eq₂ ) ) ( sym ( cong proj₁ eq₁ ) ) ( inrinr i s₂ s₁ v₂' v₁' ord ) ) ))
           (case-⊎ (λ eq → inj₂ ( inj₁ eq ))
                    (λ ord → inj₂ ( inj₂ ( choice i s₁ s₂ t₁ t₂ ( subst₂ (λ x y → l₃ ∣ l₄ ∣ loc ∣ w ∣ i ∣ s₁ ∣ s₂ ⊢⁺ x < y) ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₂ ) ) ( inrinr i s₁ s₂ v₁' v₂' ord ) ) )) ))
           ( trichotomy l₄ w i s₁ s₂ v₁' v₂' )
  trichotomy ( l₃ ● l₄ ` loc ) w i s₁ s₂ t₁ t₂ = trichotomy-● l₃ l₄ loc w i s₁ s₂ t₁ t₂
    where
      trichotomy-● : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i s₁ s₂ : ℕ )
        → ( t₁ : ( l ● r ` loc ) , i , s₁ ⊨ w )
        → ( t₂ : ( l ● r ` loc ) , i , s₂ ⊨ w )
        → ( l ● r ` loc ) ∣ w ∣ i ⊢ s₂ < s₁ ⊎ s₁ ≡ s₂ ⊎ ( l ● r ` loc ) ∣ w ∣ i ⊢ s₁ < s₂
      trichotomy-● l r loc w i s₁ s₂ t₁ t₂
        with find-<-Min● l r loc w i s₁ t₁ | inspect ( find-<-Min● l r loc w i s₁ ) t₁
           | find-<-Min● l r loc w i s₂ t₂ | inspect ( find-<-Min● l r loc w i s₂ ) t₂
      ... | ( min-t₁ , _ ) | [ eq₁ ] | ( min-t₂ , _ ) | [ eq₂ ]
        with min-t₁ | min-t₂
      ... | ⊨● _ _ _ _ _ _ j₁ _ _ u₁ v₁ | ⊨● _ _ _ _ _ _ j₂ _ _ u₂ v₂
        with trichotomy l w i j₂ j₁ u₂ u₁
      ... | inj₁ j₁<j₂ =
        inj₂ ( inj₂ ( seq i s₁ s₂ t₁ t₂ ( subst₂ (λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ s₁ ∣ s₂ ⊢● x < y) ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₂ ) ) ( seq₁ i j₁ s₁ j₂ s₂ u₁ v₁ u₂ v₂ j₁<j₂ ) ) ) )
      ... | inj₂ ( inj₂ j₂<j₁ ) =
        inj₁ ( seq i s₂ s₁ t₂ t₁ ( subst₂ (λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ s₂ ∣ s₁ ⊢● x < y) ( sym ( cong proj₁ eq₂ ) ) ( sym ( cong proj₁ eq₁ ) ) ( seq₁ i j₂ s₂ j₁ s₁ u₂ v₂ u₁ v₁ j₂<j₁ ) ) )
      ... | inj₂ ( inj₁ j₂≡j₁ )
        with j₂≡j₁
      ... | refl =
        case-⊎ (λ s₁<s₂ →
          inj₂ ( inj₂ ( seq i s₁ s₂ t₁ t₂ ( subst₂ (λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ s₁ ∣ s₂ ⊢● x < y) ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₂ ) ) ( seq₂ i j₁ j₁ s₁ s₂ u₁ v₁ u₂ v₂ refl s₁<s₂ ) ) ) ))
               (case-⊎ (λ s₂≡s₁ → inj₂ ( inj₁ ( sym s₂≡s₁ ) ))
                        (λ s₂<s₁ →
                          inj₁ ( seq i s₂ s₁ t₂ t₁ ( subst₂ (λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ s₂ ∣ s₁ ⊢● x < y) ( sym ( cong proj₁ eq₂ ) ) ( sym ( cong proj₁ eq₁ ) ) ( seq₂ i j₁ j₁ s₂ s₁ u₂ v₂ u₁ v₁ refl s₂<s₁ ) ) ) ))
               ( trichotomy r w j₁ s₂ s₁ v₂ v₁ )

  -- Purpose : decision procedure for the base ( Mamouras ) order
  --           l ∣ w ∣ i ⊢ j' < j on two matches of the same regex l from the
  --           same start i.  ( This is the order claimed by Mamouras to be
  --           the greedy order ; it is not the POSIX order, and the greedy
  --           claim is not verified here. )
  -- Used in : Min*-best-go ( descend to a strictly better head ) and
  --           recursively in its own * / + / ● cases.
  -- Idea    : structural on l. ε / $ : no ( the evidence is unique, ( ) ).
  --           * : work with the minimal evidence ( find-<-Min* + inspect ) :
  --           a ⊨[] below a ⊨∷ is impossible ( ¬⊢⋆-[]-∷ / <-irrefl ) ;
  --           ⊨∷ vs ⊨[] → *-cons-nil ; ⊨∷ vs ⊨∷ → compare the heads by
  --           recursion on r, equal heads → compare the tails by recursion on
  --           r* ( *-tail ). * No-answers use find-<-Min*-canon +
  --           ¬⋆-order₁ / ¬⋆-order₂.
  --           + : work with the minimal evidence ( find-<-Min⁺ + inspect ) :
  --           inl < inr by inlinr ; inr < inl impossible ( inr≮inl ) ; same
  --           shape → recurse on the branch, with the no-answer from
  --           Min⁺-inl / Min⁺-inr + ¬inl<inl⁺ / ¬inr<inr⁺.
  --           ● : work with the minimal evidence ( find-<-Min● + inspect ) :
  --           compare the minimal splits by recursion on l₁ ( seq₁ ) ; equal
  --           splits → compare the tails by recursion on l₂ ( seq₂ ). No-
  --           answers use find-<-Min●-canon + ¬●-order₁ / ¬●-order₂.
  decide-⊢< : ∀ ( l : RE ) ( w : List Char ) ( i j j' : ℕ )
    → l , i , j ⊨ w → l , i , j' ⊨ w
    → Dec ( l ∣ w ∣ i ⊢ j' < j )
  decide-⊢< ε w i j j' ( ⊨ε _ _ ) ( ⊨ε _ _ ) = no (λ ())
  decide-⊢< ( $ c ` loc ) w i j j' ( ⊨$ _ _ _ _ _ ) ( ⊨$ _ _ _ _ _ ) = no (λ ())
  decide-⊢< ( r * nε ` loc ) w i k k' t₂ t₁
    with find-<-Min* r nε loc w i k' t₁ | inspect ( find-<-Min* r nε loc w i k' ) t₁
       | find-<-Min* r nε loc w i k t₂ | inspect ( find-<-Min* r nε loc w i k ) t₂
  ... | ( min-t₁ , _ ) | [ eq1 ] | ( min-t₂ , _ ) | [ eq2 ]
    with min-t₁ | min-t₂
  ... | ⊨[] _ _ _ _ _ | ⊨[] _ _ _ _ _ =
    no (λ { ( star _ _ _ u₁ u₂ ev ) → refute u₁ u₂ ev })
    where
      refute : ( u₁ u₂ : ( r * nε ` loc ) , i , i ⊨ w )
        → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i i i ( proj₁ ( find-<-Min* r nε loc w i i u₁ ) ) ( proj₁ ( find-<-Min* r nε loc w i i u₂ ) ) → ⊥
      refute ( ⊨[] _ _ _ _ _ ) u₂ ev with proj₁ ( find-<-Min* r nε loc w i i ( ⊨[] r nε loc w i ) )
      ... | min-u₁ with min-u₁
      ...   | ⊨[] _ _ _ _ _ = ¬⊢⋆-[]-∷ ( proj₁ ( find-<-Min* r nε loc w i i u₂ ) ) ev
      ...   | ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤i , _ , _ ) = <-irrefl refl ( ≤-trans i<j j≤i )
      refute ( ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤i , _ , _ ) ) u₂ ev = <-irrefl refl ( ≤-trans i<j j≤i )
  ... | ⊨[] _ _ _ _ _ | ⊨∷ _ _ _ _ _ _ _ =
    no (λ { ( star _ _ _ u₁ u₂ ev ) → refute u₁ u₂ ev })
    where
      refute : ( u₁ : ( r * nε ` loc ) , i , i ⊨ w ) ( u₂ : ( r * nε ` loc ) , i , k ⊨ w )
        → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i i k ( proj₁ ( find-<-Min* r nε loc w i i u₁ ) ) ( proj₁ ( find-<-Min* r nε loc w i k u₂ ) ) → ⊥
      refute ( ⊨[] _ _ _ _ _ ) u₂ ev with proj₁ ( find-<-Min* r nε loc w i i ( ⊨[] r nε loc w i ) )
      ... | min-u₁ with min-u₁
      ...   | ⊨[] _ _ _ _ _ = ¬⊢⋆-[]-∷ ( proj₁ ( find-<-Min* r nε loc w i k u₂ ) ) ev
      ...   | ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤i , _ , _ ) = <-irrefl refl ( ≤-trans i<j j≤i )
      refute ( ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤i , _ , _ ) ) u₂ ev = <-irrefl refl ( ≤-trans i<j j≤i )
  ... | ⊨∷ _ _ _ _ _ _ ( j' , i<j' , j'≤k' , u₁' , u₂' ) | ⊨[] _ _ _ _ _ =
    yes ( star i k' k t₁ t₂
          ( subst₂ (λ x y → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i k' k x y)
                   ( sym ( cong proj₁ eq1 ) ) ( sym ( cong proj₁ eq2 ) )
                   ( *-cons-nil i j' k' i<j' j'≤k' u₁' u₂' ) ) )
  ... | ⊨∷ _ _ _ _ _ _ ( j' , i<j' , j'≤k' , u₁' , u₂' ) | ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤k , u₁ , u₂ )
    with decide-⊢< r w i j j' u₁ u₁'
  ... | yes r< =
    yes ( star i k' k t₁ t₂
          ( subst₂ (λ x y → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i k' k x y)
                   ( sym ( cong proj₁ eq1 ) ) ( sym ( cong proj₁ eq2 ) )
                   ( *-head i j' j k' k i<j' j'≤k' i<j j≤k u₁' u₂' u₁ u₂ r< ) ) )
  ... | no ¬r< with j' ≟ j
  ... | yes refl =
    dec-elim ( decide-⊢< ( r * nε ` loc ) w j' k k' u₂ u₂' )
      ( λ t< → yes ( star i k' k t₁ t₂
        ( subst₂ ( λ x y → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i k' k x y )
                 ( sym ( cong proj₁ eq1 ) ) ( sym ( cong proj₁ eq2 ) )
                 ( *-tail i j' j k' k i<j' j'≤k' i<j j≤k u₁' u₂' u₁ u₂ refl t< ) ) ) )
      ( λ ¬t< → no ( λ { ( star _ _ _ t₃ t₄ ev ) →
        let ev1 = subst₂ ( λ x y → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i k' k x y )
                         ( find-<-Min*-canon r nε loc w i k' t₃ t₁ )
                         ( find-<-Min*-canon r nε loc w i k t₄ t₂ )
                         ev
            ev' = subst₂ ( λ x y → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i k' k x y )
                         ( cong proj₁ eq1 ) ( cong proj₁ eq2 ) ev1
        in ¬⋆-order₁ k' k j j' refl i<j' j'≤k' i<j j≤k u₁' u₂' u₁ u₂ ¬r< ¬t< ev' } ) )
  ... | no ¬j'≡j =
    no ( λ { ( star _ _ _ t₃ t₄ ev ) →
      let ev1 = subst₂ ( λ x y → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i k' k x y )
                       ( find-<-Min*-canon r nε loc w i k' t₃ t₁ )
                       ( find-<-Min*-canon r nε loc w i k t₄ t₂ )
                       ev
          ev' = subst₂ ( λ x y → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i k' k x y )
                       ( cong proj₁ eq1 ) ( cong proj₁ eq2 ) ev1
      in ¬⋆-order₂ k' k j j' i<j j'≤k' i<j' j≤k u₁ u₂' u₁' u₂ ¬r< ( λ eq → ¬j'≡j ( sym eq ) ) ev' } )
  decide-⊢< ( l₁ + l₂ ` loc ) w i j j' t₂ t₁
    with find-<-Min⁺ l₁ l₂ loc w i j' t₁ | inspect ( find-<-Min⁺ l₁ l₂ loc w i j' ) t₁
       | find-<-Min⁺ l₁ l₂ loc w i j t₂ | inspect ( find-<-Min⁺ l₁ l₂ loc w i j ) t₂
  ... | ( min-t' , mp' ) | [ eq' ] | ( min-t , mp ) | [ eq ]
    with min-t' | min-t
  -- minimal at j' is inl and at j is inr : inl < inr
  ... | ⊨inl _ _ _ _ _ _ v | ⊨inr _ _ _ _ _ _ u =
    yes ( choice i j' j t₁ t₂
          ( subst₂ (λ x y → l₁ ∣ l₂ ∣ loc ∣ w ∣ i ∣ j' ∣ j ⊢⁺ x < y)
                   ( sym ( cong proj₁ eq' ) ) ( sym ( cong proj₁ eq ) )
                   ( inlinr i j' j v u ) ) )
  -- minimal at j' is inr and at j is inl : impossible
  ... | ⊨inr _ _ _ _ _ _ v | ⊨inl _ _ _ _ _ _ u
    = no (λ { ( choice {l₁} {l₂} {loc} {w} _ _ _ t₁a t₂a ev ) →
          inr≮inl
            ( subst₂ (λ x y → l₁ ∣ l₂ ∣ loc ∣ w ∣ i ∣ j' ∣ j ⊢⁺ x < y)
                     ( proj₂ ( Min⁺-inr l₁ l₂ loc w i j' ( <-Min⁺-inr¬ mp' ) t₁a ) ) ( proj₂ ( Min⁺-inl l₁ l₂ loc w i j u t₂a ) )
                     ev ) })
  -- both minimal matches are inl : recurse on the left regex
  ... | ⊨inl _ _ _ _ _ _ v | ⊨inl _ _ _ _ _ _ u =
    dec-elim ( decide-⊢< l₁ w i j j' u v )
      ( λ u<v → yes ( choice i j' j t₁ t₂
             ( subst₂ (λ x y → l₁ ∣ l₂ ∣ loc ∣ w ∣ i ∣ j' ∣ j ⊢⁺ x < y)
                      ( sym ( cong proj₁ eq' ) ) ( sym ( cong proj₁ eq ) )
                      ( inlinl i j' j v u u<v ) ) ) )
      ( λ ¬u<v → no (λ { ( choice {l₁} {l₂} {loc} {w} _ _ _ t₁a t₂a ev ) →
             let ( a₁ , eq₁ ) = Min⁺-inl l₁ l₂ loc w i j' v t₁a
                 ( a₂ , eq₂ ) = Min⁺-inl l₁ l₂ loc w i j u t₂a
             in ¬inl<inl⁺ ¬u<v
                  ( subst₂ (λ x y → l₁ ∣ l₂ ∣ loc ∣ w ∣ i ∣ j' ∣ j ⊢⁺ x < y)
                           eq₁ eq₂ ev ) }) )
  -- both minimal matches are inr : recurse on the right regex
  ... | ⊨inr _ _ _ _ _ _ v | ⊨inr _ _ _ _ _ _ u =
    dec-elim ( decide-⊢< l₂ w i j j' u v )
      ( λ u<v → yes ( choice i j' j t₁ t₂
             ( subst₂ (λ x y → l₁ ∣ l₂ ∣ loc ∣ w ∣ i ∣ j' ∣ j ⊢⁺ x < y)
                      ( sym ( cong proj₁ eq' ) ) ( sym ( cong proj₁ eq ) )
                      ( inrinr i j' j v u u<v ) ) ) )
      ( λ ¬u<v → no (λ { ( choice {l₁} {l₂} {loc} {w} _ _ _ t₁a t₂a ev ) →
             let ( a₁ , eq₁ ) = Min⁺-inr l₁ l₂ loc w i j' ( <-Min⁺-inr¬ mp' ) t₁a
                 ( a₂ , eq₂ ) = Min⁺-inr l₁ l₂ loc w i j ( <-Min⁺-inr¬ mp ) t₂a
             in ¬inr<inr⁺ ¬u<v
                  ( subst₂ (λ x y → l₁ ∣ l₂ ∣ loc ∣ w ∣ i ∣ j' ∣ j ⊢⁺ x < y)
                           eq₁ eq₂ ev ) }) )
  decide-⊢< ( l₁ ● l₂ ` loc' ) w i j j' T₂ T₁
    with find-<-Min● l₁ l₂ loc' w i j T₂ | inspect ( find-<-Min● l₁ l₂ loc' w i j ) T₂
       | find-<-Min● l₁ l₂ loc' w i j' T₁ | inspect ( find-<-Min● l₁ l₂ loc' w i j' ) T₁
  ... | ( min-t , _ ) | [ eqt ] | ( min-t' , _ ) | [ eqt' ]
    with min-t | min-t'
  ... | ⊨● _ _ _ _ _ _ min-s _ _ min-u₁ min-u₂ | ⊨● _ _ _ _ _ _ min-s' _ _ min-u₁' min-u₂'
    with decide-⊢< l₁ w i min-s min-s' min-u₁ min-u₁'
  ... | yes min-s'<min-s =
    yes ( seq i j' j T₁ T₂
          ( subst₂ (λ x y → l₁ ∣ l₂ ∣ loc' ∣ w ∣ i ∣ j' ∣ j ⊢● x < y)
                   ( sym ( cong proj₁ eqt' ) ) ( sym ( cong proj₁ eqt ) )
                   ( seq₁ i min-s' j' min-s j min-u₁' min-u₂' min-u₁ min-u₂ min-s'<min-s ) ) )
  ... | no ¬min-s'<min-s with min-s ≟ min-s'
  ... | yes min-s≡min-s' =
    dec-elim ( decide-⊢< l₂ w min-s' j j' ( subst (λ x → l₂ , x , j ⊨ w ) min-s≡min-s' min-u₂ ) min-u₂' )
      ( λ j'<j →
           yes ( seq i j' j T₁ T₂
                 ( subst₂ (λ x y → l₁ ∣ l₂ ∣ loc' ∣ w ∣ i ∣ j' ∣ j ⊢● x < y)
                          ( sym ( cong proj₁ eqt' ) ) ( sym ( cong proj₁ eqt ) )
                          ( seq₂ i min-s' min-s j' j min-u₁' min-u₂' min-u₁ min-u₂
                                 ( sym min-s≡min-s' ) j'<j ) ) ) )
      ( λ ¬j'<j → no (λ { ( seq _ _ _ T₁a T₂a ev ) →
             let ev' = subst₂ (λ x y → l₁ ∣ l₂ ∣ loc' ∣ w ∣ i ∣ j' ∣ j ⊢● x < y)
                              ( find-<-Min●-canon l₁ l₂ loc' w i j' T₁a T₁ )
                              ( find-<-Min●-canon l₁ l₂ loc' w i j T₂a T₂ )
                              ev
                 ev'' = subst₂ (λ x y → l₁ ∣ l₂ ∣ loc' ∣ w ∣ i ∣ j' ∣ j ⊢● x < y)
                               ( cong proj₁ eqt' ) ( cong proj₁ eqt )
                               ev'
             in ¬●-order₁ min-u₁ min-u₂ min-u₁' min-u₂' ¬min-s'<min-s ¬j'<j ev'' }) )
  ... | no ¬min-s≡min-s' = no (λ { ( seq _ _ _ T₁a T₂a ev ) →
             let ev' = subst₂ (λ x y → l₁ ∣ l₂ ∣ loc' ∣ w ∣ i ∣ j' ∣ j ⊢● x < y)
                              ( find-<-Min●-canon l₁ l₂ loc' w i j' T₁a T₁ )
                              ( find-<-Min●-canon l₁ l₂ loc' w i j T₂a T₂ )
                              ev
                 ev'' = subst₂ (λ x y → l₁ ∣ l₂ ∣ loc' ∣ w ∣ i ∣ j' ∣ j ⊢● x < y)
                               ( cong proj₁ eqt' ) ( cong proj₁ eqt )
                               ev'
             in ¬●-order₂ min-u₁ min-u₂ min-u₁' min-u₂' ¬min-s'<min-s ¬min-s≡min-s' ev'' })

  -- Purpose : decide whether a given position a is a valid split point of
  --           l ● r on ( i , k ) : ( l , i , a ⊨ w ) × ( r , a , k ⊨ w ).
  -- Used in : find-<-Min● and find-<-Min●-canon, as the dec predicate of
  --           dec-∃-range-Max.
  -- Idea    : two independent calls to ⊨?.
  Min●-val : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i k : ℕ )
    → ( a : ℕ ) → Dec ( ( l , i , a ⊨ w ) × ( r , a , k ⊨ w ) )
  Min●-val l r loc w i k a with ⊨? l i a w
  ... | no ¬l = no (λ { (t₁a , _) → ¬l t₁a })
  ... | yes t₁a with ⊨? r a k w
  ...   | no ¬r = no (λ { (_ , t₂a) → ¬r t₂a })
  ...   | yes t₂a = yes ( t₁a , t₂a )

  -- Purpose : given the result of the maximal-split search, build the minimal
  --           ● evidence ( or ⊥ if the search found no working split ).
  -- Used in : find-<-Min● only.
  -- Idea    : inj₂ ( no split ) contradicts the witness extracted from the
  --           given evidence T. inj₁ : take the maximal split a as the
  --           evidence ; its minimality side condition ( no strictly larger
  --           working split ) follows directly from the maximality property
  --           of dec-∃-range-Max by <-irrefl.
  find-<-Min●-go : ∀ ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    → ( ( Σ[ a ∈ ℕ ] i ≤ a × a ≤ j × (( l , i , a ⊨ w ) × ( r , a , j ⊨ w )) × (∀ ( j' : ℕ ) → i ≤ j' → j' ≤ j → ( l , i , j' ⊨ w ) × ( r , j' , j ⊨ w ) → j' ≤ a ) )
        ⊎ ( ¬ ( ∃[ a ] i ≤ a × a ≤ j × ( l , i , a ⊨ w ) × ( r , a , j ⊨ w ) ) ) )
    → ( T : l ● r ` loc , i , j ⊨ w )
    → ∃[ t ] ( <-Min● l r loc w i j t )
  find-<-Min●-go l r loc w i j ( inj₂ ¬ex ) T = ⊥-elim ( ¬ex ( witness T ) )
    where
      witness : ( t : l ● r ` loc , i , j ⊨ w ) → ∃[ a ] i ≤ a × a ≤ j × ( l , i , a ⊨ w ) × ( r , a , j ⊨ w )
      witness ( ⊨● _ _ _ _ _ _ j₀ _ _ t₁ t₂ ) = j₀ , rij⊨w→i≤j t₁ , rij⊨w→i≤j t₂ , t₁ , t₂
  find-<-Min●-go l r loc w i j ( inj₁ ( a , _ , _ , ( t₁a , t₂a ) , max ) ) T =
    ⊨● l r loc i j w a (rij⊨w→i≤j t₁a) (rij⊨w→i≤j t₂a) t₁a t₂a ,
    <-min-● l r loc w i a j (rij⊨w→i≤j t₁a) (rij⊨w→i≤j t₂a) t₁a t₂a
      (λ { ( a' , t₁a' , t₂a' , a<a' ) →
        ⊥-elim ( <-irrefl refl ( ≤-trans a<a' (max a' (rij⊨w→i≤j t₁a') (rij⊨w→i≤j t₂a') (t₁a' , t₂a')) ) ) })

  -- Purpose : compute, for any evidence T of l ● r on ( i , j ), a minimal ●
  --           evidence ( <-Min● ) : the maximal working split a in [ i , j ].
  -- Used in : the seq constructor ( premise indexed by the canonical minimal
  --           evidence ), trichotomy-●, decide-⊢< ( ● case ) and
  --           find-<-Min●-canon.
  -- Idea    : run dec-∃-range-Max over [ i , j ] with dec predicate Min●-val,
  --           then hand the result to find-<-Min●-go. The result does not
  --           depend on the starting evidence T, which is exactly what makes
  --           find-<-Min●-canon ( refl ) and the subst₂ transports work.
  {-# TERMINATING #-}
  find-<-Min● l r loc w i j T =
    find-<-Min●-go l r loc w i j
      ( dec-∃-range-Max
          (λ a → ( l , i , a ⊨ w ) × ( r , a , j ⊨ w ))
          (λ a (i≤a : i ≤ a) (a≤j : a ≤ j) → Min●-val l r loc w i j a) )
      T

  -- Purpose : the minimal ● evidence does not depend on the starting
  --           evidence : proj₁ ( find-<-Min● T ) ≡ proj₁ ( find-<-Min● T' ).
  -- Used in : decide-⊢< ( ● case, both no-branches ), to transport arbitrary
  --           ⊢● evidence onto the canonical minimal evidence.
  -- Idea    : both sides reduce to the evidence built from the same closed
  --           dec-∃-range-Max computation, hence refl.
  {-# TERMINATING #-}
  find-<-Min●-canon : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i k : ℕ )
    → ( T T' : l ● r ` loc , i , k ⊨ w )
    → proj₁ ( find-<-Min● l r loc w i k T ) ≡ proj₁ ( find-<-Min● l r loc w i k T' )
  find-<-Min●-canon l r loc w i k T T'
    with dec-∃-range-Max
           (λ a → ( l , i , a ⊨ w ) × ( r , a , k ⊨ w ))
           (λ a (i≤a : i ≤ a) (a≤k : a ≤ k) → Min●-val l r loc w i k a )
  ... | inj₂ ¬ex = ⊥-elim ( ¬ex ( witness T ) )
    where
      witness : ( t : l ● r ` loc , i , k ⊨ w ) → ∃[ a ] i ≤ a × a ≤ k × ( l , i , a ⊨ w ) × ( r , a , k ⊨ w )
      witness ( ⊨● _ _ _ _ _ _ j₀ _ _ t₁ t₂ ) = j₀ , rij⊨w→i≤j t₁ , rij⊨w→i≤j t₂ , t₁ , t₂
  ... | inj₁ ( a , _ ) = refl

  -- Purpose : no ⊢● evidence can relate two canonical minimal ● evidence
  --           when the left splits are not ordered ( ¬ l₁-order ) and, at
  --           equal splits, the right tails are not ordered either.
  -- Used in : decide-⊢< ( ● case, min-s ≡ min-s' branch, no-answer ).
  -- Idea    : case split on the ⊢● constructor : seq₁ contradicts ¬s< via
  --           its left-order premise ; seq₂ ( equal splits ) contradicts
  --           ¬j'< via its right-order premise.
  {-# TERMINATING #-}
  ¬●-order₁ : ∀ { l₁ l₂ loc' w i j j' min-s min-s' }
    → ( min-u₁ : l₁ , i , min-s ⊨ w ) ( min-u₂ : l₂ , min-s , j ⊨ w )
    → ( min-u₁' : l₁ , i , min-s' ⊨ w ) ( min-u₂' : l₂ , min-s' , j' ⊨ w )
    → ¬ ( l₁ ∣ w ∣ i ⊢ min-s' < min-s )
    → ¬ ( l₂ ∣ w ∣ min-s' ⊢ j' < j )
    → l₁ ∣ l₂ ∣ loc' ∣ w ∣ i ∣ j' ∣ j ⊢●
        ( ⊨● l₁ l₂ loc' i j' w min-s' (rij⊨w→i≤j min-u₁') (rij⊨w→i≤j min-u₂') min-u₁' min-u₂' ) <
        ( ⊨● l₁ l₂ loc' i j w min-s (rij⊨w→i≤j min-u₁) (rij⊨w→i≤j min-u₂) min-u₁ min-u₂ )
    → ⊥
  ¬●-order₁ min-u₁ min-u₂ min-u₁' min-u₂' ¬s< ¬j'< ( seq₁ _ _ _ _ _ _ _ _ _ ord ) = ¬s< ord
  ¬●-order₁ min-u₁ min-u₂ min-u₁' min-u₂' ¬s< ¬j'< ( seq₂ _ _ _ _ _ _ _ _ _ eq tail ) = ¬j'< tail

  -- Purpose : as ¬●-order₁, but for unequal splits ( ¬( min-s ≡ min-s' )
  --           instead of the right-tail-order refutation ).
  -- Used in : decide-⊢< ( ● case, min-s ≢ min-s' branch, no-answer ).
  -- Idea    : seq₁ contradicts ¬s< via its left-order premise ; seq₂ carries
  --           an explicit j ≡ j' premise, contradicting ¬eq.
  {-# TERMINATING #-}
  ¬●-order₂ : ∀ { l₁ l₂ loc' w i j j' min-s min-s' }
    → ( min-u₁ : l₁ , i , min-s ⊨ w ) ( min-u₂ : l₂ , min-s , j ⊨ w )
    → ( min-u₁' : l₁ , i , min-s' ⊨ w ) ( min-u₂' : l₂ , min-s' , j' ⊨ w )
    → ¬ ( l₁ ∣ w ∣ i ⊢ min-s' < min-s )
    → ¬ ( min-s ≡ min-s' )
    → l₁ ∣ l₂ ∣ loc' ∣ w ∣ i ∣ j' ∣ j ⊢●
        ( ⊨● l₁ l₂ loc' i j' w min-s' (rij⊨w→i≤j min-u₁') (rij⊨w→i≤j min-u₂') min-u₁' min-u₂' ) <
        ( ⊨● l₁ l₂ loc' i j w min-s (rij⊨w→i≤j min-u₁) (rij⊨w→i≤j min-u₂) min-u₁ min-u₂ )
    → ⊥
  ¬●-order₂ min-u₁ min-u₂ min-u₁' min-u₂' ¬s< ¬eq ( seq₁ _ _ _ _ _ _ _ _ _ ord ) = ¬s< ord
  ¬●-order₂ min-u₁ min-u₂ min-u₁' min-u₂' ¬s< ¬eq ( seq₂ _ _ _ _ _ _ _ _ _ eq tail ) = ¬eq ( sym eq )

  -- Purpose : no ⊢⋆ evidence can relate two minimal ⊨∷ evidence with the
  --           SAME head ( j' ≡ j ) when both the head-order and the
  --           tail-order are refuted.
  -- Used in : decide-⊢< ( * case, equal-head branch, no-answer ).
  -- Idea    : *-head contradicts the head-order refutation ( ¬r< ) ; *-tail
  --           ( same head ) contradicts the tail-order refutation ( ¬t< ).
  {-# TERMINATING #-}
  ¬⋆-order₁ : ∀ { r nε loc w i }
    → ( kL kR : ℕ )
    → ( j j' : ℕ ) → ( j'≡j : j' ≡ j )
    → ( i<j' : i Nat.< j' ) → ( j'≤kL : j' Nat.≤ kL )
    → ( i<j : i Nat.< j ) → ( j≤kR : j Nat.≤ kR )
    → ( u₁' : r , i , j' ⊨ w ) → ( u₂L : r * nε ` loc , j' , kL ⊨ w )
    → ( u₁ : r , i , j ⊨ w ) → ( u₂R : r * nε ` loc , j , kR ⊨ w )
    → ¬ ( r ∣ w ∣ i ⊢ j' < j )
    → ¬ ( ( r * nε ` loc ) ∣ w ∣ j' ⊢ kL < kR )
    → r ∣ nε ∣ loc ∣ w ∣ i ∣ kL ∣ kR ⊢⋆
        ( ⊨∷ r nε loc w i kL ( j' , i<j' , j'≤kL , u₁' , u₂L ) ) <
        ( ⊨∷ r nε loc w i kR ( j , i<j , j≤kR , u₁ , u₂R ) )
    → ⊥
  ¬⋆-order₁ kL kR j .j refl i<j' j'≤kL i<j j≤kR u₁' u₂L u₁ u₂R ¬r< ¬t< ( *-head _ .j .j .kL .kR .i<j' .j'≤kL .i<j .j≤kR .u₁' .u₂L .u₁ .u₂R ord ) = ¬r< ord
  ¬⋆-order₁ kL kR j .j refl i<j' j'≤kL i<j j≤kR u₁' u₂L u₁ u₂R ¬r< ¬t< ( *-tail _ .j .j .kL .kR .i<j' .j'≤kL .i<j .j≤kR .u₁' .u₂L .u₁ .u₂R eq tail ) = ¬t< tail

  -- Purpose : as ¬⋆-order₁, but for DISTINCT heads ( ¬( j ≡ j' ) instead of
  --           the tail-order refutation ).
  -- Used in : decide-⊢< ( * case, head-inequality branch, no-answer ).
  -- Idea    : *-head contradicts the head-order refutation ( ¬r< ) ; *-tail
  --           carries an explicit j ≡ j' premise, contradicting ¬eq.
  {-# TERMINATING #-}
  ¬⋆-order₂ : ∀ { r nε loc w i }
    → ( kL kR : ℕ )
    → ( j j' : ℕ ) → ( i<j : i Nat.< j ) → ( j'≤kL : j' Nat.≤ kL )
    → ( i<j' : i Nat.< j' ) → ( j≤kR : j Nat.≤ kR )
    → ( u₁ : r , i , j ⊨ w ) → ( u₂L : r * nε ` loc , j' , kL ⊨ w )
    → ( u₁' : r , i , j' ⊨ w ) → ( u₂R : r * nε ` loc , j , kR ⊨ w )
    → ¬ ( r ∣ w ∣ i ⊢ j' < j )
    → ¬ ( j ≡ j' )
    → r ∣ nε ∣ loc ∣ w ∣ i ∣ kL ∣ kR ⊢⋆
        ( ⊨∷ r nε loc w i kL ( j' , i<j' , j'≤kL , u₁' , u₂L ) ) <
        ( ⊨∷ r nε loc w i kR ( j , i<j , j≤kR , u₁ , u₂R ) )
    → ⊥
  ¬⋆-order₂ kL kR j j' i<j j'≤kL i<j' j≤kR u₁ u₂L u₁' u₂R ¬r< ¬eq ( *-head _ .j' .j .kL .kR .i<j' .j'≤kL .i<j .j≤kR .u₁' .u₂L .u₁ .u₂R ord ) = ¬r< ord
  ¬⋆-order₂ kL kR j j' i<j j'≤kL i<j' j≤kR u₁ u₂L u₁' u₂R ¬r< ¬eq ( *-tail _ .j' .j .kL .kR .i<j' .j'≤kL .i<j .j≤kR .u₁' .u₂L .u₁ .u₂R eq tail ) = ¬eq ( sym eq )

  -- Purpose : decide whether r * nε on ( i , k ) admits a non-empty ( ⊨∷ )
  --           decomposition : some head j with r , i , j ⊨ w and a tail
  --           r * nε , j , k ⊨ w.
  -- Used in : find-<-Min* and find-<-Min*-canon.
  -- Idea    : dec-∃-range over [ suc i , k ] with the dec predicate the pair
  --           of ⊨? decisions.
  Min*-some : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i k : ℕ )
    → Dec ( ∃[ j ] ( i Nat.< j ) × ( j Nat.≤ k ) × ( r , i , j ⊨ w ) × ( r * nε ` loc , j , k ⊨ w ) )
  Min*-some r nε loc w i k = dec-∃-range ( suc i ) k
    ( λ j → ( r , i , j ⊨ w ) × ( r * nε ` loc , j , k ⊨ w ) )
    ( λ j _ _ → dec-elim ( ⊨? r i j w )
        ( λ t₁ → dec-elim ( ⊨? ( r * nε ` loc ) j k w )
          ( λ t₂ → yes ( t₁ , t₂ ) )
          ( λ ¬t₂ → no (λ { ( _ , t₂ ) → ¬t₂ t₂ }) ) )
        ( λ ¬t₁ → no (λ { ( t₁ , _ ) → ¬t₁ t₁ }) ) )

  -- Purpose : from some head j of a ⊨∷ match, descend through strictly
  --           better heads ( r ∣ w ∣ i ⊢ j' < j ) to a minimal head, then
  --           minimize the tail, yielding ←Min*.
  -- Used in : find-<-Min* ( ⊨∷ case ).
  -- Idea    : search [ suc i , k ] for a better head via dec-∃-range, the
  --           head-order being decided by decide-⊢< on r ; if one exists,
  --           recurse on it ( accepted by the termination pragma, since the
  --           descent is on a strictly better head ) ; if none exists, the
  --           current head is minimal and the tail is replaced by its own
  --           find-<-Min* minimum ( <-min-∷ side condition ¬bh ).
  --
  -- WHY THIS MODULE NEEDS --no-positivity-check ( finding )
  -- Removing the flag makes Agda reject this mutual block :
  --   "_∣_∣_⊢_<_ is not strictly positive, because it occurs … in the
  --    third argument of dec-∃-range in the 12th argument of <the with-
  --    abstraction of Min*-best-go> …, which is an index of _∣_∣_⊢_<_. "
  -- The cause is a definitional CYCLE between the base order and the star
  -- minimality, both living in this mutual block :
  --   1. base order → minimality : the star constructor of _∣_∣_⊢_<_ takes
  --      as premise  ⊢⋆ ( proj₁ ( find-<-Min* … t₁ ) ) < ( proj₁ ( find-<-Min* … t₂ ) ),
  --      i.e. to prove one * -match smaller than another you compare their
  --      CANONICAL MINIMAL forms, so find-<-Min*'s type sits in a premise
  --      of the base order's constructor ;
  --   2. minimality → base order : this function's with clause decides
  --      dec-∃-range ( suc i ) k ( λ j' → … × ( r ∣ w ∣ i ⊢ j' < j ) ), i.e.
  --      "is there a strictly better head" is decided by the BASE ORDER
  --      itself.
  -- So the base order's type flows through this function's ( mutually
  -- recursive ) with-abstraction type and back into its own constructor
  -- indices : a data type is not strictly positive in its own mutual block,
  -- and the check ( computed over the whole block, functions included )
  -- flags it.  The circularity is broken SEMANTICALLY, not syntactically :
  -- the base order is introduced only by its own ( positive ) constructors
  -- and refuted only by inspecting them ( the ( ) -cases and the
  -- ¬⋆-order / ¬●-order contradictions ) ; the minimality relations are
  -- built by total functions and consumed by plain pattern matching ; the
  -- ¬∃ … ( r ∣ w ∣ i ⊢ j' < j ) side conditions are assumptions refuted,
  -- never structures reduced.  Hence the block is safe BY INSPECTION while
  -- the checker cannot see through the cycle — the flag waives Agda's
  -- blanket positivity guarantee for it.  The structural alternative ( e.g.
  -- stop indexing the star constructor by proj₁ ( find-<-Min* … ) ) would
  -- undermine the design : indexing the order constructors by the canonical
  -- minimal evidence is what makes decide-⊢< / trichotomy and the refl-
  -- based canon lemmas go through.
  {-# TERMINATING #-}
  Min*-best-go : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i k : ℕ )
    → ( j : ℕ ) → ( i<j : i Nat.< j ) → ( j≤k : j Nat.≤ k )
    → ( t₁ : r , i , j ⊨ w ) → ( t₂ : r * nε ` loc , j , k ⊨ w )
    → ∃[ t' ] <-Min* r nε loc w i k t'
  Min*-best-go r nε loc w i k j i<j j≤k t₁ t₂
    with dec-∃-range ( suc i ) k
      ( λ j' → ( r , i , j' ⊨ w ) × ( r * nε ` loc , j' , k ⊨ w ) × ( r ∣ w ∣ i ⊢ j' < j ) )
      ( λ j' i<j' j'≤k → dec-elim ( ⊨? r i j' w )
        ( λ t₁' → dec-elim ( ⊨? ( r * nε ` loc ) j' k w )
          ( λ t₂' → dec-elim ( decide-⊢< r w i j j' t₁ t₁' )
            ( λ r< → yes ( t₁' , t₂' , r< ) )
            ( λ ¬r< → no (λ { ( _ , _ , r< ) → ¬r< r< }) ) )
          ( λ ¬t₂' → no (λ { ( _ , t₂' , _ ) → ¬t₂' t₂' }) ) )
        ( λ ¬t₁' → no (λ { ( t₁' , _ , _ ) → ¬t₁' t₁' }) ) )
  ... | yes ( j' , i<j' , j'≤k , t₁' , t₂' , r< ) = Min*-best-go r nε loc w i k j' i<j' j'≤k t₁' t₂'
  ... | no ¬bh =
    let ( t₂min , t₂pf ) = find-<-Min* r nε loc w j k t₂
    in ( ⊨∷ r nε loc w i k ( j , i<j , j≤k , t₁ , t₂min ) ,
         <-min-∷ r nε loc w i j k i<j j≤k t₁ t₂min t₂pf ¬bh )

  -- Purpose : compute, for any evidence t of r * nε on ( i , k ), the minimal
  --           * evidence ( <-Min* ) : ⊨[] for the empty match, otherwise a
  --           ⊨∷ with a minimal head and a minimal tail.
  -- Used in : the star constructor, trichotomy-*, decide-⊢< ( * case ),
  --           Min*-best-go ( tail minimization ) and find-<-Min*-canon.
  -- Idea    : ⊨[] → trivially minimal ( <-min-[] ). ⊨∷ → Min*-some provides
  --           some head, and Min*-best-go descends to the minimal one ; the
  --           no case is impossible, since the ⊨∷ evidence itself is a
  --           witness of a non-empty decomposition.
  {-# TERMINATING #-}
  find-<-Min* r nε loc w i k ( ⊨[] _ _ _ _ _ ) =
    ( ⊨[] r nε loc w i ) , <-min-[] r nε loc w i
  find-<-Min* r nε loc w i k ( ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤k , t₁ , t₂ ) )
    with Min*-some r nε loc w i k
  ... | yes ( j₀ , i<j₀ , j₀≤k , t₁₀ , t₂₀ ) = Min*-best-go r nε loc w i k j₀ i<j₀ j₀≤k t₁₀ t₂₀
  ... | no ¬ex = ⊥-elim ( ¬ex ( j , i<j , j≤k , t₁ , t₂ ) )

  -- Purpose : the minimal * evidence does not depend on the starting
  --           evidence : proj₁ ( find-<-Min* t ) ≡ proj₁ ( find-<-Min* t' ).
  -- Used in : decide-⊢< ( * case, both no-branches ), to transport arbitrary
  --           ⊢⋆ evidence onto the canonical minimal evidence.
  -- Idea    : ⊨[] / ⊨[] → refl. The mixed ⊨[] / ⊨∷ cases are empty : ⊨[]
  --           forces i ≡ k while ⊨∷ forces i < k. ⊨∷ / ⊨∷ → both sides
  --           reduce through the same closed Min*-some / Min*-best-go
  --           computation, hence refl.
  {-# TERMINATING #-}
  find-<-Min*-canon : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i k : ℕ )
    → ( t t' : r * nε ` loc , i , k ⊨ w )
    → proj₁ ( find-<-Min* r nε loc w i k t ) ≡ proj₁ ( find-<-Min* r nε loc w i k t' )
  find-<-Min*-canon r nε loc w i k t t' with t | t'
  ... | ⊨[] _ _ _ _ _ | ⊨[] _ _ _ _ _ = refl
  ... | ⊨[] _ _ _ _ _ | ⊨∷ _ _ _ _ _ _ ( j' , i<j' , j'≤k , _ , _ ) =
    ⊥-elim ( <-irrefl refl ( ≤-trans i<j' j'≤k ) )
  ... | ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤k , _ , _ ) | ⊨[] _ _ _ _ _ =
    ⊥-elim ( <-irrefl refl ( ≤-trans i<j j≤k ) )
  ... | ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤k , t₁ , t₂ ) | ⊨∷ _ _ _ _ _ _ ( j' , i<j' , j'≤k , t₁' , t₂' )
      with Min*-some r nε loc w i k
  ... | yes v = refl
  ... | no ¬ex = ⊥-elim ( ¬ex ( j , i<j , j≤k , t₁ , t₂ ) )



  import cgp.greedy.Order as GreedyOrder
  open GreedyOrder renaming ( _⊢_>_ to  _⊢_>ᵍ_ )
  open GreedyOrder renaming ( _⊢_>ⁱ_ to _⊢_>ᵍⁱ_ )

  -- UNPROVABLE : the goal of <-greedy-sound is refuted by the counterexample
  -- below ( for r , w , j = 1 , k = 3 the premise is inhabited but the
  -- ∃-∀ conclusion fails ; see ¬←greedy-sound and premise-held ) .
  --
  -- <-greedy-sound : ∀ ( r : RE ) ( w : List Char) ( j k : ℕ )
  --    -- → _∣_∣_⊢_<_ r w 0 j k
  --   → r ∣ w ∣ 0 ⊢ j < k
  --   ----------------------------------------------
  --   → ∃[ u ] ∃[ w₁ ] ∃[ w₂ ]
  --        ( ( proj₁ (flat {r} u) ≡ w₁ )
  --        × ( ( w₁ ++ w₂ ) ≡ w )
  --        × ( length w₁ ≡ j )
  --        × ( ( v : U r ) ( w₁' ,  w₂' : List Char )
  --          → ( proj₁ (flat v) ≡ w₁' )
  --          → ( length w₁' ≡ k )
  --          → ( w₁' ++ w₂' ) ≡ w
  --          → r ⊢ u >ᵍ v ) )
  -- <-greedy-sound = {!!}

  -- ========================================================================
  -- Counterexample to <-greedy-sound
  -- ========================================================================
  --
  -- For r = ( b + ( ε + b●a ) ) ● ( ( b + c ) + a●c ) , w = "bac" , j = 1 ,
  -- k = 3 :
  --
  --   * the premise r ∣ w ∣ 0 ⊢ 1 < 3 is inhabited ( <13 below ) : the
  --     canonical ( max-split ) match of ( 0 , 1 ) splits at 0 ( l @ "" via
  --     ε , rpp @ "b" via b ) and the canonical match of ( 0 , 3 ) splits
  --     at 2 ( l @ "ba" via b●a , rpp @ "c" via c ) , and ε @ ( 0 , 0 ) is
  --     below b●a @ ( 0 , 2 ) in the l-order ( inlinr : inl < inr ) ;
  --
  --   * but the ∃-∀ conclusion fails : the only parse u of r with a
  --     length-1 flat is
  --       u* = PairU (RightU (LeftU EmptyU)) (LeftU (LeftU (LetterU 'b')))
  --     and the length-3 parse
  --       v* = PairU (LeftU (LetterU 'b')) (RightU (PairU (LetterU 'a') (LetterU 'c')))
  --     is NOT below u* in the greedy order : the greedy order compares the
  --     left components first , and there is no greedy constructor for
  --     RightU _ >ᵍⁱ LeftU _ , nor an equality RightU _ ≡ LeftU _ .
  --
  --   * semantically : Mamouras' order compares the canonical max-split
  --     matches ( splits 0 and 2 ) , while the ∀ v quantifies over ALL
  --     parses of the length-3 match , including v* whose ( non-canonical )
  --     split at 1 puts a LeftU (LetterU 'b') on the left of a
  --     RightU (LeftU EmptyU) .

  -- The regex and the word .

  b : RE
  b = $ 'b' ` 0

  a : RE
  a = $ 'a' ` 0

  c : RE
  c = $ 'c' ` 0

  ba : RE
  ba = b ● a ` 0

  r₁ : RE
  r₁ = ε + ba ` 0

  l : RE
  l = b + r₁ ` 0

  bc : RE
  bc = b + c ` 0

  ac : RE
  ac = a ● c ` 0

  rpp : RE
  rpp = bc + ac ` 0

  r : RE
  r = l ● rpp ` 0

  w : List Char
  w = 'b' ∷ 'a' ∷ 'c' ∷ []

  -- Match evidence . l matches "b" ( via b ) , "" ( via ε in r₁ ) and "ba"
  -- ( via b●a in r₁ ) only ; rpp matches "b" ( via b ) , "c" ( via c ) and
  -- "ac" ( via a●c ) only .

  b-0-1m : b , 0 , 1 ⊨ w
  b-0-1m = ⊨$ 'b' 0 0 w refl

  a-1-2m : a , 1 , 2 ⊨ w
  a-1-2m = ⊨$ 'a' 0 1 w refl

  c-2-3m : c , 2 , 3 ⊨ w
  c-2-3m = ⊨$ 'c' 0 2 w refl

  r₁-0-0m : r₁ , 0 , 0 ⊨ w
  r₁-0-0m = ⊨inl ε ba 0 0 0 w (⊨ε 0 w)

  r₁-0-2m : r₁ , 0 , 2 ⊨ w
  r₁-0-2m = ⊨inr ε ba 0 0 2 w (⊨● b a 0 0 2 w 1 z≤n (s≤s (z≤n)) b-0-1m a-1-2m)

  l-0-0m : l , 0 , 0 ⊨ w
  l-0-0m = ⊨inr b r₁ 0 0 0 w r₁-0-0m

  l-0-2m : l , 0 , 2 ⊨ w
  l-0-2m = ⊨inr b r₁ 0 0 2 w r₁-0-2m

  rpp-0-1m : rpp , 0 , 1 ⊨ w
  rpp-0-1m = ⊨inl bc ac 0 0 1 w (⊨inl b c 0 0 1 w b-0-1m)

  -- documents that the split 1 of ( 0 , 3 ) is valid ( excluded from the
  -- canonical split by the maximality side condition , see j₂≡2 ) .
  rpp-1-3m : rpp , 1 , 3 ⊨ w
  rpp-1-3m = ⊨inr bc ac 0 1 3 w (⊨● a c 0 1 3 w 2 (s≤s (z≤n)) (s≤s (s≤s (z≤n))) a-1-2m c-2-3m)

  rpp-2-3m : rpp , 2 , 3 ⊨ w
  rpp-2-3m = ⊨inl bc ac 0 2 3 w (⊨inr b c 0 2 3 w c-2-3m)

  -- The two matches of r whose canonical split points drive the premise :
  -- ( 0 , 1 ) has only the valid split 0 ; ( 0 , 3 ) has the valid splits 1
  -- and 2 , hence the canonical ( max ) split is 2 .

  t₁ : r , 0 , 1 ⊨ w
  t₁ = ⊨● l rpp 0 0 1 w 0 ≤-refl z≤n l-0-0m rpp-0-1m

  t₂ : r , 0 , 3 ⊨ w
  t₂ = ⊨● l rpp 0 0 3 w 2 z≤n (s≤s (s≤s (z≤n))) l-0-2m rpp-2-3m

  -- Purpose : base order on r₁ = ε + ba : the match of "" at ( 0 , 0 ) ( via
  --           ε ) is below the match of "ba" at ( 0 , 2 ) ( via b●a ) ;
  --           ⊨inl < ⊨inr carries no premise .
  -- Used in : l-0-2 .
  -- Idea    : find-<-Min⁺ of a closed + match reduces to its canonical
  --           ⊨inl / ⊨inr evidence , so inlinr fits the premise of choice .
  r₁-0-2 : r₁ ∣ w ∣ 0 ⊢ 0 < 2
  r₁-0-2 = choice 0 0 2 r₁-0-0m r₁-0-2m
    ( inlinr 0 0 2 (⊨ε 0 w) (⊨● b a 0 0 2 w 1 z≤n (s≤s (z≤n)) b-0-1m a-1-2m) )

  -- Purpose : base order on l = b + r₁ : "" at ( 0 , 0 ) is below "ba" at
  --           ( 0 , 2 ) ; both go through the r₁ branch ( b matches neither ) ,
  --           so inrinr delegates to r₁-0-2 .
  -- Used in : <13 .
  -- Idea    : as for r₁-0-2 , the canonical evidence of the closed matches
  --           reduces to ⊨inr / ⊨inr .
  l-0-2 : l ∣ w ∣ 0 ⊢ 0 < 2
  l-0-2 = choice 0 0 2 l-0-0m l-0-2m
    ( inrinr 0 0 2 r₁-0-0m r₁-0-2m r₁-0-2 )

  -- c @ ( 0 , 1 ) would require w !! 0 ≡ just 'c' , but w !! 0 = just 'b' .
  ¬just-b≡c : ¬ ( just 'b' ≡ just 'c' )
  ¬just-b≡c ( )

  -- b @ ( 2 , 3 ) would require w !! 2 ≡ just 'b' , but w !! 2 = just 'c' .
  ¬just-c≡b : ¬ ( just 'c' ≡ just 'b' )
  ¬just-c≡b ( )

  -- Purpose : the premise of the counterexample : r ∣ w ∣ 0 ⊢ 1 < 3 .
  -- Used in : ¬←greedy-sound .
  -- Idea    : seq + seq₁ on the canonical ( max-split ) matches . The rpp
  --           side forces the split of ( 0 , 1 ) to 0 ( only "b" via b
  --           matches a length-1 suffix ) , and the canonical split of
  --           ( 0 , 3 ) is its max 2 : the rpp side of ( 0 , 3 ) matches "c"
  --           at 2 ( via c ) or "ac" at 1 ( via a●c ) only , and the
  --           maximality side condition of the canonical evidence mm₂
  --           excludes the split 1 ( the split 2 is strictly above it ) ;
  --           then l ∣ w ∣ 0 ⊢ 0 < 2 = l-0-2 .
  <13 : r ∣ w ∣ 0 ⊢ 1 < 3
  <13
    with find-<-Min● l rpp 0 w 0 1 t₁ | inspect ( find-<-Min● l rpp 0 w 0 1 ) t₁
       | find-<-Min● l rpp 0 w 0 3 t₂ | inspect ( find-<-Min● l rpp 0 w 0 3 ) t₂
  ... | ( min-t₁ , mm₁ ) | [ eq₁ ] | ( min-t₂ , mm₂ ) | [ eq₂ ]
    with min-t₁ | min-t₂
  ... | ⊨● _ _ _ _ _ _ j₁ _ _ u₁ v₁ | ⊨● _ _ _ _ _ _ j₂ _ _ u₂ v₂ =
    seq 0 1 3 t₁ t₂
      ( subst₂ ( λ x y → l ∣ rpp ∣ 0 ∣ w ∣ 0 ∣ 1 ∣ 3 ⊢● x < y )
          ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₂ ) )
          ( seq₁ 0 j₁ 1 j₂ 3 u₁ v₁ u₂ v₂ ( l-0-2-transport j₁≡0 j₂≡2 ) ) )
    where
      -- transport l-0-2 ( l ∣ w ∣ 0 ⊢ 0 < 2 ) to the canonical splits .
      l-0-2-transport : ( j₁≡0 : j₁ ≡ 0 ) ( j₂≡2 : j₂ ≡ 2 )
        → l ∣ w ∣ 0 ⊢ j₁ < j₂
      l-0-2-transport j₁≡0 j₂≡2 rewrite j₁≡0 | j₂≡2 = l-0-2

      -- the canonical split of ( 0 , 1 ) is forced to 0 : rpp matches
      -- w[j,1) only as "b" ( via b ) at j = 0 .
      j₁≡0 : j₁ ≡ 0
      j₁≡0 = j₁≡0-go j₁ v₁
        where
          j₁≡0-go : ( j₁ : ℕ ) ( v₁ : rpp , j₁ , 1 ⊨ w ) → j₁ ≡ 0
          j₁≡0-go j₁ v₁ with v₁
          ... | ⊨inl _ _ _ _ _ _ ( ⊨inl _ _ _ _ _ _ ( ⊨$ _ _ .j₁ .w _ ) ) = refl
          ... | ⊨inl _ _ _ _ _ _ ( ⊨inr _ _ _ _ _ _ ( ⊨$ _ _ .j₁ .w p ) )
            = ⊥-elim ( ¬just-b≡c p )
          ... | ⊨inr _ _ _ _ _ _ ( ⊨● _ _ _ _ _ _ j₃ _ _ ( ⊨$ _ _ .j₁ .w _ ) ( () ) )

      -- the canonical split of ( 0 , 3 ) is its max 2 : the rpp side allows
      -- j₂ = 2 ( "c" via c ) or j₂ = 1 ( "ac" via a●c ) only , and the
      -- maximality side condition of mm₂ excludes j₂ = 1 ( 2 is a valid
      -- split strictly above it ) .
      j₂≡2 : j₂ ≡ 2
      j₂≡2 = j₂≡2-go j₂ u₂ v₂ mm₂
        where
          -- mm₂ is passed with its index rebuilt as ( ⊨● … j₂ … ) from j₂ ,
          -- u₂ , v₂ : otherwise the telescope variables j₂ and min-t₂ stay
          -- independent , and the <-min-● pattern 's split could not be
          -- unified with j₂ .
          j₂≡2-go : ( j₂ : ℕ )
            → ( u₂ : l , 0 , j₂ ⊨ w )
            → ( v₂ : rpp , j₂ , 3 ⊨ w )
            → ( mm₂ : <-Min● l rpp 0 w 0 3
                     ( ⊨● l rpp 0 0 3 w j₂ ( rij⊨w→i≤j u₂ ) ( rij⊨w→i≤j v₂ ) u₂ v₂ ) )
            → j₂ ≡ 2
          j₂≡2-go j₂ u₂ v₂ mm₂ with v₂
          ... | ⊨inl _ _ _ _ _ _ ( ⊨inl _ _ _ _ _ _ ( ⊨$ _ _ .j₂ .w p ) )
            = ⊥-elim ( ¬just-c≡b p )
          ... | ⊨inl _ _ _ _ _ _ ( ⊨inr _ _ _ _ _ _ ( ⊨$ _ _ .j₂ .w _ ) ) = refl
          ... | ⊨inr _ _ _ _ _ _ ( ⊨● _ _ _ _ _ _ j₃ _ _ ( ⊨$ _ _ .j₂ .w _ ) ( ⊨$ _ _ .j₃ .w _ ) )
            with mm₂
          ... | ( <-min-● ) _ _ _ _ _ _ _ _ _ _ _ ¬ex =
            ⊥-elim ( ¬ex ( 2 , l-0-2m , rpp-2-3m , s<s (s≤s (z≤n)) ) )

  -- The parse trees .

  -- the only parse of r with a length-1 flat ( l @ "" via ε , rpp @ "b" via
  -- b )
  u* : U r
  u* = PairU ( RightU ( LeftU EmptyU ) ) ( LeftU ( LeftU ( LetterU 'b' ) ) )

  -- a parse of r whose flat is the whole word ( l @ "b" via b , rpp @ "ac"
  -- via a●c )
  v* : U r
  v* = PairU ( LeftU ( LetterU 'b' ) ) ( RightU ( PairU ( LetterU 'a' ) ( LetterU 'c' ) ) )

  flat-u* : proj₁ ( flat { r } u* ) ≡ 'b' ∷ []
  flat-u* = refl

  flat-v* : proj₁ ( flat { r } v* ) ≡ w
  flat-v* = refl

  len-w : length w ≡ 3
  len-w = refl

  -- Purpose : u* is not greedily above v* .
  -- Used in : ¬←greedy-sound .
  -- Idea    : r ⊢ u* >ᵍ v* would be sub of a >ᵍⁱ evidence ; on r = l ● rpp
  --           the only candidates are GreedyOrder.seq₁ ( needs l ⊢ RightU _
  --           >ᵍ LeftU _ : no greedy constructor relates RightU >ᵍⁱ LeftU on
  --           a + regex ) and GreedyOrder.seq₂ ( needs RightU _ ≡ LeftU _ :
  --           different constructors ) .
  ¬u*>ᵍv* : ¬ ( r ⊢ u* >ᵍ v* )
  ¬u*>ᵍv* ( sub u*>ⁱv* ) = ⊥-elim ( ¬u*>ⁱv* u*>ⁱv* )
    where
      ¬RightU≡LeftU : ¬ ( RightU ( LeftU EmptyU ) ≡ LeftU ( LetterU 'b' ) )
      ¬RightU≡LeftU ( )

      -- on a + regex the greedy >ᵍⁱ constructors are choice-lr ( LeftU >ᵍⁱ
      -- RightU ) , choice-ll ( LeftU >ᵍⁱ LeftU ) and choice-rr ( RightU
      -- >ᵍⁱ RightU ) : none relates RightU >ᵍⁱ LeftU , so the type is empty
      -- and the function needs no clauses .
      ¬RightU>ⁱLeftU : ¬ ( l ⊢ RightU ( LeftU EmptyU ) >ᵍⁱ LeftU ( LetterU 'b' ) )
      ¬RightU>ⁱLeftU ( ( ) )

      ¬RightU>LeftU : ¬ ( l ⊢ RightU ( LeftU EmptyU ) >ᵍ LeftU ( LetterU 'b' ) )
      ¬RightU>LeftU ( sub p ) = ⊥-elim ( ¬RightU>ⁱLeftU p )

      ¬u*>ⁱv* : ¬ ( r ⊢ u* >ᵍⁱ v* )
      ¬u*>ⁱv* ( GreedyOrder.seq₁ l>v ) = ⊥-elim ( ¬RightU>LeftU l>v )
      ¬u*>ⁱv* ( GreedyOrder.seq₂ u₁≡v₁ _ ) = ⊥-elim ( ¬RightU≡LeftU u₁≡v₁ )

  -- Purpose : rpp has no parse of the empty word ( its language is
  --           { "b" , "c" , "ac" } ) .
  -- Used in : uniq-u .
  -- Idea    : case split on the parse tree : every flat starts with a letter .
  no-empty-rpp : ( u : U rpp ) → ¬ ( proj₁ ( flat { rpp } u ) ≡ [] )
  no-empty-rpp ( LeftU ( LeftU ( LetterU _ ) ) ) ( )
  no-empty-rpp ( LeftU ( RightU ( LetterU _ ) ) ) ( )
  no-empty-rpp ( RightU ( PairU ( LetterU _ ) ( LetterU _ ) ) ) ( )

  -- Purpose : any parse u of r with flat u = w₁ , w₁ ++ w₂ = w and
  --           length w₁ = 1 is u* .
  -- Used in : ¬←greedy-sound .
  -- Idea    : u = PairU u₁ u₂ with u₁ : U l ( parses "b" , "" or "ba" ) and
  --           u₂ : U rpp ( parses "b" , "c" or "ac" ) ; length ( flat u₁ ) +
  --           length ( flat u₂ ) = 1 leaves only ( "" , "b" ) : "c" is
  --           excluded by the first letter of w and "ac" by its length .
  uniq-u : ( u : U r ) ( w₁ w₂ : List Char )
    → proj₁ ( flat { r } u ) ≡ w₁
    → w₁ ++ w₂ ≡ w
    → length w₁ ≡ 1
    → u ≡ u*
  uniq-u ( PairU u₁ u₂ ) w₁ w₂ flat-u≡w₁ w₁w₂≡w len-w₁≡1 with u₁ | u₂
  ... | RightU ( LeftU EmptyU ) | LeftU ( LeftU ( LetterU 'b' ) ) = refl
  ... | RightU ( LeftU EmptyU ) | LeftU ( RightU ( LetterU 'c' ) ) =
    ⊥-elim ( ¬'c'≡'b' ( proj₁ ( ∷-inj ( subst ( λ x → x ++ w₂ ≡ w ) ( sym flat-u≡w₁ ) w₁w₂≡w ) ) ) )
    where
      ¬'c'≡'b' : ¬ ( 'c' ≡ 'b' )
      ¬'c'≡'b' ( )
  ... | RightU ( LeftU EmptyU ) | RightU ( PairU ( LetterU 'a' ) ( LetterU 'c' ) ) =
    ⊥-elim ( ¬2≡1 ( trans ( cong length flat-u≡w₁ ) len-w₁≡1 ) )
    where
      ¬2≡1 : ¬ ( 2 ≡ 1 )
      ¬2≡1 ( )
  ... | LeftU ( LetterU 'b' ) | u₂ =
    ⊥-elim ( no-empty-rpp u₂ ( length≡0→[] ( suc-injective ( trans ( cong length flat-u≡w₁ ) len-w₁≡1 ) ) ) )
  ... | RightU ( RightU ( PairU ( LetterU 'b' ) ( LetterU 'a' ) ) ) | u₂ =
    ⊥-elim ( ¬suc≡0 ( suc-injective ( trans ( cong length flat-u≡w₁ ) len-w₁≡1 ) ) )
    where
      ¬suc≡0 : { n : ℕ } → ¬ ( suc n ≡ 0 )
      ¬suc≡0 ( )

  -- Purpose : refutation of <-greedy-sound at r , w , j = 1 , k = 3 : the
  --           premise is inhabited ( <13 ) but the ∃-∀ conclusion fails .
  -- Used in : counterexample .
  -- Idea    : the premise holds ( <13 ) . Any u in the ∃ is u* ( uniq-u ) ,
  --           and v* satisfies the ∀ side conditions ( flat v* = w , length
  --           w = 3 , w ++ [] = w ) but ¬u*>ᵍv* : the greedy order compares
  --           the left components first and cannot put u* above v* .
  ¬←greedy-sound : ( r ∣ w ∣ 0 ⊢ 1 < 3 )
    → ¬ ( ∃[ u ] ∃[ w₁ ] ∃[ w₂ ]
         ( ( proj₁ ( flat { r } u ) ≡ w₁ )
         × ( ( w₁ ++ w₂ ) ≡ w )
         × ( length w₁ ≡ 1 )
         × ( ( v : U r ) ( w₁' , w₂' : List Char )
           → ( proj₁ ( flat v ) ≡ w₁' )
           → ( length w₁' ≡ 3 )
           → ( ( w₁' ++ w₂' ) ≡ w )
           → r ⊢ u >ᵍ v ) ) )
  ¬←greedy-sound _ ( u , w₁ , w₂ , ( flat-u≡w₁ , w₁w₂≡w , len-w₁≡1 , ∀v ) ) =
    -- the comma form ( w₁' , w₂' : List Char ) elaborates to THREE list PIs
    -- in Agda 2.7.0.1 ( the third is anonymous and unused in the body ) , so
    -- a dummy third list argument ( [] ) must be supplied before the
    -- equality evidence .
    ⊥-elim ( ¬u*>ᵍv* ( subst ( λ u → r ⊢ u >ᵍ v* ) u≡u* ( ∀v v* w [] [] flat-v* len-w refl ) ) )
    where
      u≡u* : u ≡ u*
      u≡u* = uniq-u u w₁ w₂ flat-u≡w₁ w₁w₂≡w len-w₁≡1

  -- the premise is inhabited :
  premise-held : r ∣ w ∣ 0 ⊢ 1 < 3
  premise-held = <13

  -- the counterexample assembled : the premise holds but the conclusion
  -- fails .  ( the pair ( premise-held , ¬←greedy-sound premise-held ) :
  -- the premise is inhabited while the conclusion is refuted )
  counterexample : ( r ∣ w ∣ 0 ⊢ 1 < 3 )
    × ¬ ( ∃[ u ] ∃[ w₁ ] ∃[ w₂ ]
         ( ( proj₁ ( flat { r } u ) ≡ w₁ )
         × ( ( w₁ ++ w₂ ) ≡ w )
         × ( length w₁ ≡ 1 )
         × ( ( v : U r ) ( w₁' , w₂' : List Char )
           → ( proj₁ ( flat v ) ≡ w₁' )
           → ( length w₁' ≡ 3 )
           → ( ( w₁' ++ w₂' ) ≡ w )
           → r ⊢ u >ᵍ v ) ) )
  counterexample = premise-held , ¬←greedy-sound premise-held
 ```



