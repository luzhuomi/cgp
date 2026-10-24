# RelatedWorkMamouras3 ( base )

Split out of RelatedWorkMamouras3.lagda.md to shorten build times : this
file holds the stable development ( matching relation , base order , greedy
parser and its decision procedure ) and is type-checked once and cached ;
RelatedWorkMamouras3.lagda.md holds only the properties stated on top of it
and re-exports everything below with ` public ` .

```agda
{-# OPTIONS --rewriting --no-positivity-check #-}
module cgp.posix.RelatedWorkMamouras3Base where

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
  ≤-antisym ; m∸n≡0⇒m≤n ; n≤1+n ; ≤-step ; m≤n⇒m<n∨m≡n ; ≤-pred ;
  m+[n∸m]≡n ; n∸n≡0 ; +-∸-comm ; ∸-+-assoc ; +-monoʳ-< ; +-monoˡ-≤ ; m≤m+n ;
  ∸-monoˡ-≤ )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; tail; concatMap ; _∷ʳ_ ; length ; take ; drop )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-cancelʳ ; ++-conicalʳ ; ++-conicalˡ ;
  length-++ ; ++-assoc ; ∷-injective ; take-[] ; drop-[] ; drop-drop ; take++drop≡id ;
  length-drop
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
  -- evidence from the closed search dec-∃-range ( independent of the
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
        → ¬ ( ∃[ j' ] ( l , i , j' ⊨ w ) × ( r , j' , k ⊨ w ) × ( l ∣ w ∣ i ⊢ j' < j ) ) -- ( l | w | i  ⊢ j' < j ) )
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
    *-cons-nil : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char }
      → ( i j k : ℕ )
      → ( i<j : i Nat.< j ) ( j≤k : j Nat.≤ k )
      → ( t₁ : ( r , i , j ⊨ w ) )
      → ( t₂ : ( r * nε ` loc , j , k ⊨ w ) )
      → r ∣ nε ∣ loc ∣ w ∣ i ∣ k ∣ i ⊢⋆ ( ⊨∷ r nε loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) < ( ⊨[] r nε loc w i )
    *-head : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char }
      → ( i j j' k k' : ℕ )
      → ( i<j : i Nat.< j ) ( j≤k : j Nat.≤ k )
      → ( i<j' : i Nat.< j' ) ( j'≤k' : j' Nat.≤ k' )
      → ( t₁ : ( r , i , j ⊨ w ) )
      → ( t₂ : ( r * nε ` loc , j , k ⊨ w ) )
      → ( t₁' : ( r , i , j' ⊨ w ) )
      → ( t₂' : ( r * nε ` loc , j' , k' ⊨ w ) )
      → r ∣ w ∣ i ⊢ j < j'
      → r ∣ nε ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⋆ ( ⊨∷ r nε loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) < ( ⊨∷ r nε loc w i k' ( j' , i<j' , j'≤k' , t₁' , t₂' ) )
    *-tail : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char }
      → ( i j j' k k' : ℕ )
      → ( i<j : i Nat.< j ) ( j≤k : j Nat.≤ k ) ( i<j' : i Nat.< j' ) ( j'≤k' : j' Nat.≤ k' )
      → ( t₁ : ( r , i , j ⊨ w ) )
      → ( t₂ : ( r * nε ` loc , j , k ⊨ w ) )
      → ( t₁' : ( r , i , j' ⊨ w ) )
      → ( t₂' : ( r * nε ` loc , j' , k' ⊨ w ) )
      → ( j ≡ j' )
      → ( r * nε ` loc ) ∣ w ∣ j ⊢ k < k'
      → r ∣ nε ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⋆ ( ⊨∷ r nε loc w i k ( j , i<j , j≤k , t₁ , t₂ ) ) < ( ⊨∷ r nε loc w i k' ( j' , i<j' , j'≤k' , t₁' , t₂' ) )

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
  --           dec-∃-range.
  -- Idea    : two independent calls to ⊨?.
  Min●-val : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i k : ℕ )
    → ( a : ℕ ) → Dec ( ( l , i , a ⊨ w ) × ( r , a , k ⊨ w ) )
  Min●-val l r loc w i k a with ⊨? l i a w
  ... | no ¬l = no (λ { (t₁a , _) → ¬l t₁a })
  ... | yes t₁a with ⊨? r a k w
  ...   | no ¬r = no (λ { (_ , t₂a) → ¬r t₂a })
  ...   | yes t₂a = yes ( t₁a , t₂a )

  -- Purpose : given the result of the working-split search, build the minimal
  --           ● evidence ( or ⊥ if the search found no working split ).
  -- Used in : find-<-Min● only.
  -- Idea    : no ( no split ) contradicts the witness extracted from the
  --           given evidence T. yes : some working split a — descend to the
  --           order-minimal one ( find-<-Min●-descend ).
  find-<-Min●-go : ∀ ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    → Dec ( ∃[ a ] i ≤ a × a ≤ j × ( l , i , a ⊨ w ) × ( r , a , j ⊨ w ) )
    → ( T : l ● r ` loc , i , j ⊨ w )
    → ∃[ t ] ( <-Min● l r loc w i j t )
  find-<-Min●-go l r loc w i j ( no ¬ex ) T = ⊥-elim ( ¬ex ( witness T ) )
    where
      witness : ( t : l ● r ` loc , i , j ⊨ w ) → ∃[ a ] i ≤ a × a ≤ j × ( l , i , a ⊨ w ) × ( r , a , j ⊨ w )
      witness ( ⊨● _ _ _ _ _ _ j₀ _ _ t₁ t₂ ) = j₀ , rij⊨w→i≤j t₁ , rij⊨w→i≤j t₂ , t₁ , t₂
  find-<-Min●-go l r loc w i j ( yes ( a , i≤a , a≤j , ( t₁a , t₂a ) ) ) T
    = find-<-Min●-descend l r loc w i j a i≤a a≤j t₁a t₂a

  -- Purpose : from a working split s of l ● r on ( i , j ), descend through
  --           working splits strictly smaller in the l-order
  --           ( l ∣ w ∣ i ⊢ s' < s ) until none remains : the order-minimal
  --           working split, with its <-Min● evidence.
  -- Used in : find-<-Min●-go ( yes case ) only.
  -- Idea    : same descent scheme as Min*-best-go : search [ i , j ] for a
  --           strictly smaller working split, the l-order being decided by
  --           decide-⊢< on l ; if one exists, recurse on it ; if none
  --           exists, the current split is order-minimal and ¬bh ( bounds
  --           dropped , derivable via rij⊨w→i≤j ) is exactly the <-min-●
  --           side condition. Termination : the descent is strictly
  --           decreasing in the base order of l, which is a strict total
  --           order on the finite positions of [ i , j ] ( trichotomy ).
  {-# TERMINATING #-}
  find-<-Min●-descend : ∀ ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    → ( s : ℕ ) → ( i≤s : i ≤ s ) → ( s≤j : s ≤ j )
    → ( t₁ : l , i , s ⊨ w ) → ( t₂ : r , s , j ⊨ w )
    → ∃[ t ] ( <-Min● l r loc w i j t )
  find-<-Min●-descend l r loc w i j s i≤s s≤j t₁ t₂
    with dec-∃-range i j
      ( λ s' → ( l , i , s' ⊨ w ) × ( r , s' , j ⊨ w ) × ( l ∣ w ∣ i ⊢ s' < s ) )
      ( λ s' i≤s' s'≤j → dec-elim ( ⊨? l i s' w )
        ( λ t₁' → dec-elim ( ⊨? r s' j w )
          ( λ t₂' → dec-elim ( decide-⊢< l w i s s' t₁ t₁' )
            ( λ l< → yes ( t₁' , t₂' , l< ) )
            ( λ ¬l< → no ( λ { ( _ , _ , l< ) → ¬l< l< } ) ) )
          ( λ ¬t₂' → no ( λ { ( _ , t₂' , _ ) → ¬t₂' t₂' } ) ) )
        ( λ ¬t₁' → no ( λ { ( t₁' , _ , _ ) → ¬t₁' t₁' } ) ) )
  ... | yes ( s' , i≤s' , s'≤j , t₁' , t₂' , l< ) =
    find-<-Min●-descend l r loc w i j s' i≤s' s'≤j t₁' t₂'
  ... | no ¬bh =
    ⊨● l r loc i j w s i≤s s≤j t₁ t₂ ,
    <-min-● l r loc w i s j i≤s s≤j t₁ t₂
      ( λ { ( s' , t₁' , t₂' , l< ) →
        ¬bh ( s' , rij⊨w→i≤j t₁' , rij⊨w→i≤j t₂' , t₁' , t₂' , l< ) } )

  -- Purpose : compute, for any evidence T of l ● r on ( i , j ), a minimal ●
  --           evidence ( <-Min● ) : the working split whose left evidence is
  --           minimal in the l-order ( Mamouras : no strictly smaller
  --           working split ).
  -- Used in : the seq constructor ( premise indexed by the canonical minimal
  --           evidence ), trichotomy-●, decide-⊢< ( ● case ) and
  --           find-<-Min●-canon.
  -- Idea    : run dec-∃-range over [ i , j ] with dec predicate Min●-val to
  --           get some working split, then descend to the order-minimal one
  --           ( find-<-Min●-go ). The search is closed and the result does
  --           not depend on the starting evidence T, which is exactly what
  --           makes find-<-Min●-canon ( refl ) and the subst₂ transports
  --           work.
  {-# TERMINATING #-}
  find-<-Min● l r loc w i j T =
    find-<-Min●-go l r loc w i j
      ( dec-∃-range i j
          (λ a → ( l , i , a ⊨ w ) × ( r , a , j ⊨ w ))
          (λ a (i≤a : i ≤ a) (a≤j : a ≤ j) → Min●-val l r loc w i j a) )
      T

  -- Purpose : the minimal ● evidence does not depend on the starting
  --           evidence : proj₁ ( find-<-Min● T ) ≡ proj₁ ( find-<-Min● T' ).
  -- Used in : decide-⊢< ( ● case, both no-branches ), to transport arbitrary
  --           ⊢● evidence onto the canonical minimal evidence.
  -- Idea    : both sides reduce to the evidence built from the same closed
  --           dec-∃-range search and descent ( independent of T ), hence
  --           refl.
  {-# TERMINATING #-}
  find-<-Min●-canon : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i k : ℕ )
    → ( T T' : l ● r ` loc , i , k ⊨ w )
    → proj₁ ( find-<-Min● l r loc w i k T ) ≡ proj₁ ( find-<-Min● l r loc w i k T' )
  find-<-Min●-canon l r loc w i k T T'
    with dec-∃-range i k
           (λ a → ( l , i , a ⊨ w ) × ( r , a , k ⊨ w ))
           (λ a (i≤a : i ≤ a) (a≤k : a ≤ k) → Min●-val l r loc w i k a )
  ... | no ¬ex = ⊥-elim ( ¬ex ( witness T ) )
    where
      witness : ( t : l ● r ` loc , i , k ⊨ w ) → ∃[ a ] i ≤ a × a ≤ k × ( l , i , a ⊨ w ) × ( r , a , k ⊨ w )
      witness ( ⊨● _ _ _ _ _ _ j₀ _ _ t₁ t₂ ) = j₀ , rij⊨w→i≤j t₁ , rij⊨w→i≤j t₂ , t₁ , t₂
  ... | yes ( a , _ ) = refl

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

  -- Purpose : the head / tail split lemmas at s₀ = i + length a for a
  --           parse whose flat is a ++ b with side conditions for ( i , j ) .
  -- Used in : U⊨ ( ● and * cases ) .
  -- Idea    : prefix / rest rewrites of the side conditions .
  record SplitLemmas ( w : List Char ) ( i j : ℕ ) ( a b : List Char ) : Set where
    field
      i≤s₀ : i ≤ i + length a
      fl₁ : length a ≡ ( i + length a ) ∸ i
      fw₁ : a ++ drop ( i + length a ) w ≡ drop i w
      s₀≤j : ( i + length a ) ≤ j
      fl₂ : length b ≡ j ∸ ( i + length a )
      fw₂ : b ++ drop j w ≡ drop ( i + length a ) w

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming ( _⊢_>_ to  _⊢_>ᵍ_ )
open GreedyOrder renaming ( _⊢_>ⁱ_ to _⊢_>ᵍⁱ_ )

{-# TERMINATING #-}
mutual

    -- a non-empty iteration is strictly better (smaller) than the empty match
      -----------------------------------------------------------------------

    -- compare the heads
      -----------------------------------------------------------------------

    -- same head, compare the tails
      -----------------------------------------------------------------------

  -- the order is empty when the head of the left match is the empty iteration
  -- Purpose : ⊨[] is not below itself in ⊢⋆.
  -- Used in : no call sites yet ( kept for the irreflexivity of ⊢⋆ ).
  -- Idea    : ( ) — every ⊢⋆ constructor has a ⊨∷ left-hand side, so a ⊨[]
  --           left-hand side cannot be produced.
  ¬⊢⋆-[]-[] : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char } { i : ℕ }
    → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i i i ( ⊨[] r nε loc w i ) ( ⊨[] r nε loc w i ) → ⊥
  ¬⊢⋆-[]-[] ()

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


  -- ---------------------------------------------------------------------
  -- <-greedy-sound : the Mamouras base order is sound for the greedy
  -- parse-tree order >ᵍ .
  --
  -- The sub-premises of the seq₂ / *-tail constructors live at the split
  -- position ( ≠ 0 ) , so the proof runs on the generalized statement
  -- ( arbitrary start i , word drop i w ) ; the stated <-greedy-sound is
  -- its i = 0 instance ( drop 0 w ≡ w , j ∸ 0 ≡ j ) .
  --
  --   r ∣ w ∣ i ⊢ j < k
  --     ⇒ ∃ u w₁ w₂ . flat u ≡ w₁ × w₁ ++ w₂ ≡ drop i w × length w₁ ≡ j ∸ i
  --         × ∀ v . ( flat v a prefix of drop i w of length k ∸ i )
  --             ⇒ r ⊢ u >ᵍ v
  --
  -- Key invariant : in every case the side conditions of
  -- <-Min⁺ / <-Min● / <-Min* of the RIGHT ( larger ) match rule out
  -- exactly the parse shapes the >ᵍ constructors cannot relate : a mixed
  -- RightU / LeftU shape would witness a working split ( head ) strictly
  -- smaller in the base order than the canonical one .
  -- ---------------------------------------------------------------------

  -- small list / nat helpers ------------------------------------------------

  -- Purpose : take m after i , then take n after i + m , is take m + n
  --           after i .
  -- Used in : greedyU-flat ( ● and * cases ) .
  -- Idea    : induction on w .
  take-split : ( w : List Char ) ( i m n : ℕ )
    → take m ( drop i w ) ++ take n ( drop ( i + m ) w ) ≡ take ( m + n ) ( drop i w )
  take-split [] i m n =
    begin
      take m ( drop i [] ) ++ take n ( drop ( i + m ) [] )
    ≡⟨ cong₂ _++_ ( cong ( take m ) ( drop-[] i ) ) ( cong ( take n ) ( drop-[] ( i + m ) ) ) ⟩
      take m [] ++ take n []
    ≡⟨ cong₂ _++_ ( take-[] m ) ( take-[] n ) ⟩
      [] ++ []
    ≡⟨⟩
      []
    ≡⟨ sym ( take-[] ( m + n ) ) ⟩
      take ( m + n ) []
    ≡⟨ sym ( cong ( take ( m + n ) ) ( drop-[] i ) ) ⟩
      take ( m + n ) ( drop i [] )
    ∎
  take-split ( x ∷ ws ) zero zero n = refl
  take-split ( x ∷ ws ) zero ( suc m' ) n = cong ( x ∷_ ) ( take-split ws zero m' n )
  take-split ( x ∷ ws ) ( suc i' ) m n = take-split ws i' m n

  -- Purpose : from w !! i ≡ just c extract drop i w ≡ c ∷ drop ( suc i ) w .
  -- Used in : greedyU-flat ( $ case ) .
  -- Idea    : induction on w ( the empty case is impossible : [] !! i is
  --           nothing ) .
  lookup-just→drop : ( w : List Char ) ( i : ℕ ) ( c : Char )
    → w !! i ≡ just c → drop i w ≡ c ∷ drop ( suc i ) w
  lookup-just→drop [] i c p with p
  ... | ()
  lookup-just→drop ( x ∷ ws ) zero c p with p
  ... | refl = refl
  lookup-just→drop ( x ∷ ws ) ( suc i' ) c p = lookup-just→drop ws i' c p

  -- Purpose : ( j ∸ i ) + ( k ∸ j ) ≡ k ∸ i , for i ≤ j ≤ k .
  -- Used in : greedyU-flat ( ● and * cases ) .
  -- Idea    : induction on the triple ( peeling one position off each end ) .
  ∸-+∸ : ( i j k : ℕ ) → i ≤ j → j ≤ k → ( j ∸ i ) + ( k ∸ j ) ≡ k ∸ i
  ∸-+∸ zero zero k _ _ = refl
  ∸-+∸ zero ( suc j ) k _ j≤k = m+[n∸m]≡n j≤k
  ∸-+∸ ( suc i ) ( suc j ) ( suc k ) ( s≤s i≤j ) ( s≤s j≤k ) = ∸-+∸ i j k i≤j j≤k

  -- Purpose : suc n ∸ n ≡ 1 .
  -- Used in : greedyU-flat ( $ case ) .
  -- Idea    : induction on n .
  suc-n∸n≡1 : ( n : ℕ ) → suc n ∸ n ≡ 1
  suc-n∸n≡1 zero = refl
  suc-n∸n≡1 ( suc n ) = suc-n∸n≡1 n

  -- Purpose : the greedy witness : the canonical parse of ( i , j ) ,
  --           re-canonicalizing the sub-evidence at every node : + is
  --           decided by the closed ⊨? , ● by find-<-Min● , * by
  --           find-<-Min* ( including the tail of each ⊨∷ , since
  --           find-<-Min* does not reduce to the identity on a canonical
  --           match ) .
  -- Used in : <-greedy-sound-go ( the witness u ) , go , greedy-max .
  -- Idea    : structural on the regex ; evidence independent ( see
  --           greedyU-indep / greedyList-indep ) .
  greedyU : ( l : RE ) → ( i j : ℕ ) → ( w : List Char )
    → ( l , i , j ⊨ w ) → U l
  greedyU ε i j w ( ⊨ε _ _ ) = EmptyU
  greedyU ( $ c ` loc ) i j w ( ⊨$ _ _ _ _ _ ) = LetterU c
  greedyU ( l₁ + l₂ ` loc ) i j w t with ⊨? l₁ i j w
  ... | yes a = LeftU ( greedyU l₁ i j w a )
  ... | no ¬a with t
  ...   | ( ⊨inr _ _ _ _ _ _ b₀ ) = RightU ( greedyU l₂ i j w b₀ )
  ...   | ( ⊨inl _ _ _ _ _ _ a₀ ) = ⊥-elim ( ¬a a₀ )
  greedyU ( l₁ ● l₂ ` loc ) i j w t with find-<-Min● l₁ l₂ loc w i j t
  ... | ( ⊨● _ _ _ _ _ _ s₁ _ _ a₁ b₁ , _ ) =
    PairU ( greedyU l₁ i s₁ w a₁ ) ( greedyU l₂ s₁ j w b₁ )
  greedyU ( r * nε ` loc ) i j w t =
    ListU ( greedyList r nε loc i j w ( proj₁ ( find-<-Min* r nε loc w i j t ) ) )

  -- Purpose : the greedy head list of a star match ( one U r per ⊨∷
  --           head , each head re-canonicalized by find-<-Min* , and the
  --           tail re-canonicalized at every step ) .
  -- Used in : greedyU ( * case ) .
  -- Idea    : structural on the match evidence .
  {-# TERMINATING #-}
  greedyList : ( r : RE ) → ( nε : ε∉ r ) → ( loc : ℕ )
    → ( i j : ℕ ) → ( w : List Char )
    → ( r * nε ` loc , i , j ⊨ w ) → List ( U r )
  greedyList r _ _ _ _ _ ( ⊨[] _ _ _ _ _ ) = []
  greedyList r nε loc i j w ( ⊨∷ _ _ _ _ _ _ ( j₁ , _ , _ , t₁ , t₂ ) ) =
    ( greedyU r i j₁ w t₁ ) ∷
    ( greedyList r nε loc j₁ j w ( proj₁ ( find-<-Min* r nε loc w j₁ j t₂ ) ) )

  -- Purpose : flat soundness of greedyU : the parse of ( i , j ) flattens
  --           to the substring w [ i , j ) .
  -- Used in : <-greedy-sound-go ( the flat / length side conditions ) .
  -- Idea    : induction on the regex ; ● / * via the canonical
  --           sub-evidence and take-split .
  greedyU-flat : ( l : RE ) ( i j : ℕ ) ( w : List Char )
    → ( t : l , i , j ⊨ w )
    → proj₁ ( flat { l } ( greedyU l i j w t ) ) ≡ take ( j ∸ i ) ( drop i w )
  greedyU-flat ε i j w ( ⊨ε _ _ )
    rewrite n∸n≡0 i = refl
  greedyU-flat ( $ c ` loc ) i j w ( ⊨$ _ _ _ _ p )
    rewrite suc-n∸n≡1 i =
    begin
      c ∷ []
    ≡⟨⟩
      take 1 ( c ∷ drop ( suc i ) w )
    ≡⟨ cong ( take 1 ) ( sym ( lookup-just→drop w i c p ) ) ⟩
      take 1 ( drop i w )
    ∎
  greedyU-flat ( l₁ + l₂ ` loc ) i j w t with ⊨? l₁ i j w
  ... | yes a = greedyU-flat l₁ i j w a
  ... | no ¬a with t
  ...   | ( ⊨inr _ _ _ _ _ _ b₀ ) = greedyU-flat l₂ i j w b₀
  ...   | ( ⊨inl _ _ _ _ _ _ a₀ ) = ⊥-elim ( ¬a a₀ )
  greedyU-flat ( l₁ ● l₂ ` loc ) i j w t with find-<-Min● l₁ l₂ loc w i j t
  ... | ( ⊨● _ _ _ _ _ _ s₁ _ _ a₁ b₁ , _ )
    rewrite greedyU-flat l₁ i s₁ w a₁ | greedyU-flat l₂ s₁ j w b₁ =
    begin
      take ( s₁ ∸ i ) ( drop i w ) ++ take ( j ∸ s₁ ) ( drop s₁ w )
    ≡⟨ cong₂ _++_ refl ( cong ( λ n → take ( j ∸ s₁ ) ( drop n w ) ) ( sym ( m+[n∸m]≡n ( rij⊨w→i≤j a₁ ) ) ) ) ⟩
      take ( s₁ ∸ i ) ( drop i w ) ++ take ( j ∸ s₁ ) ( drop ( i + ( s₁ ∸ i ) ) w )
    ≡⟨ take-split w i ( s₁ ∸ i ) ( j ∸ s₁ ) ⟩
      take ( ( s₁ ∸ i ) + ( j ∸ s₁ ) ) ( drop i w )
    ≡⟨ cong ( λ n → take n ( drop i w ) ) ( ∸-+∸ i s₁ j ( rij⊨w→i≤j a₁ ) ( rij⊨w→i≤j b₁ ) ) ⟩
      take ( j ∸ i ) ( drop i w )
    ∎
  greedyU-flat ( r * nε ` loc ) i j w t =
    begin
      proj₁ ( flat ( greedyU ( r * nε ` loc ) i j w t ) )
    ≡⟨⟩
      proj₁ ( flat ( ListU ( greedyList r nε loc i j w ( proj₁ ( find-<-Min* r nε loc w i j t ) ) ) ) )
    ≡⟨ greedyList-flat r nε loc i j w ( proj₁ ( find-<-Min* r nε loc w i j t ) ) ⟩
      take ( j ∸ i ) ( drop i w )
    ∎

  -- Purpose : flat soundness of greedyList : the head list of ( i , j )
  --           flattens to the substring w [ i , j ) .
  -- Used in : greedyU-flat ( * case ) .
  -- Idea    : induction on the match evidence ( * case via take-split ) .
  {-# TERMINATING #-}
  greedyList-flat : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( i j : ℕ ) ( w : List Char )
    → ( t : r * nε ` loc , i , j ⊨ w )
    → proj₁ ( flat ( ListU { r } { nε } { loc } ( greedyList r nε loc i j w t ) ) )
      ≡ take ( j ∸ i ) ( drop i w )
  greedyList-flat r _ _ i j w ( ⊨[] _ _ _ _ _ )
    rewrite n∸n≡0 i = refl
  greedyList-flat r nε loc i j w ( ⊨∷ _ _ _ _ _ _ ( j₁ , i<j₁ , j₁≤j , t₁ , t₂ ) )
    rewrite greedyU-flat r i j₁ w t₁
          | greedyList-flat r nε loc j₁ j w ( proj₁ ( find-<-Min* r nε loc w j₁ j t₂ ) ) =
    begin
      take ( j₁ ∸ i ) ( drop i w ) ++ take ( j ∸ j₁ ) ( drop j₁ w )
    ≡⟨ cong₂ _++_ refl ( cong ( λ n → take ( j ∸ j₁ ) ( drop n w ) ) ( sym ( m+[n∸m]≡n ( <⇒≤ i<j₁ ) ) ) ) ⟩
      take ( j₁ ∸ i ) ( drop i w ) ++ take ( j ∸ j₁ ) ( drop ( i + ( j₁ ∸ i ) ) w )
    ≡⟨ take-split w i ( j₁ ∸ i ) ( j ∸ j₁ ) ⟩
      take ( ( j₁ ∸ i ) + ( j ∸ j₁ ) ) ( drop i w )
    ≡⟨ cong ( λ n → take n ( drop i w ) ) ( ∸-+∸ i j₁ j ( <⇒≤ i<j₁ ) j₁≤j ) ⟩
      take ( j ∸ i ) ( drop i w )
    ∎

  -- more helpers for U⊨ -----------------------------------------------

  -- Purpose : drop i w ≡ c ∷ w₂' → w !! i ≡ just c .
  -- Used in : U⊨ ( $ case ) .
  -- Idea    : induction on i .
  drop≡∷→lookup : ( w : List Char ) ( i : ℕ ) ( c : Char ) ( w₂' : List Char )
    → drop i w ≡ c ∷ w₂' → w !! i ≡ just c
  drop≡∷→lookup [] zero c w₂' p with p
  ... | ()
  drop≡∷→lookup [] ( suc _ ) c w₂' p with p
  ... | ()
  drop≡∷→lookup ( x ∷ ws ) zero c w₂' p with p
  ... | refl = refl
  drop≡∷→lookup ( x ∷ ws ) ( suc i' ) c w₂' p = drop≡∷→lookup ws i' c w₂' p

  -- Purpose : take ( length xs ) ( xs ++ ys ) ≡ xs .
  -- Used in : prefix→take .
  -- Idea    : induction on xs .
  take-length-++ : ( xs ys : List Char )
    → take ( length xs ) ( xs ++ ys ) ≡ xs
  take-length-++ [] ys = refl
  take-length-++ ( x ∷ xs ) ys = cong ( x ∷_ ) ( take-length-++ xs ys )

  -- Purpose : drop ( length xs ) ( xs ++ ys ) ≡ ys .
  -- Used in : split-helper .
  -- Idea    : induction on xs .
  drop-length-++ : ( xs ys : List Char )
    → drop ( length xs ) ( xs ++ ys ) ≡ ys
  drop-length-++ [] ys = refl
  drop-length-++ ( x ∷ xs ) ys = drop-length-++ xs ys

  -- Purpose : a prefix xs of length n of ( xs ++ ys ≡ zs ) is take n zs .
  -- Used in : split-helper .
  -- Idea    : take ( length xs ) ( xs ++ ys ) ≡ xs , then rewrite .
  prefix→take : ( xs ys zs : List Char ) ( n : ℕ )
    → xs ++ ys ≡ zs → length xs ≡ n → xs ≡ take n zs
  prefix→take xs ys zs n p l =
    begin
      xs
    ≡⟨ sym ( take-length-++ xs ys ) ⟩
      take ( length xs ) ( xs ++ ys )
    ≡⟨ cong ( take ( length xs ) ) p ⟩
      take ( length xs ) zs
    ≡⟨ cong ( λ m → take m zs ) l ⟩
      take n zs
    ∎

  -- Purpose : flat decomposes over PairU and over the head of a ListU .
  -- Used in : ε∉r→0<flat ( ● and * cases ) .
  -- Idea    : the with-block in the definition of flat fires on the branch .
  flat-PairU : ∀ { l r : RE } { loc : ℕ }
    → ( u₁ : U l ) ( u₂ : U r )
    → proj₁ ( flat ( PairU { l } { r } { loc } u₁ u₂ ) )
      ≡ proj₁ ( flat u₁ ) ++ proj₁ ( flat u₂ )
  flat-PairU u₁ u₂ with flat u₁ | flat u₂
  ... | ( xs₁ , _ ) | ( xs₂ , _ ) = refl

  flat-ListU-cons : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ }
    → ( u : U r ) ( us : List ( U r ) )
    → proj₁ ( flat ( ListU { r } { nε } { loc } ( u ∷ us ) ) )
      ≡ proj₁ ( flat u ) ++ proj₁ ( flat ( ListU { r } { nε } { loc } us ) )
  flat-ListU-cons { r } { nε } { loc } u us with flat u | flat ( ListU { r } { nε } { loc } us )
  ... | ( xs₁ , _ ) | ( xs₂ , _ ) = refl

  -- Purpose : 0 < a → 0 < a + b , and 0 < b → 0 < a + b .
  -- Used in : ε∉r→0<flat ( ● and * cases ) .
  -- Idea    : case split on the other summand ( suc _ is positive ) .
  0<a→0<a+b : ( a b : ℕ ) → 0 < a → 0 < a + b
  0<a→0<a+b a zero 0<a rewrite +-identityʳ a = 0<a
  0<a→0<a+b a ( suc n' ) _ rewrite +-suc a n' = z<s

  0<b→0<a+b : ( a b : ℕ ) → 0 < b → 0 < a + b
  0<b→0<a+b zero b 0<b = 0<b
  0<b→0<a+b ( suc _ ) b _ = z<s

  -- Purpose : ε ∉ r → every parse of r flattens to a non-empty word .
  -- Used in : U⊨ ( * case : i < s₀ ) .
  -- Idea    : induction on u ( ε∉ is a reason : ● branches on fst / snd ) .
  ε∉r→0<flat : ( r : RE ) ( nε : ε∉ r ) → ( u : U r ) → 0 < length ( proj₁ ( flat u ) )
  ε∉r→0<flat ε nε EmptyU = ⊥-elim ( ( ε∉r→¬ε∈r nε ) ε∈ε )
  ε∉r→0<flat _ _ ( LetterU _ ) = z<s
  ε∉r→0<flat ( l + r' ` loc ) ( ε∉ ε∉l + _ ) ( LeftU u₁ ) =
    ε∉r→0<flat l ε∉l u₁
  ε∉r→0<flat ( l + r' ` loc ) ( ε∉ _ + ε∉r' ) ( RightU u₂ ) =
    ε∉r→0<flat r' ε∉r' u₂
  ε∉r→0<flat ( l ● r' ` loc ) ( ε∉fst ε∉l ) ( PairU u₁ u₂ )
    rewrite flat-PairU { l } { r' } { loc } u₁ u₂ =
    subst ( λ n → 0 < n ) ( sym ( length-++ ( proj₁ ( flat u₁ ) ) ) )
      ( 0<a→0<a+b _ _ ( ε∉r→0<flat l ε∉l u₁ ) )
  ε∉r→0<flat ( l ● r' ` loc ) ( ε∉snd ε∉r' ) ( PairU u₁ u₂ )
    rewrite flat-PairU { l } { r' } { loc } u₁ u₂ =
    subst ( λ n → 0 < n ) ( sym ( length-++ ( proj₁ ( flat u₁ ) ) ) )
      ( 0<b→0<a+b _ _ ( ε∉r→0<flat r' ε∉r' u₂ ) )
  ε∉r→0<flat ( r' * n₀ ` loc ) nε₀ ( ListU [] ) =
    ⊥-elim ( ( ε∉r→¬ε∈r { r' * n₀ ` loc } nε₀ ) ε∈* )
  ε∉r→0<flat ( r' * nε ` loc ) _ ( ListU ( u ∷ us ) )
    rewrite flat-ListU-cons { r' } { nε } { loc } u us =
    subst ( λ n → 0 < n ) ( sym ( length-++ ( proj₁ ( flat u ) ) ) )
      ( 0<a→0<a+b _ _ ( ε∉r→0<flat r' nε u ) )

  split-helper : ( w : List Char ) ( i j : ℕ ) ( i≤j : i Nat.≤ j )
    → ( w₂' a b : List Char )
    → ( length ( a ++ b ) ≡ j ∸ i )
    → ( ( a ++ b ) ++ w₂' ≡ drop i w )
    → SplitLemmas w i j a b
  split-helper w i j i≤j w₂' a b fl fw =
    record { i≤s₀ = i≤s₀ ; fl₁ = fl₁ ; fw₁ = fw₁
           ; s₀≤j = s₀≤j ; fl₂ = fl₂ ; fw₂ = fw₂ }
    where
      s₀ = i + length a

      -- i ≤ s₀ .
      i≤s₀ : i ≤ s₀
      i≤s₀ = m≤m+n i ( length a )

      -- length a ≡ s₀ ∸ i .
      fl₁ : length a ≡ s₀ ∸ i
      fl₁ =
        begin
          length a
        ≡⟨ sym ( cong ( λ n → n + length a ) ( n∸n≡0 i ) ) ⟩
          ( i ∸ i ) + length a
        ≡⟨ sym ( +-∸-comm { i } ( length a ) { i } ( ≤-refl ) ) ⟩
          s₀ ∸ i
        ∎

      -- drop s₀ w ≡ drop ( s₀ ∸ i ) ( drop i w ) .
      drop-s₀ : drop s₀ w ≡ drop ( s₀ ∸ i ) ( drop i w )
      drop-s₀ =
        sym ( trans ( drop-drop i ( s₀ ∸ i ) w )
                 ( cong ( λ n → drop n w ) ( m+[n∸m]≡n i≤s₀ ) ) )

      -- a ++ ( b ++ w₂' ) ≡ drop i w .
      ps₁ : a ++ ( b ++ w₂' ) ≡ drop i w
      ps₁ = trans ( sym ( ++-assoc a b w₂' ) ) fw

      -- a ≡ take ( s₀ ∸ i ) ( drop i w ) .
      a≡take : a ≡ take ( s₀ ∸ i ) ( drop i w )
      a≡take = prefix→take a ( b ++ w₂' ) ( drop i w ) ( s₀ ∸ i ) ps₁ fl₁

      -- a ++ drop s₀ w ≡ drop i w .
      fw₁ : a ++ drop s₀ w ≡ drop i w
      fw₁ =
        begin
          a ++ drop s₀ w
        ≡⟨ cong ( λ xs → xs ++ drop s₀ w ) a≡take ⟩
          take ( s₀ ∸ i ) ( drop i w ) ++ drop s₀ w
        ≡⟨ cong ( λ ys → take ( s₀ ∸ i ) ( drop i w ) ++ ys ) drop-s₀ ⟩
          take ( s₀ ∸ i ) ( drop i w ) ++ drop ( s₀ ∸ i ) ( drop i w )
        ≡⟨ take++drop≡id ( s₀ ∸ i ) ( drop i w ) ⟩
          drop i w
        ∎

      -- i + ( length a + length b ) ≡ j .
      i+ab≡j : i + ( length a + length b ) ≡ j
      i+ab≡j =
        begin
          i + ( length a + length b )
        ≡⟨ cong ( i +_ ) ( sym ( length-++ a ) ) ⟩
          i + length ( a ++ b )
        ≡⟨ cong ( i +_ ) fl ⟩
          i + ( j ∸ i )
        ≡⟨ m+[n∸m]≡n i≤j ⟩
          j
        ∎

      -- s₀ ≤ j .
      s₀≤j : s₀ ≤ j
      s₀≤j =
        subst ( λ k → s₀ ≤ k ) i+ab≡j
          ( +-monoʳ-≤ i ( m≤m+n ( length a ) ( length b ) ) )

      -- length b ≡ j ∸ s₀ .
      fl₂ : length b ≡ j ∸ s₀
      fl₂ =
        begin
          length b
        ≡⟨ sym ( cong ( λ n → n + length b ) ( n∸n≡0 ( length a ) ) ) ⟩
           ( length a ∸ length a ) + length b
         ≡⟨ sym ( +-∸-comm { length a } ( length b ) { length a } ( ≤-refl ) ) ⟩
          ( length a + length b ) ∸ length a
        ≡⟨ cong ( λ x → x ∸ length a ) ( trans ( sym ( length-++ a ) ) fl ) ⟩
          ( j ∸ i ) ∸ length a
        ≡⟨ cong ( λ x → ( j ∸ i ) ∸ x ) fl₁ ⟩
          ( j ∸ i ) ∸ ( s₀ ∸ i )
        ≡⟨ ∸-+-assoc j i ( s₀ ∸ i ) ⟩
          j ∸ ( i + ( s₀ ∸ i ) )
        ≡⟨ cong ( j ∸_ ) ( m+[n∸m]≡n i≤s₀ ) ⟩
          j ∸ s₀
        ∎

      -- b ++ w₂' ≡ drop s₀ w .
      b++w₂' : b ++ w₂' ≡ drop s₀ w
      b++w₂' =
        sym
          ( begin
              drop s₀ w
            ≡⟨ drop-s₀ ⟩
              drop ( s₀ ∸ i ) ( drop i w )
            ≡⟨ cong ( λ xs → drop ( s₀ ∸ i ) xs ) ( sym fw ) ⟩
              drop ( s₀ ∸ i ) ( ( a ++ b ) ++ w₂' )
            ≡⟨ cong ( λ xs → drop ( s₀ ∸ i ) xs ) ( ++-assoc a b w₂' ) ⟩
              drop ( s₀ ∸ i ) ( a ++ ( b ++ w₂' ) )
            ≡⟨ cong ( λ n → drop n ( a ++ ( b ++ w₂' ) ) ) ( sym fl₁ ) ⟩
              drop ( length a ) ( a ++ ( b ++ w₂' ) )
            ≡⟨ drop-length-++ a ( b ++ w₂' ) ⟩
              b ++ w₂'
            ∎ )

      -- drop ( j ∸ s₀ ) ( drop s₀ w ) ≡ drop j w .
      E1 : drop ( j ∸ s₀ ) ( drop s₀ w ) ≡ drop j w
      E1 =
        trans ( drop-drop s₀ ( j ∸ s₀ ) w )
              ( cong ( λ n → drop n w ) ( m+[n∸m]≡n s₀≤j ) )

      -- b ≡ take ( j ∸ s₀ ) ( drop s₀ w ) .
      b≡take : b ≡ take ( j ∸ s₀ ) ( drop s₀ w )
      b≡take = prefix→take b w₂' ( drop s₀ w ) ( j ∸ s₀ ) b++w₂' fl₂

      -- b ++ drop j w ≡ drop s₀ w .
      fw₂ : b ++ drop j w ≡ drop s₀ w
      fw₂ =
        begin
          b ++ drop j w
        ≡⟨ cong ( λ xs → xs ++ drop j w ) b≡take ⟩
          take ( j ∸ s₀ ) ( drop s₀ w ) ++ drop j w
        ≡⟨ cong ( λ ys → take ( j ∸ s₀ ) ( drop s₀ w ) ++ ys ) ( sym E1 ) ⟩
          take ( j ∸ s₀ ) ( drop s₀ w ) ++ drop ( j ∸ s₀ ) ( drop s₀ w )
        ≡⟨ take++drop≡id ( j ∸ s₀ ) ( drop s₀ w ) ⟩
          drop s₀ w
        ∎

  -- Purpose : a parse tree whose flat is the substring w [ i , j )
  --           witnesses ( r , i , j ⊨ w ) .
  -- Used in : <-greedy-sound-go ( the minimality side conditions of the
  --           right match , applied to the arbitrary v ) .
  -- Idea    : induction on v ( which determines the shape of r ) ; the
  --           ● / * cases split at s₀ = i + length ( flat of the head )
  --           via split-helper .
  U⊨ : ( r : RE ) ( i j : ℕ ) ( w : List Char )
    → ( i Nat.≤ j )
    → ( v : U r ) ( w₁' w₂' : List Char )
    → proj₁ ( flat v ) ≡ w₁'
    → length w₁' ≡ j ∸ i
    → w₁' ++ w₂' ≡ drop i w
    → ( r , i , j ⊨ w )

  -- ε : the span collapses to i .
  U⊨ ε i j w i≤j EmptyU w₁' w₂' fp fl fw
    rewrite sym fp =
    subst ( λ k → ε , i , k ⊨ w )
      ( ≤-antisym i≤j ( m∸n≡0⇒m≤n ( sym fl ) ) )
      ( ⊨ε i w )

  -- $ : the span is one character .
  U⊨ ( $ c ` loc ) i j w i≤j ( LetterU c ) w₁' w₂' fp fl fw
    rewrite sym fp =
    subst ( λ k → ( $ c ` loc ) , i , k ⊨ w ) ( sym ( j≡suci ) )
      ( ⊨$ c loc i w ( drop≡∷→lookup w i c w₂' ( sym fw ) ) )
    where
      -- j ≡ suc i ( written as suc i , not i + 1 , which is stuck ) .
      j≡suci : j ≡ suc i
      j≡suci =
        begin
          j
        ≡⟨ sym ( m+[n∸m]≡n i≤j ) ⟩
          i + ( j ∸ i )
        ≡⟨ cong ( i +_ ) ( sym fl ) ⟩
          i + 1
        ≡⟨ trans ( +-suc i zero ) ( cong suc ( +-identityʳ i ) ) ⟩
          suc i
        ∎

  -- + ( left )
  U⊨ ( l₁ + l₂ ` loc ) i j w i≤j ( LeftU v₁ ) w₁' w₂' fp fl fw =
    ⊨inl l₁ l₂ loc i j w
      ( U⊨ l₁ i j w i≤j v₁ w₁' w₂' fp fl fw )

  -- + ( right )
  U⊨ ( l₁ + l₂ ` loc ) i j w i≤j ( RightU v₂ ) w₁' w₂' fp fl fw =
    ⊨inr l₁ l₂ loc i j w
      ( U⊨ l₂ i j w i≤j v₂ w₁' w₂' fp fl fw )

  -- ● : split at s₀ = i + length ( flat v₁ ) .
  U⊨ ( l₁ ● l₂ ` loc ) i j w i≤j ( PairU v₁ v₂ ) w₁' w₂' fp fl fw
    rewrite fp =
    ( ⊨● l₁ l₂ loc i j w s₀ i≤s₀ s₀≤j
        ( U⊨ l₁ i s₀ w i≤s₀ v₁ ( proj₁ ( flat v₁ ) ) ( drop s₀ w ) refl fl₁ fw₁ )
        ( U⊨ l₂ s₀ j w s₀≤j v₂ ( proj₁ ( flat v₂ ) ) ( drop j w ) refl fl₂ fw₂ ) )
    where
      s₀ = i + length ( proj₁ ( flat v₁ ) )
      -- Transport the side conditions from w₁' to
      -- proj₁ ( flat v₁ ) ++ proj₁ ( flat v₂ ) .
      w₁'≡ab : w₁' ≡ proj₁ ( flat v₁ ) ++ proj₁ ( flat v₂ )
      w₁'≡ab = trans ( sym fp ) ( flat-PairU { l₁ } { l₂ } { loc } v₁ v₂ )
      fl' : length ( proj₁ ( flat v₁ ) ++ proj₁ ( flat v₂ ) ) ≡ j ∸ i
      fl' = subst ( λ xs → length xs ≡ j ∸ i ) w₁'≡ab fl
      fw' : ( proj₁ ( flat v₁ ) ++ proj₁ ( flat v₂ ) ) ++ w₂' ≡ drop i w
      fw' = subst ( λ xs → xs ++ w₂' ≡ drop i w ) w₁'≡ab fw
      split = split-helper w i j i≤j w₂'
        ( proj₁ ( flat v₁ ) ) ( proj₁ ( flat v₂ ) ) fl' fw'
      i≤s₀ = SplitLemmas.i≤s₀ split
      fl₁ = SplitLemmas.fl₁ split
      fw₁ = SplitLemmas.fw₁ split
      s₀≤j = SplitLemmas.s₀≤j split
      fl₂ = SplitLemmas.fl₂ split
      fw₂ = SplitLemmas.fw₂ split

  -- * ( empty list ) : the span collapses to i .
  U⊨ ( r * n₀ ` loc ) i j w i≤j ( ListU [] ) w₁' w₂' fp fl fw
    rewrite sym fp =
    subst ( λ k → ( r * n₀ ` loc ) , i , k ⊨ w )
      ( ≤-antisym i≤j ( m∸n≡0⇒m≤n ( sym fl ) ) )
      ( ⊨[] r n₀ loc w i )

  -- * ( non-empty list ) : split at s₀ = i + length ( flat u ) .
  U⊨ ( r * n₀ ` loc ) i j w i≤j ( ListU ( u ∷ us ) ) w₁' w₂' fp fl fw
    rewrite fp =
    ( ⊨∷ r n₀ loc w i j
        ( s₀ , subst ( λ x → x < s₀ ) ( +-identityʳ i )
                  ( +-monoʳ-< i ( ε∉r→0<flat r n₀ u ) ) , s₀≤j
          , ( U⊨ r i s₀ w i≤s₀ u ( proj₁ ( flat u ) ) ( drop s₀ w ) refl fl₁ fw₁ )
          , ( U⊨ ( r * n₀ ` loc ) s₀ j w s₀≤j ( ListU { r } { n₀ } { loc } us )
                ( proj₁ ( flat ( ListU { r } { n₀ } { loc } us ) ) ) ( drop j w ) refl fl₂ fw₂ ) ) )
    where
      s₀ = i + length ( proj₁ ( flat u ) )
      -- Transport the side conditions from w₁' to
      -- proj₁ ( flat u ) ++ proj₁ ( flat ( ListU us ) ) .
      w₁'≡ab : w₁' ≡ proj₁ ( flat u ) ++ proj₁ ( flat ( ListU { r } { n₀ } { loc } us ) )
      w₁'≡ab = trans ( sym fp ) ( flat-ListU-cons { r } { n₀ } { loc } u us )
      fl' : length ( proj₁ ( flat u ) ++ proj₁ ( flat ( ListU { r } { n₀ } { loc } us ) ) ) ≡ j ∸ i
      fl' = subst ( λ xs → length xs ≡ j ∸ i ) w₁'≡ab fl
      fw' : ( proj₁ ( flat u ) ++ proj₁ ( flat ( ListU { r } { n₀ } { loc } us ) ) ) ++ w₂' ≡ drop i w
      fw' = subst ( λ xs → xs ++ w₂' ≡ drop i w ) w₁'≡ab fw
      split = split-helper w i j i≤j w₂'
        ( proj₁ ( flat u ) ) ( proj₁ ( flat ( ListU { r } { n₀ } { loc } us ) ) ) fl' fw'
      i≤s₀ = SplitLemmas.i≤s₀ split
      fl₁ = SplitLemmas.fl₁ split
      fw₁ = SplitLemmas.fw₁ split
      s₀≤j = SplitLemmas.s₀≤j split
      fl₂ = SplitLemmas.fl₂ split
      fw₂ = SplitLemmas.fw₂ split

  -- ---------------------------------------------------------------------
  -- ⊢<-trans : transitivity of the Mamouras base order .
  --
  -- Purpose : q ∣ w ∣ i ⊢ j < k × q ∣ w ∣ i ⊢ k < k'
  --           ⇒ q ∣ w ∣ i ⊢ j < k' .
  -- Used in : ←greedy-sound-go ( the seq₂ / *-tail sub-premises live at
  --           the split position ≠ 0 ) and in ⊢<-trans-+/-●/-⋆ below .
  -- Idea    : case split on q : ε / $ have no constructors ; + compares
  --           the four minimal shapes ( inlinr needs no premise ; inlinl /
  --           inrinr extract the sub-order premises and recurse on the
  --           branch ; the rest is refuted by <-Min⁺-inr¬ / inr≮inl ) ;
  --           ● / * compare the canonical splits / heads .
  -- ---------------------------------------------------------------------

  -- Purpose : a ⊢⁺ proof relating a minimal ⊨inr shape at j to a minimal
  --           ⊨inl shape at k is impossible .
  -- Used in : ⊢<-trans-+ ( the inr<inl refutations ) .
  -- Idea    : no ⊢⁺ constructor has an ⊨inr left side and an ⊨inl right
  --           side : the proof argument type is empty .  The helper is
  --           defined at the top level so the empty-pattern check is
  --           performed in a clean context , avoiding the unifier leak
  --           that occurs when the check is done inside a with-branch
  --           with multiple active find-<-Min⁺ inspect constraints .
  inr<inl-+ : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k : ℕ )
    ( a : r , i , j ⊨ w ) ( b : l , i , k ⊨ w )
    → ( P : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺
           ( ⊨inr l r loc i j w a ) < ( ⊨inl l r loc i k w b ) )
    → ⊥
  inr<inl-+ l r loc w i j k a b P with P
  ... | ()

  -- Purpose : extract the l-order premise of an already-transported
  --           ⊢⁺ proof whose two ends are concrete ⊨inl shapes .
  -- Used in : ⊢<-trans-+ ( inl/inl good branch ) via ⊢⁺-inlinl-prem .
  -- Idea    : the pattern match happens inside this top-level helper ,
  --           so the caller's find-<-Min⁺ inspect constraints do not
  --           interfere with constructor unification .
  ⊢⁺-inlinl-go : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k : ℕ )
    → ( a : l , i , j ⊨ w ) ( b : l , i , k ⊨ w )
    → ( P' : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺
           ( ⊨inl l r loc i j w a ) < ( ⊨inl l r loc i k w b ) )
    → l ∣ w ∣ i ⊢ j < k
  -- the inlinr / inrinr cases are impossible ( their ⊨inr side cannot
  -- unify with the ⊨inl side ) : no clause needed .
  ⊢⁺-inlinl-go l r loc w i j k a b ( inlinl .i .j .k .a .b ord ) = ord

  -- Purpose : transport a ⊢⁺ proof from the computed Min⁺ shapes to
  --           concrete ⊨inl shapes and extract the l-order premise .
  -- Used in : ⊢<-trans-+ ( inl/inl good branch ) .
  -- Idea    : the transport and pattern match happen inside this
  --           top-level helper ; the caller only supplies the equalities
  --           from Min⁺-inl , keeping the with-branch context simple .
  ⊢⁺-inlinl-prem : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k : ℕ )
    ( t₁ : ( l + r ` loc ) , i , j ⊨ w ) ( t₂ : ( l + r ` loc ) , i , k ⊨ w )
    → ( P : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺
           ( Min⁺ l r loc w i j t₁ ) < ( Min⁺ l r loc w i k t₂ ) )
    → ( a : l , i , j ⊨ w ) ( b : l , i , k ⊨ w )
    → ( e₁ : Min⁺ l r loc w i j t₁ ≡ ⊨inl l r loc i j w a )
    → ( e₂ : Min⁺ l r loc w i k t₂ ≡ ⊨inl l r loc i k w b )
    → l ∣ w ∣ i ⊢ j < k
  ⊢⁺-inlinl-prem l r loc w i j k t₁ t₂ P a b e₁ e₂ =
    ⊢⁺-inlinl-go l r loc w i j k a b
      ( subst₂ ( λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺ x < y ) e₁ e₂ P )

  -- Purpose : dual of ⊢⁺-inlinl-go : both ends concrete ⊨inr .
  ⊢⁺-inrinr-go : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k : ℕ )
    → ( a : r , i , j ⊨ w ) ( b : r , i , k ⊨ w )
    → ( P' : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺
           ( ⊨inr l r loc i j w a ) < ( ⊨inr l r loc i k w b ) )
    → r ∣ w ∣ i ⊢ j < k
  -- the inlinr / inlinl cases are impossible ( their ⊨inl side cannot
  -- unify with the ⊨inr side ) : no clause needed .
  ⊢⁺-inrinr-go l r loc w i j k a b ( inrinr .i .j .k .a .b ord ) = ord

  -- Purpose : dual of ⊢⁺-inlinl-prem : transport to concrete ⊨inr
  --           shapes and extract the r-order premise .
  ⊢⁺-inrinr-prem : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k : ℕ )
    ( t₁ : ( l + r ` loc ) , i , j ⊨ w ) ( t₂ : ( l + r ` loc ) , i , k ⊨ w )
    → ( P : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺
           ( Min⁺ l r loc w i j t₁ ) < ( Min⁺ l r loc w i k t₂ ) )
    → ( a : r , i , j ⊨ w ) ( b : r , i , k ⊨ w )
    → ( e₁ : Min⁺ l r loc w i j t₁ ≡ ⊨inr l r loc i j w a )
    → ( e₂ : Min⁺ l r loc w i k t₂ ≡ ⊨inr l r loc i k w b )
    → r ∣ w ∣ i ⊢ j < k
  ⊢⁺-inrinr-prem l r loc w i j k t₁ t₂ P a b e₁ e₂ =
    ⊢⁺-inrinr-go l r loc w i j k a b
      ( subst₂ ( λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺ x < y ) e₁ e₂ P )

  -- Purpose : the + case of ⊢<-trans with outer minimal shapes inl@j and
  --           inr@k' : the result is inlinr , no inner inspect needed .
  {-# TERMINATING #-}
  ⊢<-trans-+-inl-inr : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( l + r ` loc ) , i , j ⊨ w )
    → ( s₂ : ( l + r ` loc ) , i , k' ⊨ w )
    → ( a : l , i , j ⊨ w ) ( b : r , i , k' ⊨ w )
    → ( e₁ : Min⁺ l r loc w i j t₁ ≡ ⊨inl l r loc i j w a )
    → ( e₂' : Min⁺ l r loc w i k' s₂ ≡ ⊨inr l r loc i k' w b )
    → ( l + r ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-+-inl-inr l r loc w i j k k' t₁ s₂ a b e₁ e₂' =
    choice i j k' t₁ s₂
      ( subst₂ ( λ u v → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢⁺ u < v )
          ( sym e₁ ) ( sym e₂' ) ( inlinr i j k' a b ) )

  -- Purpose : the + case of ⊢<-trans with outer minimal shapes inl@j and
  --           inl@k' : compare the inner minimal shapes at k .
  -- Used in : ⊢<-trans-+ .
  -- Idea    : isolate the inner inspect-with and its empty-proof refutation
  --           in a separate function so the unifier leak is confined here .
  {-# TERMINATING #-}
  ⊢<-trans-+-inl-inl : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( l + r ` loc ) , i , j ⊨ w )
    → ( t₂ : ( l + r ` loc ) , i , k ⊨ w )
    → ( s₁ : ( l + r ` loc ) , i , k ⊨ w )
    → ( s₂ : ( l + r ` loc ) , i , k' ⊨ w )
    → ( P : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺
           ( Min⁺ l r loc w i j t₁ ) < ( Min⁺ l r loc w i k t₂ ) )
    → ( P' : l ∣ r ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⁺
           ( Min⁺ l r loc w i k s₁ ) < ( Min⁺ l r loc w i k' s₂ ) )
    → ( a : l , i , j ⊨ w ) ( b : l , i , k' ⊨ w )
    → ( e₁ : Min⁺ l r loc w i j t₁ ≡ ⊨inl l r loc i j w a )
    → ( e₂' : Min⁺ l r loc w i k' s₂ ≡ ⊨inl l r loc i k' w b )
    → ( l + r ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-+-inl-inl l r loc w i j k k' t₁ t₂ s₁ s₂ P P' a b e₁ e₂'
    with ⊨? l i k w
  -- l matches at k : both inner shapes are inl : good , inlinl :
  ... | yes x =
    let ( x' , e₂ ) = Min⁺-inl l r loc w i k x t₂
        ( y' , e₁' ) = Min⁺-inl l r loc w i k x s₁
    in  choice i j k' t₁ s₂
          ( subst₂ ( λ u v → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢⁺ u < v )
              ( sym e₁ ) ( sym e₂' )
              ( inlinl i j k' a b
                  ( ⊢<-trans l w i j k k'
                      ( ⊢⁺-inlinl-prem l r loc w i j k t₁ t₂ P a x' e₁ e₂ )
                      ( ⊢⁺-inlinl-prem l r loc w i k k' s₁ s₂ P' y' b e₁' e₂' ) ) ) )
  -- l does not match at k : both inner shapes are inr ;
  --     P' is inr<inl ( empty ) , refute via top-level helper :
  ... | no ¬x =
    let ( y' , e₁' ) = Min⁺-inr l r loc w i k ¬x s₁
    in  ⊥-elim ( inr<inl-+ l r loc w i k k' y' b
                  ( subst₂ ( λ u v → l ∣ r ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⁺ u < v )
                      e₁' e₂' P' ) )

  -- Purpose : the + case of ⊢<-trans with outer minimal shapes inr@j and
  --           inr@k' : compare the inner minimal shapes at k .
  {-# TERMINATING #-}
  ⊢<-trans-+-inr-inr : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( l + r ` loc ) , i , j ⊨ w )
    → ( t₂ : ( l + r ` loc ) , i , k ⊨ w )
    → ( s₁ : ( l + r ` loc ) , i , k ⊨ w )
    → ( s₂ : ( l + r ` loc ) , i , k' ⊨ w )
    → ( P : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺
           ( Min⁺ l r loc w i j t₁ ) < ( Min⁺ l r loc w i k t₂ ) )
    → ( P' : l ∣ r ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⁺
           ( Min⁺ l r loc w i k s₁ ) < ( Min⁺ l r loc w i k' s₂ ) )
    → ( a : r , i , j ⊨ w ) ( b : r , i , k' ⊨ w )
    → ( e₁ : Min⁺ l r loc w i j t₁ ≡ ⊨inr l r loc i j w a )
    → ( e₂' : Min⁺ l r loc w i k' s₂ ≡ ⊨inr l r loc i k' w b )
    → ( l + r ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-+-inr-inr l r loc w i j k k' t₁ t₂ s₁ s₂ P P' a b e₁ e₂'
    with ⊨? l i k w
  -- l matches at k : both inner shapes are inl ;
  --     P is inr<inl ( empty ) , refute via top-level helper :
  ... | yes x =
    let ( x' , e₂ ) = Min⁺-inl l r loc w i k x t₂
    in  ⊥-elim ( inr<inl-+ l r loc w i j k a x'
                  ( subst₂ ( λ u v → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺ u < v )
                      e₁ e₂ P ) )
  -- l does not match at k : both inner shapes are inr : good , inrinr :
  ... | no ¬x =
    let ( x' , e₂ ) = Min⁺-inr l r loc w i k ¬x t₂
        ( y' , e₁' ) = Min⁺-inr l r loc w i k ¬x s₁
    in  choice i j k' t₁ s₂
          ( subst₂ ( λ u v → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢⁺ u < v )
              ( sym e₁ ) ( sym e₂' )
              ( inrinr i j k' a b
                  ( ⊢<-trans r w i j k k'
                      ( ⊢⁺-inrinr-prem l r loc w i j k t₁ t₂ P a x' e₁ e₂ )
                      ( ⊢⁺-inrinr-prem l r loc w i k k' s₁ s₂ P' y' b e₁' e₂' ) ) ) )

  -- Purpose : the + case of ⊢<-trans with outer minimal shapes inr@j and
  --           inl@k' : the goal is empty ; refute via ⊨? at k .
  -- Used in : ⊢<-trans-+ .
  -- Idea    : use ⊨? ( instead of find-<-Min⁺ inspect ) so each branch has at
  --           most one empty-proof refutation and the unifier leak is confined .
  {-# TERMINATING #-}
  ⊢<-trans-+-inr-inl : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( l + r ` loc ) , i , j ⊨ w )
    → ( t₂ : ( l + r ` loc ) , i , k ⊨ w )
    → ( s₁ : ( l + r ` loc ) , i , k ⊨ w )
    → ( s₂ : ( l + r ` loc ) , i , k' ⊨ w )
    → ( P : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺
           ( Min⁺ l r loc w i j t₁ ) < ( Min⁺ l r loc w i k t₂ ) )
    → ( P' : l ∣ r ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⁺
           ( Min⁺ l r loc w i k s₁ ) < ( Min⁺ l r loc w i k' s₂ ) )
    → ( a : r , i , j ⊨ w ) ( b : l , i , k' ⊨ w )
    → ( e₁ : Min⁺ l r loc w i j t₁ ≡ ⊨inr l r loc i j w a )
    → ( e₂' : Min⁺ l r loc w i k' s₂ ≡ ⊨inl l r loc i k' w b )
    → ( l + r ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-+-inr-inl l r loc w i j k k' t₁ t₂ s₁ s₂ P P' a b e₁ e₂'
    with ⊨? l i k w
  -- l matches at k : min-t₂ = inl , min-s₁ = inl ; P is inr<inl ( empty ) :
  ... | yes lk =
    let ( x , e₂ ) = Min⁺-inl l r loc w i k lk t₂
    in  ⊥-elim ( inr<inl-+ l r loc w i j k a x
                  ( subst₂ ( λ u v → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺ u < v )
                      e₁ e₂ P ) )
  -- l does not match at k : min-t₂ = inr , min-s₁ = inr ; P' is inr<inl ( empty ) :
  ... | no ¬lk =
    let ( y , e₁' ) = Min⁺-inr l r loc w i k ¬lk s₁
    in  ⊥-elim ( inr<inl-+ l r loc w i k k' y b
                  ( subst₂ ( λ u v → l ∣ r ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⁺ u < v )
                      e₁' e₂' P' ) )

  {-# TERMINATING #-}
  ⊢<-trans-+ : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( l + r ` loc ) , i , j ⊨ w )
    → ( t₂ : ( l + r ` loc ) , i , k ⊨ w )
    → ( s₁ : ( l + r ` loc ) , i , k ⊨ w )
    → ( s₂ : ( l + r ` loc ) , i , k' ⊨ w )
    → ( P : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⁺
           ( Min⁺ l r loc w i j t₁ ) < ( Min⁺ l r loc w i k t₂ ) )
    → ( P' : l ∣ r ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⁺
           ( Min⁺ l r loc w i k s₁ ) < ( Min⁺ l r loc w i k' s₂ ) )
    → ( l + r ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-+ l r loc w i j k k' t₁ t₂ s₁ s₂ P P'
    with ⊨? l i j w | ⊨? l i k' w
  -- l matches at j and at k' : both minimal shapes are inl :
  ... | yes a | yes b =
    let ( a' , e₁ ) = Min⁺-inl l r loc w i j a t₁
        ( b' , e₂' ) = Min⁺-inl l r loc w i k' b s₂
    in ⊢<-trans-+-inl-inl l r loc w i j k k' t₁ t₂ s₁ s₂ P P' a' b' e₁ e₂'
  -- l matches at j , not at k' : inlinr ( no inner inspect needed ) :
  ... | yes a | no ¬b =
    let ( a' , e₁ ) = Min⁺-inl l r loc w i j a t₁
        ( b' , e₂' ) = Min⁺-inr l r loc w i k' ¬b s₂
    in ⊢<-trans-+-inl-inr l r loc w i j k k' t₁ s₂ a' b' e₁ e₂'
  -- l matches at k' , not at j : empty goal ; refute via ⊨? at k :
  ... | no ¬a | yes b =
    let ( a' , e₁ ) = Min⁺-inr l r loc w i j ¬a t₁
        ( b' , e₂' ) = Min⁺-inl l r loc w i k' b s₂
    in ⊢<-trans-+-inr-inl l r loc w i j k k' t₁ t₂ s₁ s₂ P P' a' b' e₁ e₂'
  -- l matches at neither j nor k' : both minimal shapes are inr :
  ... | no ¬a | no ¬b =
    let ( a' , e₁ ) = Min⁺-inr l r loc w i j ¬a t₁
        ( b' , e₂' ) = Min⁺-inr l r loc w i k' ¬b s₂
    in ⊢<-trans-+-inr-inr l r loc w i j k k' t₁ t₂ s₁ s₂ P P' a' b' e₁ e₂'

  -- Purpose : the split position of a ● match ( the j in ⊨● ... j ... ) .
  -- Used in : ⊢<-trans-● ( comparing the middle splits via canon ) .
  ⊨●-split : ∀ { l r : RE } { loc : ℕ } { w : List Char } { i k : ℕ }
    → ( ( l ● r ` loc ) , i , k ⊨ w ) → ℕ
  ⊨●-split ( ⊨● _ _ _ _ _ _ j _ _ _ _ ) = j

  -- Purpose : the head of a * match ; ⊨[] has no head ( returns 0 , only
  --           used via cong when both sides are known to be ⊨∷ ) .
  -- Used in : ⊢<-trans-⋆ ( comparing the middle heads via canon ) .
  ⊨*-head : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { w : List Char } { i k : ℕ }
    → ( ( r * nε ` loc ) , i , k ⊨ w ) → ℕ
  ⊨*-head ( ⊨∷ _ _ _ _ _ _ ( j , _ , _ , _ , _ ) ) = j
  ⊨*-head ( ⊨[] _ _ _ _ _ ) = 0

  -- Purpose : the ● case of ⊢<-trans : glue two ⊢● steps at the middle
  --           position k .
  -- Used in : ⊢<-trans ( ● case ) .
  -- Idea    : deconstruct the two ⊢● steps ( seq₁ / seq₂ ) ; the two middle
  --           minimal splits ( of t₂ and s₁ at ( i , k ) ) coincide by
  --           find-<-Min●-canon , so the four combinations reduce to
  --           transitivity of the l- or r-order :
  --             seq₁ / seq₁ : j₁ < j₂ = j₃ < j₄ ⇒ j₁ < j₄ ( l-trans ) ;
  --             seq₁ / seq₂ : j₁ < j₂ = j₃ = j₄   ⇒ j₁ < j₄ ( l , direct ) ;
  --             seq₂ / seq₁ : j₁ = j₂ = j₃ < j₄   ⇒ j₁ < j₄ ( l , direct ) ;
  --             seq₂ / seq₂ : j₁ = j₂ = j₃ = j₄   ⇒ r-tail-trans .
  --           No find-<-Min● inspect : the with-branches deconstruct the
  --           ⊢● proofs themselves , so no inspect equation is active while
  --           P / P' are used ( unifier-leak confinement , cf. ⊢<-trans-+ ) .
  {-# TERMINATING #-}
  ⊢<-trans-● : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( l ● r ` loc ) , i , j ⊨ w )
    → ( t₂ : ( l ● r ` loc ) , i , k ⊨ w )
    → ( s₁ : ( l ● r ` loc ) , i , k ⊨ w )
    → ( s₂ : ( l ● r ` loc ) , i , k' ⊨ w )
    → ( P : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢●
           ( proj₁ ( find-<-Min● l r loc w i j t₁ ) ) < ( proj₁ ( find-<-Min● l r loc w i k t₂ ) ) )
    → ( P' : l ∣ r ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢●
           ( proj₁ ( find-<-Min● l r loc w i k s₁ ) ) < ( proj₁ ( find-<-Min● l r loc w i k' s₂ ) ) )
    → ( l ● r ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-● l r loc w i j k k' t₁ t₂ s₁ s₂ P P'
    with find-<-Min● l r loc w i j t₁ | inspect ( find-<-Min● l r loc w i j ) t₁
       | find-<-Min● l r loc w i k t₂ | inspect ( find-<-Min● l r loc w i k ) t₂
       | find-<-Min● l r loc w i k s₁ | inspect ( find-<-Min● l r loc w i k ) s₁
       | find-<-Min● l r loc w i k' s₂ | inspect ( find-<-Min● l r loc w i k' ) s₂
  ... | ( min-t₁ , _ ) | [ eq₁ ] | ( min-t₂ , _ ) | [ eq₂ ]
      | ( min-s₁ , _ ) | [ eq₃ ] | ( min-s₂ , _ ) | [ eq₄ ]
      with min-t₁ | min-t₂ | min-s₁ | min-s₂
  ... | ⊨● _ _ _ _ _ _ j₁ _ _ u₁ v₁ | ⊨● _ _ _ _ _ _ j₂ _ _ u₂ v₂
      | ⊨● _ _ _ _ _ _ j₃ _ _ u₃ v₃ | ⊨● _ _ _ _ _ _ j₄ _ _ u₄ v₄
      with P | P'
  -- seq₁ / seq₁ : j₁ < j₂ = j₃ < j₄ ⇒ j₁ < j₄ by l-transitivity :
  ... | seq₁ .i .j₁ .j .j₂ .k .u₁ .v₁ .u₂ .v₂ l<j₂
      | seq₁ .i .j₃ .k .j₄ .k' .u₃ .v₃ .u₄ .v₄ l3<j₄ =
    let j₂≡j₃ = cong ⊨●-split
                ( trans ( sym ( cong proj₁ eq₂ ) )
                    ( trans ( find-<-Min●-canon l r loc w i k t₂ s₁ )
                            ( cong proj₁ eq₃ ) ) )
    in  ⊢<-trans-●-11 l r loc w i j k k' t₁ t₂ s₁ s₂
          j₁ u₁ v₁ j₂ j₃ j₄ u₄ v₄ l<j₂ l3<j₄ j₂≡j₃
          ( cong proj₁ eq₁ ) ( cong proj₁ eq₄ )
  -- seq₁ / seq₂ : j₁ < j₂ = j₃ = j₄ ⇒ j₁ < j₄ directly :
  ... | seq₁ .i .j₁ .j .j₂ .k .u₁ .v₁ .u₂ .v₂ l<j₂
      | seq₂ .i .j₃ .j₄ .k .k' .u₃ .v₃ .u₄ .v₄ j₃≡j₄ r<j₃<k' =
    let j₂≡j₃ = cong ⊨●-split
                ( trans ( sym ( cong proj₁ eq₂ ) )
                    ( trans ( find-<-Min●-canon l r loc w i k t₂ s₁ )
                            ( cong proj₁ eq₃ ) ) )
    in  ⊢<-trans-●-12 l r loc w i j k k' t₁ t₂ s₁ s₂
          j₁ u₁ v₁ j₂ j₃ j₄ u₄ v₄ l<j₂ j₃≡j₄ r<j₃<k' j₂≡j₃
          ( cong proj₁ eq₁ ) ( cong proj₁ eq₄ )
  -- seq₂ / seq₁ : j₁ = j₂ = j₃ < j₄ ⇒ j₁ < j₄ directly :
  ... | seq₂ .i .j₁ .j₂ .j .k .u₁ .v₁ .u₂ .v₂ j₁≡j₂ r<j₁<k
      | seq₁ .i .j₃ .k .j₄ .k' .u₃ .v₃ .u₄ .v₄ l3<j₄ =
    let j₂≡j₃ = cong ⊨●-split
                ( trans ( sym ( cong proj₁ eq₂ ) )
                    ( trans ( find-<-Min●-canon l r loc w i k t₂ s₁ )
                            ( cong proj₁ eq₃ ) ) )
    in  ⊢<-trans-●-21 l r loc w i j k k' t₁ t₂ s₁ s₂
          j₁ j₂ j₃ j₄ u₁ v₁ u₄ v₄ j₁≡j₂ r<j₁<k l3<j₄ j₂≡j₃
          ( cong proj₁ eq₁ ) ( cong proj₁ eq₄ )
  -- seq₂ / seq₂ : j₁ = j₂ = j₃ = j₄ ⇒ r-tail-transitivity :
  ... | seq₂ .i .j₁ .j₂ .j .k .u₁ .v₁ .u₂ .v₂ j₁≡j₂ r<j₁<k
      | seq₂ .i .j₃ .j₄ .k .k' .u₃ .v₃ .u₄ .v₄ j₃≡j₄ r<j₃<k' =
    let j₂≡j₃ = cong ⊨●-split
                ( trans ( sym ( cong proj₁ eq₂ ) )
                    ( trans ( find-<-Min●-canon l r loc w i k t₂ s₁ )
                            ( cong proj₁ eq₃ ) ) )
    in  ⊢<-trans-●-22 l r loc w i j k k' t₁ t₂ s₁ s₂
          j₁ j₂ j₃ j₄ u₁ v₁ u₄ v₄ j₁≡j₂ r<j₁<k j₃≡j₄ r<j₃<k' j₂≡j₃
          ( cong proj₁ eq₁ ) ( cong proj₁ eq₄ )

  -- Purpose : the four ( seq₁ / seq₂ ) × ( seq₁ / seq₂ ) combinations of
  --           ⊢<-trans-● ; each takes all shape data explicitly ( no with ,
  --           no inspect ) so that the caller's with-branches stay trivial .
  -- Used in : ⊢<-trans-● .
  -- Idea    : the two middle minimal splits ( of t₂ and s₁ at ( i , k ) )
  --           coincide by find-<-Min●-canon ; the split equality is extracted
  --           via cong ⊨●-split on the transported canon equation , and the
  --           conclusion is a fresh seq₁ / seq₂ transported back onto the
  --           minimal evidence with subst₂ ( cf. decide-⊢< , ● case ) .
  {-# TERMINATING #-}
  ⊢<-trans-●-11 : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( l ● r ` loc ) , i , j ⊨ w )
    → ( t₂ : ( l ● r ` loc ) , i , k ⊨ w )
    → ( s₁ : ( l ● r ` loc ) , i , k ⊨ w )
    → ( s₂ : ( l ● r ` loc ) , i , k' ⊨ w )
    → ( j₁ : ℕ ) ( u₁ : l , i , j₁ ⊨ w ) ( v₁ : r , j₁ , j ⊨ w )
    → ( j₂ : ℕ ) ( j₃ : ℕ ) ( j₄ : ℕ )
    → ( u₄ : l , i , j₄ ⊨ w ) ( v₄ : r , j₄ , k' ⊨ w )
    → ( l ∣ w ∣ i ⊢ j₁ < j₂ )
    → ( l ∣ w ∣ i ⊢ j₃ < j₄ )
    → ( j₂ ≡ j₃ )
    → ( e₁ : proj₁ ( find-<-Min● l r loc w i j t₁ )
              ≡ ⊨● l r loc i j w j₁ ( rij⊨w→i≤j u₁ ) ( rij⊨w→i≤j v₁ ) u₁ v₁ )
    → ( e₄ : proj₁ ( find-<-Min● l r loc w i k' s₂ )
              ≡ ⊨● l r loc i k' w j₄ ( rij⊨w→i≤j u₄ ) ( rij⊨w→i≤j v₄ ) u₄ v₄ )
    → ( l ● r ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-●-11 l r loc w i j k k' t₁ t₂ s₁ s₂
    j₁ u₁ v₁ j₂ j₃ j₄ u₄ v₄ l<j₂ l3<j₄ j₂≡j₃ e₁ e₄ =
    let l1 = subst ( λ m → l ∣ w ∣ i ⊢ j₁ < m ) j₂≡j₃ l<j₂
    in  seq i j k' t₁ s₂
          ( subst₂ ( λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢● x < y )
              ( sym e₁ ) ( sym e₄ )
              ( seq₁ i j₁ j j₄ k' u₁ v₁ u₄ v₄
                  ( ⊢<-trans l w i j₁ j₃ j₄ l1 l3<j₄ ) ) )

  {-# TERMINATING #-}
  ⊢<-trans-●-12 : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( l ● r ` loc ) , i , j ⊨ w )
    → ( t₂ : ( l ● r ` loc ) , i , k ⊨ w )
    → ( s₁ : ( l ● r ` loc ) , i , k ⊨ w )
    → ( s₂ : ( l ● r ` loc ) , i , k' ⊨ w )
    → ( j₁ : ℕ ) ( u₁ : l , i , j₁ ⊨ w ) ( v₁ : r , j₁ , j ⊨ w )
    → ( j₂ : ℕ ) ( j₃ : ℕ ) ( j₄ : ℕ )
    → ( u₄ : l , i , j₄ ⊨ w ) ( v₄ : r , j₄ , k' ⊨ w )
    → ( l ∣ w ∣ i ⊢ j₁ < j₂ )
    → ( j₃ ≡ j₄ )
    → ( r ∣ w ∣ j₃ ⊢ k < k' )
    → ( j₂ ≡ j₃ )
    → ( e₁ : proj₁ ( find-<-Min● l r loc w i j t₁ )
              ≡ ⊨● l r loc i j w j₁ ( rij⊨w→i≤j u₁ ) ( rij⊨w→i≤j v₁ ) u₁ v₁ )
    → ( e₄ : proj₁ ( find-<-Min● l r loc w i k' s₂ )
              ≡ ⊨● l r loc i k' w j₄ ( rij⊨w→i≤j u₄ ) ( rij⊨w→i≤j v₄ ) u₄ v₄ )
    → ( l ● r ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-●-12 l r loc w i j k k' t₁ t₂ s₁ s₂
    j₁ u₁ v₁ j₂ j₃ j₄ u₄ v₄ l<j₂ j₃≡j₄ r<j₃<k' j₂≡j₃ e₁ e₄ =
    seq i j k' t₁ s₂
      ( subst₂ ( λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢● x < y )
          ( sym e₁ ) ( sym e₄ )
          ( seq₁ i j₁ j j₄ k' u₁ v₁ u₄ v₄
              ( subst ( λ m → l ∣ w ∣ i ⊢ j₁ < m )
                  ( trans j₂≡j₃ j₃≡j₄ ) l<j₂ ) ) )

  {-# TERMINATING #-}
  ⊢<-trans-●-21 : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( l ● r ` loc ) , i , j ⊨ w )
    → ( t₂ : ( l ● r ` loc ) , i , k ⊨ w )
    → ( s₁ : ( l ● r ` loc ) , i , k ⊨ w )
    → ( s₂ : ( l ● r ` loc ) , i , k' ⊨ w )
    → ( j₁ : ℕ ) ( j₂ : ℕ ) ( j₃ : ℕ ) ( j₄ : ℕ )
    → ( u₁ : l , i , j₁ ⊨ w ) ( v₁ : r , j₁ , j ⊨ w )
    → ( u₄ : l , i , j₄ ⊨ w ) ( v₄ : r , j₄ , k' ⊨ w )
    → ( j₁ ≡ j₂ )
    → ( r ∣ w ∣ j₁ ⊢ j < k )
    → ( l ∣ w ∣ i ⊢ j₃ < j₄ )
    → ( j₂ ≡ j₃ )
    → ( e₁ : proj₁ ( find-<-Min● l r loc w i j t₁ )
              ≡ ⊨● l r loc i j w j₁ ( rij⊨w→i≤j u₁ ) ( rij⊨w→i≤j v₁ ) u₁ v₁ )
    → ( e₄ : proj₁ ( find-<-Min● l r loc w i k' s₂ )
              ≡ ⊨● l r loc i k' w j₄ ( rij⊨w→i≤j u₄ ) ( rij⊨w→i≤j v₄ ) u₄ v₄ )
    → ( l ● r ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-●-21 l r loc w i j k k' t₁ t₂ s₁ s₂
    j₁ j₂ j₃ j₄ u₁ v₁ u₄ v₄ j₁≡j₂ r<j₁<k l3<j₄ j₂≡j₃ e₁ e₄ =
    seq i j k' t₁ s₂
      ( subst₂ ( λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢● x < y )
          ( sym e₁ ) ( sym e₄ )
          ( seq₁ i j₁ j j₄ k' u₁ v₁ u₄ v₄
              ( subst ( λ m → l ∣ w ∣ i ⊢ m < j₄ )
                  ( sym ( trans j₁≡j₂ j₂≡j₃ ) ) l3<j₄ ) ) )

  {-# TERMINATING #-}
  ⊢<-trans-●-22 : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( l ● r ` loc ) , i , j ⊨ w )
    → ( t₂ : ( l ● r ` loc ) , i , k ⊨ w )
    → ( s₁ : ( l ● r ` loc ) , i , k ⊨ w )
    → ( s₂ : ( l ● r ` loc ) , i , k' ⊨ w )
    → ( j₁ : ℕ ) ( j₂ : ℕ ) ( j₃ : ℕ ) ( j₄ : ℕ )
    → ( u₁ : l , i , j₁ ⊨ w ) ( v₁ : r , j₁ , j ⊨ w )
    → ( u₄ : l , i , j₄ ⊨ w ) ( v₄ : r , j₄ , k' ⊨ w )
    → ( j₁ ≡ j₂ )
    → ( r ∣ w ∣ j₁ ⊢ j < k )
    → ( j₃ ≡ j₄ )
    → ( r ∣ w ∣ j₃ ⊢ k < k' )
    → ( j₂ ≡ j₃ )
    → ( e₁ : proj₁ ( find-<-Min● l r loc w i j t₁ )
              ≡ ⊨● l r loc i j w j₁ ( rij⊨w→i≤j u₁ ) ( rij⊨w→i≤j v₁ ) u₁ v₁ )
    → ( e₄ : proj₁ ( find-<-Min● l r loc w i k' s₂ )
              ≡ ⊨● l r loc i k' w j₄ ( rij⊨w→i≤j u₄ ) ( rij⊨w→i≤j v₄ ) u₄ v₄ )
    → ( l ● r ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-●-22 l r loc w i j k k' t₁ t₂ s₁ s₂
    j₁ j₂ j₃ j₄ u₁ v₁ u₄ v₄ j₁≡j₂ r<j₁<k j₃≡j₄ r<j₃<k' j₂≡j₃ e₁ e₄ =
    let j₁≡j₃ = trans j₁≡j₂ j₂≡j₃
        j₁≡j₄ = trans j₁≡j₃ j₃≡j₄
        tail = ⊢<-trans r w j₁ j k k' r<j₁<k
                 ( subst ( λ m → r ∣ w ∣ m ⊢ k < k' ) ( sym j₁≡j₃ ) r<j₃<k' )
    in  seq i j k' t₁ s₂
          ( subst₂ ( λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢● x < y )
              ( sym e₁ ) ( sym e₄ )
              ( seq₂ i j₁ j₄ j k' u₁ v₁ u₄ v₄ j₁≡j₄ tail ) )

  -- Purpose : the ( *-head / *-head ) and ( *-head / *-tail ) combinations
  --           of ⊢<-trans-⋆ ; the middle heads coincide by canon :
  --           j₁ < j₂ = j₃ < j₄ ⇒ j₁ < j₄ ;  j₁ < j₂ = j₃ = j₄ ⇒ j₁ < j₄ .
  -- Used in : ⊢<-trans-⋆ ( all-⊨∷ shape branch ) .
  -- Idea    : as in ⊢<-trans-●-11 / -12 : the middle head equality j₂ ≡ j₃
  --           is computed by the caller ( on with-bound concrete shapes )
  --           and passed in ; the conclusion is a fresh *-head transported
  --           back onto the minimal evidence with subst₂ .
  {-# TERMINATING #-}
  ⊢<-trans-⋆-11 : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( r * nε ` loc ) , i , j ⊨ w )
    → ( t₂ : ( r * nε ` loc ) , i , k ⊨ w )
    → ( s₁ : ( r * nε ` loc ) , i , k ⊨ w )
    → ( s₂ : ( r * nε ` loc ) , i , k' ⊨ w )
    → ( j₁ : ℕ ) ( j₂ : ℕ ) ( j₃ : ℕ ) ( j₄ : ℕ )
    → ( i<j₁ : i Nat.< j₁ ) ( j₁≤j : j₁ Nat.≤ j )
    → ( u₁ : r , i , j₁ ⊨ w ) ( v₁ : r * nε ` loc , j₁ , j ⊨ w )
    → ( i<j₄ : i Nat.< j₄ ) ( j₄≤k' : j₄ Nat.≤ k' )
    → ( u₄ : r , i , j₄ ⊨ w ) ( v₄ : r * nε ` loc , j₄ , k' ⊨ w )
    → ( r ∣ w ∣ i ⊢ j₁ < j₂ )
    → ( r ∣ w ∣ i ⊢ j₃ < j₄ )
    → ( j₂ ≡ j₃ )
    → ( e₁ : proj₁ ( find-<-Min* r nε loc w i j t₁ )
              ≡ ⊨∷ r nε loc w i j ( j₁ , i<j₁ , j₁≤j , u₁ , v₁ ) )
    → ( e₄ : proj₁ ( find-<-Min* r nε loc w i k' s₂ )
              ≡ ⊨∷ r nε loc w i k' ( j₄ , i<j₄ , j₄≤k' , u₄ , v₄ ) )
    → ( r * nε ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-⋆-11 r nε loc w i j k k' t₁ t₂ s₁ s₂
    j₁ j₂ j₃ j₄ i<j₁ j₁≤j u₁ v₁ i<j₄ j₄≤k' u₄ v₄
    r<j₁<j₂ r<j₃<j₄ j₂≡j₃ e₁ e₄ =
    let r1 = subst ( λ m → r ∣ w ∣ i ⊢ j₁ < m ) j₂≡j₃ r<j₁<j₂
    in  star i j k' t₁ s₂
          ( subst₂ ( λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢⋆ x < y )
              ( sym e₁ ) ( sym e₄ )
              ( *-head i j₁ j₄ j k' i<j₁ j₁≤j i<j₄ j₄≤k' u₁ v₁ u₄ v₄
                  ( ⊢<-trans r w i j₁ j₃ j₄ r1 r<j₃<j₄ ) ) )

  {-# TERMINATING #-}
  ⊢<-trans-⋆-12 : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( r * nε ` loc ) , i , j ⊨ w )
    → ( t₂ : ( r * nε ` loc ) , i , k ⊨ w )
    → ( s₁ : ( r * nε ` loc ) , i , k ⊨ w )
    → ( s₂ : ( r * nε ` loc ) , i , k' ⊨ w )
    → ( j₁ : ℕ ) ( j₂ : ℕ ) ( j₃ : ℕ ) ( j₄ : ℕ )
    → ( i<j₁ : i Nat.< j₁ ) ( j₁≤j : j₁ Nat.≤ j )
    → ( u₁ : r , i , j₁ ⊨ w ) ( v₁ : r * nε ` loc , j₁ , j ⊨ w )
    → ( i<j₄ : i Nat.< j₄ ) ( j₄≤k' : j₄ Nat.≤ k' )
    → ( u₄ : r , i , j₄ ⊨ w ) ( v₄ : r * nε ` loc , j₄ , k' ⊨ w )
    → ( r ∣ w ∣ i ⊢ j₁ < j₂ )
    → ( j₃ ≡ j₄ )
    → ( j₂ ≡ j₃ )
    → ( e₁ : proj₁ ( find-<-Min* r nε loc w i j t₁ )
              ≡ ⊨∷ r nε loc w i j ( j₁ , i<j₁ , j₁≤j , u₁ , v₁ ) )
    → ( e₄ : proj₁ ( find-<-Min* r nε loc w i k' s₂ )
              ≡ ⊨∷ r nε loc w i k' ( j₄ , i<j₄ , j₄≤k' , u₄ , v₄ ) )
    → ( r * nε ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-⋆-12 r nε loc w i j k k' t₁ t₂ s₁ s₂
    j₁ j₂ j₃ j₄ i<j₁ j₁≤j u₁ v₁ i<j₄ j₄≤k' u₄ v₄
    r<j₁<j₂ j₃≡j₄ j₂≡j₃ e₁ e₄ =
    star i j k' t₁ s₂
      ( subst₂ ( λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢⋆ x < y )
          ( sym e₁ ) ( sym e₄ )
          ( *-head i j₁ j₄ j k' i<j₁ j₁≤j i<j₄ j₄≤k' u₁ v₁ u₄ v₄
              ( subst ( λ m → r ∣ w ∣ i ⊢ j₁ < m )
                  ( trans j₂≡j₃ j₃≡j₄ ) r<j₁<j₂ ) ) )

  -- Purpose : the ( *-tail / *-head ) and ( *-tail / *-tail ) combinations
  --           of ⊢<-trans-⋆ ; the middle heads coincide by canon :
  --           j₁ = j₂ = j₃ < j₄ ⇒ j₁ < j₄ ;
  --           j₁ = j₂ = j₃ = j₄ ⇒ tail-transitivity on r * nε .
  -- Used in : ⊢<-trans-⋆ ( all-⊨∷ shape branch ) .
  {-# TERMINATING #-}
  ⊢<-trans-⋆-21 : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( r * nε ` loc ) , i , j ⊨ w )
    → ( t₂ : ( r * nε ` loc ) , i , k ⊨ w )
    → ( s₁ : ( r * nε ` loc ) , i , k ⊨ w )
    → ( s₂ : ( r * nε ` loc ) , i , k' ⊨ w )
    → ( j₁ : ℕ ) ( j₂ : ℕ ) ( j₃ : ℕ ) ( j₄ : ℕ )
    → ( i<j₁ : i Nat.< j₁ ) ( j₁≤j : j₁ Nat.≤ j )
    → ( u₁ : r , i , j₁ ⊨ w ) ( v₁ : r * nε ` loc , j₁ , j ⊨ w )
    → ( i<j₄ : i Nat.< j₄ ) ( j₄≤k' : j₄ Nat.≤ k' )
    → ( u₄ : r , i , j₄ ⊨ w ) ( v₄ : r * nε ` loc , j₄ , k' ⊨ w )
    → ( j₁ ≡ j₂ )
    → ( r ∣ w ∣ i ⊢ j₃ < j₄ )
    → ( j₂ ≡ j₃ )
    → ( e₁ : proj₁ ( find-<-Min* r nε loc w i j t₁ )
              ≡ ⊨∷ r nε loc w i j ( j₁ , i<j₁ , j₁≤j , u₁ , v₁ ) )
    → ( e₄ : proj₁ ( find-<-Min* r nε loc w i k' s₂ )
              ≡ ⊨∷ r nε loc w i k' ( j₄ , i<j₄ , j₄≤k' , u₄ , v₄ ) )
    → ( r * nε ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-⋆-21 r nε loc w i j k k' t₁ t₂ s₁ s₂
    j₁ j₂ j₃ j₄ i<j₁ j₁≤j u₁ v₁ i<j₄ j₄≤k' u₄ v₄
    j₁≡j₂ r<j₃<j₄ j₂≡j₃ e₁ e₄ =
    star i j k' t₁ s₂
      ( subst₂ ( λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢⋆ x < y )
          ( sym e₁ ) ( sym e₄ )
          ( *-head i j₁ j₄ j k' i<j₁ j₁≤j i<j₄ j₄≤k' u₁ v₁ u₄ v₄
              ( subst ( λ m → r ∣ w ∣ i ⊢ m < j₄ )
                  ( sym ( trans j₁≡j₂ j₂≡j₃ ) ) r<j₃<j₄ ) ) )

  {-# TERMINATING #-}
  ⊢<-trans-⋆-22 : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( r * nε ` loc ) , i , j ⊨ w )
    → ( t₂ : ( r * nε ` loc ) , i , k ⊨ w )
    → ( s₁ : ( r * nε ` loc ) , i , k ⊨ w )
    → ( s₂ : ( r * nε ` loc ) , i , k' ⊨ w )
    → ( j₁ : ℕ ) ( j₂ : ℕ ) ( j₃ : ℕ ) ( j₄ : ℕ )
    → ( i<j₁ : i Nat.< j₁ ) ( j₁≤j : j₁ Nat.≤ j )
    → ( u₁ : r , i , j₁ ⊨ w ) ( v₁ : r * nε ` loc , j₁ , j ⊨ w )
    → ( i<j₄ : i Nat.< j₄ ) ( j₄≤k' : j₄ Nat.≤ k' )
    → ( u₄ : r , i , j₄ ⊨ w ) ( v₄ : r * nε ` loc , j₄ , k' ⊨ w )
    → ( j₁ ≡ j₂ )
    → ( r * nε ` loc ∣ w ∣ j₁ ⊢ j < k )
    → ( j₃ ≡ j₄ )
    → ( r * nε ` loc ∣ w ∣ j₃ ⊢ k < k' )
    → ( j₂ ≡ j₃ )
    → ( e₁ : proj₁ ( find-<-Min* r nε loc w i j t₁ )
              ≡ ⊨∷ r nε loc w i j ( j₁ , i<j₁ , j₁≤j , u₁ , v₁ ) )
    → ( e₄ : proj₁ ( find-<-Min* r nε loc w i k' s₂ )
              ≡ ⊨∷ r nε loc w i k' ( j₄ , i<j₄ , j₄≤k' , u₄ , v₄ ) )
    → ( r * nε ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-⋆-22 r nε loc w i j k k' t₁ t₂ s₁ s₂
    j₁ j₂ j₃ j₄ i<j₁ j₁≤j u₁ v₁ i<j₄ j₄≤k' u₄ v₄
    j₁≡j₂ tail₁ j₃≡j₄ tail₂ j₂≡j₃ e₁ e₄ =
    let j₁≡j₃ = trans j₁≡j₂ j₂≡j₃
        j₁≡j₄ = trans j₁≡j₃ j₃≡j₄
        tail = ⊢<-trans ( r * nε ` loc ) w j₁ j k k' tail₁
                 ( subst ( λ m → ( r * nε ` loc ) ∣ w ∣ m ⊢ k < k' )
                     ( sym j₁≡j₃ ) tail₂ )
    in  star i j k' t₁ s₂
          ( subst₂ ( λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢⋆ x < y )
              ( sym e₁ ) ( sym e₄ )
              ( *-tail i j₁ j₄ j k' i<j₁ j₁≤j i<j₄ j₄≤k' u₁ v₁ u₄ v₄
                  j₁≡j₄ tail ) )

  -- Purpose : the ⊨[] LHS case of ⊢<-trans-⋆ ( a-branch ) : P is
  --           impossible , since every ⊢⋆ constructor has an ⊨∷ LHS .
  -- Used in : ⊢<-trans-⋆ ( a-branch , min-t₁ = ⊨[] r nε loc w i ) .
  -- Idea    : the shape constraint min-t₁ = ⊨[] r nε loc w i lets the
  --           caller's P unify with the concrete-⊨[]-LHS premise ( the
  --           stuck find on the RHS is absorbed by the implicit meta ) ,
  --           then ¬⊢⋆-[]-∷ finishes .  A nested `with P` in the branch
  --           itself is not an option : it would break Agda's with-clause
  --           grouping ( the following shape branch gets swallowed into
  --           the nested with : "Unexpected with patterns" ) .
  ¬⊢⋆-min-[]-a : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i k : ℕ )
    → { min-t₂ : ( r * nε ` loc ) , i , k ⊨ w }
    → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i i k ( ⊨[] r nε loc w i ) min-t₂ → ⊥
  ¬⊢⋆-min-[]-a r nε loc w i k { min-t₂ } P = ¬⊢⋆-[]-∷ min-t₂ P

  -- Purpose : the ⊨[] LHS case of ⊢<-trans-⋆ ( b-branch ) : P' is
  --           impossible , ditto .
  -- Used in : ⊢<-trans-⋆ ( b-branch , min-s₁ = ⊨[] r nε loc w i ) .
  -- Idea    : as ¬⊢⋆-min-[]-a .
  ¬⊢⋆-min-[]-b : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i k' : ℕ )
    → { min-s₂ : ( r * nε ` loc ) , i , k' ⊨ w }
    → _∣_∣_∣_∣_∣_∣_⊢⋆_<_ r nε loc w i i k' ( ⊨[] r nε loc w i ) min-s₂ → ⊥
  ¬⊢⋆-min-[]-b r nε loc w i k' { min-s₂ } P' = ¬⊢⋆-[]-∷ min-s₂ P'

  -- Purpose : the * case of ⊢<-trans : glue two ⊢⋆ steps at the middle
  --           position k .
  -- Used in : ⊢<-trans ( * case ) .
  -- Idea    : inspect the four minimal matches ( find-<-Min* + inspect ) and
  --           match their shapes ; the two middle minimal matches ( of t₂
  --           and s₁ at ( i , k ) ) coincide by find-<-Min*-canon :
  --             min-t₁ = ⊨[]          : P impossible ( ⊢⋆ LHS is ⊨∷ ) ;
  --             min-s₁ = ⊨[]          : P' impossible ( ditto ) ;
  --             min-t₂ = ⊨[] , min-s₁ = ⊨∷ : i < j₃ ≤ k with k ≡ i ( ⊥ ) ;
  --             otherwise             : one merged branch over P | P' with
  --                                     P ∈ { *-head , *-tail } and
  --                                     P' ∈ { *-head , *-tail ,
  --                                             *-cons-nil } ; the
  --                                     *-cons-nil cases ( min-s₂ = ⊨[] ,
  --                                     k' ≡ i ) build *-cons-nil directly ;
  --                                     the rest glue the heads via the
  --                                     middle canon ( helpers
  --                                     ⊢<-trans-⋆-11 .. -22 ) .
  --           The with-branches stay trivial ( top-level helper calls ) so
  --           that unifier state does not leak between pattern checks
  --           ( cf. ⊢<-trans-● ) .
  {-# TERMINATING #-}
  ⊢<-trans-⋆ : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char ) ( i j k k' : ℕ )
    → ( t₁ : ( r * nε ` loc ) , i , j ⊨ w )
    → ( t₂ : ( r * nε ` loc ) , i , k ⊨ w )
    → ( s₁ : ( r * nε ` loc ) , i , k ⊨ w )
    → ( s₂ : ( r * nε ` loc ) , i , k' ⊨ w )
    → ( P : r ∣ nε ∣ loc ∣ w ∣ i ∣ j ∣ k ⊢⋆
           ( proj₁ ( find-<-Min* r nε loc w i j t₁ ) ) < ( proj₁ ( find-<-Min* r nε loc w i k t₂ ) ) )
    → ( P' : r ∣ nε ∣ loc ∣ w ∣ i ∣ k ∣ k' ⊢⋆
           ( proj₁ ( find-<-Min* r nε loc w i k s₁ ) ) < ( proj₁ ( find-<-Min* r nε loc w i k' s₂ ) ) )
    → ( r * nε ` loc ) ∣ w ∣ i ⊢ j < k'
  ⊢<-trans-⋆ r nε loc w i j k k' t₁ t₂ s₁ s₂ P P'
    with find-<-Min* r nε loc w i j t₁ | inspect ( find-<-Min* r nε loc w i j ) t₁
       | find-<-Min* r nε loc w i k t₂ | inspect ( find-<-Min* r nε loc w i k ) t₂
       | find-<-Min* r nε loc w i k s₁ | inspect ( find-<-Min* r nε loc w i k ) s₁
       | find-<-Min* r nε loc w i k' s₂ | inspect ( find-<-Min* r nε loc w i k' ) s₂
  ... | ( min-t₁ , _ ) | [ eq₁ ] | ( min-t₂ , _ ) | [ eq₂ ]
      | ( min-s₁ , _ ) | [ eq₃ ] | ( min-s₂ , _ ) | [ eq₄ ]
      with min-t₁ | min-t₂ | min-s₁ | min-s₂
  -- min-t₁ = ⊨[] : P impossible ( every ⊢⋆ constructor has an ⊨∷ LHS ) ;
  --   the helper absorbs the stuck find on P's RHS via an implicit meta :
  ... | ⊨[] r nε loc w i | _ | _ | _ =
    ⊥-elim ( ¬⊢⋆-min-[]-a r nε loc w i k P )
  -- min-s₁ = ⊨[] : P' impossible ( ditto ) :
  ... | ⊨∷ _ _ _ _ _ _ _ | _ | ⊨[] r nε loc w i | _ =
    ⊥-elim ( ¬⊢⋆-min-[]-b r nε loc w i k' P' )
  -- min-t₂ = ⊨[] but min-s₁ = ⊨∷ : the shape constraint min-t₂ =
  --   ⊨[] r nε loc w i forces k ≡ i , while the ⊨∷ payload of min-s₁
  --   requires i < j₃ ≤ k , hence i < i :
  ... | ⊨∷ _ _ _ _ _ _ _ | ⊨[] r nε loc w i | ⊨∷ r nε loc w i k ( j₃ , i<j₃ , j₃≤k , u₃ , v₃ ) | _ =
    ⊥-elim ( <-irrefl refl ( ≤-trans i<j₃ j₃≤k ) )
  -- min-s₂ = ⊨[] or ⊨∷ : one merged shape branch ( the last one ) whose
  --     body is `with P | P'` ; P ∈ { *-head , *-tail } and
  --     P' ∈ { *-head , *-tail , *-cons-nil } .  In the *-cons-nil cases
  --     ( min-s₂ = ⊨[] , k' ≡ i ) the pattern check leaves k' ≟ i pending
  --     and the body builds *-cons-nil directly ; in the *-head / *-tail
  --     cases j₄ , i<j₄ , j₄≤k' , u₄ , v₄ are bound by the P' pattern and
  --     the constraint min-s₂ ≡ ⊨∷ ... that the helpers need for e₄ is
  --     carried by the pattern context .
  ... | ⊨∷ _ _ _ _ _ _ ( j₁ , i<j₁ , j₁≤j , u₁ , v₁ )
      | ⊨∷ _ _ _ _ _ _ ( j₂ , i<j₂ , j₂≤k , u₂ , v₂ )
      | ⊨∷ _ _ _ _ _ _ ( j₃ , i<j₃ , j₃≤k , u₃ , v₃ )
      | _
      with P | P'
  -- *-head / *-head : j₁ < j₂ = j₃ < j₄ ⇒ j₁ < j₄ by l-transitivity :
  ... | *-head .i .j₁ .j₂ .j .k .i<j₁ .j₁≤j .i<j₂ .j₂≤k .u₁ .v₁ .u₂ .v₂ r<j₁<j₂
      | *-head .i .j₃ j₄ .k .k' .i<j₃ .j₃≤k i<j₄ j₄≤k' .u₃ .v₃ u₄ v₄ r<j₃<j₄ =
    let j₂≡j₃ = cong ⊨*-head
                ( trans ( sym ( cong proj₁ eq₂ ) )
                    ( trans ( find-<-Min*-canon r nε loc w i k t₂ s₁ )
                            ( cong proj₁ eq₃ ) ) )
    in  ⊢<-trans-⋆-11 r nε loc w i j k k' t₁ t₂ s₁ s₂
          j₁ j₂ j₃ j₄ i<j₁ j₁≤j u₁ v₁ i<j₄ j₄≤k' u₄ v₄ r<j₁<j₂ r<j₃<j₄ j₂≡j₃
          ( cong proj₁ eq₁ ) ( cong proj₁ eq₄ )
  -- *-head / *-tail : j₁ < j₂ = j₃ = j₄ ⇒ j₁ < j₄ directly :
  ... | *-head .i .j₁ .j₂ .j .k .i<j₁ .j₁≤j .i<j₂ .j₂≤k .u₁ .v₁ .u₂ .v₂ r<j₁<j₂
      | *-tail .i .j₃ j₄ .k .k' .i<j₃ .j₃≤k i<j₄ j₄≤k' .u₃ .v₃ u₄ v₄ j₃≡j₄ tail₂ =
    let j₂≡j₃ = cong ⊨*-head
                ( trans ( sym ( cong proj₁ eq₂ ) )
                    ( trans ( find-<-Min*-canon r nε loc w i k t₂ s₁ )
                            ( cong proj₁ eq₃ ) ) )
    in  ⊢<-trans-⋆-12 r nε loc w i j k k' t₁ t₂ s₁ s₂
          j₁ j₂ j₃ j₄ i<j₁ j₁≤j u₁ v₁ i<j₄ j₄≤k' u₄ v₄ r<j₁<j₂ j₃≡j₄ j₂≡j₃
          ( cong proj₁ eq₁ ) ( cong proj₁ eq₄ )
  -- *-head / *-cons-nil : min-s₂ = ⊨[] ( k' ≡ i ) ⇒ *-cons-nil :
  ... | *-head .i .j₁ .j₂ .j .k .i<j₁ .j₁≤j .i<j₂ .j₂≤k .u₁ .v₁ .u₂ .v₂ r<j₁<j₂
      | *-cons-nil .i .j₃ .k .i<j₃ .j₃≤k .u₃ .v₃ =
    star i j k' t₁ s₂
      ( subst₂ ( λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢⋆ x < y )
          ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₄ ) )
          ( *-cons-nil i j₁ j i<j₁ j₁≤j u₁ v₁ ) )
  -- *-tail / *-head : j₁ = j₂ = j₃ < j₄ ⇒ j₁ < j₄ :
  ... | *-tail .i .j₁ .j₂ .j .k .i<j₁ .j₁≤j .i<j₂ .j₂≤k .u₁ .v₁ .u₂ .v₂ j₁≡j₂ tail₁
      | *-head .i .j₃ j₄ .k .k' .i<j₃ .j₃≤k i<j₄ j₄≤k' .u₃ .v₃ u₄ v₄ r<j₃<j₄ =
    let j₂≡j₃ = cong ⊨*-head
                ( trans ( sym ( cong proj₁ eq₂ ) )
                    ( trans ( find-<-Min*-canon r nε loc w i k t₂ s₁ )
                            ( cong proj₁ eq₃ ) ) )
    in  ⊢<-trans-⋆-21 r nε loc w i j k k' t₁ t₂ s₁ s₂
          j₁ j₂ j₃ j₄ i<j₁ j₁≤j u₁ v₁ i<j₄ j₄≤k' u₄ v₄ j₁≡j₂ r<j₃<j₄ j₂≡j₃
          ( cong proj₁ eq₁ ) ( cong proj₁ eq₄ )
  -- *-tail / *-tail : j₁ = j₂ = j₃ = j₄ ⇒ tail-transitivity on r * nε :
  ... | *-tail .i .j₁ .j₂ .j .k .i<j₁ .j₁≤j .i<j₂ .j₂≤k .u₁ .v₁ .u₂ .v₂ j₁≡j₂ tail₁
      | *-tail .i .j₃ j₄ .k .k' .i<j₃ .j₃≤k i<j₄ j₄≤k' .u₃ .v₃ u₄ v₄ j₃≡j₄ tail₂ =
    let j₂≡j₃ = cong ⊨*-head
                ( trans ( sym ( cong proj₁ eq₂ ) )
                    ( trans ( find-<-Min*-canon r nε loc w i k t₂ s₁ )
                            ( cong proj₁ eq₃ ) ) )
    in  ⊢<-trans-⋆-22 r nε loc w i j k k' t₁ t₂ s₁ s₂
          j₁ j₂ j₃ j₄ i<j₁ j₁≤j u₁ v₁ i<j₄ j₄≤k' u₄ v₄ j₁≡j₂ tail₁ j₃≡j₄ tail₂ j₂≡j₃
          ( cong proj₁ eq₁ ) ( cong proj₁ eq₄ )
  -- *-tail / *-cons-nil : min-s₂ = ⊨[] ( k' ≡ i ) ⇒ *-cons-nil :
  ... | *-tail .i .j₁ .j₂ .j .k .i<j₁ .j₁≤j .i<j₂ .j₂≤k .u₁ .v₁ .u₂ .v₂ j₁≡j₂ tail₁
      | *-cons-nil .i .j₃ .k .i<j₃ .j₃≤k .u₃ .v₃ =
    star i j k' t₁ s₂
      ( subst₂ ( λ x y → r ∣ nε ∣ loc ∣ w ∣ i ∣ j ∣ k' ⊢⋆ x < y )
          ( sym ( cong proj₁ eq₁ ) ) ( sym ( cong proj₁ eq₄ ) )
          ( *-cons-nil i j₁ j i<j₁ j₁≤j u₁ v₁ ) )

  {-# TERMINATING #-}
  ⊢<-trans : ( q : RE ) ( w : List Char ) ( i j k k' : ℕ )
    → q ∣ w ∣ i ⊢ j < k
    → q ∣ w ∣ i ⊢ k < k'
    → q ∣ w ∣ i ⊢ j < k'
  ⊢<-trans ε w i j k k' () ()
  ⊢<-trans ( $ c ` loc ) w i j k k' () ()
  ⊢<-trans ( l + r ` loc ) w i j k k'
    ( choice i j k t₁ t₂ ev ) ( choice i k k' s₁ s₂ ev' ) =
    ⊢<-trans-+ l r loc w i j k k' t₁ t₂ s₁ s₂ ev ev'
  ⊢<-trans ( l ● r ` loc ) w i j k k'
    ( seq _ _ _ t₁ t₂ P ) ( seq _ _ _ s₁ s₂ P' ) =
    ⊢<-trans-● l r loc w i j k k' t₁ t₂ s₁ s₂ P P'
  ⊢<-trans ( r * nε ` loc ) w i j k k'
    ( star _ _ _ t₁ t₂ P ) ( star _ _ _ s₁ s₂ P' ) =
    ⊢<-trans-⋆ r nε loc w i j k k' t₁ t₂ s₁ s₂ P P'



  -- Purpose : the greedy witness does not depend on the match evidence :
  --           + is decided by the closed ⊨? , ● / * by find-<-Min● /
  --           find-<-Min* ( evidence independent by canonicity ) .
  -- Used in : go ( + / ● / * cases : bridging the ⊨? or ⊢-t₁ match to the
  --           canonical payload ) .
  -- Idea    : structural on the regex ( the + / no branch only ) ;
  --           ● / * by find-<-Min●-canon / find-<-Min*-canon .
  greedyU-indep : ( l : RE ) ( i j : ℕ ) ( w : List Char )
    → ( t t' : l , i , j ⊨ w )
    → greedyU l i j w t ≡ greedyU l i j w t'
  greedyU-indep ε i j w t t' with t | t'
  ... | ( ⊨ε _ _ ) | ( ⊨ε _ _ ) = refl
  greedyU-indep ( $ c ` loc ) i j w t t' with t | t'
  ... | ( ⊨$ _ _ _ _ _ ) | ( ⊨$ _ _ _ _ _ ) = refl
  greedyU-indep ( l₁ + l₂ ` loc ) i j w t t' with ⊨? l₁ i j w
  ... | yes a = refl
  ... | no ¬a with t | t'
  ... | ( ⊨inr _ _ _ _ _ _ b₀ ) | ( ⊨inr _ _ _ _ _ _ b₀' ) = cong RightU ( greedyU-indep l₂ i j w b₀ b₀' )
  ... | ( ⊨inr _ _ _ _ _ _ _ ) | ( ⊨inl _ _ _ _ _ _ a₀' ) = ⊥-elim ( ¬a a₀' )
  ... | ( ⊨inl _ _ _ _ _ _ a₀ ) | _ = ⊥-elim ( ¬a a₀ )
  greedyU-indep ( l₁ ● l₂ ` loc ) i j w t t'
    with find-<-Min● l₁ l₂ loc w i j t
       | find-<-Min● l₁ l₂ loc w i j t'
  ... | ( ⊨● _ _ _ _ .j w s₁ _ _ a₁ b₁ , ev₁₀ )
     | ( ⊨● _ _ _ _ .j w s₁' _ _ a₁' b₁' , ev₂₀ )
    with trichotomy l₁ w i s₁ s₁' a₁ a₁'
  ... | inj₂ ( inj₁ s₁≡s₁' )
    rewrite s₁≡s₁' | sym s₁≡s₁' =
    cong₂ PairU ( greedyU-indep l₁ i s₁ w a₁ a₁' )
               ( greedyU-indep l₂ s₁ j w b₁ b₁' )
  ... | inj₁ s₁'<s₁ =
    ⊥-elim ( <-Min●-¬ex ev₁₀ ( s₁' , a₁' , b₁' , s₁'<s₁ ) )
  ... | inj₂ ( inj₂ s₁<s₁' ) =
    ⊥-elim ( <-Min●-¬ex ev₂₀ ( s₁ , a₁ , b₁ , s₁<s₁' ) )
  greedyU-indep ( r * nε ` loc ) i j w t t'
    = cong ( ListU { r } { nε } { loc } )
        ( cong ( greedyList r nε loc i j w )
              ( find-<-Min*-canon r nε loc w i j t t' ) )

  -- Purpose : the <-Min● evidence of a ⊨● canonical form carries its
  --           ¬ex side condition ( no smaller l-split matches ) .
  -- Used in : greedyU-indep ( ● case : uniqueness of the canonical split ) ,
  --           ⊢-strict ( ● case : the seq₁ refutation ) .
  -- Idea    : read the ¬ex field of <-min-● .
  <-Min●-¬ex : ∀ { l r : RE } { loc : ℕ } { w : List Char }
    { i j s : ℕ } { a : l , i , s ⊨ w } { b : r , s , j ⊨ w }
    → ( e : <-Min● l r loc w i j ( ⊨● l r loc i j w s (rij⊨w→i≤j a) (rij⊨w→i≤j b) a b ) )
    → ¬ ( ∃[ s' ] ( l , i , s' ⊨ w ) × ( r , s' , j ⊨ w ) × ( l ∣ w ∣ i ⊢ s' < s ) )
  <-Min●-¬ex ( <-min-● _ _ _ _ _ _ _ _ _ _ _ ¬ex ) = ¬ex


  -- Purpose : for a parse at span ( i , k ) whose flat is the prefix w₁ of
  --           drop i w , the tail w₂ is drop k w ; returns the length /
  --           tail side conditions re-stated for the parse flat a .
  -- Used in : go ( + case ) , greedy-max ( + case ) .
  -- Idea    : prefix→take + take++drop≡id + ++-cancelˡ + drop-drop .
  w₂→dropk : ( w : List Char ) ( i k : ℕ )
    → ( w₁ w₂ a : List Char )
    → ( fa : a ≡ w₁ )
    → ( fl : length w₁ ≡ k ∸ i )
    → ( fw : w₁ ++ w₂ ≡ drop i w )
    → ( i≤k : i Nat.≤ k )
    → ( length a ≡ k ∸ i ) × ( a ++ drop k w ≡ drop i w )
  w₂→dropk w i k w₁ w₂ a fa fl fw i≤k = fl-a , fw-a
    where
      -- w₁ ≡ take ( k ∸ i ) ( drop i w ) .
      w₁≡take : w₁ ≡ take ( k ∸ i ) ( drop i w )
      w₁≡take = prefix→take w₁ w₂ ( drop i w ) ( k ∸ i ) fw fl

      -- take ( k ∸ i ) ( drop i w ) ++ drop ( k ∸ i ) ( drop i w )
      -- ≡ take ( k ∸ i ) ( drop i w ) ++ w₂ .
      cancel-prem : take ( k ∸ i ) ( drop i w ) ++ drop ( k ∸ i ) ( drop i w )
                  ≡
                  take ( k ∸ i ) ( drop i w ) ++ w₂
      cancel-prem =
        begin
          take ( k ∸ i ) ( drop i w ) ++ drop ( k ∸ i ) ( drop i w )
        ≡⟨ take++drop≡id ( k ∸ i ) ( drop i w ) ⟩
          drop i w
        ≡⟨ sym fw ⟩
          w₁ ++ w₂
        ≡⟨ sym ( cong ( λ xs → xs ++ w₂ ) ( sym w₁≡take ) ) ⟩
          take ( k ∸ i ) ( drop i w ) ++ w₂
        ∎

      -- w₂ ≡ drop ( k ∸ i ) ( drop i w ) .
      w₂≡drop : w₂ ≡ drop ( k ∸ i ) ( drop i w )
      w₂≡drop =
        ++-cancelˡ ( take ( k ∸ i ) ( drop i w ) )
                   w₂
                   ( drop ( k ∸ i ) ( drop i w ) )
                   ( sym cancel-prem )

      -- w₂ ≡ drop k w .
      -- drop-drop : drop ( k ∸ i ) ( drop i w ) ≡ drop ( i + ( k ∸ i ) ) w .
      w₂≡dropk : w₂ ≡ drop k w
      w₂≡dropk =
        trans w₂≡drop
          ( trans ( drop-drop i ( k ∸ i ) w )
                ( cong ( λ n → drop n w ) ( m+[n∸m]≡n i≤k ) ) )

      -- length a ≡ k ∸ i .
      fl-a : length a ≡ k ∸ i
      fl-a = trans ( cong length fa ) fl

      -- a ++ drop k w ≡ drop i w .
      fw-a : a ++ drop k w ≡ drop i w
      fw-a =
        begin
          a ++ drop k w
        ≡⟨ cong ( λ xs → xs ++ drop k w ) fa ⟩
          w₁ ++ drop k w
        ≡⟨ cong ( w₁ ++_ ) ( sym w₂≡dropk ) ⟩
          w₁ ++ w₂
        ≡⟨ fw ⟩
          drop i w
        ∎


  -- Purpose : a positive number is not ≤ 0 .
  -- Used in : take-inj ( the empty-list clauses ) .
  -- Idea    : no constructor of ≤ builds suc n ≤ 0 .
  ¬suc≤0 : ( n : ℕ ) → ¬ ( suc n ≤ zero )
  ¬suc≤0 _ ()


  -- Purpose : take 0 is [] , but a positive take of a non-empty list is
  --           non-empty : the two are unequal .
  -- Used in : take-inj ( the non-empty zero clauses ) .
  -- Idea    : with on p : both sides reduce to clashing list constructors .
  ¬take0-takepos : ( x : Char ) ( xs : List Char ) ( n : ℕ )
    → ( p : take 0 ( x ∷ xs ) ≡ take ( suc n ) ( x ∷ xs ) ) → ⊥
  ¬take0-takepos x xs n p with p
  ... | ()


  -- Purpose : two prefixes of the same word of length ≤ |word| are equal
  --           only if their lengths agree .
  -- Used in : go ( * case : the *-head equal-head refutation ) .
  -- Idea    : induction on the word .
  take-inj : ( xs : List Char ) ( a b : ℕ )
    → a ≤ length xs → b ≤ length xs
    → take a xs ≡ take b xs → a ≡ b
  take-inj [] zero zero _ _ _ = refl
  take-inj [] zero ( suc _ ) _ b≤ _ = ⊥-elim ( ¬suc≤0 _ b≤ )
  take-inj [] ( suc _ ) _ a≤ _ _ = ⊥-elim ( ¬suc≤0 _ a≤ )
  take-inj ( _ ∷ xs ) zero zero _ _ _ = refl
  take-inj ( _ ∷ xs ) zero ( suc b' ) _ b≤ p = ⊥-elim ( ¬take0-takepos _ xs b' p )
  take-inj ( _ ∷ xs ) ( suc a' ) zero a≤ _ p = ⊥-elim ( ¬take0-takepos _ xs a' ( sym p ) )
  take-inj ( _ ∷ xs ) ( suc a' ) ( suc b' ) a≤ b≤ p
    = cong suc ( take-inj xs a' b' ( ≤-pred a≤ ) ( ≤-pred b≤ )
                 ( proj₂ ( ∷-injective p ) ) )


  -- Purpose : a take within the word length keeps its full length .
  -- Used in : <-greedy-sound-go ( the length side condition of the witness ) .
  -- Idea    : induction on n .
  take≤length : ( xs : List Char ) ( n : ℕ )
    → n ≤ length xs → length (take n xs) ≡ n
  take≤length _ zero _ = refl
  take≤length [] ( suc n ) ()
  take≤length ( _ ∷ xs ) ( suc n ) ( s≤s n≤len ) =
    cong suc ( take≤length xs n n≤len )


  -- Purpose : the end of a non-degenerate match span lies within the word
  --           ( the degenerate ⊨[] span ( i , i ) carries no bound ) .
  -- Used in : go ( * case : the take-inj bounds of the *-head refutation ) ,
  --           <-greedy-sound-go ( the length side condition ) .
  -- Idea    : induction on the match evidence ; the $ case on the start .
  {-# TERMINATING #-}
  match→end≤len : ( r : RE ) ( i j : ℕ ) ( w : List Char )
    → ( i Nat.< j ) → ( r , i , j ⊨ w ) → j ≤ length w
  match→end≤len ε i j w i<j ( ⊨ε _ _ ) = ⊥-elim ( <-irrefl refl i<j )
  match→end≤len ( $ c ` loc ) i ( suc i ) [] i<sucI ( ⊨$ _ _ .i [] p ) with p
  ... | ()
  match→end≤len ( $ c ` loc ) i ( suc i ) ( x ∷ ws ) i<sucI ( ⊨$ _ _ .i ( x ∷ ws ) p ) with i
  ... | zero = +-monoʳ-≤ 1 z≤n
  ... | ( suc i' ) with i<sucI
  ... | ( s≤s i'<sucI' ) = +-monoʳ-≤ 1 ( match→end≤len ( $ c ` loc ) i' ( suc i' ) ws i'<sucI' ( ⊨$ c loc i' ws p ) )
  match→end≤len ( l₁ + l₂ ` loc ) i j w i<j ( ⊨inl _ _ _ _ _ _ t₁ ) =
    match→end≤len l₁ i j w i<j t₁
  match→end≤len ( l₁ + l₂ ` loc ) i j w i<j ( ⊨inr _ _ _ _ _ _ t₁ ) =
    match→end≤len l₂ i j w i<j t₁
  match→end≤len ( l₁ ● l₂ ` loc ) i j w i<j ( ⊨● _ _ _ _ .j w s _ _ t₁ t₂ )
    with m≤n⇒m<n∨m≡n ( rij⊨w→i≤j t₂ )
  ... | inj₁ s<j = match→end≤len l₂ s j w s<j t₂
  ... | inj₂ s≡j = match→end≤len l₁ i j w i<j
                   ( subst ( λ x → l₁ , i , x ⊨ w ) s≡j t₁ )
  match→end≤len ( r * nε ` loc ) i j w i<j ( ⊨[] _ _ _ _ _ ) =
    ⊥-elim ( <-irrefl refl i<j )
  match→end≤len ( r * nε ` loc ) i j w i<j ( ⊨∷ _ _ _ _ _ _ ( s , i<s , s≤j , t₁ , t₂ ) )
    with m≤n⇒m<n∨m≡n s≤j
  ... | inj₁ s<j = match→end≤len ( r * nε ` loc ) s j w s<j t₂
  ... | inj₂ s≡j = subst ( λ x → x ≤ length w ) s≡j
                   ( match→end≤len r i s w i<s t₁ )


  -- Purpose : the base order is strict : no match is below itself .
  -- Used in : go ( * case : the *-head / *-tail equal-head refutations ) .
  -- Idea    : structural on the regex ; the * case descends on the span
  --           ( the tail start strictly increases along *-tail ) .
  {-# TERMINATING #-}
  ⊢-strict : ( q : RE ) ( w : List Char ) ( i j : ℕ )
    → ( q ∣ w ∣ i ⊢ j < j ) → ⊥
  ⊢-strict ε w i j ()
  ⊢-strict ( $ c ` loc ) w i j ()
  ⊢-strict ( l + r ` loc ) w i j p with p
  ... | ( choice i .j .j t₁ t₂ ev ) = ⊢-strict⁺ l r loc w i j t₁ t₂ ev
  ⊢-strict ( l ● r ` loc ) w i j p with p
  ... | ( seq i .j .j t₁ t₂ P )
    with find-<-Min● l r loc w i j t₁
       | find-<-Min● l r loc w i j t₂
  ... | ( ⊨● _ _ _ _ .j w s₁ _ _ a₁ b₁ , ev₁₀ )
     | ( ⊨● _ _ _ _ .j w s₂ _ _ a₂ b₂ , ev₂₀ )
    with P
  ... | ( seq₂ _ s₁ s₂ .j .j a₁ b₁ a₂ b₂ _ ord' ) = ⊢-strict r w s₁ j ord'
  ... | ( seq₁ _ s₁ .j s₂ .j a₁ b₁ a₂ b₂ ord ) =
    ⊥-elim ( <-Min●-¬ex ev₂₀ ( s₁ , a₁ , b₁ , ord ) )
  ⊢-strict ( r * nε ` loc ) w i j p with p
  ... | ( star i j j t₁ t₂ P )
    with m≤n⇒m<n∨m≡n ( rij⊨w→i≤j t₁ )
  ... | inj₁ _ = ⊢-strict⋆-suc r nε loc w i j t₁ t₂ P
  ... | inj₂ i≡j = ⊢-strict⋆-zero r nε loc w i j t₁ t₂ P i≡j

  -- Purpose : the degenerate span of ⊢-strict ( * case ) : with i ≡ j the
  --           head split s of ⊨∷ ( i , j , … ) would satisfy i < s ≤ i .
  -- Used in : ⊢-strict ( * case ) .
  -- Idea    : ⊨[] head : no ⊢⋆ constructor has a ⊨[] left-hand side ;
  --           ⊨∷ head : i < s ≤ i .
  ⊢-strict⋆-zero : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char )
    ( i j : ℕ ) → ( t₁ t₂ : r * nε ` loc , i , j ⊨ w )
    → ( P : r ∣ nε ∣ loc ∣ w ∣ i ∣ j ∣ j ⊢⋆
           ( proj₁ ( find-<-Min* r nε loc w i j t₁ ) )
           < ( proj₁ ( find-<-Min* r nε loc w i j t₂ ) ) )
    → ( i≡j : i ≡ j ) → ⊥
  ⊢-strict⋆-zero r nε loc w i j ( ⊨[] _ _ _ _ _ ) t₂ P i≡j with P
  ... | ()
  ⊢-strict⋆-zero r nε loc w i j ( ⊨∷ _ _ _ _ _ _ ( s , i<s , s≤j , _ , _ ) ) t₂ P i≡j =
    ⊥-elim ( <-irrefl i≡j ( ≤-trans i<s s≤j ) )

  -- Purpose : the non-degenerate span of ⊢-strict ( * case ) : the
  --           canonical head of ( i , j ) is unique ( *-head ) and the tail
  --           start strictly increases ( *-tail ) .
  -- Used in : ⊢-strict ( * case ) .
  -- Idea    : ⊨[] head : no ⊢⋆ constructor has a ⊨[] left-hand side ;
  --           *-head contradicts the ¬ex side condition of the minimal
  --           ⊨∷ ( <-min-∷ ) ; *-tail by the strict span .
  ⊢-strict⋆-suc : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char )
    ( i j : ℕ ) → ( t₁ t₂ : r * nε ` loc , i , j ⊨ w )
    → ( P : r ∣ nε ∣ loc ∣ w ∣ i ∣ j ∣ j ⊢⋆
           ( proj₁ ( find-<-Min* r nε loc w i j t₁ ) )
           < ( proj₁ ( find-<-Min* r nε loc w i j t₂ ) ) )
    → ⊥
  ⊢-strict⋆-suc r nε loc w i j t₁ t₂ P
    with find-<-Min* r nε loc w i j t₁
       | find-<-Min* r nε loc w i j t₂
  ... | ( min-t₁ , _ ) | ( min-t₂ , ev₂₀ )
    with min-t₁
  ... | ( ⊨[] _ _ _ _ _ )
    = ⊥-elim ( ¬⊢⋆-[]-∷ min-t₂ P )
  ... | ( ⊨∷ _ _ _ _ _ _ ( s₁ , i<s₁ , s₁≤j , h₁ , t₁t ) ) with min-t₂
  ... | ( ⊨[] _ _ _ _ _ ) = ⊥-elim ( <-irrefl refl ( ≤-trans i<s₁ s₁≤j ) )
  ... | ( ⊨∷ _ _ _ _ _ _ ( s₂ , i<s₂ , s₂≤j , h₂ , t₂t ) ) with P
  ... | ( *-tail i s₁ s₂ j j i<s₁ s₁≤j i<s₂ s₂≤j h₁ t₁t h₂ t₂t _ ord' )
    = ⊢-strict ( r * nε ` loc ) w s₁ j ord'
  ... | ( *-head i s₁ s₂ j j i<s₁ s₁≤j i<s₂ s₂≤j h₁ t₁t h₂ t₂t ord )
    with ev₂₀
  ... | ( <-min-∷ _ _ _ _ _ _ _ _ _ _ _ _ ¬ex₂ ) =
    ⊥-elim ( ¬ex₂ ( s₁ , i<s₁ , s₁≤j , h₁ , t₁t , ord ) )

  -- Purpose : the + case of ⊢-strict : ⊨? decides the canonical shape of
  --           Min⁺ ( Min⁺-inl / Min⁺-inr ) ; ev is transported onto that
  --           shape , where only inlinl / inrinr remain , each carrying the
  --           strict l / r base order .
  -- Used in : ⊢-strict ( + case ) .
  -- Idea    : ⊨? = yes : both canonical forms are ⊨inl ( Min⁺-inl ) ;
  --           ⊨? = no : both canonical forms are ⊨inr ( Min⁺-inr ) .
  ⊢-strict⁺ : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    → ( t₁ t₂ : l + r ` loc , i , j ⊨ w )
    → ( ev : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j ⊢⁺
           ( Min⁺ l r loc w i j t₁ ) < ( Min⁺ l r loc w i j t₂ ) )
    → ⊥
  ⊢-strict⁺ l r loc w i j t₁ t₂ ev with ⊨? l i j w
  ... | yes a = ⊢-strict⁺-yes l r loc w i j a t₁ t₂ ev
  ... | no ¬a
    = let e₁ = Min⁺-inr l r loc w i j ¬a t₁
          e₂ = Min⁺-inr l r loc w i j ¬a t₂
      in
      ⊢-strict⁺-inrinrinr l r loc w i j ( proj₁ e₁ ) ( proj₁ e₂ )
        ( subst₂ ( λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j ⊢⁺ x < y )
                 ( proj₂ e₁ ) ( proj₂ e₂ ) ev )

  -- ⊨? = yes : transport ev onto the canonical ⊨inl shape ( Min⁺-inl ) .
  ⊢-strict⁺-yes : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    ( a : l , i , j ⊨ w )
    ( t₁ t₂ : l + r ` loc , i , j ⊨ w )
    ( ev : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j ⊢⁺
            ( Min⁺ l r loc w i j t₁ ) < ( Min⁺ l r loc w i j t₂ ) )
    → ⊥
  ⊢-strict⁺-yes l r loc w i j a t₁ t₂ ev =
    let e₁ = Min⁺-inl l r loc w i j a t₁
        e₂ = Min⁺-inl l r loc w i j a t₂
    in
    ⊢-strict⁺-inlinlinl l r loc w i j ( proj₁ e₁ ) ( proj₁ e₂ )
      ( subst₂ ( λ x y → l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j ⊢⁺ x < y )
               ( proj₂ e₁ )
               ( proj₂ e₂ )
               ev )

  -- canonical shape inl / inl : only inlinl , with the strict l order .
  ⊢-strict⁺-inlinlinl : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    ( a₁ a₂ : l , i , j ⊨ w )
    ( ev : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j ⊢⁺
            ( ⊨inl l r loc i j w a₁ ) < ( ⊨inl l r loc i j w a₂ ) )
    → ⊥
  ⊢-strict⁺-inlinlinl l r loc w i j a₁ a₂ ev with ev
  ... | ( inlinl _ _ _ _ _ ord ) = ⊢-strict l w i j ord

  -- canonical shape inr / inr : only inrinr , with the strict r order .
  ⊢-strict⁺-inrinrinr : ( l r : RE ) ( loc : ℕ ) ( w : List Char ) ( i j : ℕ )
    ( b₁ b₂ : r , i , j ⊨ w )
    → ( ev : l ∣ r ∣ loc ∣ w ∣ i ∣ j ∣ j ⊢⁺
           ( ⊨inr l r loc i j w b₁ ) < ( ⊨inr l r loc i j w b₂ ) )
    → ⊥
  ⊢-strict⁺-inrinrinr l r loc w i j b₁ b₂ ev with ev
  ... | ( inrinr _ _ _ _ _ ord ) = ⊢-strict r w i j ord


  -- Purpose : the left ( smaller-span ) match carried by a base-order proof .
  -- Used in : go , greedy-max , <-greedy-sound-go ( the witness span ) .
  -- Idea    : every ⊢ constructor carries the raw matches .
  ⊢-t₁ : ( r : RE ) ( w : List Char ) ( i j k : ℕ )
    → ( r ∣ w ∣ i ⊢ j < k ) → ( r , i , j ⊨ w )
  ⊢-t₁ _ _ _ _ _ ( choice i j k t₁ _ _ ) = t₁
  ⊢-t₁ _ _ _ _ _ ( seq i j k t₁ _ _ ) = t₁
  ⊢-t₁ _ _ _ _ _ ( star i j k t₁ _ _ ) = t₁


  -- Purpose : when l₁ matches the span ( a ) , the greedy parse of the
  --           + regex is a LeftU carrying the greedy parse of a ,
  --           independent of the evidence of t .
  -- Used in : go ( + case : the LeftU bridge ) .
  -- Idea    : greedyU-indep to the Min⁺ shape , Min⁺-inl to the ⊨inl
  --           shape , then the + clause of greedyU ( the ⊨? = yes branch )
  --           with greedyU-indep on the payload .
  greedyU-+inl : ( l₁ l₂ : RE ) ( loc : ℕ ) ( i j : ℕ ) ( w : List Char )
    → ( t : ( l₁ + l₂ ` loc ) , i , j ⊨ w )
    → ( a : l₁ , i , j ⊨ w )
    → greedyU ( l₁ + l₂ ` loc ) i j w t ≡ LeftU ( greedyU l₁ i j w a )
  greedyU-+inl l₁ l₂ loc i j w t a
    = trans ( greedyU-indep ( l₁ + l₂ ` loc ) i j w
                        t ( Min⁺ l₁ l₂ loc w i j t ) )
            ( trans ( cong ( greedyU ( l₁ + l₂ ` loc ) i j w )
                          ( proj₂ ( Min⁺-inl l₁ l₂ loc w i j a t ) ) )
                    ( inlU ( proj₁ ( Min⁺-inl l₁ l₂ loc w i j a t ) )
                            a ) )
    where
      inlU : ( a' a'' : l₁ , i , j ⊨ w )
        → greedyU ( l₁ + l₂ ` loc ) i j w
                   ( ⊨inl l₁ l₂ loc i j w a' )
          ≡ LeftU ( greedyU l₁ i j w a'' )
      inlU a' a'' with ⊨? l₁ i j w
      ... | yes a₀ = cong LeftU ( greedyU-indep l₁ i j w a₀ a'' )
      ... | no ¬a₀ = ⊥-elim ( ¬a₀ a' )


  -- Purpose : the dual of greedyU-+inl : when l₁ does not match the span
  --           ( ¬a ) , the greedy parse of the + regex is a RightU
  --           carrying the greedy parse of the l₂ match b .
  -- Used in : go ( + case : the RightU bridge ) .
  -- Idea    : greedyU-indep to the Min⁺ shape , Min⁺-inr to the ⊨inr
  --           shape , then the + clause of greedyU ( the ⊨? = no branch )
  --           with greedyU-indep on the payload .
  greedyU-+inr : ( l₁ l₂ : RE ) ( loc : ℕ ) ( i j : ℕ ) ( w : List Char )
    → ( t : ( l₁ + l₂ ` loc ) , i , j ⊨ w )
    → ( b : l₂ , i , j ⊨ w )
    → ( ¬a : ¬ ( l₁ , i , j ⊨ w ) )
    → greedyU ( l₁ + l₂ ` loc ) i j w t ≡ RightU ( greedyU l₂ i j w b )
  greedyU-+inr l₁ l₂ loc i j w t b ¬a
    = trans ( greedyU-indep ( l₁ + l₂ ` loc ) i j w
                        t ( Min⁺ l₁ l₂ loc w i j t ) )
            ( trans ( cong ( greedyU ( l₁ + l₂ ` loc ) i j w )
                          ( proj₂ ( Min⁺-inr l₁ l₂ loc w i j ¬a t ) ) )
                    ( inrU ( proj₁ ( Min⁺-inr l₁ l₂ loc w i j ¬a t ) )
                            b ) )
    where
      inrU : ( b' b'' : l₂ , i , j ⊨ w )
        → greedyU ( l₁ + l₂ ` loc ) i j w
                   ( ⊨inr l₁ l₂ loc i j w b' )
          ≡ RightU ( greedyU l₂ i j w b'' )
      inrU b' b'' with ⊨? l₁ i j w
      ... | yes a₀ = ⊥-elim ( ¬a a₀ )
      ... | no ¬a₀ = cong RightU ( greedyU-indep l₂ i j w b' b'' )


  -- Purpose : the greedy head list of a * match : greedyList on the
  --           find-<-Min* canonical evidence .
  -- Used in : go ( * case : the *-tail branch ) .
  -- Idea    : one line ; the canonical evidence re-canonicalizes the tail
  --           at every step ( see greedyList ) .
  greedyList-max : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( w : List Char )
    → ( i k : ℕ )
    → ( t : r * nε ` loc , i , k ⊨ w )
    → List ( U r )
  greedyList-max r nε loc w i k t
    = greedyList r nε loc i k w
        ( proj₁ ( find-<-Min* r nε loc w i k t ) )


  -- Purpose : the greedy witness of the span ( i , k ) : the greedy parse
  --           of the match evidence .
  -- Used in : <-greedy-sound-go ( the right-hand greedy witness ) .
  -- Idea    : a name for clarity ; greedyU is evidence independent
  --           ( greedyU-indep ) .
  greedy-max : ( r : RE ) ( w : List Char ) ( i k : ℕ )
    → ( t : r , i , k ⊨ w ) → U r
  greedy-max r w i k t = greedyU r i k w t


  -- Purpose : transport the LEFT sub-witness of a ● split across an
  --           equality of the split position , carrying the sub-evidence
  --           via subst ( fixes the left endpoint i ) .
  -- Used in : greedyU-●-pair-transport , go ( * case : *-tail branch ,
  --           head≡ ) .
  -- Idea    : single refl clause ( path induction on the split equality ) ;
  --           in the refl case the subst is the identity , so refl .
  greedyU-●-L-transport : ( l₁ : RE ) ( i : ℕ ) ( w : List Char )
    → ( s s' : ℕ ) → ( s≡s' : s ≡ s' )
    → ( a : l₁ , i , s ⊨ w )
    → greedyU l₁ i s w a
        ≡ greedyU l₁ i s' w ( subst ( λ m → l₁ , i , m ⊨ w ) s≡s' a )
  greedyU-●-L-transport l₁ i w s s' s≡s' a with s≡s'
  ... | refl = refl


  -- Purpose : transport the RIGHT sub-witness of a ● split across an
  --           equality of the split position , carrying the sub-evidence
  --           via subst ( fixes the right endpoint k ) .
  -- Used in : greedyU-●-pair-transport .
  -- Idea    : single refl clause ( path induction on the split equality ) ;
  --           in the refl case the subst is the identity , so refl .
  greedyU-●-R-transport : ( l₂ : RE ) ( k : ℕ ) ( w : List Char )
    → ( s s' : ℕ ) → ( s≡s' : s ≡ s' )
    → ( b : l₂ , s , k ⊨ w )
    → greedyU l₂ s k w b
        ≡ greedyU l₂ s' k w ( subst ( λ m → l₂ , m , k ⊨ w ) s≡s' b )
  greedyU-●-R-transport l₂ k w s s' s≡s' b with s≡s'
  ... | refl = refl


  -- Purpose : transport the whole ● pair-witness across an equality of
  --           the split position ( s₂ ≡ s₂c ) , from the ( s₂ , a₂ , b₂ )
  --           decomposition to the ( s₂c , a₂c , b₂c ) decomposition .
  -- Used in : go ( ● case , both the seq₁ / seq₂ branches ) .
  -- Idea    : first transport each sub-witness across the split ( carrying
  --           the sub-evidence via subst ) , then swap the carried
  --           sub-evidence to the target one ( greedyU-indep ) ; the body
  --           is entirely literal ( no with , no rewrite , no
  --           with-equation reliance ) .
  greedyU-●-pair-transport : ( l₁ l₂ : RE ) ( loc : ℕ ) ( i k : ℕ ) ( w : List Char )
    → ( s₂ s₂c : ℕ )
    → ( a₂ : l₁ , i , s₂ ⊨ w ) ( b₂ : l₂ , s₂ , k ⊨ w )
    → ( a₂c : l₁ , i , s₂c ⊨ w ) ( b₂c : l₂ , s₂c , k ⊨ w )
    → ( bridge : s₂ ≡ s₂c )
    → PairU ( greedyU l₁ i s₂ w a₂ ) ( greedyU l₂ s₂ k w b₂ )
        ≡ PairU ( greedyU l₁ i s₂c w a₂c ) ( greedyU l₂ s₂c k w b₂c )
  greedyU-●-pair-transport l₁ l₂ loc i k w s₂ s₂c a₂ b₂ a₂c b₂c bridge
    = trans ( cong₂ ( λ x y → PairU x y )
              ( greedyU-●-L-transport l₁ i w s₂ s₂c bridge a₂ )
              ( greedyU-●-R-transport l₂ k w s₂ s₂c bridge b₂ ) )
            ( cong₂ ( λ x y → PairU x y )
              ( greedyU-indep l₁ i s₂c w a₂t a₂c )
              ( greedyU-indep l₂ s₂c k w b₂t b₂c ) )
    where
      a₂t : l₁ , i , s₂c ⊨ w
      a₂t = subst ( λ m → l₁ , i , m ⊨ w ) bridge a₂
      b₂t : l₂ , s₂c , k ⊨ w
      b₂t = subst ( λ m → l₂ , m , k ⊨ w ) bridge b₂


  -- Purpose : the greedy witness of a * match on the degenerate span
  --           ( i , i ) is the empty list ( only ⊨[] inhabits that span ;
  --           ⊨∷ would force i < j ≤ i ) .
  -- Used in : go ( * case : the ⊨∷ / ⊨[] branch , the RHS transport ) .
  -- Idea    : the ⊨[] clauses of greedyU / find-<-Min* / greedyList all
  --           compute , so refl ; the ⊨∷ case is empty ( <-irrefl ) .
  greedyU-⋆-[] : ( r₀ : RE ) ( nε : ε∉ r₀ ) ( loc : ℕ ) ( w : List Char )
    → ( i : ℕ ) → ( t : ( r₀ * nε ` loc ) , i , i ⊨ w )
    → greedyU ( r₀ * nε ` loc ) i i w t ≡ ListU []
  greedyU-⋆-[] r₀ nε loc w i t with t
  ... | ( ⊨[] _ _ _ _ _ ) = refl
  ... | ( ⊨∷ _ _ _ _ _ _ ( j , i<j , j≤i , _ , _ ) )
    = ⊥-elim ( <-irrefl refl ( ≤-trans i<j j≤i ) )


  -- Purpose : the greedy head list of a * match whose canonical evidence
  --           decomposes as the ⊨∷ head ( j₂ , h₂ , tl₂ ) , stated in the
  --           raw t₂₀ projection form : the cons of the greedy head parse
  --           and the re-canonicalized tail equals greedyList on the
  --           find-<-Min* canonical evidence of t₂₀ .
  -- Used in : go ( * case : the ⊨∷ / ⊨∷ branches ( *-head / *-tail ) ,
  --           RHS transport , first step ) .
  -- Idea    : greedyList's ⊨∷ clause computes on the explicit ⊨∷ shape ;
  --           min₂₀ rewrites the canonical evidence back to t₂₀'s
  --           projection ( greedyList-max unfolds ) .
  greedyU-⋆-∷-rhs : ( r₀ : RE ) ( nε : ε∉ r₀ ) ( loc : ℕ ) ( w : List Char )
    → ( i k : ℕ ) → ( t₂₀ : ( r₀ * nε ` loc ) , i , k ⊨ w )
    → ( j₂ : ℕ ) → ( i<j₂ : i Nat.< j₂ ) → ( j₂≤k : j₂ Nat.≤ k )
    → ( h₂ : r₀ , i , j₂ ⊨ w ) → ( tl₂ : r₀ * nε ` loc , j₂ , k ⊨ w )
    → ( min₂₀ : proj₁ ( find-<-Min* r₀ nε loc w i k t₂₀ )
             ≡ ⊨∷ r₀ nε loc w i k ( j₂ , i<j₂ , j₂≤k , h₂ , tl₂ ) )
    → ListU ( greedyU r₀ i j₂ w h₂
         ∷ greedyList-max r₀ nε loc w j₂ k tl₂ )
      ≡ ListU ( greedyList r₀ nε loc i k w
                    ( proj₁ ( find-<-Min* r₀ nε loc w i k t₂₀ ) ) )
  greedyU-⋆-∷-rhs r₀ nε loc w i k t₂₀ j₂ i<j₂ j₂≤k h₂ tl₂ min₂₀
    = begin
      ListU ( greedyU r₀ i j₂ w h₂
           ∷ greedyList-max r₀ nε loc w j₂ k tl₂ )
    ≡⟨⟩
      ListU ( greedyU r₀ i j₂ w h₂
           ∷ greedyList r₀ nε loc j₂ k w
                 ( proj₁ ( find-<-Min* r₀ nε loc w j₂ k tl₂ ) ) )
    ≡⟨⟩
      ListU ( greedyList r₀ nε loc i k w
                   ( ⊨∷ r₀ nε loc w i k ( j₂ , i<j₂ , j₂≤k , h₂ , tl₂ ) ) )
    ≡⟨ cong ( ListU { r₀ } { nε } { loc } )
            ( cong ( greedyList r₀ nε loc i k w ) ( sym min₂₀ ) ) ⟩
      ListU ( greedyList r₀ nε loc i k w
                   ( proj₁ ( find-<-Min* r₀ nε loc w i k t₂₀ ) ) )
    ∎


  -- Purpose : transport the greedy head list of a * match across an
  --           equality of the left span endpoint , carrying the evidence
  --           via subst ( fixes the right endpoint k ) .
  -- Used in : go ( * case : the *-tail branch , tail> ) .
  -- Idea    : single refl clause ( path induction on the span equality ) ;
  --           in the refl case the subst is the identity , so refl .
  greedyList-max-transport : ( r₀ : RE ) ( nε : ε∉ r₀ ) ( loc : ℕ )
    → ( w : List Char ) → ( k : ℕ )
    → ( s s' : ℕ ) → ( s≡s' : s ≡ s' )
    → ( t' : r₀ * nε ` loc , s' , k ⊨ w )
    → greedyList-max r₀ nε loc w s k
          ( subst ( λ m → r₀ * nε ` loc , m , k ⊨ w ) ( sym s≡s' ) t' )
      ≡ greedyList-max r₀ nε loc w s' k t'
  greedyList-max-transport r₀ nε loc w k s s' s≡s' t' with s≡s'
  ... | refl = refl


  -- Purpose : the core comparison of <-greedy-sound-go : the greedy
  --           witness of the smaller span ( i , j ) is above the greedy
  --           witness of the larger span ( i , k ) in the greedy order .
  -- Used in : <-greedy-sound-go ( the ∀ part ) .
  -- Idea    : structural on the regex and on the ⊢⁺ / ⊢● / ⊢⋆ evidence :
  --           the sub-premise of each base-order constructor is exactly
  --           the sub-premise of the matching >ᵍ constructor ( choice-ll /
  --           choice-lr / choice-rr , seq₁ / seq₂ , star-cons-nil /
  --           star-head / star-tail ) ; the mixed shapes are empty by the
  --           shapes of the base-order constructors ( inr<inl-+ ,
  --           ¬⊢⋆-[]-[] , ¬⊢⋆-[]-∷ ) .
  go : ( r : RE ) ( w : List Char ) ( i j k : ℕ )
    → ( p : r ∣ w ∣ i ⊢ j < k )
    → ( t₂ : r , i , k ⊨ w )
    → r ⊢ ( greedyU r i j w ( ⊢-t₁ r w i j k p ) )
        >ᵍ ( greedyU r i k w t₂ )
  go ε w i j k () t₂
  go ( $ c ` loc ) w i j k () t₂
  go ( l₁ + l₂ ` loc ) w i j k ( choice i j k t₁ t₂₀ ev⁺ ) t₂
    with find-<-Min⁺ l₁ l₂ loc w i j t₁
       | find-<-Min⁺ l₁ l₂ loc w i k t₂₀
  ... | ( min-t₁ , ev₁₀ ) | ( min-t₂₀ , ev₂₀ )
    with min-t₁ | min-t₂₀
  ... | ( ⊨inl _ _ _ _ _ _ a₁ ) | ( ⊨inl _ _ _ _ _ _ a₂ )
    = subst₂ ( λ u v → ( l₁ + l₂ ` loc ) ⊢ u >ᵍ v )
        ( sym ( greedyU-+inl l₁ l₂ loc i j w t₁ a₁ ) )
        ( sym ( greedyU-+inl l₁ l₂ loc i k w t₂ a₂ ) )
        ( GreedyOrder.sub
            ( GreedyOrder.choice-ll ll-prem ) )
    where
      p₁' : l₁ ∣ w ∣ i ⊢ j < k
      p₁' = ⊢⁺-inlinl-go l₁ l₂ loc w i j k a₁ a₂ ev⁺
      ll-prem : l₁ ⊢ ( greedyU l₁ i j w a₁ )
                >ᵍ ( greedyU l₁ i k w a₂ )
      ll-prem rewrite sym ( greedyU-indep l₁ i j w
                                ( ⊢-t₁ l₁ w i j k p₁' ) a₁ )
        = go l₁ w i j k p₁' a₂
  ... | ( ⊨inl _ _ _ _ _ _ a₁ ) | ( ⊨inr _ _ _ _ _ _ b₂ )
    = subst₂ ( λ u v → ( l₁ + l₂ ` loc ) ⊢ u >ᵍ v )
        ( sym ( greedyU-+inl l₁ l₂ loc i j w t₁ a₁ ) )
        ( sym ( greedyU-+inr l₁ l₂ loc i k w t₂ b₂
                           ( <-Min⁺-inr¬ ev₂₀ ) ) )
        ( GreedyOrder.sub ( GreedyOrder.choice-lr ) )
  ... | ( ⊨inr _ _ _ _ _ _ b₁ ) | ( ⊨inl _ _ _ _ _ _ a₂ )
    = ⊥-elim ( inr<inl-+ l₁ l₂ loc w i j k b₁ a₂ ev⁺ )
  ... | ( ⊨inr _ _ _ _ _ _ b₁ ) | ( ⊨inr _ _ _ _ _ _ b₂ )
    = subst₂ ( λ u v → ( l₁ + l₂ ` loc ) ⊢ u >ᵍ v )
        ( sym ( greedyU-+inr l₁ l₂ loc i j w t₁ b₁
                           ( <-Min⁺-inr¬ ev₁₀ ) ) )
        ( sym ( greedyU-+inr l₁ l₂ loc i k w t₂ b₂
                           ( <-Min⁺-inr¬ ev₂₀ ) ) )
        ( GreedyOrder.sub
            ( GreedyOrder.choice-rr rr-prem ) )
    where
      p₂ : l₂ ∣ w ∣ i ⊢ j < k
      p₂ = ⊢⁺-inrinr-go l₁ l₂ loc w i j k b₁ b₂ ev⁺
      rr-prem : l₂ ⊢ ( greedyU l₂ i j w b₁ )
                >ᵍ ( greedyU l₂ i k w b₂ )
      rr-prem rewrite sym ( greedyU-indep l₂ i j w
                                ( ⊢-t₁ l₂ w i j k p₂ ) b₁ )
        = go l₂ w i j k p₂ b₂
  go ( l₁ ● l₂ ` loc ) w i j k ( seq i j k t₁ t₂₀ ev● ) t₂
    with find-<-Min● l₁ l₂ loc w i j t₁
       | find-<-Min● l₁ l₂ loc w i k t₂₀ | inspect ( find-<-Min● l₁ l₂ loc w i k ) t₂₀
       | find-<-Min● l₁ l₂ loc w i k t₂ | inspect ( find-<-Min● l₁ l₂ loc w i k ) t₂
  ... | ( min-t₁ , _ ) | ( min-t₂₀ , _ ) | [ eq₂₀ ]
      | ( min-t₂c , _ ) | [ eq₂ ]
    with min-t₁ | min-t₂₀ | min-t₂c
  ... | ( ⊨● _ _ _ _ _ _ s₁ _ _ a₁ b₁ )
      | ( ⊨● _ _ _ _ _ _ s₂ _ _ a₂ b₂ )
      | ( ⊨● _ _ _ _ _ _ s₂c _ _ a₂c b₂c )
    with ev●
  ... | ( seq₁ .i .s₁ .j .s₂ .k .a₁ .b₁ .a₂ .b₂ prem₁ )
    = let s₂≡s₂c = cong ⊨●-split
                ( trans ( sym ( cong proj₁ eq₂₀ ) )
                    ( trans ( find-<-Min●-canon l₁ l₂ loc w i k t₂₀ t₂ )
                            ( cong proj₁ eq₂ ) ) )
      in  subst ( λ v → ( l₁ ● l₂ ` loc ) ⊢
                  PairU ( greedyU l₁ i s₁ w a₁ ) ( greedyU l₂ s₁ j w b₁ ) >ᵍ v )
            ( greedyU-●-pair-transport l₁ l₂ loc i k w s₂ s₂c a₂ b₂
                a₂c b₂c s₂≡s₂c )
            ( GreedyOrder.sub
                ( GreedyOrder.seq₁ seq₁-prem ) )
    where
      seq₁-prem : l₁ ⊢ ( greedyU l₁ i s₁ w a₁ )
                  >ᵍ ( greedyU l₁ i s₂ w a₂ )
      seq₁-prem rewrite sym ( greedyU-indep l₁ i s₁ w
                                  ( ⊢-t₁ l₁ w i s₁ s₂ prem₁ ) a₁ )
        = go l₁ w i s₁ s₂ prem₁ a₂
  ... | ( seq₂ .i .s₁ .s₂ .j .k .a₁ .b₁ .a₂ .b₂ s₁≡s₂ p₂ )
    = let s₂≡s₂c = cong ⊨●-split
                ( trans ( sym ( cong proj₁ eq₂₀ ) )
                    ( trans ( find-<-Min●-canon l₁ l₂ loc w i k t₂₀ t₂ )
                            ( cong proj₁ eq₂ ) ) )
      in  subst ( λ v → ( l₁ ● l₂ ` loc ) ⊢
                  PairU ( greedyU l₁ i s₁ w a₁ ) ( greedyU l₂ s₁ j w b₁ ) >ᵍ v )
            ( greedyU-●-pair-transport l₁ l₂ loc i k w s₂ s₂c a₂ b₂
                a₂c b₂c s₂≡s₂c )
            ( GreedyOrder.sub
                ( GreedyOrder.seq₂ head≡ seq₂-prem ) )
    where
      a₁t : l₁ , i , s₂ ⊨ w
      a₁t = subst ( λ m → l₁ , i , m ⊨ w ) s₁≡s₂ a₁
      b₂t : l₂ , s₁ , k ⊨ w
      b₂t = subst ( λ m → l₂ , m , k ⊨ w ) ( sym s₁≡s₂ ) b₂
      head≡ : greedyU l₁ i s₁ w a₁ ≡ greedyU l₁ i s₂ w a₂
      head≡
        = trans ( greedyU-●-L-transport l₁ i w s₁ s₂ s₁≡s₂ a₁ )
                ( greedyU-indep l₁ i s₂ w a₁t a₂ )
      go-rewrite : l₂ ⊢ ( greedyU l₂ s₁ j w b₁ )
                   >ᵍ ( greedyU l₂ s₁ k w b₂t )
      go-rewrite rewrite sym ( greedyU-indep l₂ s₁ j w
                                   ( ⊢-t₁ l₂ w s₁ j k p₂ ) b₁ )
        = go l₂ w s₁ j k p₂ b₂t
      seq₂-prem : l₂ ⊢ ( greedyU l₂ s₁ j w b₁ )
                   >ᵍ ( greedyU l₂ s₂ k w b₂ )
      seq₂-prem
        = subst ( λ v → l₂ ⊢ ( greedyU l₂ s₁ j w b₁ ) >ᵍ v )
            ( sym ( greedyU-●-R-transport l₂ k w s₂ s₁
                    ( sym s₁≡s₂ ) b₂ ) )
            go-rewrite
  go ( r₀ * nε ` loc ) w i j k ( star i j k t₁ t₂₀ ev⋆ ) t₂
    with find-<-Min* r₀ nε loc w i j t₁ | inspect ( find-<-Min* r₀ nε loc w i j ) t₁
       | find-<-Min* r₀ nε loc w i k t₂₀ | inspect ( find-<-Min* r₀ nε loc w i k ) t₂₀
       | find-<-Min* r₀ nε loc w i k t₂ | inspect ( find-<-Min* r₀ nε loc w i k ) t₂
  ... | ( min-t₁ , _ ) | [ eq₁₀ ]
      | ( min-t₂₀ , _ ) | [ eq₂₀ ]
      | ( min-t₂c , _ ) | [ eq₂ ]
    with min-t₁ | min-t₂₀
  ... | ( ⊨[] _ _ _ _ _ ) | ( ⊨[] _ _ _ _ _ )
    = ⊥-elim ( ¬⊢⋆-[]-[] ev⋆ )
  ... | ( ⊨[] _ _ _ _ _ ) | ( ⊨∷ _ _ _ _ _ _ m₂₀ )
    = ⊥-elim ( ¬⊢⋆-[]-∷ ( ⊨∷ r₀ nε loc w i k m₂₀ ) ev⋆ )
  ... | ( ⊨∷ _ _ _ _ _ _ ( j₁ , i<j₁ , j₁≤j , h₁ , tl₁ ) )
    | ( ⊨[] _ _ _ _ _ )
    = let bridge = trans ( sym ( cong proj₁ eq₂₀ ) )
                       ( trans ( find-<-Min*-canon r₀ nε loc w i k
                                      t₂₀ t₂ )
                               ( cong proj₁ eq₂ ) )
      in  subst ( λ v → ( r₀ * nε ` loc ) ⊢
               ListU ( greedyU r₀ i j₁ w h₁
                    ∷ greedyList-max r₀ nε loc w j₁ j tl₁ )
               >ᵍ v )
          ( trans ( sym ( greedyU-⋆-[] r₀ nε loc w i t₂₀ ) )
                  ( cong ( ListU { r₀ } { nε } { loc } )
                         ( cong ( greedyList r₀ nε loc i k w )
                                ( trans ( cong proj₁ eq₂₀ ) bridge ) ) ) )
          ( GreedyOrder.sub ( GreedyOrder.star-cons-nil ) )
  ... | ( ⊨∷ _ _ _ _ _ _ ( j₁ , i<j₁ , j₁≤j , h₁ , tl₁ ) )
    | ( ⊨∷ _ _ _ _ _ _ ( j₂ , i<j₂ , j₂≤k , h₂ , tl₂ ) )
    with ev⋆
  ... | ( *-head .i .j₁ .j₂ .j .k _ _ _ _ _ _ _ _ prem₁ )
    = let bridge = trans ( sym ( cong proj₁ eq₂₀ ) )
                       ( trans ( find-<-Min*-canon r₀ nε loc w i k
                                      t₂₀ t₂ )
                               ( cong proj₁ eq₂ ) )
      in  subst ( λ v → ( r₀ * nε ` loc ) ⊢
               ListU ( greedyU r₀ i j₁ w h₁
                    ∷ greedyList-max r₀ nε loc w j₁ j tl₁ )
               >ᵍ v )
          ( trans ( greedyU-⋆-∷-rhs r₀ nε loc w i k t₂₀ j₂ i<j₂
                         j₂≤k h₂ tl₂ ( cong proj₁ eq₂₀ ) )
                  ( cong ( ListU { r₀ } { nε } { loc } )
                         ( cong ( greedyList r₀ nε loc i k w )
                                ( trans ( cong proj₁ eq₂₀ ) bridge ) ) ) )
          ( GreedyOrder.sub
              ( GreedyOrder.star-head head-prem ) )
    where
      head-prem : r₀ ⊢ ( greedyU r₀ i j₁ w h₁ )
                   >ᵍ ( greedyU r₀ i j₂ w h₂ )
      head-prem rewrite sym ( greedyU-indep r₀ i j₁ w
                                  ( ⊢-t₁ r₀ w i j₁ j₂ prem₁ ) h₁ )
        = go r₀ w i j₁ j₂ prem₁ h₂
  ... | ( *-tail .i .j₁ .j₂ .j .k _ _ _ _ _ _ _ _ j₁≡j₂ p₂ )
    = let bridge = trans ( sym ( cong proj₁ eq₂₀ ) )
                       ( trans ( find-<-Min*-canon r₀ nε loc w i k
                                      t₂₀ t₂ )
                               ( cong proj₁ eq₂ ) )
      in  subst ( λ v → ( r₀ * nε ` loc ) ⊢
               ListU ( greedyU r₀ i j₁ w h₁
                    ∷ greedyList-max r₀ nε loc w j₁ j tl₁ )
               >ᵍ v )
          ( trans ( greedyU-⋆-∷-rhs r₀ nε loc w i k t₂₀ j₂ i<j₂
                         j₂≤k h₂ tl₂ ( cong proj₁ eq₂₀ ) )
                  ( cong ( ListU { r₀ } { nε } { loc } )
                         ( cong ( greedyList r₀ nε loc i k w )
                                ( trans ( cong proj₁ eq₂₀ ) bridge ) ) ) )
          ( GreedyOrder.sub
              ( GreedyOrder.star-tail head≡ tail> ) )
    where
      h₁t : r₀ , i , j₂ ⊨ w
      h₁t = subst ( λ m → r₀ , i , m ⊨ w ) j₁≡j₂ h₁
      tl₂t : ( r₀ * nε ` loc ) , j₁ , k ⊨ w
      tl₂t = subst ( λ m → r₀ * nε ` loc , m , k ⊨ w )
                   ( sym j₁≡j₂ ) tl₂
      head≡ : greedyU r₀ i j₁ w h₁ ≡ greedyU r₀ i j₂ w h₂
      head≡
        = trans ( greedyU-●-L-transport r₀ i w j₁ j₂ j₁≡j₂ h₁ )
                ( greedyU-indep r₀ i j₂ w h₁t h₂ )
      go-tail : ( r₀ * nε ` loc ) ⊢
                ListU ( greedyList-max r₀ nε loc w j₁ j tl₁ )
                >ᵍ ListU ( greedyList-max r₀ nε loc w j₁ k tl₂t )
      go-tail
        = subst ( λ v → ( r₀ * nε ` loc ) ⊢
                         v >ᵍ ListU ( greedyList-max
                                          r₀ nε loc w j₁ k tl₂t ) )
            ( cong ( ListU { r₀ } { nε } { loc } )
                   ( cong ( greedyList r₀ nε loc j₁ j w )
                          ( find-<-Min*-canon
                             r₀ nε loc w j₁ j
                             ( ⊢-t₁ ( r₀ * nε ` loc ) w j₁ j k p₂ )
                             tl₁ ) ) )
            ( go ( r₀ * nε ` loc ) w j₁ j k p₂ tl₂t )
      tail> : ( r₀ * nε ` loc ) ⊢
              ListU ( greedyList-max r₀ nε loc w j₁ j tl₁ )
              >ᵍ ListU ( greedyList-max r₀ nε loc w j₂ k tl₂ )
      tail>
        = subst ( λ v → ( r₀ * nε ` loc ) ⊢
                         ListU ( greedyList-max r₀ nε loc w j₁ j tl₁ )
                         >ᵍ v )
            ( cong ( ListU { r₀ } { nε } { loc } )
                   ( greedyList-max-transport r₀ nε loc w k
                                              j₁ j₂ j₁≡j₂ tl₂ ) )
            go-tail


  -- Purpose : the Mamouras base order is sound for the greedy parse-tree
  --           order >ᵍ ( the greedy-witness form of <-greedy-sound ) :
  --           if the base order relates the spans ( i , j ) and ( i , k ) ,
  --           the greedy witness of the smaller span is above the greedy
  --           witness of the larger span .
  -- Used in : — ( top-level goal of this file ) .
  -- Idea    : u is the greedy witness of ( i , j ) ( greedyU on the match
  --           carried by the base-order proof , ⊢-t₁ ) ; the flat /
  --           concatenation / length side conditions follow from
  --           greedyU-flat / take++drop≡id / take≤length ( the bound
  --           j ∸ i ≤ length ( drop i w ) from match→end≤len + ∸-monoˡ-≤ ,
  --           the degenerate i ≡ j case trivial ) ; the ∀ part is go
  --           ( the right-hand witness is the greedy parse of the
  --           evidence t₂ , greedy-max ) .
  ←greedy-sound-go : ( r : RE ) ( w : List Char ) ( i j k : ℕ )
    → ( p : r ∣ w ∣ i ⊢ j < k )
    → ∃[ u ] ∃[ w₁ ] ∃[ w₂ ]
         ( proj₁ ( flat { r } u ) ≡ w₁
         × w₁ ++ w₂ ≡ drop i w
         × length w₁ ≡ j ∸ i
         × ∀ ( t₂ : r , i , k ⊨ w )
             → r ⊢ u >ᵍ ( greedy-max r w i k t₂ ) )
  ←greedy-sound-go r w i j k p
    = ( greedyU r i j w t₁
      , w₁
      , w₂
      , ( flat-ev , concat-ev , len-ev , ∀-ev ) )
    where
      t₁ : r , i , j ⊨ w
      t₁ = ⊢-t₁ r w i j k p
      w₁ : List Char
      w₁ = take ( j ∸ i ) ( drop i w )
      w₂ : List Char
      w₂ = drop ( j ∸ i ) ( drop i w )
      j∸i≤len : j ∸ i ≤ length ( drop i w )
      j∸i≤len with m≤n⇒m<n∨m≡n ( rij⊨w→i≤j t₁ )
      ... | inj₁ i<j =
        subst ( λ n → j ∸ i ≤ n )
          ( sym ( length-drop i w ) )
          ( ∸-monoˡ-≤ i ( match→end≤len r i j w i<j t₁ ) )
      ... | inj₂ i≡j rewrite i≡j | n∸n≡0 j = z≤n
      flat-ev : proj₁ ( flat { r } ( greedyU r i j w t₁ ) ) ≡ w₁
      flat-ev = greedyU-flat r i j w t₁
      concat-ev : w₁ ++ w₂ ≡ drop i w
      concat-ev = take++drop≡id ( j ∸ i ) ( drop i w )
      len-ev : length w₁ ≡ j ∸ i
      len-ev = take≤length ( drop i w ) ( j ∸ i ) j∸i≤len
      ∀-ev : ∀ ( t₂ : r , i , k ⊨ w )
        → r ⊢ ( greedyU r i j w t₁ )
             >ᵍ ( greedy-max r w i k t₂ )
      ∀-ev t₂ = go r w i j k p t₂
```
