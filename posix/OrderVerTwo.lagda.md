```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.OrderVerTwo where

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
open Nat using ( ℕ ; suc ; zero ; _>_ ; _≥_ ; _≤_  )

import Data.Nat.Properties as NatProperties
open NatProperties using ( <⇒≤ ; ≤-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl)

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst ; _≡?_)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)


import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)


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


data _⊢_>_ : ∀ ( r : RE ) → U r → U r → Set

data _⊢_>_  where

  seq₁ : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U  l } { v₂ v₂' : U r }
    → l ⊢ v₁ >  v₁'
    → length (proj₁ (flat (PairU {l} {r} {loc} v₁ v₂))) ≥ length (proj₁ (flat (PairU {l} {r} {loc} v₁' v₂')))
    ------------------------------------------------------------------
    → l ● r ` loc ⊢ PairU v₁ v₂ > PairU v₁' v₂'

  seq₂ : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U l } { v₂ v₂' : U r }
    → v₁ ≡ v₁'
    → r ⊢ v₂ > v₂'
    -------------------------------------------------------------------
    → ( l ● r ` loc) ⊢ (PairU v₁ v₂) > (PairU v₁' v₂')

  choice-lr : ∀ { l r : RE } { loc : ℕ } { v₁ : U l } { v₂ : U r }
    → length (proj₁ (flat v₁)) ≥ length (proj₁ (flat v₂))
    -------------------------------------------------------------------    
    → ( l + r ` loc ) ⊢ (LeftU v₁) > (RightU v₂)


  choice-rl : ∀ { l r : RE } { loc : ℕ } { v₁ : U r } { v₂ : U l }
    → length (proj₁ (flat v₁)) > length (proj₁ (flat v₂))
    -------------------------------------------------------------------    
    → ( l + r ` loc ) ⊢ (RightU v₁) > (LeftU v₂)

  choice-ll : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U l }
    → l ⊢ v₁ > v₁'
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (LeftU v₁) > (LeftU v₁')


  choice-rr : ∀ { l r : RE } { loc : ℕ } { v₂ v₂'  : U r }
    →  r ⊢ v₂ >  v₂'
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (RightU v₂) > (RightU v₂')


  star-cons-nil : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v : U r } { vs : List (U r) }
    → ( r * nε ` loc ) ⊢ (ListU (v ∷ vs)) > ( ListU [] )

  -- star-nil-cons rule is not needed as we are dealing with non problematic regular expression.


  -- the following rule is weakened by only considering len | v₁ ∷ vs₁ | >= len | v₂ ∷ vs₂ |
  -- notation  | v |  is proj₁ (flat v)
  -- do we need the same treament for seq₁ ? 

  star-head : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v₁ v₂ : U r } { vs₁ vs₂ : List (U r) }
    → r ⊢ v₁ > v₂
    -- → length (proj₁ (flat v₁)) ≥ length (proj₁ (flat v₂)) -- is this redundant? 
    → length (proj₁ (flat (ListU {r} {nε} {loc} (v₁ ∷ vs₁)))) ≥ length (proj₁ (flat (ListU  {r} {nε} {loc} (v₂ ∷ vs₂))))
    ----------------------------------------------------------------------
    → ( r * nε ` loc ) ⊢ (ListU (v₁ ∷ vs₁)) > (ListU (v₂ ∷ vs₂))


  star-tail : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v₁ v₂ : U r } { vs₁ vs₂ : List (U r) }
    → v₁ ≡ v₂
    → ( r * nε ` loc ) ⊢ (ListU vs₁) > (ListU vs₂)
    ----------------------------------------------------------------------
    → ( r * nε ` loc ) ⊢ (ListU (v₁ ∷ vs₁)) > (ListU (v₂ ∷ vs₂))


```


F. Ausaf, R. Dyckhoff, and C. Urban. “POSIX Lexing with Derivatives of Regular Expressions (Proof Pearl)”. In: Proc. of the 7th International Conference on
Interactive Theorem Proving (ITP). Vol. 9807. LNCS. 2016, pp. 69–86.

has the following definition of POSIX relation

P1

-------------------
([], ε) --> EmptyU


PC

-------------------
([c], $ c) --> LetterU c



P + L

(s, r₁) --> v₁
------------------------
(s, r₁ + r₂) --> LeftU v₁


P + R

(s, r₂) --> v₂   s∉ ⟦r₁⟧  
------------------------
(s, r₁ + r₂) --> RightU v₂



PS

(s₁, r₁) --> v₁     (s₂, r₂) --> v₂
¬∃ ( s₃ , s₄ ) . s₃ ≢ [] ∧ (s₃ ++ s₄) ≡ s₂ ∧ (s₁ ++ s₃) ∈⟦ r₁ ⟧ ∧ s₄ ∈⟦ r₂ ⟧ )
------------------------------------------------------------------------------
(s₁ ++ s₂, r₁ ● r₂) --> PairU v₁ v₂



P[]

---------------------------------------
([], r*) --> ListU []


P*

(s1, r) --> v       (s2, r*) --> ListU vs       |v| ≢ []
¬∃ ( s3 , s4 ) . s3 ≢ [] ∧ (s3 ++ s4) ≡ s2 ∧ (s1 ++ s3) ∈⟦ r ⟧ ∧ s4 ∈⟦ r* ⟧ 
-----------------------------------------------------------------------------
(s1 ++ s2, r* ) --> ListU (v ∷ vs)


It seems that the relationship is weaker. It fixes a particular word. 

```agda
infix 4 _,_⇒_

data _,_⇒_ : ∀ ( w : List Char ) → ( r : RE ) → U r → Set where
  p₁  : [] , ε ⇒ EmptyU 
  pc  : ∀ {c : Char} {loc : ℕ}  → [ c ] , $ c ` loc ⇒ LetterU c
  p+l : ∀ { w : List Char } { l r : RE } { loc : ℕ } { v : U l }
    →  w , l ⇒ v   
    ------------------------------------------------------------
    → w , l + r ` loc ⇒ LeftU v
  p+r : ∀ { w : List Char } { l r : RE } { loc : ℕ } { v : U r } 
    →  w , r ⇒ v
    → ¬ ( w ∈⟦ l ⟧ )
    ------------------------------------------------------------
    → w , l + r ` loc ⇒ RightU v
  ps : ∀ { w₁ w₂ : List Char } { l r : RE } { loc : ℕ } { v₁ : U l } { v₂ : U r }
    →  w₁ , l ⇒ v₁
    →  w₂ , r ⇒ v₂
    → ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) × (w₃ ++ w₄ ≡ w₂) × ( (w₁ ++ w₃) ∈⟦ l ⟧ ) × w₄ ∈⟦ r ⟧ )
    ------------------------------------------------------------
    → (w₁ ++ w₂) , l ● r ` loc ⇒ PairU v₁ v₂
    
  p[] : ∀ { r : RE } {ε∉r : ε∉ r } { loc : ℕ }
    → [] , r * ε∉r ` loc ⇒ ListU []
    
  p* : ∀ { w₁ w₂ : List Char } { r : RE } {ε∉r : ε∉ r } { loc : ℕ } {v : U r } { vs : List (U r) }
    →  w₁ , r ⇒ v
    →  w₂ , r * ε∉r ` loc ⇒ ListU vs
    →  ¬ w₁ ≡ []
    → ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) × (w₃ ++ w₄ ≡ w₂) × ( (w₁ ++ w₃) ∈⟦ r ⟧ ) × w₄ ∈⟦ r * ε∉r ` loc ⟧ )
    -----------------------------------------------------------
    → (w₁ ++ w₂) , r * ε∉r ` loc ⇒ ListU (v ∷ vs)
    
```


Lemma : a posix value is the largest value in posix ordering


```agda
postulate
  ⇒>-max : ∀ { r : RE } { v : U r } { w : List Char} 
    → w , r ⇒ v
    → ( u : U r )
    ------------------------
    → ( v ≡ u ) ⊎ ( r ⊢ v > u )


{-
len|xs++ys|≥len|xs++zs| : ∀ { A : Set } { xs ys zs : List A }
  → length ys ≥ length zs
  -----------------------------------
  → length (xs ++ ys) ≥ length (xs ++ zs)
len|xs++ys|≥len|xs++zs| {A} {[]}        {ys} {zs} len-ys≥len-zs = len-ys≥len-zs
len|xs++ys|≥len|xs++zs| {A} {(x ∷ xs)} {ys} {zs} len-ys≥len-zs = Nat.s≤s (len|xs++ys|≥len|xs++zs|  {A} {xs} {ys} {zs} len-ys≥len-zs)


-- do we still need this lemma to achieve transitivity? what if we apply the same > and = trick of the choice-ll and choice-rr rules to star-head and seq₁? 
>→len|≥| : { r : RE } { u v : U r } 
    → r ⊢ u > v
    -------------------------------------
    → length (proj₁ (flat u)) ≥ length (proj₁ (flat v))
>→len|≥| {ε}           {EmptyU}      {EmptyU} = λ ()
>→len|≥| {$ c ` loc}   {LetterU _}   {LetterU _} = λ ()
>→len|≥| {l ● r ` loc} {PairU v₁ v₂} {PairU u₁ u₂} (seq₁ v₁>u₁ len|v₁v₂|≥len|u₁u₂|) = len|v₁v₂|≥len|u₁u₂|
>→len|≥| {l ● r ` loc} {PairU v₁ v₂} {PairU u₁ u₂} (seq₂ v₁≡u₁ v₂>u₂) rewrite v₁≡u₁ = len|xs++ys|≥len|xs++zs| {Char} {proj₁ (flat u₁)} {proj₁ (flat v₂)} {proj₁ (flat u₂)} len|v₂|≥len|u₂|  
  where 
    len|v₂|≥len|u₂| : length (proj₁ (flat v₂)) ≥ length (proj₁ (flat u₂))
    len|v₂|≥len|u₂| = >→len|≥| v₂>u₂
>→len|≥| {l + r ` loc} {LeftU v₁} {LeftU v₂} (choice-ll v₁>v₂) = >→len|≥| v₁>v₂
>→len|≥| {l + r ` loc} {RightU v₁} {RightU v₂} (choice-rr v₁>v₂) = >→len|≥| v₁>v₂
>→len|≥| {l + r ` loc} {LeftU v₁} {RightU v₂} (choice-lr len|v₁|≥len|v₂|) = len|v₁|≥len|v₂|
>→len|≥| {l + r ` loc} {RightU v₁} {LeftU v₂} (choice-rl len|v₁|>len|v₂|) = <⇒≤  len|v₁|>len|v₂|
>→len|≥| {r * ε∉r ` loc } {ListU []} {ListU []} = λ()
>→len|≥| {r * ε∉r ` loc } {ListU []} {ListU ( u ∷ us) } = λ()
>→len|≥| {r * ε∉r ` loc } {ListU (v ∷ vs) } {ListU [] } star-cons-nil = Nat.z≤n
>→len|≥| {r * ε∉r ` loc } {ListU (v ∷ vs) } {ListU ( u ∷ us)} (star-head u>v len|v∷vs|>len|u∷us|) = len|v∷vs|>len|u∷us|
>→len|≥| {r * ε∉r ` loc } {ListU (v ∷ vs) } {ListU ( u ∷ us)} (star-tail v≡u vs>us) rewrite v≡u =  len|xs++ys|≥len|xs++zs| {Char} {proj₁ (flat u)} {proj₁ (flat (ListU {r} {ε∉r} {loc} vs))} {proj₁ (flat (ListU {r} {ε∉r} {loc} us))} len|vs|≥len|us|  
  where 
    len|vs|≥len|us| : length (proj₁ (flat (ListU {r} {ε∉r} {loc} vs))) ≥ length (proj₁ (flat (ListU {r} {ε∉r} {loc} us)))
    len|vs|≥len|us| = >→len|≥| vs>us



len|>|→> : { r : RE } { u v : U r } 
    → length (proj₁ (flat u)) > length (proj₁ (flat v))
    -------------------------------------
    → r ⊢ u > v
len|>|→> {ε} {EmptyU} {EmptyU} = λ()
len|>|→> {$ c ` loc} {LetterU _ } {LetterU _} len[c]>len[c] = Nullary.contradiction len[c]>len[c] (<-irrefl refl) 
len|>|→> {l ● r ` loc} {PairU v₁ v₂} {PairU u₁ u₂} len|v₁v₂|>len|u₁u₂| = {!!} 
  -- with v₁ ≟ u₁
-- ... | yes v₁≡u₁ = {!!}
-}
```

case v₁≡u₁  : len|v₂|>len|u₂| implies v₂ > u₂ we have seq₂

case v₁ > u₁ : seq₁ v₁>u₁ len|v₁v₂|>len|u₁u₂|
case ¬ v₁ > u₁ : ¬ len|v₁| > len|u₁| implies
                 len|u₁| ≥ len|v₁| implies 
                 len|v₂| > len|u₂| implies
                 v₂ > u₂ ? 
is r ⊢ _ > _ total ?

case len|v₁|>len|u₁| : ind-hyp v₁>u₁, we have seq₁
case len|u₁|≥len|v₁| : len|v₁v₂|>len|u₁u₂| implies len|u₂|>len|v₂|,
                       by ind-hyp we have. u₂ > v₂ but then? 



Note : The > order is transitive. 

```agda



{-
>-trans : { r : RE } { u₁ u₂ u₃ : U r }
  → r ⊢ u₁ > u₂
  → r ⊢ u₂ > u₃
  -----------------
  → r ⊢ u₁ > u₃
>-trans {ε} = λ()
>-trans {$ c ` loc} = λ()
>-trans {r * ε∉r ` loc} star-cons-nil = λ()
>-trans {r * ε∉r ` loc} {ListU (v₁ ∷ vs₁)} {ListU (v₂ ∷ vs₂)} {ListU (v₃ ∷ vs₃)}
        (star-head v₁>v₂ len|v₁∷vs₁|≥len|v₂∷vs₂| )   (star-head v₂>v₃ len|v₂∷vs₂|≥len|v₃∷vs₃| ) = star-head (>-trans v₁>v₂ v₂>v₃) (≤-trans len|v₂∷vs₂|≥len|v₃∷vs₃| len|v₁∷vs₁|≥len|v₂∷vs₂| )

>-trans {r * ε∉r ` loc} {ListU (v₁ ∷ vs₁)} {ListU (v₂ ∷ vs₂)} {ListU (v₃ ∷ vs₃)}
        (star-head v₁>v₂ len|v₁∷vs₁|≥len|v₂∷vs₂| )   (star-tail v₂≡v₃ vs₂>vs₃) rewrite (sym v₂≡v₃) = star-head v₁>v₂ len|v₁∷vs₁|≥len|v₂∷vs₃|
  where
    len|vs₂|≥len|vs₃| : length (proj₁ (flat (ListU vs₂))) ≥ length (proj₁ (flat (ListU vs₃)))
    len|vs₂|≥len|vs₃| = >→len|≥|  vs₂>vs₃

    len|v₂∷vs₂|≥len|v₂∷vs₃| : length (proj₁ (flat (ListU {r} {ε∉r} {loc} (v₂ ∷ vs₂)))) ≥ length (proj₁ (flat (ListU {r} {ε∉r} {loc} (v₂ ∷ vs₃))))
    len|v₂∷vs₂|≥len|v₂∷vs₃| = len|xs++ys|≥len|xs++zs| {Char} {proj₁ (flat v₂)} {proj₁ (flat (ListU {r} {ε∉r} {loc} vs₂))} {proj₁ (flat (ListU {r} {ε∉r} {loc} vs₃))} len|vs₂|≥len|vs₃| 

    len|v₁∷vs₁|≥len|v₂∷vs₃| : length (proj₁ (flat (ListU {r} {ε∉r} {loc} (v₁ ∷ vs₁)))) ≥ length (proj₁ (flat (ListU {r} {ε∉r} {loc} (v₂ ∷ vs₃))))
    len|v₁∷vs₁|≥len|v₂∷vs₃| = ≤-trans len|v₂∷vs₂|≥len|v₂∷vs₃| len|v₁∷vs₁|≥len|v₂∷vs₂|

    
    
>-trans {r * ε∉r ` loc} (star-head v₁>v₂ _ )         star-cons-nil  = star-cons-nil
>-trans {r * ε∉r ` loc} (star-tail v₁≡v₂ vs₁>vs₂) (star-tail v₂≡v₃ vs₂>vs₃) rewrite (sym v₂≡v₃) = star-tail v₁≡v₂ (>-trans vs₁>vs₂ vs₂>vs₃)
>-trans {r * ε∉r ` loc} {ListU (v₁ ∷ vs₁)} {ListU (v₂ ∷ vs₂)} {ListU (v₃ ∷ vs₃)}
  (star-tail v₁≡v₂ vs₁>vs₂) (star-head v₂>v₃ len|v₂∷vs₂|≥len|v₃∷vs₃|) rewrite v₁≡v₂ = star-head v₂>v₃ (≤-trans  len|v₂∷vs₂|≥len|v₃∷vs₃| len|v₂∷vs₁|≥len|v₂∷vs₂|)
  where
    len|vs₁|≥len|vs₂| :  length (proj₁ (flat (ListU {r} {ε∉r} {loc} vs₁))) ≥ length (proj₁ (flat (ListU {r} {ε∉r} {loc} vs₂)))
    len|vs₁|≥len|vs₂| = >→len|≥|  vs₁>vs₂

    len|v₂∷vs₁|≥len|v₂∷vs₂| : length (proj₁ (flat (ListU {r} {ε∉r} {loc} (v₂ ∷ vs₁)))) ≥ length (proj₁ (flat (ListU {r} {ε∉r} {loc} (v₂ ∷ vs₂))))
    len|v₂∷vs₁|≥len|v₂∷vs₂| =  len|xs++ys|≥len|xs++zs| {Char} {proj₁ (flat v₂)} {proj₁ (flat (ListU {r} {ε∉r} {loc} vs₁))} {proj₁ (flat (ListU {r} {ε∉r} {loc} vs₂))} len|vs₁|≥len|vs₂| 
 
>-trans {r * ε∉r ` loc} (star-tail v₁≡v₂ vs₁>vs₂) star-cons-nil  = star-cons-nil
>-trans {l + r ` loc} (choice-ll {l} {r} {.loc} {v₁} {v₂} v₁>v₂) (choice-lr {l} {r} {.loc} {.v₂} {v₃} len|v₂|≥len|v₃|) = choice-lr ( ≤-trans len|v₂|≥len|v₃| ( >→len|≥| v₁>v₂) ) -- we have l ⊢ v₁ > v₂, how to get |v₁| ≥ |v₂|
>-trans {l + r ` loc} (choice-ll {l} {r} {.loc} {v₁} {v₂} v₁>v₂) (choice-ll {l} {r} {.loc} {.v₂} {v₃} v₂>v₃)     = choice-ll (>-trans v₁>v₂ v₂>v₃)
>-trans {l + r ` loc} (choice-lr {l} {r} {.loc} {v₁} {v₂} len|v₁|≥len|v₂|) (choice-rr {l} {r} {.loc} {.v₂} {v₃} v₂>v₃) = choice-lr ( ≤-trans (>→len|≥| v₂>v₃) len|v₁|≥len|v₂| )
>-trans {l + r ` loc} (choice-lr {l} {r} {.loc} {v₁} {v₂} len|v₁|≥len|v₂|) (choice-rl {l} {r} {.loc} {.v₂} {v₃} len|v₂|>len|v₃|) = choice-ll {!!}  -- we know len|v₁|>len|v₃|, can we construct v₁>v₃, do we need len|>|→> ?
-- len|>|→> seems to be invalid.
-- is there a contradiction here? 
>-trans {l + r ` loc} (choice-rr {l} {r} {.loc} {v₁} {v₂} v₁>v₂) (choice-rr {l} {r} {.loc} {.v₂} {v₃} v₂>v₃)     = choice-rr (>-trans v₁>v₂ v₂>v₃)

-}

```

Maybe we need to weaken the transitivity lemma to include the underlying word.

a) Does r ⊢ v₁ > v₂ imply |v₁| ≥ |v₂| ? no.
counter example: r = ( a ● (a + ε) )*

r ⊢ 
 Cons (Pair a (L a))     (Cons (Pair a (R Empty)) Nil)
 > 
 Cons (Pair a (R Empty)) (Cons (Pair a (L a)) (Cons (Pair a (R Empty)) Nil))

with star-head (seq₂ (choice-rl 1>0)) as the proof

but | Cons (Pair a (L a))     (Cons (Pair a (R Empty)) Nil) | = aaa
    | Cons (Pair a (R Empty)) (Cons (Pair a (L a)) (Cons (Pair a (R Empty)) Nil)) | = aaaa
    

b) Does |v₁| ≥ |v₂| imply  r ⊢ v₁ > v₂ ? no. 

same counter example above i.e. a).


For a) to hold, the only rule that we need to weaken is star-head

we need to ensure that |v₁| ≥ |v₂| and |v₁| + |vs₁| ≥ |v₂| + |vs₂|

which will reject the counter example above. 

>>> what about nested *, the ≡ won't hold but that's problematic.


>>> what about ● ? 

r = ( ( a + ε ) ● ( a + ε ) ) ● ( a + ε )

r ⊢ Pair (Pair (L a) (R Empty)) (R Empty)
  >
    Pair (Pair (R Empty) (L a)) (L a)

>>> what about the following

r = ( ( a + ε ) ● ( a * ) ) ● ( a + ε )

r ⊢ Pair (Pair (L a) (List [])) (L a)
  >
    Pair (Pair (R Empty) (List [a,a])) (L a)

proof is seq₁ (seq₁ choice-lr 1>0)

but in FLOPS 2014 paper, we assume ● is always right associative. 
