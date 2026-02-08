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
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ; proj₁flat-v≡[]→ε∈r ; flat-[]→flat-[]-left ; flat-[]→flat-[]-right )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ;
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ;
  concatmap-pdinstance-snd ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with   
  ) 



import cgp.posix.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; pdUConcat ;
  pdUMany[_,_]; pdUMany-aux )



import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _>_ ; _≥_ ; _≤_  )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl)

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


Note that we have adjusted the POSIX ordering defined in FLOPS 2014 as follows, the one in FLOPS 2014 has an issue with the cyclic relation >
refer to the MatchingIssue.md, section "Updated on Feb 6 2026". 



The adjustment is to introduce a top level > and an internal level >ⁱ

The internal level >ⁱ is the same as the one defined in FLOPS 2024 modulo the inductive call.



r₁ ⊢ v₁ > v₁'
-------------------------------------------- (Seq₁)
r₁ ● r₂ ⊢ PairU v₁ v₂ >ⁱ PairU v₁' v₂'



v₁ ≡ v₁'  r₂ ⊢ v₂ > v₂'
-------------------------------------------- (Seq₂)
r₁ ● r₂ ⊢ PairU v₁ v₂ >ⁱ PairU v₁' v₂'


r₁ ⊢ v₁ > v₁'
----------------------------------(ChoiceLL)
r₁ + r₂ ⊢ LeftU v₁ >ⁱ LeftU v₁' 


r₂ ⊢ v₂ > v₂'
----------------------------------(ChoiceRR)
r₁ + r₂ ⊢ RightU v₂ >ⁱ RightU v₂' 


length |v₁| ≥ length |v₂|
----------------------------------------------(ChoiceLR)
r₁ + r₂ ⊢ LeftU v₁ >ⁱ RightU v₂ 



length |v₂| > length |v₁|
----------------------------------------------(ChoiceRL)
r₁ + r₂ ⊢ RightU v₂ >ⁱ LeftU v₁ 


r ⊢ v₁ > v₂ 
---------------------------------(StarHd)
r* ⊢ ConsU v₁ vs₁ >ⁱ ConsU v₂ vs₂


v₁ ≡ v₂        r* ⊢ vs₁ > vs₂ 
---------------------------------(StarTl)
r* ⊢ ConsU v₁ vs₁ >ⁱ ConsU v₂ vs₂



length |v| + length |vs| == 0
-----------------------------------------------(StarNilCons)
r* ⊢ NilU >ⁱ ConsU v vs



length |v| + length |vs| > 0
------------------------------------------------(StarNilCons)
r* ⊢ ConsU v vs >ⁱ NilU



The top level > has the following two rules

len |v₁| ≡ len |v₂|
r ⊢ v₁ >ⁱ v₂
--------------------------------(≡-len)
r ⊢ v₁ > v₂

len |v₁| > len |v₂|
--------------------------------(>-len)
r ⊢ v₁ > v₂



```agda
infix 4 _⊢_>_
infix 4 _⊢_>ⁱ_

-- the top level > 
data _⊢_>_ : ∀ ( r : RE ) → U r → U r → Set

-- the internal >
data _⊢_>ⁱ_ : ∀ ( r : RE ) → U r → U r → Set 


data _⊢_>_ where
  len-≡ : ∀ { r : RE } { v₁ v₂ : U r }
    → length (proj₁ (flat v₁)) ≡ length (proj₁ (flat v₂))
    → r ⊢ v₁ >ⁱ v₂
    -----------------------------------------------------
    → r ⊢ v₁ > v₂

  len-> : ∀ { r : RE } { v₁ v₂ : U r }
    → length (proj₁ (flat v₁)) > length (proj₁ (flat v₂))
    -----------------------------------------------------
    → r ⊢ v₁ > v₂

data _⊢_>ⁱ_  where

  seq₁ : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U  l } { v₂ v₂' : U r }
    → l ⊢ v₁ >  v₁'
    ------------------------------------------------------------------
    → l ● r ` loc ⊢ PairU v₁ v₂ >ⁱ PairU v₁' v₂'

  seq₂ : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U l } { v₂ v₂' : U r }
    → v₁ ≡ v₁'
    → r ⊢ v₂ > v₂'
    -------------------------------------------------------------------
    → ( l ● r ` loc) ⊢ (PairU v₁ v₂) >ⁱ (PairU v₁' v₂')

  choice-lr : ∀ { l r : RE } { loc : ℕ } { v₁ : U l } { v₂ : U r }
    → length (proj₁ (flat v₁)) ≥ length (proj₁ (flat v₂))
    -------------------------------------------------------------------    
    → ( l + r ` loc ) ⊢ (LeftU v₁) >ⁱ (RightU v₂)


  choice-rl : ∀ { l r : RE } { loc : ℕ } { v₁ : U r } { v₂ : U l }
    → length (proj₁ (flat v₁)) > length (proj₁ (flat v₂))
    -------------------------------------------------------------------    
    → ( l + r ` loc ) ⊢ (RightU v₁) >ⁱ  (LeftU v₂)

  choice-ll : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U l }
    → l ⊢ v₁ > v₁'
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (LeftU v₁) >ⁱ (LeftU v₁')


  choice-rr : ∀ { l r : RE } { loc : ℕ } { v₂ v₂'  : U r }
    →  r ⊢ v₂ >  v₂'
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (RightU v₂) >ⁱ (RightU v₂')


  star-cons-nil : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v : U r } { vs : List (U r) }
    → ( r * nε ` loc ) ⊢ (ListU (v ∷ vs)) >ⁱ ( ListU [] )

  -- star-nil-cons rule is not needed as we are dealing with non problematic regular expression.


  -- notation  | v |  is proj₁ (flat v)
  -- do we need the same treament for seq₁ ? 

  star-head : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v₁ v₂ : U r } { vs₁ vs₂ : List (U r) }
    → r ⊢ v₁ > v₂
    ----------------------------------------------------------------------
    → ( r * nε ` loc ) ⊢ (ListU (v₁ ∷ vs₁)) >ⁱ (ListU (v₂ ∷ vs₂))


  star-tail : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v₁ v₂ : U r } { vs₁ vs₂ : List (U r) }
    → v₁ ≡ v₂
    → ( r * nε ` loc ) ⊢ (ListU vs₁) > (ListU vs₂)
    ----------------------------------------------------------------------
    → ( r * nε ` loc ) ⊢ (ListU (v₁ ∷ vs₁)) >ⁱ (ListU (v₂ ∷ vs₂))


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
len|xs++ys|≥len|xs++zs| {A} {(x ∷ xs)} {ys} {zs} len-ys≥len-zs = Nat.s≤s (len|xs++ys|≥len|xs++zs| {A} {xs} {ys} {zs}  len-ys≥len-zs) 

-}




>→len|≥| : { r : RE } { u v : U r } 
           → r ⊢ u > v
           -------------------------------------
           → length (proj₁ (flat u)) ≥ length (proj₁ (flat v))
>→len|≥| {r} {u} {v} (len-> len-u>len-v) = <⇒≤ len-u>len-v
>→len|≥| {r} {u} {v} (len-≡ len-u≡len-v u>ⁱv) = ≤-reflexive (sym len-u≡len-v)  




len|>|→> : { r : RE } { u v : U r } 
    → length (proj₁ (flat u)) > length (proj₁ (flat v))
    -------------------------------------
    → r ⊢ u > v
len|>|→> {r} {u} {v} len|u|>len|v| = len-> len|u|>len|v|



```


Note : The > order is transitive. 

```agda




>-trans : { r : RE } { u₁ u₂ u₃ : U r }
    → r ⊢ u₁ > u₂
    → r ⊢ u₂ > u₃
    -----------------
    → r ⊢ u₁ > u₃

>ⁱ-trans : { r : RE } { u₁ u₂ u₃ : U r }
  → r ⊢ u₁ >ⁱ u₂
  → r ⊢ u₂ >ⁱ u₃
  -----------------
  → r ⊢ u₁ >ⁱ u₃


>-trans {r} {u₁} {u₂} {u₃} (len-≡ {r} {v₁} {v₂} len-|v₁|≡len-|v₂| v₁>ⁱv₂) (len-≡ {r} {.v₂} {v₃} len-|v₂|≡len-|v₃| v₂>ⁱv₃) =
  len-≡ {r} {v₁} {v₃} (trans len-|v₁|≡len-|v₂| len-|v₂|≡len-|v₃|) (>ⁱ-trans v₁>ⁱv₂ v₂>ⁱv₃)
>-trans {r} {u₁} {u₂} {u₃} (len-≡ {r} {v₁} {v₂} len-|v₁|≡len-|v₂| v₁>ⁱv₂) (len-> {r} {.v₂} {v₃} len-|v₂|>len-|v₃|) = 
  len-> {r} {v₁} {v₃} len-|v₁|>len|v₃|
  where
    len-|v₁|>len|v₃| : length (proj₁ (flat u₁)) > length (proj₁ (flat u₃))
    len-|v₁|>len|v₃| rewrite  len-|v₁|≡len-|v₂| = len-|v₂|>len-|v₃| 
>-trans {r} {u₁} {u₂} {u₃} (len-> {r} {v₁} {v₂} len-|v₁|>len-|v₂|) (len-> {r} {.v₂} {v₃} len-|v₂|>len-|v₃|) = len-> {r} {v₁} {v₃} (<-trans len-|v₂|>len-|v₃| len-|v₁|>len-|v₂| )
>-trans {r} {u₁} {u₂} {u₃} (len-> {r} {v₁} {v₂} len-|v₁|>len-|v₂|) (len-≡ {r} {.v₂} {v₃} len-|v₂|≡len-|v₃|  v₂>ⁱv₃) = len-> {r} {v₁} {v₃} len-|v₁|>len|v₃|
  where
    len-|v₁|>len|v₃| : length (proj₁ (flat u₁)) > length (proj₁ (flat u₃))
    len-|v₁|>len|v₃| rewrite (sym len-|v₂|≡len-|v₃|) = len-|v₁|>len-|v₂| 



>ⁱ-trans {ε} = λ()
>ⁱ-trans {$ c ` loc} = λ()
>ⁱ-trans {r * ε∉r ` loc} star-cons-nil = λ()
>ⁱ-trans {r * ε∉r ` loc} {ListU (v₁ ∷ vs₁)} {ListU (v₂ ∷ vs₂)} {ListU (v₃ ∷ vs₃)}
        (star-head v₁>v₂)   (star-head v₂>v₃ ) = star-head (>-trans v₁>v₂ v₂>v₃) 

>ⁱ-trans {r * ε∉r ` loc} {ListU (v₁ ∷ vs₁)} {ListU (v₂ ∷ vs₂)} {ListU (v₃ ∷ vs₃)}
        (star-head v₁>v₂ )   (star-tail v₂≡v₃ vs₂>vs₃) rewrite (sym v₂≡v₃) = star-head v₁>v₂

>ⁱ-trans {r * ε∉r ` loc} (star-head v₁>v₂ )         star-cons-nil  = star-cons-nil
>ⁱ-trans {r * ε∉r ` loc} (star-tail v₁≡v₂ vs₁>vs₂) (star-tail v₂≡v₃ vs₂>vs₃) rewrite (sym v₂≡v₃) = star-tail v₁≡v₂ (>-trans vs₁>vs₂ vs₂>vs₃)
>ⁱ-trans {r * ε∉r ` loc} {ListU (v₁ ∷ vs₁)} {ListU (v₂ ∷ vs₂)} {ListU (v₃ ∷ vs₃)}
  (star-tail v₁≡v₂ vs₁>vs₂) (star-head v₂>v₃) rewrite v₁≡v₂ = star-head v₂>v₃
  
>ⁱ-trans {r * ε∉r ` loc} (star-tail v₁≡v₂ vs₁>vs₂) star-cons-nil  = star-cons-nil
>ⁱ-trans {l + r ` loc} (choice-ll {l} {r} {.loc} {v₁} {v₂} v₁>v₂) (choice-lr {l} {r} {.loc} {.v₂} {v₃} len|v₂|≥len|v₃|) = choice-lr ( ≤-trans len|v₂|≥len|v₃| ( >→len|≥| v₁>v₂) ) 
>ⁱ-trans {l + r ` loc} (choice-ll {l} {r} {.loc} {v₁} {v₂} v₁>v₂) (choice-ll {l} {r} {.loc} {.v₂} {v₃} v₂>v₃)     = choice-ll (>-trans v₁>v₂ v₂>v₃)
>ⁱ-trans {l + r ` loc} (choice-lr {l} {r} {.loc} {v₁} {v₂} len|v₁|≥len|v₂|) (choice-rr {l} {r} {.loc} {.v₂} {v₃} v₂>v₃) = choice-lr ( ≤-trans (>→len|≥| v₂>v₃) len|v₁|≥len|v₂| )
>ⁱ-trans {l + r ` loc} (choice-lr {l} {r} {.loc} {v₁} {v₂} len|v₁|≥len|v₂|) (choice-rl {l} {r} {.loc} {.v₂} {v₃} len|v₂|>len|v₃|) = choice-ll (len|>|→> len|v₁|>len|v₃| )
  where
    len|v₁|>len|v₃| : length (proj₁ (flat v₁)) > length (proj₁ (flat v₃))
    len|v₁|>len|v₃| = ≤-trans len|v₂|>len|v₃| len|v₁|≥len|v₂|  

>ⁱ-trans {l + r ` loc} (choice-rr {l} {r} {.loc} {v₁} {v₂} v₁>v₂) (choice-rr {l} {r} {.loc} {.v₂} {v₃} v₂>v₃)     = choice-rr (>-trans v₁>v₂ v₂>v₃)
>ⁱ-trans {l + r ` loc} (choice-rr {l} {r} {.loc} {v₁} {v₂} v₁>v₂) (choice-rl {l} {r} {.loc} {.v₂} {v₃} len|v₂|>len|v₃|) =  choice-rl ( ≤-trans len|v₂|>len|v₃| (>→len|≥| v₁>v₂ ) ) 
>ⁱ-trans {l + r ` loc} (choice-rl {l} {r} {.loc} {v₁} {v₂} len|v₁|>len|v₂|) (choice-lr {l} {r} {.loc} {.v₂} {v₃} len|v₂|≥len|v₃|) = choice-rr (len|>|→> (≤-trans (Nat.s≤s len|v₂|≥len|v₃|)  len|v₁|>len|v₂|) )
>ⁱ-trans {l + r ` loc} (choice-rl {l} {r} {.loc} {v₁} {v₂} len|v₁|>len|v₂|) (choice-ll {l} {r} {.loc} {.v₂} {v₃} v₂>v₃) = choice-rl ( ≤-trans (Nat.s≤s (>→len|≥| v₂>v₃ )) len|v₁|>len|v₂| )
>ⁱ-trans {l ● r ` loc} (seq₁ v₁>v₂) (seq₁ v₂>v₃) = seq₁ (>-trans v₁>v₂ v₂>v₃ )
>ⁱ-trans {l ● r ` loc} (seq₁ v₁>v₂) (seq₂ v₂≡v₃ vs₂>vs₃) rewrite v₂≡v₃ = seq₁ v₁>v₂ 
>ⁱ-trans {l ● r ` loc} (seq₂ v₁≡v₂ vs₁>vs₂) (seq₂ v₂≡v₃ vs₂>vs₃) rewrite (sym v₁≡v₂) = seq₂ v₂≡v₃ (>-trans vs₁>vs₂ vs₂>vs₃)
>ⁱ-trans {l ● r ` loc} (seq₂ v₁≡v₂ vs₁>vs₂) (seq₁ v₂>v₃) rewrite v₁≡v₂ = seq₁ v₂>v₃ 
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





Lemma u₁ > u₂ implies ¬ u₁ ≡ u₂


```agda
>→¬≡ : { r : RE } { u₁ u₂ : U r }
  → r ⊢ u₁ > u₂ 
  -----------------
  → ¬ u₁ ≡ u₂ 




>ⁱ→¬≡ : { r : RE } { u₁ u₂ : U r }
    → r ⊢ u₁ >ⁱ u₂ 
    -----------------
    → ¬ u₁ ≡ u₂ 


>→¬≡ {r} {u} {v} (len-≡ len|u|≡len|v| u>ⁱv) = >ⁱ→¬≡ u>ⁱv
>→¬≡ {r} {u} {v} (len-> len|u|>len|v|) u≡v rewrite u≡v = <-irrefl refl len|u|>len|v|



>ⁱ→¬≡ {ε} {EmptyU}    {EmptyU} = λ() 
>ⁱ→¬≡ {$ c ` loc}     {LetterU _} {LetterU _} = λ()

>ⁱ→¬≡ {r * ε∉r ` loc} {ListU (u ∷ us)} {ListU []} star-cons-nil = λ ()
>ⁱ→¬≡ {r * ε∉r ` loc} {ListU (u ∷ us)} {ListU (v ∷ vs)} (star-head u>v) = λ list-u∷us≡list-v∷vs → ¬u≡v (proj₁ (ParseTree.inv-listU u us v vs list-u∷us≡list-v∷vs)) 
  where
    ¬u≡v : ¬ u ≡ v
    ¬u≡v = >→¬≡ {r} {u} {v} u>v
>ⁱ→¬≡ {r * ε∉r ` loc} {ListU (u ∷ us)} {ListU (v ∷ vs)} (star-tail u≡v list-us>list-vs) = λ list-u∷us≡list-v∷vs → ¬us≡vs (proj₂ (ParseTree.inv-listU u us v vs list-u∷us≡list-v∷vs))
  where
    ¬list-us≡list-vs : ¬ (ListU us) ≡ (ListU vs)
    ¬list-us≡list-vs = >→¬≡ {r * ε∉r ` loc} {ListU us} {ListU vs} list-us>list-vs

    ¬us≡vs : ¬ us ≡ vs
    ¬us≡vs us≡vs = ¬list-us≡list-vs list-us≡list-vs
      where
        list-us≡list-vs : (ListU {r} {ε∉r} {loc} us) ≡ (ListU {r} {ε∉r} {loc} vs)
        list-us≡list-vs rewrite (cong (λ x → ListU {r} {ε∉r} {loc} x) us≡vs ) = refl 
>ⁱ→¬≡ {l ● r ` loc} {PairU u₁ u₂} {PairU v₁ v₂} (seq₁ u₁>v₁) = λ pair-u₁u₂≡pair-v₁v₂ → ¬u₁≡v₁ (proj₁ (ParseTree.inv-pairU u₁ u₂ v₁ v₂ pair-u₁u₂≡pair-v₁v₂))
  where
    ¬u₁≡v₁ : ¬ u₁ ≡ v₁
    ¬u₁≡v₁ = >→¬≡ {l} {u₁} {v₁} u₁>v₁
>ⁱ→¬≡ {l ● r ` loc} {PairU u₁ u₂} {PairU v₁ v₂} (seq₂ u₁≡v₁ u₂>v₂) = λ pair-u₁u₂≡pair-v₁v₂ → ¬u₂≡v₂ (proj₂ (ParseTree.inv-pairU u₁ u₂ v₁ v₂ pair-u₁u₂≡pair-v₁v₂))
  where
    ¬u₂≡v₂ : ¬ u₂ ≡ v₂
    ¬u₂≡v₂ = >→¬≡ {r} {u₂} {v₂} u₂>v₂
>ⁱ→¬≡ {l + r ` loc} {LeftU u} {RightU v} _  = λ ()
>ⁱ→¬≡ {l + r ` loc} {RightU u} {LeftU v} _  = λ ()
>ⁱ→¬≡ {l + r ` loc} {LeftU u} {LeftU v} (choice-ll u>v)  = λ left-u≡left-v →  ¬u≡v (ParseTree.inv-leftU u v left-u≡left-v)
  where 
    ¬u≡v : ¬ u ≡ v
    ¬u≡v = >→¬≡ {l} {u} {v} u>v
>ⁱ→¬≡ {l + r ` loc} {RightU u} {RightU v} (choice-rr u>v)  = λ right-u≡right-v →  ¬u≡v (ParseTree.inv-rightU u v right-u≡right-v)
  where 
    ¬u≡v : ¬ u ≡ v
    ¬u≡v = >→¬≡ {r} {u} {v} u>v

```



### Definition 30: >-sortedness 


```agda
data >-maybe : ∀ { r : RE } ( u : U r ) → ( mv : Maybe (U r) ) → Set where 
  >-nothing : ∀ { r : RE }
    → { u : U r } 
    ------------------------ 
    → >-maybe {r} u nothing

  >-just : ∀ { r : RE }
    → { u : U r }
    → { v : U r }
    → r ⊢ u > v 
    ---------------------------
    → >-maybe {r} u (just v)


data >-sorted : ∀ { r : RE } ( us : List (U r) ) → Set where
  >-nil : ∀ { r : RE } → >-sorted {r} []
  >-cons : ∀ { r : RE }
    → { u : U r }
    → { us : List (U r) } 
    → >-sorted {r} us
    → >-maybe {r} u (head us)
    --------------------------
    → >-sorted {r} ( u ∷ us  )



-- concatenating two >-sorted lists of parse trees  yields a >-sorted list.
concat-sorted : ∀ { r : RE } 
  → ( us₁ : List ( U r ) )
  → ( us₂ : List ( U r ) )
  → >-sorted { r } us₁
  → >-sorted { r } us₂
  → All (λ u₁ → >-maybe {r} u₁ (head us₂)) us₁
  ----------------------------------------------
  → >-sorted { r } (us₁ ++ us₂)
concat-sorted []               us₂        >-nil        us₂-sorted    []                            = us₂-sorted
concat-sorted us₁              []         us₁-sorted   >-nil         _  rewrite (++-identityʳ us₁) = us₁-sorted
concat-sorted (u₁ ∷ [])        (u₂ ∷ us₂) us₁-sorted   u₂us₂-sorted  (>-just u₁>u₂ ∷ [] )          = >-cons u₂us₂-sorted (>-just u₁>u₂)
concat-sorted (u₁ ∷ u₁' ∷ us₁) (u₂ ∷ us₂) (>-cons u₁'us₁-sorted (>-just u₁>u₁'))  u₂us₂-sorted (>-just u₁>u₂ ∷ pxs) = >-cons ind-hyp (>-just u₁>u₁')
  where
    ind-hyp = concat-sorted (u₁' ∷ us₁) (u₂ ∷ us₂) u₁'us₁-sorted u₂us₂-sorted pxs


```


### Lemma 31: Parse trees generated by mkAllEmptyU is >-sorted. 

Let r be a non problematic regular expression, such that ε∈r.
Then (mkAllEmptyU ε∈r) is greedily sorted. 


```agda
-----------------------------------------------------------------------------
-- Sub Lemma 31.1 - 31.4  BEGIN
----------------------------------------------------------------------------


-- aux lemma
-- weakened compared to the version on greedy.Order
-- we assume all us and vs are empty parse trees

map-leftU-sorted : ∀ { l r : RE } { loc : ℕ }
  → ( us : List (U l) )
  → >-sorted {l} us
  → All (Flat-[] l) us     
  ---------------------------------------------
  → >-sorted {l + r ` loc } (List.map LeftU us)
map-leftU-sorted []          >-nil []  = >-nil
map-leftU-sorted ( u ∷ [] ) (>-cons >-nil >-nothing ) _ 
  = >-cons >-nil >-nothing 
map-leftU-sorted {l} {r} {loc} ( u ∷ (v ∷ us) ) (>-cons  >-sorted-us (>-just u>v)) ((flat-[] _ proj₁flatu≡[]) ∷ (flat-[] _ proj₁flatv≡[]) ∷ flat-[]-us) 
  = >-cons (map-leftU-sorted (v ∷ us) >-sorted-us ((flat-[] v proj₁flatv≡[]) ∷ flat-[]-us))
           (>-just (len-≡ len-|left-u|≡len-|left-v| (choice-ll u>v)) ) 
  where
    |left-u|≡[] : proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ []
    |left-u|≡[] with flat-[]→flat-[]-left {l} {r} {loc} {u} (flat-[] u proj₁flatu≡[])
    ... | flat-[] (LeftU _)  proj₁flat-leftu≡[] = proj₁flat-leftu≡[] 
    |left-v|≡[] : proj₁ (flat (LeftU {l} {r} {loc} v)) ≡ []
    |left-v|≡[] with flat-[]→flat-[]-left {l} {r} {loc} {v} (flat-[] v proj₁flatv≡[])
    ... | flat-[] (LeftU _)  proj₁flat-leftv≡[] = proj₁flat-leftv≡[]
    |left-u|≡|left-v| : proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ proj₁ (flat (LeftU {l} {r} {loc} v))
    |left-u|≡|left-v| rewrite |left-v|≡[] = proj₁flatu≡[]
    len-|left-u|≡len-|left-v| : length (proj₁ (flat (LeftU {l} {r} {loc} u))) ≡ length (proj₁ (flat (LeftU {l} {r} {loc} v)))
    len-|left-u|≡len-|left-v| rewrite |left-u|≡|left-v| = refl 
           



map-rightU-sorted : ∀ { l r : RE } { loc : ℕ }
  → ( us : List (U r) )
  → >-sorted {r} us
  → All (Flat-[] r) us     
  ---------------------------------------------
  → >-sorted {l + r ` loc } (List.map RightU us)
map-rightU-sorted []          >-nil []  = >-nil
map-rightU-sorted ( u ∷ [] ) (>-cons >-nil >-nothing ) _ 
  = >-cons >-nil >-nothing 
map-rightU-sorted {l} {r} {loc} ( u ∷ (v ∷ us) ) (>-cons  >-sorted-us (>-just u>v)) ((flat-[] _ proj₁flatu≡[]) ∷ (flat-[] _ proj₁flatv≡[]) ∷ flat-[]-us) 
  = >-cons (map-rightU-sorted (v ∷ us) >-sorted-us ((flat-[] v proj₁flatv≡[]) ∷ flat-[]-us))
           (>-just (len-≡ len-|right-u|≡len-|right-v| (choice-rr u>v)) ) 
  where
    |right-u|≡[] : proj₁ (flat (RightU {l} {r} {loc} u)) ≡ []
    |right-u|≡[] with flat-[]→flat-[]-right {l} {r} {loc} {u} (flat-[] u proj₁flatu≡[])
    ... | flat-[] (RightU _)  proj₁flat-rightu≡[] = proj₁flat-rightu≡[] 
    |right-v|≡[] : proj₁ (flat (RightU {l} {r} {loc} v)) ≡ []
    |right-v|≡[] with flat-[]→flat-[]-right {l} {r} {loc} {v} (flat-[] v proj₁flatv≡[])
    ... | flat-[] (RightU _)  proj₁flat-rightv≡[] = proj₁flat-rightv≡[]
    |right-u|≡|right-v| : proj₁ (flat (RightU {l} {r} {loc} u)) ≡ proj₁ (flat (RightU {l} {r} {loc} v))
    |right-u|≡|right-v| rewrite |right-v|≡[] = proj₁flatu≡[]
    len-|right-u|≡len-|right-v| : length (proj₁ (flat (RightU {l} {r} {loc} u))) ≡ length (proj₁ (flat (RightU {l} {r} {loc} v)))
    len-|right-u|≡len-|right-v| rewrite |right-u|≡|right-v| = refl 
           



map-leftU-rightU-sorted : ∀ { l r : RE } { ε∈l : ε∈ l } { ε∈r : ε∈ r } { loc : ℕ }
  → ( us : List (U l) )
  → ( vs : List (U r) )
  → >-sorted {l} us   
  → >-sorted {r} vs
  → All (Flat-[] l) us   
  → All (Flat-[] r) vs  
  → >-sorted {l + r ` loc } ((List.map LeftU us) ++ (List.map RightU vs))
map-leftU-rightU-sorted               []  vs    >-sorted-l-[] >-sorted-r-vs _ flat-[]-vs = map-rightU-sorted vs >-sorted-r-vs flat-[]-vs
map-leftU-rightU-sorted {l} {r} {ε∈l} {ε∈r} {loc} us               []        >-sorted-l-us >-sorted-r-[] flat-[]-us flat-[]-vs rewrite (cong (λ x → >-sorted x) (++-identityʳ (List.map (LeftU {l} {r} {loc}) us)))
  = map-leftU-sorted us >-sorted-l-us flat-[]-us
map-leftU-rightU-sorted {l} {r} {ε∈l} {ε∈r} {loc} (u ∷ [])        (v ∷ vs) >-sorted-l-uus >-sorted-r-vs ((flat-[] _ proj₁flatu≡[]) ∷ []) ((flat-[] _ proj₁flatv≡[]) ∷ all-flat-[]-vs)
  = >-cons (map-rightU-sorted (v ∷ vs) >-sorted-r-vs ((flat-[] _ proj₁flatv≡[]) ∷ all-flat-[]-vs) ) (>-just (len-≡ len-|left-u|≡len-|right-v| (choice-lr (≤-reflexive (sym len-|left-u|≡len-|right-v|) ) ) ) )
  where
    |left-u|≡[] : proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ []
    |left-u|≡[] with flat-[]→flat-[]-left {l} {r} {loc} {u} (flat-[] u proj₁flatu≡[])
    ... | flat-[] (LeftU _)  proj₁flat-leftu≡[] = proj₁flat-leftu≡[] 
    |right-v|≡[] : proj₁ (flat (RightU {l} {r} {loc} v)) ≡ []
    |right-v|≡[] with flat-[]→flat-[]-right {l} {r} {loc} {v} (flat-[] v proj₁flatv≡[])
    ... | flat-[] (RightU _)  proj₁flat-rightv≡[] = proj₁flat-rightv≡[]
    |left-u|≡|right-v| : proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ proj₁ (flat (RightU {l} {r} {loc} v))
    |left-u|≡|right-v| rewrite |right-v|≡[] = proj₁flatu≡[]
    len-|left-u|≡len-|right-v| : length (proj₁ (flat (LeftU {l} {r} {loc} u))) ≡ length (proj₁ (flat (RightU {l} {r} {loc} v)))
    len-|left-u|≡len-|right-v| rewrite |left-u|≡|right-v| = refl
    len-|u|≡len-|v| : length (proj₁ (flat u)) ≡ length (proj₁ (flat v))
    len-|u|≡len-|v| rewrite (trans proj₁flatu≡[] (sym proj₁flatv≡[])) = refl 
  
map-leftU-rightU-sorted {l} {r} {ε∈l} {ε∈r} {loc} (u ∷ u' ∷ us)   (v ∷ vs) >-sorted-l-uuus >-sorted-r-vvs ((flat-[] _ proj₁flatu≡[]) ∷ (flat-[] _ proj₁flatu'≡[]) ∷ all-flat-[]-us) all-flat-[]-vvs  with >-sorted-l-uuus
... | >-cons {l} >-sorted-uus (>-just  u>u' )   =
  >-cons (map-leftU-rightU-sorted {l} {r} {ε∈l} {ε∈r} {loc} (u' ∷ us) (v ∷ vs)  >-sorted-uus  >-sorted-r-vvs ((flat-[] u' proj₁flatu'≡[]) ∷ all-flat-[]-us) all-flat-[]-vvs)
    ((>-just (len-≡ len-|left-u|≡len-|left-u'| (choice-ll  u>u') )) )
  where 
    |left-u|≡[] : proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ []
    |left-u|≡[] with flat-[]→flat-[]-left {l} {r} {loc} {u} (flat-[] u proj₁flatu≡[])
    ... | flat-[] (LeftU _)  proj₁flat-leftu≡[] = proj₁flat-leftu≡[] 
    |left-u'|≡[] : proj₁ (flat (LeftU {l} {r} {loc} u')) ≡ []
    |left-u'|≡[] with flat-[]→flat-[]-left {l} {r} {loc} {u'} (flat-[] u' proj₁flatu'≡[])
    ... | flat-[] (LeftU _)  proj₁flat-leftu'≡[] = proj₁flat-leftu'≡[]
    |left-u|≡|left-u'| : proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ proj₁ (flat (LeftU {l} {r} {loc} u'))
    |left-u|≡|left-u'| rewrite |left-u'|≡[] = proj₁flatu≡[]
    len-|left-u|≡len-|left-u'| : length (proj₁ (flat (LeftU {l} {r} {loc} u))) ≡ length (proj₁ (flat (LeftU {l} {r} {loc} u')))
    len-|left-u|≡len-|left-u'| rewrite |left-u|≡|left-u'| = refl 



map-pairU-empty-sorted : ∀ { l r : RE } { loc : ℕ }
  → ( us : List (U l) )
  → ( vs : List (U r) )
  → All (Flat-[] l) us
  → All (Flat-[] r) vs
  → >-sorted {l} us   
  → >-sorted {r} vs
  -------------------------------------------------------------------------------------------
  → >-sorted {l ● r ` loc } (List.foldr _++_ [] (List.map (λ u₁ → List.map (PairU u₁) vs) us))
map-pairU-empty-sorted  {l} {r} {loc} []        vs []                _              >-sorted-[]                 >-sorted-vs  = >-nil
map-pairU-empty-sorted  {l} {r} {loc} (u ∷ [])  vs (flat-[]-u ∷ _ )  all-flat-[]-vs (>-cons  >-nil >-nothing)   >-sorted-vs rewrite (cong (λ x → >-sorted x) (++-identityʳ (List.map (PairU {l} {r} {loc} u) vs)))  = map-pair-u-vs-sorted u flat-[]-u vs all-flat-[]-vs >-sorted-vs
  where
    map-pair-u-vs-sorted : ( u : U l ) → Flat-[] l u → ( vs : List (U r )) → All (Flat-[] r) vs → >-sorted {r} vs → >-sorted { l ● r ` loc } (List.map (PairU u) vs)
    map-pair-u-vs-sorted u _                     []         []  >-nil = >-nil
    map-pair-u-vs-sorted u (flat-[] _ flat-u≡[]) ( v ∷ vs ) ((flat-[] v flat-v≡[]) ∷ all-flat-[]-vs) (>-cons >-sorted-vs v>head-vs) with >-sorted-vs
    ... | >-nil          = >-cons (map-pair-u-vs-sorted u (flat-[] u flat-u≡[]) vs all-flat-[]-vs >-sorted-vs) >-nothing
    ... | >-cons  >-sorted-vs' v'>head-vs' with v>head-vs | all-flat-[]-vs 
    ...            | >-just {r} {_} {v'} v>v' | ((flat-[] v' flat-v'≡[]) ∷ all-flat-[]-vs')  = >-cons (map-pair-u-vs-sorted u (flat-[] u flat-u≡[]) vs all-flat-[]-vs  >-sorted-vs) (>-just (len-≡ len-|pairuv|≡len-|pair-uv'| (seq₂ refl v>v') ))
      where
        |pairuv|≡[] : proj₁ (flat (PairU {l} {r} {loc} u v)) ≡ []
        |pairuv|≡[] rewrite flat-u≡[] | flat-v≡[] = refl 
        |pairuv'|≡[] : proj₁ (flat (PairU {l} {r} {loc} u v')) ≡ []
        |pairuv'|≡[] rewrite flat-u≡[] | flat-v'≡[] = refl
        |pairuv|≡|pairuv'| : proj₁ (flat (PairU {l} {r} {loc} u v)) ≡  proj₁ (flat (PairU {l} {r} {loc} u v'))
        |pairuv|≡|pairuv'| rewrite |pairuv'|≡[] = |pairuv|≡[]
        len-|pairuv|≡len-|pair-uv'| : length (proj₁ (flat (PairU {l} {r} {loc} u v))) ≡ length (proj₁ (flat (PairU {l} {r} {loc} u v') ))
        len-|pairuv|≡len-|pair-uv'| rewrite |pairuv|≡|pairuv'| = refl 

map-pairU-empty-sorted  {l} {r} {loc} (u ∷ u' ∷ us)  vs (flat-[] u flat-u≡[] ∷ flat-[] u' flat-u'≡[] ∷ all-flat-[]-us) all-flat-[]-vs (>-cons >-sorted-uus (>-just u>u'))  >-sorted-vs
  = combine {u} {u'} {vs} {us} {vs} u>u' (flat-[] u flat-u≡[]) (flat-[] u' flat-u'≡[]) all-flat-[]-vs all-flat-[]-vs  (map-pair-u-vs-sorted u (flat-[] u flat-u≡[]) vs all-flat-[]-vs >-sorted-vs) ind-hyp
  where
    map-pair-u-vs-sorted : ( u : U l ) → Flat-[] l u → ( vs : List (U r )) → All (Flat-[] r) vs → >-sorted {r} vs → >-sorted { l ● r ` loc } (List.map (PairU u) vs)
    map-pair-u-vs-sorted u _                     []         []  >-nil = >-nil
    map-pair-u-vs-sorted u (flat-[] _ flat-u≡[]) ( v ∷ vs ) ((flat-[] v flat-v≡[]) ∷ all-flat-[]-vs) (>-cons >-sorted-vs v>head-vs) with >-sorted-vs
    ... | >-nil          = >-cons (map-pair-u-vs-sorted u (flat-[] u flat-u≡[]) vs all-flat-[]-vs >-sorted-vs) >-nothing
    ... | >-cons  >-sorted-vs' v'>head-vs' with v>head-vs | all-flat-[]-vs 
    ...            | >-just {r} {_} {v'} v>v' | ((flat-[] v' flat-v'≡[]) ∷ all-flat-[]-vs')  = >-cons (map-pair-u-vs-sorted u (flat-[] u flat-u≡[]) vs all-flat-[]-vs  >-sorted-vs) (>-just (len-≡ len-|pairuv|≡len-|pair-uv'| (seq₂ refl v>v') ))
      where
        |pairuv|≡[] : proj₁ (flat (PairU {l} {r} {loc} u v)) ≡ []
        |pairuv|≡[] rewrite flat-u≡[] | flat-v≡[] = refl 
        |pairuv'|≡[] : proj₁ (flat (PairU {l} {r} {loc} u v')) ≡ []
        |pairuv'|≡[] rewrite flat-u≡[] | flat-v'≡[] = refl
        |pairuv|≡|pairuv'| : proj₁ (flat (PairU {l} {r} {loc} u v)) ≡  proj₁ (flat (PairU {l} {r} {loc} u v'))
        |pairuv|≡|pairuv'| rewrite |pairuv'|≡[] = |pairuv|≡[]
        len-|pairuv|≡len-|pair-uv'| : length (proj₁ (flat (PairU {l} {r} {loc} u v))) ≡ length (proj₁ (flat (PairU {l} {r} {loc} u v') ))
        len-|pairuv|≡len-|pair-uv'| rewrite |pairuv|≡|pairuv'| = refl 


    ind-hyp : >-sorted {l ● r ` loc } (concatMap (λ u₁ → List.map (PairU u₁) vs) (u' ∷ us))
    ind-hyp = map-pairU-empty-sorted {l} {r} {loc} (u' ∷ us) vs (flat-[] u' flat-u'≡[] ∷ all-flat-[]-us) all-flat-[]-vs >-sorted-uus >-sorted-vs

    -- we need to generalize the input vs
    -- `ts` as the duplicated generalized vs, which can be inductively reduced w/o affecting the concatMap (map (PairU u) vs) (u' ∷ us) bit
    -- all the uses of concatMap have been desugared into foldr _++_ [] (map ... )
    combine   :  { u u' : U l } { ts : List (U r) }  { us : List (U l) } { vs : List (U r)  }
              →   l ⊢ u > u'
              →   Flat-[] l u
              →   Flat-[] l u'
              →   All (Flat-[] r) ts 
              →   All (Flat-[] r) vs 
              →   >-sorted {l ● r ` loc } (List.map (PairU {l} {r} {loc} u) ts)
              →   >-sorted {l ● r ` loc } (List.foldr _++_ [] (List.map (λ u₁ → List.map (PairU u₁) vs) (u' ∷ us)))
            -----------------------------------------------------------------------------------
              →   >-sorted {l ● r ` loc } ((List.map (PairU {l} {r} {loc} u) ts)  ++ (List.foldr _++_ [] (List.map (λ u₁ → List.map (PairU u₁) vs) (u' ∷ us))))
    combine {u} {u'} {[]}      {us} {[]}     u>u' _ _                                          _ _  >-nil                                              >-sorted-ys = >-sorted-ys
    combine {u} {u'} {[]}      {us} {vs}     u>u' _ _                                          _ _  >-nil                                              >-sorted-ys = >-sorted-ys
    combine {u} {u'} {t ∷ []} {us} {v ∷ vs} u>u'  (flat-[] _ flat-u≡[]) (flat-[] _ flat-u'≡[]) ((flat-[] _ flat-t≡[]) ∷ _)  ((flat-[] _ flat-v≡[]) ∷ all-flat-[]-vs) (>-cons >-sorted-map-pair-u-ts u-t>head-map-pair-u-ts)  >-sorted-ys = 
      >-cons  >-sorted-ys (>-just  (len-≡ len-|pairut|≡len-|pair-u'v| (seq₁ u>u') ))
      where
        |pairut|≡[] : proj₁ (flat (PairU {l} {r} {loc} u t)) ≡ []
        |pairut|≡[] rewrite flat-u≡[] | flat-t≡[] = refl 
        |pairu'v|≡[] : proj₁ (flat (PairU {l} {r} {loc} u' v)) ≡ []
        |pairu'v|≡[] rewrite flat-u'≡[] | flat-v≡[] = refl
        |pairut|≡|pairu'v| : proj₁ (flat (PairU {l} {r} {loc} u t)) ≡  proj₁ (flat (PairU {l} {r} {loc} u' v))
        |pairut|≡|pairu'v| rewrite |pairu'v|≡[] = |pairut|≡[]
        len-|pairut|≡len-|pair-u'v| : length (proj₁ (flat (PairU {l} {r} {loc} u t))) ≡ length (proj₁ (flat (PairU {l} {r} {loc} u' v) ))
        len-|pairut|≡len-|pair-u'v| rewrite |pairut|≡|pairu'v| = refl 
        
    combine {u} {u'} {t ∷ t' ∷ ts} {us} {vs} u>u' (flat-[] _ flat-u≡[]) (flat-[] _ flat-u'≡[]) (flat-[]-t ∷ all-flat-t'ts)  all-flat-vs                              (>-cons >-sorted-map-pair-u-tts u-t>head-map-pair-u-tts) >-sorted-ys =
      >-cons  ind-hyp' u-t>head-map-pair-u-tts
      where
        ind-hyp' : >-sorted {l ● r ` loc } ((List.map (PairU {l} {r} {loc} u) (t' ∷ ts))  ++ (List.foldr _++_ [] (List.map (λ u₁ → List.map (PairU u₁) vs) (u' ∷ us))))
        ind-hyp' = combine {u} {u'} {t' ∷ ts} {us} {vs} u>u' (flat-[] _ flat-u≡[]) (flat-[] _ flat-u'≡[]) all-flat-t'ts all-flat-vs  >-sorted-map-pair-u-tts >-sorted-ys
    -- the following is impossible to be reached actually, since ts is a subfix of vs
    combine {u} {u'} {t ∷ []}   {us}  {[]}    u>u' (flat-[] _ flat-u≡[]) (flat-[] _ flat-u'≡[]) ((flat-[] _ flat-t≡[]) ∷ _) []  >-sorted-xs  >-sorted-ys
      rewrite (cong (λ x → >-sorted (List.map (PairU {l} {r} {loc} u) (t ∷ []) ++ x )) (foldr++ys-map-λ_→[]-xs≡ys us []) )
      | (cong (λ x → >-sorted x) ( ++-identityʳ (List.map (PairU {l} {r} {loc} u) (t ∷ [])) ))                                   = >-sorted-xs




-----------------------------------------------------------------------------
-- Sub Lemma 31.1 - 31.4  END
----------------------------------------------------------------------------

```

#### Main proof for Lemma 31

```agda

-- main lemma and its proof
mkAllEmptyU-sorted : ∀ { r : RE }
  → ( ε∈r : ε∈ r)
  → >-sorted (mkAllEmptyU {r} ε∈r) 
mkAllEmptyU-sorted {$ c ` loc }         = λ()
mkAllEmptyU-sorted {ε}             ε∈ε = >-cons >-nil >-nothing 
mkAllEmptyU-sorted {r * nε ` loc}  ε∈* = >-cons >-nil >-nothing 
mkAllEmptyU-sorted {l + r  ` loc}  (ε∈ ε∈l <+ ε∉r) = map-leftU-sorted es ind-hyp  (mkAllEmptyU-sound {l} ε∈l) 
  where
    es : List (U l)
    es = mkAllEmptyU ε∈l 
    ind-hyp : >-sorted  (mkAllEmptyU ε∈l)
    ind-hyp = mkAllEmptyU-sorted {l} ε∈l
mkAllEmptyU-sorted {l + r  ` loc}  (ε∈ ε∉l +> ε∈r) = map-rightU-sorted es ind-hyp (mkAllEmptyU-sound {r} ε∈r) 
  where
    es : List (U r)
    es = mkAllEmptyU ε∈r 
    ind-hyp : >-sorted  (mkAllEmptyU ε∈r)
    ind-hyp = mkAllEmptyU-sorted {r} ε∈r
mkAllEmptyU-sorted {l + r  ` loc}  (ε∈ ε∈l + ε∈r) =  map-leftU-rightU-sorted {l} {r} {ε∈l} {ε∈r} {loc} l-es r-es l-ind-hyp r-ind-hyp (mkAllEmptyU-sound {l} ε∈l) (mkAllEmptyU-sound {r} ε∈r)
  where
    r-es : List (U r)
    r-es = mkAllEmptyU ε∈r 
    r-ind-hyp : >-sorted  (mkAllEmptyU ε∈r)
    r-ind-hyp = mkAllEmptyU-sorted {r} ε∈r

    l-es : List (U l)
    l-es = mkAllEmptyU ε∈l
    l-ind-hyp : >-sorted  (mkAllEmptyU ε∈l)
    l-ind-hyp = mkAllEmptyU-sorted {l} ε∈l
mkAllEmptyU-sorted {l ● r ` loc }  (ε∈ ε∈l ● ε∈r ) = map-pairU-empty-sorted l-es r-es (mkAllEmptyU-sound {l} ε∈l) (mkAllEmptyU-sound {r} ε∈r) l-ind-hyp r-ind-hyp
  where
    r-es : List (U r)
    r-es = mkAllEmptyU ε∈r 
    r-ind-hyp : >-sorted  (mkAllEmptyU ε∈r)
    r-ind-hyp = mkAllEmptyU-sorted {r} ε∈r


    l-es : List (U l)
    l-es = mkAllEmptyU ε∈l
    l-ind-hyp : >-sorted  (mkAllEmptyU ε∈l)
    l-ind-hyp = mkAllEmptyU-sorted {l} ε∈l
```


### Definition 32: >-Strict increasing PDInstance

Let r be a non problematic regular expression.
Let c be a letter.
Let pdi be a PDInstance  w.r.t r and c.
We say pdi is >-inc (strict increasing) iff, 
  1. p is the partial derivative inhabited in pdi, and
  2. inj is the injection function from parse trees of p to parse trees of r.
  3. for all parse trees of p, u₁ and u₂  where p ⊢ u₁ > u₂
  Then r ⊢ inj u₁ > inj u₂ 

```agda

data >-Inc : ∀ { r : RE } { c : Char } →  PDInstance r c  → Set where
  >-inc : ∀ { p r : RE } { c : Char } { inj : U p →  U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( (u₁ : U p) → (u₂ : U p)
        →  p ⊢ u₁ > u₂  → r ⊢ inj u₁ > inj u₂ ) -- strict increasing evidence 
    → >-Inc {r} {c} (pdinstance {p} {r} {c} inj sound-ev)
```

### Lemma 33: all pdinstances from pdU[ r , c ] are >-strict increasing .

Let r be a  non problematic regular expression.
Let c be a letter.
Then for all pdi ∈ pdU[ r , c], pdi is >-strict increasing .



#### Sub Lemma 33.1 - 33.9 : >-Inc is preserved inductively by the pdinstance operations. 

```agda
-----------------------------------------------------------------------------
-- Sub Lemma 33.1 - 33.9  BEGIN
-----------------------------------------------------------------------------


>-inc-map-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( pdis : List (PDInstance l c) )
    → All (>-Inc {l} {c}) pdis
    → All (>-Inc {l + r ` loc } {c}) (List.map pdinstance-left pdis)
>-inc-map-left [] [] = []
>-inc-map-left {l} {r} {loc} {c} ((pdinstance {p} {l} {c}  inj sound-ev) ∷ pdis)
  (>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ ∷ pxs)
  = >-inc >-inc-ev   ∷ >-inc-map-left pdis pxs
  where

    len-|inj-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (inj u))) ≡ suc (length (proj₁ (flat u)))
    len-|inj-u|≡len-|u|+1 u rewrite (sound-ev u) = refl 

    >-inc-ev : ∀ (u₁ : U p)
              → (u₂ : U p)
              → p ⊢ u₁ > u₂
              --------------
              → (l + r ` loc) ⊢ LeftU (inj u₁) > LeftU (inj u₂)
    >-inc-ev u₁ u₂ (len-> len|u₁|>len|u₂|) = len-> len-|left-inj-u₁|>len-|left-inj-u₂|
      where
        |left-inj-u₁|≡|inj-u₁| : proj₁ (flat (LeftU {l} {r} {loc} (inj u₁))) ≡ proj₁ (flat (inj u₁))
        |left-inj-u₁|≡|inj-u₁| = refl
        |left-inj-u₂|≡|inj-u₂| : proj₁ (flat (LeftU {l} {r} {loc} (inj u₂))) ≡ proj₁ (flat (inj u₂))
        |left-inj-u₂|≡|inj-u₂| = refl
  
        len-|left-inj-u₁|>len-|left-inj-u₂| : length (proj₁ (flat (LeftU {l} {r} {loc} (inj u₁)))) > length (proj₁ (flat (LeftU {l} {r} {loc} (inj u₂))))
        len-|left-inj-u₁|>len-|left-inj-u₂| rewrite |left-inj-u₁|≡|inj-u₁| | |left-inj-u₂|≡|inj-u₂| | len-|inj-u|≡len-|u|+1 u₁ | len-|inj-u|≡len-|u|+1 u₂ = Nat.s≤s len|u₁|>len|u₂| 


    >-inc-ev u₁ u₂ (len-≡ len|u₁|≡len|u₂| u₁>ⁱu₂) =
      let inj-u₁>inj-u₂ = u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂  (len-≡ len|u₁|≡len|u₂| u₁>ⁱu₂)
      in (len-≡ len-|left-inj-u₁|≡len-|left-inj-u₂| (choice-ll  inj-u₁>inj-u₂) )
      where
        |left-inj-u₁|≡|inj-u₁| : proj₁ (flat (LeftU {l} {r} {loc} (inj u₁))) ≡ proj₁ (flat (inj u₁))
        |left-inj-u₁|≡|inj-u₁| = refl
        |left-inj-u₂|≡|inj-u₂| : proj₁ (flat (LeftU {l} {r} {loc} (inj u₂))) ≡ proj₁ (flat (inj u₂))
        |left-inj-u₂|≡|inj-u₂| = refl

        len-|left-inj-u₁|≡len-|left-inj-u₂| : length (proj₁ (flat (LeftU {l} {r} {loc} (inj u₁)))) ≡ length (proj₁ (flat (LeftU {l} {r} {loc} (inj u₂))))
        len-|left-inj-u₁|≡len-|left-inj-u₂| rewrite |left-inj-u₁|≡|inj-u₁| | |left-inj-u₂|≡|inj-u₂| | len-|inj-u|≡len-|u|+1 u₁ | len-|inj-u|≡len-|u|+1 u₂ = cong suc len|u₁|≡len|u₂|  



>-inc-map-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( pdis : List (PDInstance r c) )
    → All (>-Inc {r} {c}) pdis
    → All (>-Inc {l + r ` loc } {c}) (List.map pdinstance-right pdis)
>-inc-map-right [] [] = []
>-inc-map-right {l} {r} {loc} {c} ((pdinstance {p} {r} {c}  inj sound-ev) ∷ pdis)
  (>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ ∷ pxs)
  = >-inc >-inc-ev   ∷ >-inc-map-right pdis pxs
  where

    len-|inj-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (inj u))) ≡ suc (length (proj₁ (flat u)))
    len-|inj-u|≡len-|u|+1 u rewrite (sound-ev u) = refl 

    >-inc-ev : ∀ (u₁ : U p)
              → (u₂ : U p)
              → p ⊢ u₁ > u₂
              --------------
              → (l + r ` loc) ⊢ RightU (inj u₁) > RightU (inj u₂)
    >-inc-ev u₁ u₂ (len-> len|u₁|>len|u₂|) = len-> len-|right-inj-u₁|>len-|right-inj-u₂|
      where
        |right-inj-u₁|≡|inj-u₁| : proj₁ (flat (RightU {l} {r} {loc} (inj u₁))) ≡ proj₁ (flat (inj u₁))
        |right-inj-u₁|≡|inj-u₁| = refl
        |right-inj-u₂|≡|inj-u₂| : proj₁ (flat (RightU {l} {r} {loc} (inj u₂))) ≡ proj₁ (flat (inj u₂))
        |right-inj-u₂|≡|inj-u₂| = refl
  
        len-|right-inj-u₁|>len-|right-inj-u₂| : length (proj₁ (flat (RightU {l} {r} {loc} (inj u₁)))) > length (proj₁ (flat (RightU {l} {r} {loc} (inj u₂))))
        len-|right-inj-u₁|>len-|right-inj-u₂| rewrite |right-inj-u₁|≡|inj-u₁| | |right-inj-u₂|≡|inj-u₂| | len-|inj-u|≡len-|u|+1 u₁ | len-|inj-u|≡len-|u|+1 u₂ = Nat.s≤s len|u₁|>len|u₂| 


    >-inc-ev u₁ u₂ (len-≡ len|u₁|≡len|u₂| u₁>ⁱu₂) =
      let inj-u₁>inj-u₂ = u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂  (len-≡ len|u₁|≡len|u₂| u₁>ⁱu₂)
      in (len-≡ len-|right-inj-u₁|≡len-|right-inj-u₂| (choice-rr  inj-u₁>inj-u₂) )
      where
        |right-inj-u₁|≡|inj-u₁| : proj₁ (flat (RightU {l} {r} {loc} (inj u₁))) ≡ proj₁ (flat (inj u₁))
        |right-inj-u₁|≡|inj-u₁| = refl
        |right-inj-u₂|≡|inj-u₂| : proj₁ (flat (RightU {l} {r} {loc} (inj u₂))) ≡ proj₁ (flat (inj u₂))
        |right-inj-u₂|≡|inj-u₂| = refl

        len-|right-inj-u₁|≡len-|right-inj-u₂| : length (proj₁ (flat (RightU {l} {r} {loc} (inj u₁)))) ≡ length (proj₁ (flat (RightU {l} {r} {loc} (inj u₂))))
        len-|right-inj-u₁|≡len-|right-inj-u₂|
          rewrite |right-inj-u₁|≡|inj-u₁| | |right-inj-u₂|≡|inj-u₂| | len-|inj-u|≡len-|u|+1 u₁ | len-|inj-u|≡len-|u|+1 u₂ = cong suc len|u₁|≡len|u₂|  




>-inc-map-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
               → ( pdis : List (PDInstance l c ) )
               → All (>-Inc {l} {c}) pdis
               → All (>-Inc {l ● r ` loc} {c}) (List.map (pdinstance-fst {l} {r} {loc} {c}) pdis)
>-inc-map-fst [] [] = []

>-inc-map-fst {l} {r} {loc} {c} ((pdinstance {p} {l} {c}  inj sound-ev) ∷ pdis) (>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ ∷ pxs)
  = (>-inc >-inc-ev)  ∷  >-inc-map-fst pdis pxs
  where
    injFst : U (p ● r ` loc)   → U (l ● r ` loc ) -- the p can only be seq ε or ● 
    injFst = mkinjFst inj

    len-|inj-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (inj u))) ≡ suc (length (proj₁ (flat u)))
    len-|inj-u|≡len-|u|+1 u rewrite (sound-ev u) = refl 

    len-|injFst-pair-uv|≡len-|pair-uv|+1 : (u : U p) → (v : U r) → length (proj₁ (flat ((PairU {l} {r} {loc} (inj u) v)))) ≡ suc (length (proj₁ (flat (PairU {p} {r} {loc} u v))))
    len-|injFst-pair-uv|≡len-|pair-uv|+1 u v rewrite (sound-ev u) = refl 
    
    >-inc-ev : ∀ (uv₁ : U ( p ● r ` loc ))
              → (uv₂ : U ( p ● r ` loc ))
              → (p ● r ` loc )  ⊢ uv₁ > uv₂
              ------------------------------------
              → (l ● r ` loc) ⊢ (injFst uv₁) > (injFst uv₂)

    >-inc-ev (PairU u₁ v₁)  (PairU u₂ v₂) (len-> len|pair-u₁v₁|>len|pair-u₂v₂|) = len-> len-|injFst-pair-u₁v₁|>len-|injFst-pair-u₂v₂|
      where
        len-|injFst-pair-u₁v₁|>len-|injFst-pair-u₂v₂| : length (proj₁ (flat (PairU {l} {r} {loc}  (inj u₁) v₁))) > length (proj₁ (flat (PairU {l} {r} {loc} (inj u₂) v₂)))
        len-|injFst-pair-u₁v₁|>len-|injFst-pair-u₂v₂| rewrite (len-|injFst-pair-uv|≡len-|pair-uv|+1 u₁ v₁) | (len-|injFst-pair-uv|≡len-|pair-uv|+1 u₂ v₂) = Nat.s≤s len|pair-u₁v₁|>len|pair-u₂v₂| 
      
    >-inc-ev (PairU u₁ v₁)  (PairU u₂ v₂) (len-≡ len|pair-u₁v₁|≡len|pair-u₂v₂| (seq₁  u₁>u₂)) = 
      let inj-u₁>inj-u₂ = u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ u₁>u₂
      in (len-≡ len-|injFst-pair-u₁v₁|>len≡|injFst-pair-u₂v₂| (seq₁ inj-u₁>inj-u₂))
      where
        len-|injFst-pair-u₁v₁|>len≡|injFst-pair-u₂v₂| : length (proj₁ (flat (PairU {l} {r} {loc}  (inj u₁) v₁))) ≡ length (proj₁ (flat (PairU {l} {r} {loc} (inj u₂) v₂)))
        len-|injFst-pair-u₁v₁|>len≡|injFst-pair-u₂v₂| rewrite (len-|injFst-pair-uv|≡len-|pair-uv|+1 u₁ v₁) | (len-|injFst-pair-uv|≡len-|pair-uv|+1 u₂ v₂) = cong suc len|pair-u₁v₁|≡len|pair-u₂v₂|  

    >-inc-ev (PairU u₁ v₁)  (PairU u₂ v₂) (len-≡ len|pair-u₁v₁|≡len|pair-u₂v₂| (seq₂  u₁≡u₂ v₁>v₂ )) = len-≡ len-|injFst-pair-u₁v₁|>len≡|injFst-pair-u₂v₂| (seq₂ inj-u₁≡inj-u₂ v₁>v₂)  
      where
        len-|injFst-pair-u₁v₁|>len≡|injFst-pair-u₂v₂| : length (proj₁ (flat (PairU {l} {r} {loc}  (inj u₁) v₁))) ≡ length (proj₁ (flat (PairU {l} {r} {loc} (inj u₂) v₂)))
        len-|injFst-pair-u₁v₁|>len≡|injFst-pair-u₂v₂| rewrite (len-|injFst-pair-uv|≡len-|pair-uv|+1 u₁ v₁) | (len-|injFst-pair-uv|≡len-|pair-uv|+1 u₂ v₂) = cong suc len|pair-u₁v₁|≡len|pair-u₂v₂| 
        inj-u₁≡inj-u₂ : inj u₁ ≡ inj u₂ 
        inj-u₁≡inj-u₂ = cong inj u₁≡u₂
