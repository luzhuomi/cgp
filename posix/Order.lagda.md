```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.Order where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ∷-inj  ;
  w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ ;
  w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ ;
  ¬m>n→n≡m⊎n>m 
  {- ; ¬≡[]→¬length≡0 ; ¬≡0→>0 ; []→length≡0  ; ¬0>0 -}  )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;
  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ;
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
  compose-pdi-with 
  ) 



import cgp.posix.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; pdUConcat ;
  pdUMany[_,_]; pdUMany-aux ;
  pdinstance-oplus ; fuse ; mkfuseInj ;
  advance-pdi*-with-c
  )



import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _>_ ; _≥_ ; _≤_  ; _+_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ;
  length-++ 
  -- ; length-++-sucʳ -- this is only available after v2.3
  )


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

-- TODO: greedy order can be adjusted into this 2-level style, can lne order be adjusted in this 2-level style?
-- if yes, the robustness check will be easier to establish.
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
    → length (proj₁ (flat v₁)) ≥ length (proj₁ (flat v₂))                -- is this check redunant? if we come from the top level >, the length of both parse trees must be same
    -------------------------------------------------------------------    
    → ( l + r ` loc ) ⊢ (LeftU v₁) >ⁱ (RightU v₂)


  choice-rl : ∀ { l r : RE } { loc : ℕ } { v₁ : U r } { v₂ : U l }       -- is this rule reduant? if we come from the top level >, the length of both parse trees must be same
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
  ps : ∀ { w₁ w₂ w : List Char } { l r : RE } { loc : ℕ } { v₁ : U l } { v₂ : U r }
    →  w ≡ w₁ ++ w₂  -- having a separate index variable w make the proof easier  
    →  w₁ , l ⇒ v₁
    →  w₂ , r ⇒ v₂
    → ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) × (w₃ ++ w₄ ≡ w₂) × ( (w₁ ++ w₃) ∈⟦ l ⟧ ) × w₄ ∈⟦ r ⟧ )
    -----------------s-------------------------------------------
    → w , l ● r ` loc ⇒ PairU v₁ v₂
    
  p[] : ∀ { r : RE } {ε∉r : ε∉ r } { loc : ℕ }
    → [] , r * ε∉r ` loc ⇒ ListU []
    
  p* : ∀ { w₁ w₂ w : List Char } { r : RE } {ε∉r : ε∉ r } { loc : ℕ } {v : U r } { vs : List (U r) }
    →  w ≡ w₁ ++ w₂  -- having a separate index variable w make the proof easier
    →  w₁ , r ⇒ v
    →  w₂ , r * ε∉r ` loc ⇒ ListU vs
    →  ¬ w₁ ≡ []
    → ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) × (w₃ ++ w₄ ≡ w₂) × ( (w₁ ++ w₃) ∈⟦ r ⟧ ) × w₄ ∈⟦ r * ε∉r ` loc ⟧ )
    -----------------------------------------------------------
    → w , r * ε∉r ` loc ⇒ ListU (v ∷ vs)
    
```




```agda

{-
len|ys|≥len|zs|→len|xs++ys|≥len|xs++zs| : ∀ { A : Set } { xs ys zs : List A }
  → length ys ≥ length zs
  -----------------------------------
  → length (xs ++ ys) ≥ length (xs ++ zs)
len|ys|≥len|zs|→len|xs++ys|≥len|xs++zs| {A} {[]}        {ys} {zs} len-ys≥len-zs = len-ys≥len-zs
len|ys|≥len|zs|→len|xs++ys|≥len|xs++zs| {A} {(x ∷ xs)} {ys} {zs} len-ys≥len-zs = Nat.s≤s (len|ys|≥len|zs|→len|xs++ys|≥len|xs++zs| {A} {xs} {ys} {zs}  len-ys≥len-zs) 

-}


len|ys|>len|zs|→len|xs++ys|>len|xs++zs|ʳ : ∀ { A : Set } { xs ys zs : List A }
  → length ys > length zs
  -----------------------------------
  → length (xs ++ ys) > length (xs ++ zs)
len|ys|>len|zs|→len|xs++ys|>len|xs++zs|ʳ {A} {[]}       {ys} {zs} len-ys>len-zs = len-ys>len-zs
len|ys|>len|zs|→len|xs++ys|>len|xs++zs|ʳ {A} {(x ∷ xs)} {ys} {zs} len-ys>len-zs = Nat.s≤s (len|ys|>len|zs|→len|xs++ys|>len|xs++zs|ʳ {A} {xs} {ys} {zs}  len-ys>len-zs) 


-- this is copied from stdlib Data.List.Properties 2.3
length-++-sucʳ : ∀ {A : Set} (xs : List A) (y : A) (ys : List A) →
                 length (xs ++ y ∷ ys) ≡ suc (length (xs ++ ys))
length-++-sucʳ []       _ _  = refl
length-++-sucʳ (_ ∷ xs) y ys = cong suc (length-++-sucʳ xs y ys)

len|xs|>len|ys|→len|xs++zs|>len|ys++zs|ˡ : ∀ { A : Set } { xs ys zs : List A }
  → length xs > length ys
  -----------------------------------
  → length (xs ++ zs) > length (ys ++ zs)
len|xs|>len|ys|→len|xs++zs|>len|ys++zs|ˡ {A} {xs} {ys} {[]} len-xs>len-ys rewrite ++-identityʳ xs | ++-identityʳ ys  = len-xs>len-ys
len|xs|>len|ys|→len|xs++zs|>len|ys++zs|ˡ {A} {xs} {ys} {z ∷ zs} len-xs>len-ys rewrite length-++-sucʳ xs z zs | length-++-sucʳ ys z zs  =  Nat.s≤s (len|xs|>len|ys|→len|xs++zs|>len|ys++zs|ˡ {A} {xs} {ys} {zs}  len-xs>len-ys)  





len|ys|≡len|zs|→len|xs++ys|≡len|xs++zs| : ∀ { A : Set } { xs ys zs : List A }
  → length ys ≡ length zs
  -----------------------------------
  → length (xs ++ ys) ≡ length (xs ++ zs)
len|ys|≡len|zs|→len|xs++ys|≡len|xs++zs| {A} {[]}     {ys} {zs} len-|ys|≡len-|zs| = len-|ys|≡len-|zs| 
len|ys|≡len|zs|→len|xs++ys|≡len|xs++zs| {A} {x ∷ xs} {ys} {zs} len-|ys|≡len-|zs| = cong suc (len|ys|≡len|zs|→len|xs++ys|≡len|xs++zs| {A} {xs} {ys} {zs} len-|ys|≡len-|zs|) 




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


>-trans {r} {u₁} {u₂} {u₃} (len-≡ {r} {v₁} {v₂} len-|v₁|≡len-|v₂| v₁>ⁱv₂) (len-≡ {r} .{v₂} {v₃} len-|v₂|≡len-|v₃| v₂>ⁱv₃) =
  len-≡ {r} {v₁} {v₃} (trans len-|v₁|≡len-|v₂| len-|v₂|≡len-|v₃|) (>ⁱ-trans v₁>ⁱv₂ v₂>ⁱv₃)
>-trans {r} {u₁} {u₂} {u₃} (len-≡ {r} {v₁} {v₂} len-|v₁|≡len-|v₂| v₁>ⁱv₂) (len-> {r} .{v₂} {v₃} len-|v₂|>len-|v₃|) = 
  len-> {r} {v₁} {v₃} len-|v₁|>len|v₃|
  where
    len-|v₁|>len|v₃| : length (proj₁ (flat u₁)) > length (proj₁ (flat u₃))
    len-|v₁|>len|v₃| rewrite  len-|v₁|≡len-|v₂| = len-|v₂|>len-|v₃| 
>-trans {r} {u₁} {u₂} {u₃} (len-> {r} {v₁} {v₂} len-|v₁|>len-|v₂|) (len-> {r} .{v₂} {v₃} len-|v₂|>len-|v₃|) = len-> {r} {v₁} {v₃} (<-trans len-|v₂|>len-|v₃| len-|v₁|>len-|v₂| )
>-trans {r} {u₁} {u₂} {u₃} (len-> {r} {v₁} {v₂} len-|v₁|>len-|v₂|) (len-≡ {r} .{v₂} {v₃} len-|v₂|≡len-|v₃|  v₂>ⁱv₃) = len-> {r} {v₁} {v₃} len-|v₁|>len|v₃|
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
>ⁱ-trans {l + r ` loc} (choice-ll {l} {r} .{loc} {v₁} {v₂} v₁>v₂) (choice-lr {l} {r} .{loc} .{v₂} {v₃} len|v₂|≥len|v₃|) = choice-lr ( ≤-trans len|v₂|≥len|v₃| ( >→len|≥| v₁>v₂) ) 
>ⁱ-trans {l + r ` loc} (choice-ll {l} {r} .{loc} {v₁} {v₂} v₁>v₂) (choice-ll {l} {r} .{loc} .{v₂} {v₃} v₂>v₃)     = choice-ll (>-trans v₁>v₂ v₂>v₃)
>ⁱ-trans {l + r ` loc} (choice-lr {l} {r} .{loc} {v₁} {v₂} len|v₁|≥len|v₂|) (choice-rr {l} {r} .{loc} .{v₂} {v₃} v₂>v₃) = choice-lr ( ≤-trans (>→len|≥| v₂>v₃) len|v₁|≥len|v₂| )
>ⁱ-trans {l + r ` loc} (choice-lr {l} {r} .{loc} {v₁} {v₂} len|v₁|≥len|v₂|) (choice-rl {l} {r} .{loc} .{v₂} {v₃} len|v₂|>len|v₃|) = choice-ll (len|>|→> len|v₁|>len|v₃| )
  where
    len|v₁|>len|v₃| : length (proj₁ (flat v₁)) > length (proj₁ (flat v₃))
    len|v₁|>len|v₃| = ≤-trans len|v₂|>len|v₃| len|v₁|≥len|v₂|  

>ⁱ-trans {l + r ` loc} (choice-rr {l} {r} .{loc} {v₁} {v₂} v₁>v₂) (choice-rr {l} {r} .{loc} .{v₂} {v₃} v₂>v₃)     = choice-rr (>-trans v₁>v₂ v₂>v₃)
>ⁱ-trans {l + r ` loc} (choice-rr {l} {r} .{loc} {v₁} {v₂} v₁>v₂) (choice-rl {l} {r} .{loc} .{v₂} {v₃} len|v₂|>len|v₃|) =  choice-rl ( ≤-trans len|v₂|>len|v₃| (>→len|≥| v₁>v₂ ) ) 
>ⁱ-trans {l + r ` loc} (choice-rl {l} {r} .{loc} {v₁} {v₂} len|v₁|>len|v₂|) (choice-lr {l} {r} .{loc} .{v₂} {v₃} len|v₂|≥len|v₃|) = choice-rr (len|>|→> (≤-trans (Nat.s≤s len|v₂|≥len|v₃|)  len|v₁|>len|v₂|) )
>ⁱ-trans {l + r ` loc} (choice-rl {l} {r} .{loc} {v₁} {v₂} len|v₁|>len|v₂|) (choice-ll {l} {r} .{loc} .{v₂} {v₃} v₂>v₃) = choice-rl ( ≤-trans (Nat.s≤s (>→len|≥| v₂>v₃ )) len|v₁|>len|v₂| )
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
>ⁱ→¬≡ {r * ε∉r ` loc} {ListU (u ∷ us)} {ListU (v ∷ vs)} (star-head u>v) = λ list-u∷us≡list-v∷vs → ¬u≡v (proj₁ (inv-listU u us v vs list-u∷us≡list-v∷vs)) 
  where
    ¬u≡v : ¬ u ≡ v
    ¬u≡v = >→¬≡ {r} {u} {v} u>v
>ⁱ→¬≡ {r * ε∉r ` loc} {ListU (u ∷ us)} {ListU (v ∷ vs)} (star-tail u≡v list-us>list-vs) = λ list-u∷us≡list-v∷vs → ¬us≡vs (proj₂ (inv-listU u us v vs list-u∷us≡list-v∷vs))
  where
    ¬list-us≡list-vs : ¬ (ListU us) ≡ (ListU vs)
    ¬list-us≡list-vs = >→¬≡ {r * ε∉r ` loc} {ListU us} {ListU vs} list-us>list-vs

    ¬us≡vs : ¬ us ≡ vs
    ¬us≡vs us≡vs = ¬list-us≡list-vs list-us≡list-vs
      where
        list-us≡list-vs : (ListU {r} {ε∉r} {loc} us) ≡ (ListU {r} {ε∉r} {loc} vs)
        list-us≡list-vs rewrite (cong (λ x → ListU {r} {ε∉r} {loc} x) us≡vs ) = refl 
>ⁱ→¬≡ {l ● r ` loc} {PairU u₁ u₂} {PairU v₁ v₂} (seq₁ u₁>v₁) = λ pair-u₁u₂≡pair-v₁v₂ → ¬u₁≡v₁ (proj₁ (inv-pairU u₁ u₂ v₁ v₂ pair-u₁u₂≡pair-v₁v₂))
  where
    ¬u₁≡v₁ : ¬ u₁ ≡ v₁
    ¬u₁≡v₁ = >→¬≡ {l} {u₁} {v₁} u₁>v₁
>ⁱ→¬≡ {l ● r ` loc} {PairU u₁ u₂} {PairU v₁ v₂} (seq₂ u₁≡v₁ u₂>v₂) = λ pair-u₁u₂≡pair-v₁v₂ → ¬u₂≡v₂ (proj₂ (inv-pairU u₁ u₂ v₁ v₂ pair-u₁u₂≡pair-v₁v₂))
  where
    ¬u₂≡v₂ : ¬ u₂ ≡ v₂
    ¬u₂≡v₂ = >→¬≡ {r} {u₂} {v₂} u₂>v₂
>ⁱ→¬≡ {l + r ` loc} {LeftU u} {RightU v} _  = λ ()
>ⁱ→¬≡ {l + r ` loc} {RightU u} {LeftU v} _  = λ ()
>ⁱ→¬≡ {l + r ` loc} {LeftU u} {LeftU v} (choice-ll u>v)  = λ left-u≡left-v →  ¬u≡v (inv-leftU u v left-u≡left-v)
  where 
    ¬u≡v : ¬ u ≡ v
    ¬u≡v = >→¬≡ {l} {u} {v} u>v
>ⁱ→¬≡ {l + r ` loc} {RightU u} {RightU v} (choice-rr u>v)  = λ right-u≡right-v →  ¬u≡v (inv-rightU u v right-u≡right-v)
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



#### Sub Lemma 33.1 - 33.19 : >-Inc is preserved inductively by the pdinstance operations. 

```agda
-----------------------------------------------------------------------------
-- Sub Lemma 33.1 - 33.19  BEGIN
-----------------------------------------------------------------------------


>-inc-left : ∀ {l r : RE } { loc : ℕ } { c : Char }
  → (pdi : PDInstance l c )
  → >-Inc {l} {c} pdi
  → >-Inc {l + r ` loc } {c} (pdinstance-left pdi)
>-inc-left {l} {r} {loc} {c} (pdinstance {p} {l} {c}  inj sound-ev)
  (>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) = >-inc >-inc-ev
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
  

>-inc-map-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( pdis : List (PDInstance l c) )
    → All (>-Inc {l} {c}) pdis
    → All (>-Inc {l + r ` loc } {c}) (List.map pdinstance-left pdis)
>-inc-map-left [] [] = []
>-inc-map-left {l} {r} {loc} {c} (pdi ∷ pdis) (>-inc-pdi ∷ >-inc-pdis) =
  ((>-inc-left pdi >-inc-pdi) ∷  (>-inc-map-left pdis >-inc-pdis))



>-inc-right : ∀ {l r : RE } { loc : ℕ } { c : Char }
  → (pdi : PDInstance r c )
  → >-Inc {r} {c} pdi
  → >-Inc {l + r ` loc } {c} (pdinstance-right pdi)
>-inc-right {l} {r} {loc} {c} (pdinstance {p} {r} {c}  inj sound-ev)
  (>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) = >-inc >-inc-ev
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





>-inc-map-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( pdis : List (PDInstance r c) )
    → All (>-Inc {r} {c}) pdis
    → All (>-Inc {l + r ` loc } {c}) (List.map pdinstance-right pdis)
>-inc-map-right [] [] = []
>-inc-map-right {l} {r} {loc} {c} (pdi ∷ pdis) (>-inc-pdi ∷ >-inc-pdis) =
  ((>-inc-right pdi >-inc-pdi) ∷  (>-inc-map-right pdis >-inc-pdis))


>-inc-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c  )
  → >-Inc {l} {c} pdi
  → >-Inc {l ● r ` loc} {c} (pdinstance-fst {l} {r} {loc} {c} pdi)
>-inc-fst {l} {r} {loc} {c} (pdinstance {p} {l} {c}  inj sound-ev) (>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) = >-inc >-inc-ev
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

  

>-inc-map-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
               → ( pdis : List (PDInstance l c ) )
               → All (>-Inc {l} {c}) pdis
               → All (>-Inc {l ● r ` loc} {c}) (List.map (pdinstance-fst {l} {r} {loc} {c}) pdis)
>-inc-map-fst [] [] = []
>-inc-map-fst {l} {r} {loc} {c} (pdi ∷ pdis) (>-inc-pdi ∷ all->-inc-pdis) = >-inc-fst pdi >-inc-pdi ∷  >-inc-map-fst pdis all->-inc-pdis

-----------------------------------------------------------------------------------------
-- aux lemma to show that injSnd is >-strict increasing
>-inc-injSnd : ∀ {l r p : RE } { loc : ℕ } { c : Char } 
         → ( v : U l )
         → ( inj : U p → U r )
         → ( ∀ ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) )
         → ( u₁ : U p )
         → ( u₂ : U p )
         → r ⊢ inj u₁ > inj u₂
         --------------------------------------------------------------------------
         → ( l ● r ` loc ) ⊢  (mkinjSnd inj v u₁) > (mkinjSnd inj v u₂) 
>-inc-injSnd {l} {r} {p} {loc} {c} v inj sound-ev u₁ u₂ (len-≡ len|inj-u₁|≡len|inj-u₂| inj-u₁>inj-u₂) = len-≡ len-|injSnd-pair-vu₁|≡len-|injSnd-pair-vu₂| (seq₂ refl (len-≡ len|inj-u₁|≡len|inj-u₂| inj-u₁>inj-u₂)) 
  where
    -- len-|injSnd-pair-uv|≡len-|pair-uv|+1 : (u : U l) → (v : U p) → length (proj₁ (flat ((PairU {l} {r} {loc} u (inj v))))) ≡ suc (length (proj₁ (flat (PairU {l} {p} {loc} u v))))
    -- len-|injSnd-pair-uv|≡len-|pair-uv|+1 u v rewrite (sound-ev v) = {!!} 
    len-|injSnd-pair-vu₁|≡len-|injSnd-pair-vu₂| : length (proj₁ (flat ((PairU {l} {r} {loc} v (inj u₁))))) ≡ length (proj₁ (flat ((PairU {l} {r} {loc} v (inj u₂)))))
    len-|injSnd-pair-vu₁|≡len-|injSnd-pair-vu₂|  =   (len|ys|≡len|zs|→len|xs++ys|≡len|xs++zs| {Char} {proj₁ (flat v)} {proj₁ (flat (inj u₁))} {proj₁ (flat (inj u₂))} len|inj-u₁|≡len|inj-u₂| )
>-inc-injSnd {l} {r} {p} {loc} {c} v inj sound-ev u₁ u₂ (len-> len|inj-u₁|>len|inj-u₂|) = len-> (len|ys|>len|zs|→len|xs++ys|>len|xs++zs|ʳ {Char} {proj₁ (flat v)} {proj₁ (flat (inj u₁))} {proj₁ (flat (inj u₂))} len|inj-u₁|>len|inj-u₂| ) 



-- aux lemma to show that mk-snd-pdi is >-strict increasing
>-inc-mk-snd-pdi : ∀ { l r : RE } { loc : ℕ } { c : Char }
   → ( e-flat-[]-e : (∃[ e ] Flat-[] l e)  )
   → ( pdi : PDInstance r c )
   → >-Inc {r} {c} pdi 
   -------------------------------------------------------------------
   → >-Inc (mk-snd-pdi {l} {r} {loc} {c} e-flat-[]-e pdi) 
>-inc-mk-snd-pdi {l} {r} {loc} {c} (e , flat-[] e' proj₁∘flate≡[]) (pdinstance {p} {r} {c} inj s-ev) (>-inc >-inc-inj) =
  >-inc (λ u₁ u₂ u₁>u₂ → ( >-inc-injSnd {l} {r} {p} {loc} e inj s-ev u₁ u₂  (>-inc-inj u₁ u₂ u₁>u₂))  )
  where
    -- duplicated from mk-snd-pdi from PartialDerivativeParseTree so that the PDInstance can be inferred
    -- this is needed because p is an existential type `hidden` inside PDInstance r c 
    injSnd :  U p → U (l ● r ` loc)
    injSnd = mkinjSnd {l} {r} {p} {loc} inj e
    injSnd-s-ev =
      (λ u → 
           begin
             proj₁ (flat (PairU {l} {r} {loc} e (inj u)))
           ≡⟨⟩
             (proj₁ (flat e)) ++ (proj₁ (flat (inj u)))
           ≡⟨ cong (λ x → ( x ++  (proj₁ (flat (inj u))))) proj₁∘flate≡[] ⟩  --  e must be an empty; we do have flat v ≡ [] from mkAllEmptyU-sound
             [] ++ (proj₁ (flat (inj u)))
           ≡⟨⟩
             proj₁ (flat (inj u))
           ≡⟨ s-ev u ⟩
             c ∷ (proj₁ (flat u))
           ∎
          )    


-- aux lemma to show that concatMap pdinstance-snd  is >-strict increasing

>-inc-pdinstance-snd : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( e-flat-[]-e : ∃[ e ] Flat-[] l e )
  → ( pdis : List (PDInstance r c ) )
  → All (>-Inc {r} {c}) pdis
  ---------------------------------------------------------------------------
  → All  (>-Inc {l ● r ` loc} {c}) (List.map  (mk-snd-pdi e-flat-[]-e ) pdis )
>-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e-flat-[]-e []           [] = [] 
>-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e-flat-[]-e (pdi ∷ pdis) (>-inc-pdi ∷ all>-inc-pdis) = (>-inc-mk-snd-pdi e-flat-[]-e pdi >-inc-pdi) ∷ >-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e-flat-[]-e pdis all>-inc-pdis

>-inc-concatmap-pdinstance-snd-sub :  ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( e-flat-[]-es  : List ( ∃[ e ] Flat-[] l e ) )
  → ( pdis : List (PDInstance r c ) )
  → All (>-Inc {r} {c}) pdis
  -----------------------------------------------------------------------------------------------------
  → All (>-Inc {l ● r ` loc} {c}) (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) e-flat-[]-es)
>-inc-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} [] _ _ = []
>-inc-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} ( e-flat-[]-e ∷ e-flat-[]-es ) pdis all>-inc-pdis =
  all-concat  (>-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  e-flat-[]-e  pdis all>-inc-pdis)
              (>-inc-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} e-flat-[]-es pdis all>-inc-pdis)  


>-inc-concatmap-pdinstance-snd : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
               → ( pdis : List (PDInstance r c ) )
               → All (>-Inc {r} {c}) pdis
               → All (>-Inc {l ● r ` loc} {c}) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  pdis)
>-inc-concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis all>-inc-pdis = >-inc-concatmap-pdinstance-snd-sub  {l} {r} {ε∈l} {loc} {c} (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es) pdis all>-inc-pdis
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l    

>-inc-map-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
               → ( pdis : List (PDInstance r c)  )
               → All (>-Inc {r} {c}) pdis
               → All (>-Inc {r * ε∉r ` loc} {c}) (List.map (pdinstance-star {r} {ε∉r} {loc} {c}) pdis)
>-inc-map-star {r} {ε∉r} {loc} {c} [] [] = []
>-inc-map-star {r} {ε∉r} {loc} {c} (pdinstance {p} {r} {c} inj s-ev ∷ pdis) (>-inc >-ev ∷ pxs)  =
  >-inc >-inc-ev ∷ >-inc-map-star pdis pxs
  where
    injList : U (p ● (r * ε∉r ` loc ) ` loc ) → U ( r * ε∉r ` loc )
    injList = mkinjList inj   

    len-|inj-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (inj u))) ≡ suc (length (proj₁ (flat u)))
    len-|inj-u|≡len-|u|+1 u rewrite (s-ev u) = refl 

    len-|injList-pair-uvs|≡len-|pair-uvs|+1 : (u : U p) → (vs : U ( r * ε∉r ` loc )) → length (proj₁ (flat (injList (PairU {p} {r * ε∉r ` loc} {loc} u vs)))) ≡ suc (length (proj₁ (flat (PairU {p} {r * ε∉r ` loc} {loc} u vs))))
    len-|injList-pair-uvs|≡len-|pair-uvs|+1 u (ListU vs) =
      begin
        length (proj₁ (flat (injList (PairU {p} {r * ε∉r ` loc} {loc} u (ListU vs)))))
      ≡⟨⟩
        length (proj₁ (flat (ListU {r} {ε∉r} {loc} ((inj u) ∷ vs ))))
      ≡⟨⟩
        length ((proj₁ (flat (inj u))) ++ (proj₁ (flat (ListU {r} {ε∉r} {loc} vs))))
      ≡⟨ length-++ (proj₁ (flat (inj u))) {(proj₁ (flat (ListU {r} {ε∉r} {loc} vs)))} ⟩
        length (proj₁ (flat (inj u))) + length (proj₁ (flat (ListU vs)))
      ≡⟨ cong (λ x → ( x + (length (proj₁ (flat (ListU {r} {ε∉r} {loc} vs)))))) (len-|inj-u|≡len-|u|+1 u) ⟩
        (suc (length (proj₁ (flat u)))) + length (proj₁ (flat (ListU vs)))
      ≡⟨⟩
        suc (length (proj₁ (flat u))) + length (proj₁ (flat (ListU vs)))
      ≡⟨⟩
        suc ((length (proj₁ (flat u))) + length (proj₁ (flat (ListU vs))))
      ≡⟨ cong suc (sym ( length-++ (proj₁ (flat u)) )) ⟩ 
        suc (length (((proj₁ (flat u))) ++ (proj₁ (flat (ListU vs)))) )
      ≡⟨⟩ 
        suc (length (proj₁ (flat (PairU {p} {r * ε∉r ` loc} {loc} u (ListU vs)))))
      ∎ 


    >-inc-ev : ∀ (uv₁ : U ( p ● (r * ε∉r ` loc ) ` loc ))
              → (uv₂ : U ( p ● (r * ε∉r ` loc ) ` loc ))
              → (p ● (r * ε∉r ` loc ) ` loc )  ⊢ uv₁ > uv₂
              ------------------------------------
              → (r * ε∉r ` loc) ⊢ (injList uv₁) > (injList uv₂)

    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (len-> len-|pair-u₁-vs₁|>len-|pair-u₂-vs₂|) = len-> len-|list-inj-u₁∷vs₁|>len-|list-inj-u₂∷vs₂|
      where
        len-|list-inj-u₁∷vs₁|>len-|list-inj-u₂∷vs₂| : length (proj₁ (flat (ListU {r} {ε∉r} {loc} ((inj u₁) ∷ vs₁)) )) > length (proj₁ (flat (ListU {r} {ε∉r} {loc} ((inj u₂) ∷ vs₂)) ))
        len-|list-inj-u₁∷vs₁|>len-|list-inj-u₂∷vs₂|
          rewrite len-|injList-pair-uvs|≡len-|pair-uvs|+1 u₁ (ListU {r} {ε∉r} {loc} vs₁) |  len-|injList-pair-uvs|≡len-|pair-uvs|+1 u₂ (ListU {r} {ε∉r} {loc} vs₂) = Nat.s≤s len-|pair-u₁-vs₁|>len-|pair-u₂-vs₂| 

    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (len-≡ len-|pair-u₁-vs₁|≡len-|pair-u₂-vs₂| (seq₁ u₁>u₂)) = 
      let inj-u₁>inj-u₂ = >-ev u₁ u₂ u₁>u₂
      in len-≡ len-|list-inj-u₁∷vs₁|≡len-|list-inj-u₂∷vs₂| (star-head {r} {loc} {ε∉r} {inj u₁} {inj u₂} {vs₁} {vs₂} inj-u₁>inj-u₂)
      where
        len-|list-inj-u₁∷vs₁|≡len-|list-inj-u₂∷vs₂| : length (proj₁ (flat (ListU {r} {ε∉r} {loc} ((inj u₁) ∷ vs₁)) )) ≡ length (proj₁ (flat (ListU {r} {ε∉r} {loc} ((inj u₂) ∷ vs₂)) ))
        len-|list-inj-u₁∷vs₁|≡len-|list-inj-u₂∷vs₂|
          rewrite len-|injList-pair-uvs|≡len-|pair-uvs|+1 u₁ (ListU {r} {ε∉r} {loc} vs₁) |  len-|injList-pair-uvs|≡len-|pair-uvs|+1 u₂ (ListU {r} {ε∉r} {loc} vs₂) = cong suc len-|pair-u₁-vs₁|≡len-|pair-u₂-vs₂| 
    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (len-≡ len-|pair-u₁-vs₁|≡len-|pair-u₂-vs₂| (seq₂  u₁≡u₂ list-vs₁>list-vs₂ )) =
      len-≡ len-|list-inj-u₁∷vs₁|≡len-|list-inj-u₂∷vs₂| (star-tail inj-u₁≡inj-u₂ list-vs₁>list-vs₂)  
      where
        inj-u₁≡inj-u₂ : inj u₁ ≡ inj u₂ 
        inj-u₁≡inj-u₂ = cong inj u₁≡u₂
        len-|list-inj-u₁∷vs₁|≡len-|list-inj-u₂∷vs₂| : length (proj₁ (flat (ListU {r} {ε∉r} {loc} ((inj u₁) ∷ vs₁)) )) ≡ length (proj₁ (flat (ListU {r} {ε∉r} {loc} ((inj u₂) ∷ vs₂)) ))
        len-|list-inj-u₁∷vs₁|≡len-|list-inj-u₂∷vs₂|
          rewrite len-|injList-pair-uvs|≡len-|pair-uvs|+1 u₁ (ListU {r} {ε∉r} {loc} vs₁) |  len-|injList-pair-uvs|≡len-|pair-uvs|+1 u₂ (ListU {r} {ε∉r} {loc} vs₂) = cong suc len-|pair-u₁-vs₁|≡len-|pair-u₂-vs₂|


-- sub lemmas to show that pdinstance-oplus preserves >-inc 


>-inc-fuse-left-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdiˡ : PDInstance l c ) -- these are all the leftU? 
  → ( pdiʳ : PDInstance r c ) -- these are all the rightU? 
  → >-Inc (pdinstance-left {l} {r} {loc} {c} pdiˡ)
  → >-Inc (pdinstance-right {l} {r} {loc} {c} pdiʳ)
  -----------------------------------------------------------
  → >-Inc (fuse {l + r ` loc} {loc} {c}  (pdinstance-left {l} {r} {loc} {c} pdiˡ) (pdinstance-right {l} {r} {loc} {c} pdiʳ))
>-inc-fuse-left-right {l} {r} {loc} {c} (pdinstance {pˡ} {l} {_} inj-l s-ev-l) (pdinstance {pʳ} {r} {_} inj-r s-ev-r) (>-inc u₁>u₂→inj-l-u₁>inj-l-u₂) (>-inc u₁>u₂→inj-r-u₁>inj-r-u₂) = >-inc ev-> 

  where
    inj : U (pˡ + pʳ ` loc ) → U ( l + r ` loc )
    inj = mkfuseInj (LeftU ∘ inj-l)  (RightU ∘ inj-r)


    sound-ev : (u : U (pˡ + pʳ ` loc)) 
               → proj₁ (flat (inj u))  ≡ c ∷ proj₁ (flat u)
    sound-ev (LeftU v₁) = s-ev-l v₁
    sound-ev (RightU v₂) = s-ev-r v₂


    len-|inj-u|≡len-|u|+1 : (u : U (pˡ + pʳ ` loc )) → length (proj₁ (flat (inj u))) ≡ suc (length (proj₁ (flat u)))
    len-|inj-u|≡len-|u|+1 u rewrite (sound-ev u) = refl

    len-|inj-l-u|≡len-|u|+1 : ( u : U pˡ ) → length (proj₁ (flat (inj-l u))) ≡ suc (length (proj₁ (flat u)))
    len-|inj-l-u|≡len-|u|+1 u rewrite (s-ev-l u) = refl 

    len-|inj-r-u|≡len-|u|+1 : ( u : U pʳ ) → length (proj₁ (flat (inj-r u))) ≡ suc (length (proj₁ (flat u)))
    len-|inj-r-u|≡len-|u|+1 u rewrite (s-ev-r u) = refl 

    ev-> : ( u₁ : U ( pˡ + pʳ ` loc ) )
        →  ( u₂ : U ( pˡ + pʳ ` loc ) ) 
        →  pˡ + pʳ ` loc ⊢ u₁ > u₂
        -------------------------------
        → l + r ` loc  ⊢ inj u₁ > inj u₂
    ev-> (LeftU v₁) (LeftU v₂) (len-≡ len-|left-v₁|≡len|left-v₂| (choice-ll v₁>v₂) ) = u₁>u₂→inj-l-u₁>inj-l-u₂ v₁ v₂ v₁>v₂ 
    ev-> (RightU v₁) (RightU v₂) (len-≡ len-|right-v₁|≡len|right-v₂| (choice-rr v₁>v₂) ) = u₁>u₂→inj-r-u₁>inj-r-u₂ v₁ v₂ v₁>v₂ 
        
    ev-> (LeftU v₁) (RightU v₂) (len-≡ len-|left-v₁|≡len|right-v₂| (choice-lr len|v₁|≥len|v₂|) ) = inj-left-v₁>inj-right-v₂ 
      where
        len|inj-left-v₁|≡len|inj-right-v₂| : length (proj₁ (flat (inj (LeftU v₁)))) ≡ length (proj₁ (flat (inj (RightU v₂))))
        len|inj-left-v₁|≡len|inj-right-v₂| rewrite len-|inj-u|≡len-|u|+1 (LeftU v₁) | len-|inj-u|≡len-|u|+1 (RightU v₂) = cong suc len-|left-v₁|≡len|right-v₂|
        len|inj-l-v₁|≡len|inj-r-v₂| : length (proj₁ (flat (inj-l v₁))) ≡ length (proj₁ (flat (inj-r v₂)))
        len|inj-l-v₁|≡len|inj-r-v₂| rewrite len-|inj-l-u|≡len-|u|+1 v₁ | len-|inj-r-u|≡len-|u|+1 v₂  = cong suc len-|left-v₁|≡len|right-v₂| 
        inj-left-v₁>inj-right-v₂ : l + r ` loc  ⊢ inj (LeftU v₁) > inj (RightU v₂)
        inj-left-v₁>inj-right-v₂ =
          len-≡ len|inj-left-v₁|≡len|inj-right-v₂| (choice-lr (≤-reflexive  (sym len|inj-l-v₁|≡len|inj-r-v₂| )) )  
    ev-> (RightU v₁) (LeftU v₂) (len-≡ len-|left-v₁|≡len|right-v₂| (choice-rl len|v₁|>len|v₂|) ) = Nullary.contradiction len|v₁|>len|v₂|  ¬len|v₁|>len|v₂|
      where
        len|v₁|≡len|v₂| : length (proj₁ (flat v₁)) ≡ length (proj₁ (flat v₂))
        len|v₁|≡len|v₂| = len-|left-v₁|≡len|right-v₂| 
        ¬len|v₁|>len|v₂| : ¬ length (proj₁ (flat v₁)) > length (proj₁ (flat v₂))
        ¬len|v₁|>len|v₂| = <-irrefl (sym len|v₁|≡len|v₂|) 
    ev-> v₁ v₂ (len-> len-|v₁|>len|v₂|) = len-> len|inj-v₁|>len|inj-v₂|
      where
        len|inj-v₁|>len|inj-v₂| : length (proj₁ (flat (inj v₁))) > length (proj₁ (flat (inj v₂)))
        len|inj-v₁|>len|inj-v₂| rewrite len-|inj-u|≡len-|u|+1 v₁ | len-|inj-u|≡len-|u|+1 v₂ = Nat.s≤s len-|v₁|>len|v₂| 

-- oplus >-inc for l + r case
>-inc-pdinstance-oplus-+ : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdisˡ : List (PDInstance l c) )
  → ( pdisʳ : List (PDInstance r c) )
  → All >-Inc pdisˡ
  → All >-Inc pdisʳ
  -----------------------------------------------------------------------------------------------------------------------
  → All >-Inc (pdinstance-oplus {l + r ` loc} {loc} {c} (List.map (pdinstance-left {l} {r} {loc} {c}) pdisˡ) (List.map (pdinstance-right {l} {r} {loc} {c}) pdisʳ)) 
>-inc-pdinstance-oplus-+ {l} {r} {loc} {c} [] pdisʳ [] all->-inc-pdisʳ           =  >-inc-map-right pdisʳ all->-inc-pdisʳ
>-inc-pdinstance-oplus-+ {l} {r} {loc} {c} (pdiˡ ∷ pdisˡ) [] all->-inc-pdisˡ [] = >-inc-map-left (pdiˡ ∷ pdisˡ) all->-inc-pdisˡ
>-inc-pdinstance-oplus-+ {l} {r} {loc} {c} (pdiˡ ∷ pdisˡ) (pdiʳ ∷ pdisʳ) (>-inc-pdiˡ ∷ all->-inc-pdisˡ)  (>-inc-pdiʳ ∷ all->-inc-pdisʳ)  = -- we can't apply IH on this level. hence we need a sub proof to apply IH 
  
  >-inc-pdinstance-oplus-sub (pdiˡ ∷ pdisˡ) (pdiʳ ∷ pdisʳ) (>-inc-pdiˡ ∷ all->-inc-pdisˡ)  (>-inc-pdiʳ ∷ all->-inc-pdisʳ)  
  where
    >-inc-pdinstance-oplus-sub : ( psˡ : List (PDInstance l c) )
        → ( psʳ : List (PDInstance r c) )
        → All >-Inc psˡ
        → All >-Inc psʳ
        → All >-Inc (concatMap (λ pˡ → List.map (fuse {l + r ` loc} {loc} {c} pˡ) (List.map (pdinstance-right  {l} {r} {loc} {c}) psʳ )) (List.map pdinstance-left psˡ))
    >-inc-pdinstance-oplus-sub []         psʳ        [] _ = []
    >-inc-pdinstance-oplus-sub (pˡ ∷ psˡ) []         (>-inc-pˡ ∷ all->-inc-psˡ) []                         = >-inc-pdinstance-oplus-sub psˡ [] all->-inc-psˡ []  
    >-inc-pdinstance-oplus-sub (pˡ ∷ psˡ) (pʳ ∷ psʳ) (>-inc-pˡ ∷ all->-inc-psˡ) (>-inc-pʳ ∷ all->-inc-psʳ) = all-concat first rest
      where
        first : All >-Inc (List.map (fuse {l + r ` loc} {loc} {c}  (pdinstance-left {l} {r} {loc} {c} pˡ)) (List.map (pdinstance-right {l} {r} {loc} {c}) (pʳ ∷ psʳ)))
        first = sub  (pʳ ∷ psʳ)  (>-inc-pʳ ∷ all->-inc-psʳ)  
          where
            sub : (qs : List (PDInstance r c)) → All >-Inc qs
                  →  All >-Inc (List.map (fuse {l + r ` loc} {loc} {c}  (pdinstance-left {l} {r} {loc} {c} pˡ)) (List.map (pdinstance-right {l} {r} {loc} {c}) qs))
            sub [] [] = []
            sub (q ∷ qs) (>-inc-q ∷ all->-inc-qs) = (>-inc-fuse-left-right pˡ q (>-inc-left {l} {r} {loc} {c} pˡ >-inc-pˡ) (>-inc-right {l} {r} {loc} {c} q >-inc-q) ) ∷ (sub qs all->-inc-qs) 
        rest : All >-Inc (List.foldr _++_ [] (List.map (λ pˡ₁ → List.map (fuse pˡ₁) (pdinstance-right  {l} {r} {loc} {c} pʳ ∷ List.map pdinstance-right psʳ)) (List.map pdinstance-left psˡ)))
        rest = >-inc-pdinstance-oplus-sub psˡ (pʳ ∷ psʳ) all->-inc-psˡ  (>-inc-pʳ ∷ all->-inc-psʳ) 

-- oplus >-inc for (l + s) ● r case

  
-- this should be moved to PDInstance
concatmap-pdinstance-snd-[]≡[] : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
    → concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} [] ≡ []
concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c} = sub e-flat-es 
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l
    e-flat-es :  List ( ∃[ e ] (Flat-[] l e) )
    e-flat-es = zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es
    sub : (xs :  List ( ∃[ e ] (Flat-[] l e) )) → concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x []) xs ≡ []
    sub [] = refl
    sub (x ∷ xs) = sub xs


concatmap-λx→[]-xs≡[] : ∀ { A : Set } { B : Set} ( xs : List A )
  → (concatMap (λ x → [] {A = B} ) xs   ) ≡ []
concatmap-λx→[]-xs≡[] {A} {B} [] = refl
concatmap-λx→[]-xs≡[] {A} {B} (x ∷ xs) = concatmap-λx→[]-xs≡[] xs 


-- similar to flat-[], a parse tree PairU x y is Flat-[]-fst iff the first component x is flattened to [] 
data Flat-[]-Fst : (l r : RE) ( loc : ℕ ) → ( u : U ( l ● r ` loc ) ) → Set where
  flat-[]-fst :  ∀ {l r : RE} { loc : ℕ } 
    → ( x : U l )
    → ( y : U r )
    → ( (proj₁ (flat {l} x) ) ≡ [] )
    -------------------------------------------------
    → Flat-[]-Fst l r loc ( PairU {l} {r} {loc} x y )

-- A PDInstance is Flat-[]-Fst-PDI  iff all parse trees produced by its injection function are Flat-[]-Fst. 
data Flat-[]-Fst-PDI : ∀ {l r : RE} { loc : ℕ } { c : Char } →  (PDInstance ( l ● r ` loc ) c) → Set where
  fst-flat-[] : ∀ { p l r : RE} { loc : ℕ } { c : Char }
    → (inj : U p → U (l ● r ` loc ) )
    → (sound-ev : ( ∀ ( u : U p ) → ( proj₁ ( flat {l ● r ` loc } (inj u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) )  )
    → ( ∀ ( u : U p ) →  (Flat-[]-Fst l r loc (inj u)))
    --------------------------------------------------
    → Flat-[]-Fst-PDI  {l} {r} {loc} {c} (pdinstance {p} {l ● r ` loc} {c} inj sound-ev)

-- goal >-Inc (fuse (pdinstance-fst pdiˡ) (pdinstance _injʳ _s-evʳ)) 


flat-[]-fst-pdinstance-snd :  ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( e-flat-[]-e : ∃[ e ] Flat-[] l e )
  → ( pdis : List (PDInstance r c ) )
  --------------------------------------------------
  → All (Flat-[]-Fst-PDI {l} {r} {loc} {c} ) (List.map  (mk-snd-pdi e-flat-[]-e ) pdis )
flat-[]-fst-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e-flat-[]-e  [] rewrite Utils.map-[] {(PDInstance r c )} {(PDInstance (l ● r ` loc) c )} {[]} {λ x → mk-snd-pdi e-flat-[]-e x } refl = []
flat-[]-fst-pdinstance-snd {l} {r} {ε∈l} {loc} {c} (e , flat-[] e' ev ) (pdi@(pdinstance {p} {r} {c} inj s-ev) ∷ pdis) = prf ∷ (flat-[]-fst-pdinstance-snd  {l} {r} {ε∈l} {loc} {c} (e , flat-[] e ev) pdis)
  where
    -- copied and modified from PDInstance.mk-snd-pdi 
    injSnd-s-ev =
                (λ u → 
                   begin
                     proj₁ (flat (PairU {l} {r} {loc} e (inj u)))
                   ≡⟨⟩
                     (proj₁ (flat e)) ++ (proj₁ (flat (inj u)))
                   ≡⟨ cong (λ x → ( x ++  (proj₁ (flat (inj u))))) ev ⟩  --  e must be an empty; we do have flat v ≡ [] from mkAllEmptyU-sound
                     [] ++ (proj₁ (flat (inj u)))
                   ≡⟨⟩
                     proj₁ (flat (inj u))
                   ≡⟨ s-ev u ⟩
                     c ∷ (proj₁ (flat u))
                   ∎
                )

    prf : Flat-[]-Fst-PDI {l} {r} {loc} {c} (mk-snd-pdi (e , flat-[] e ev) pdi)
    prf = fst-flat-[] (mkinjSnd inj e)
           injSnd-s-ev 
           (λ u → flat-[]-fst e (inj u) ev) 

  
flat-[]-fst-concatmap-pdinstance-snd-sub :  ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( e-flat-[]-es  : List ( ∃[ e ] Flat-[] l e ) )
  → ( pdis : List (PDInstance r c ) )
  -----------------------------------------------------------------------------------------------------
  → All (Flat-[]-Fst-PDI {l} {r} {loc} {c} ) (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) e-flat-[]-es)
flat-[]-fst-concatmap-pdinstance-snd-sub  {l} {r} {ε∈l} {loc} {c} [] _  = []
flat-[]-fst-concatmap-pdinstance-snd-sub  {l} {r} {ε∈l} {loc} {c} ( e-flat-[]-e ∷ e-flat-[]-es ) pdis =
  all-concat (flat-[]-fst-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e-flat-[]-e pdis)
   (flat-[]-fst-concatmap-pdinstance-snd-sub  {l} {r} {ε∈l} {loc} {c} e-flat-[]-es pdis) 

>-inc-fuse-fst-pdi-flat-[]-fst-pdi : ∀ { l r : RE } {ε∈l : ε∈ l } { loc : ℕ } { c : Char }
    → ( pdiˡ : PDInstance l c )
    → ( pdiʳ : PDInstance (l ● r ` loc) c ) -- must be pdinstance-snd'ed (i.e. mk-snd-pdi) pdi
    → >-Inc pdiˡ
    → >-Inc pdiʳ
    → Flat-[]-Fst-PDI pdiʳ 
    -----------------------------------------------------------
    → >-Inc (fuse {l ● r ` loc} {loc} {c}  (pdinstance-fst {l} {r} {loc} {c} pdiˡ) pdiʳ)

>-inc-fuse-fst-pdi-flat-[]-fst-pdi {l} {r} {ε∈l} {loc} {c} (pdinstance {pˡ} {l} {_} inj-l s-ev-l)
                                   (pdinstance {pʳ} {l●r} {_} .inj-snd-r .s-ev-injsnd-r)
                                   (>-inc u₁>u₂→inj-l-u₁>inj-l-u₂)
                                   (>-inc u₁>u₂→inj-snd-r-u₁>inj-r-u₂)
                                   (fst-flat-[] inj-snd-r s-ev-injsnd-r fst-flat-[]-injsnd-ev)
                                   = >-inc ev  

  where
    -- copied and monomorphized from PDInstance.pdinstance-fst
    injFst : U ( pˡ ● r ` loc)  → U (l ● r ` loc )
    injFst = mkinjFst inj-l
    -- copied and monomorphized from PDInstance.pdinstance-fst
    sound-injfst-inj-l : ∀ ( u : U ( pˡ ● r ` loc) ) → (proj₁ (flat { l ● r ` loc } (injFst u )) ≡ c ∷ (proj₁ (flat { pˡ ● r ` loc } u)))
    sound-injfst-inj-l (PairU {pˡ} {r} {loc} u v) =
               begin
                 proj₁ (flat (PairU {l} {r} {loc} (inj-l u) v))
               ≡⟨⟩
                 (proj₁ (flat (inj-l u))) ++ (proj₁ (flat v))
               ≡⟨ cong (λ x → ( x ++ (proj₁ (flat v)))) (s-ev-l u) ⟩
                 (c ∷ (proj₁ (flat u))) ++ (proj₁ (flat v))
               ≡⟨⟩
                 c ∷ (proj₁ (flat (PairU {pˡ} {r} {loc} u v)))
               ∎
               
    inj : U ( (pˡ ● r ` loc) + pʳ ` loc ) → U ( l ● r ` loc )
    inj = mkfuseInj injFst inj-snd-r  



    sound-ev : (u :  U ( (pˡ ● r ` loc ) + pʳ ` loc) )  
               → proj₁ (flat (inj u))  ≡ c ∷ proj₁ (flat u)
    sound-ev (LeftU v₁) = sound-injfst-inj-l v₁
    sound-ev (RightU v₂) = s-ev-injsnd-r v₂




    len-|inj-l-u|≡len-|u|+1 : (u : U  pˡ  ) → length (proj₁ (flat (inj-l u))) ≡ suc (length (proj₁ (flat u)))
    len-|inj-l-u|≡len-|u|+1 u rewrite (s-ev-l u) = refl


    len-|inj-u|≡len-|u|+1 : (u : U (  (pˡ ● r ` loc) + pʳ ` loc ) ) → length (proj₁ (flat (inj u))) ≡ suc (length (proj₁ (flat u)))
    len-|inj-u|≡len-|u|+1 u rewrite (sound-ev u) = refl


    ev :  (u₁ u₂ : U ((pˡ ● r ` loc) + pʳ ` loc)) →
          ((pˡ ● r ` loc) + pʳ ` loc) ⊢ u₁ > u₂ →
          (l ● r ` loc) ⊢ inj u₁ > inj u₂
    ev (LeftU (PairU v₁ w₁)) (LeftU (PairU v₂ w₂)) (len-≡ len|left-v₁w₁|≡len|left-v₂w₂| (choice-ll (len-≡ len|v₁w₁|≡len|v₂w₂|  (seq₁ v₁>v₂)))) = len-≡ len|inj-left-v₁w₁|≡len|inj-left-v₂w₂| prf
        where
          len|inj-left-v₁w₁|≡len|inj-left-v₂w₂| : length (proj₁ (flat (inj (LeftU (PairU v₁ w₁))))) ≡  length (proj₁ (flat (inj  (LeftU (PairU v₂ w₂)))))
          len|inj-left-v₁w₁|≡len|inj-left-v₂w₂| rewrite len-|inj-u|≡len-|u|+1  (LeftU (PairU v₁ w₁)) | len-|inj-u|≡len-|u|+1  (LeftU (PairU v₂ w₂)) = cong suc len|left-v₁w₁|≡len|left-v₂w₂|
          prf :  (l ● r ` loc) ⊢ inj (LeftU (PairU v₁ w₁)) >ⁱ
                                 inj (LeftU (PairU v₂ w₂))
          prf with  inj (LeftU (PairU v₁ w₁)) in inj-eq₁ | inj (LeftU (PairU v₂ w₂)) in inj-eq₂ 
          ... | PairU x₁ x₂ | PairU y₁ y₂ rewrite (sym inj-eq₁) | sym inj-eq₂ = seq₁ (u₁>u₂→inj-l-u₁>inj-l-u₂ v₁ v₂ v₁>v₂)
    ev (LeftU (PairU v₁ w₁)) (LeftU (PairU v₂ w₂)) (len-≡ len|left-v₁w₁|≡len|left-v₂w₂| (choice-ll (len-≡ len|v₁w₁|≡len|v₂w₂|  (seq₂ v₁≡v₂ w₁>w₂)))) = len-≡ len|inj-left-v₁w₁|≡len|inj-left-v₂w₂| prf 
        where
          len|inj-left-v₁w₁|≡len|inj-left-v₂w₂| : length (proj₁ (flat (inj (LeftU (PairU v₁ w₁))))) ≡  length (proj₁ (flat (inj  (LeftU (PairU v₂ w₂)))))
          len|inj-left-v₁w₁|≡len|inj-left-v₂w₂| rewrite len-|inj-u|≡len-|u|+1  (LeftU (PairU v₁ w₁)) | len-|inj-u|≡len-|u|+1  (LeftU (PairU v₂ w₂)) = cong suc len|left-v₁w₁|≡len|left-v₂w₂|
          prf :  (l ● r ` loc) ⊢ inj (LeftU (PairU v₁ w₁)) >ⁱ
                                 inj (LeftU (PairU v₂ w₂))
          prf  with  inj (LeftU (PairU v₁ w₁)) in inj-eq₁ | inj (LeftU (PairU v₂ w₂)) in inj-eq₂ 
          ... | PairU x₁ x₂ | PairU y₁ y₂ rewrite (sym inj-eq₁) | sym inj-eq₂ = seq₂ (cong inj-l v₁≡v₂) w₁>w₂ 
    ev (LeftU (PairU v₁ w₁)) (LeftU (PairU v₂ w₂)) (len-≡ len|left-v₁w₁|≡len|left-v₂w₂| (choice-ll (len-> len|v₁w₁|>len|v₂w₂|))) rewrite len|left-v₁w₁|≡len|left-v₂w₂|  = Nullary.contradiction len|v₁w₁|>len|v₂w₂| (<-irrefl refl )

    ev (LeftU (PairU v₁ w₁)) (LeftU (PairU v₂ w₂)) (len-> len|left-v₁w₁|>len|left-v₂w₂|)
      {- rewrite len-|inj-l-u|≡len-|u|+1 v₁ | len-|inj-l-u|≡len-|u|+1 v₂ -} = len-> len|pair-inj-l-v₁-w₁|>len|pair-inj-l-v₂-w₂|
        where
          len|pair-inj-l-v₁-w₁|≡len|pair-v₁-w₁|+1 : length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₁) w₁))) ≡ suc (length (proj₁ (flat (PairU {pˡ} {r} {loc} v₁ w₁))))
          len|pair-inj-l-v₁-w₁|≡len|pair-v₁-w₁|+1 =
            begin
              length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₁) w₁)))
            ≡⟨⟩
              length (proj₁ (flat (inj-l v₁)) ++ (proj₁ (flat w₁))) 
            ≡⟨ length-++  (proj₁ (flat (inj-l v₁)))  ⟩
              length (proj₁ (flat (inj-l v₁))) + (length (proj₁ (flat w₁))) 
            ≡⟨ cong (_+  (length (proj₁ (flat w₁)))) ( len-|inj-l-u|≡len-|u|+1 v₁ )⟩
              suc (length (proj₁ (flat v₁))) + (length (proj₁ (flat w₁))) 
            ≡⟨⟩
              suc (length (proj₁ (flat v₁)) + (length (proj₁ (flat w₁))))
            ≡⟨ cong suc (sym (length-++ (proj₁ (flat v₁))) ) ⟩
              suc (length (proj₁ (flat (PairU {pˡ} {r} {loc} v₁ w₁))))
            ∎
            
          len|pair-inj-l-v₂-w₂|≡len|pair-v₂-w₂|+1 : length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₂) w₂))) ≡ suc (length (proj₁ (flat (PairU {pˡ} {r} {loc}  v₂ w₂))))
          len|pair-inj-l-v₂-w₂|≡len|pair-v₂-w₂|+1 = 
            begin
              length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₂) w₂)))
            ≡⟨⟩
              length (proj₁ (flat (inj-l v₂)) ++ (proj₁ (flat w₂))) 
            ≡⟨ length-++  (proj₁ (flat (inj-l v₂)))  ⟩
              length (proj₁ (flat (inj-l v₂))) + (length (proj₁ (flat w₂))) 
            ≡⟨ cong (_+  (length (proj₁ (flat w₂)))) ( len-|inj-l-u|≡len-|u|+1 v₂ )⟩
              suc (length (proj₁ (flat v₂))) + (length (proj₁ (flat w₂))) 
            ≡⟨⟩
              suc (length (proj₁ (flat v₂)) + (length (proj₁ (flat w₂))))
            ≡⟨ cong suc (sym (length-++ (proj₁ (flat v₂))) ) ⟩
              suc (length (proj₁ (flat (PairU {pˡ} {r} {loc} v₂ w₂))))
            ∎
          
          len|pair-inj-l-v₁-w₁|>len|pair-inj-l-v₂-w₂| : length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₁) w₁))) > length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₂) w₂)))
          len|pair-inj-l-v₁-w₁|>len|pair-inj-l-v₂-w₂| rewrite  len|pair-inj-l-v₁-w₁|≡len|pair-v₁-w₁|+1 | len|pair-inj-l-v₂-w₂|≡len|pair-v₂-w₂|+1 = Nat.s≤s  len|left-v₁w₁|>len|left-v₂w₂|  
          


    ev (LeftU (PairU v₁ w₁)) (RightU v₂) (len-≡ len|left-v₁w₁|≡len|right-v₂| (choice-lr len|v₁w₁|≥len|v₂|)) = len-≡ len|inj-left-v₁w₁|≡len|inj-right-v₂| prf  
        where
          len|inj-left-v₁w₁|≡len|inj-right-v₂| : length (proj₁ (flat (inj (LeftU (PairU v₁ w₁))))) ≡  length (proj₁ (flat (inj  (RightU v₂ ))))
          len|inj-left-v₁w₁|≡len|inj-right-v₂| rewrite len-|inj-u|≡len-|u|+1  (LeftU (PairU v₁ w₁)) | len-|inj-u|≡len-|u|+1  (RightU v₂) = cong suc  len|left-v₁w₁|≡len|right-v₂| 
          prf :  (l ● r ` loc) ⊢ inj (LeftU (PairU v₁ w₁)) >ⁱ
                                 inj (RightU v₂)
          prf  with  inj (LeftU (PairU v₁ w₁)) in inj-eq₁ | inj (RightU v₂) in inj-eq₂ | fst-flat-[]-injsnd-ev v₂ 
          ... | PairU x₁ x₂ | PairU y₁ y₂  | flat-[]-fst .y₁ .y₂ |y₁|≡[] rewrite (sym inj-eq₁)  = seq₁ (len-> len|inj-l-v₁|>len|flat-v₁|) 
            where
              len|inj-l-v₁|>len|flat-v₁| : length (Product.proj₁ (flat (inj-l v₁))) > length (Product.proj₁ (flat y₁))
              len|inj-l-v₁|>len|flat-v₁| rewrite |y₁|≡[] |   len-|inj-l-u|≡len-|u|+1 v₁ = Nat.s≤s Nat.z≤n 

    ev (LeftU (PairU v₁ w₁)) (RightU v₂) (len-> len|left-v₁w₁|>len|right-v₂|)  = len-> len|pair-inj-l-v₁-w₁|>len|inj-r-v₂| 
        where
          len|pair-inj-l-v₁-w₁|≡len|pair-v₁-w₁|+1 : length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₁) w₁))) ≡ suc (length (proj₁ (flat (PairU {pˡ} {r} {loc} v₁ w₁))))
          len|pair-inj-l-v₁-w₁|≡len|pair-v₁-w₁|+1 =
            begin
              length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₁) w₁)))
            ≡⟨⟩
              length (proj₁ (flat (inj-l v₁)) ++ (proj₁ (flat w₁))) 
            ≡⟨ length-++  (proj₁ (flat (inj-l v₁)))  ⟩
              length (proj₁ (flat (inj-l v₁))) + (length (proj₁ (flat w₁))) 
            ≡⟨ cong (_+  (length (proj₁ (flat w₁)))) ( len-|inj-l-u|≡len-|u|+1 v₁ )⟩
              suc (length (proj₁ (flat v₁))) + (length (proj₁ (flat w₁))) 
            ≡⟨⟩
              suc (length (proj₁ (flat v₁)) + (length (proj₁ (flat w₁))))
            ≡⟨ cong suc (sym (length-++ (proj₁ (flat v₁))) ) ⟩
              suc (length (proj₁ (flat (PairU {pˡ} {r} {loc} v₁ w₁))))
            ∎
        
          len|pair-inj-l-v₁-w₁|>len|inj-r-v₂| : length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₁) w₁))) > length (proj₁ (flat (inj (RightU v₂))))
          len|pair-inj-l-v₁-w₁|>len|inj-r-v₂|  rewrite  len|pair-inj-l-v₁-w₁|≡len|pair-v₁-w₁|+1 |  len-|inj-u|≡len-|u|+1 (RightU v₂)  = Nat.s≤s len|left-v₁w₁|>len|right-v₂| 
      
    ev (RightU v₁) (RightU v₂) (len-≡ len|right-v₁|≡len|right-v₂| (choice-rr v₁>v₂)) = u₁>u₂→inj-snd-r-u₁>inj-r-u₂ v₁ v₂ v₁>v₂
    ev (RightU v₁) (RightU v₂) (len-> len|right-v₁|>len|right-v₂|) = u₁>u₂→inj-snd-r-u₁>inj-r-u₂ v₁ v₂ (len-> len|right-v₁|>len|right-v₂|)

    ev (RightU v₁) (LeftU (PairU v₂ w₂)) (len-≡ len|right-v₁|≡len|left-v₂w₂| (choice-rl len|right-v₁|>len|left-v₂w₂|)) rewrite len|right-v₁|≡len|left-v₂w₂|  = Nullary.contradiction len|right-v₁|>len|left-v₂w₂| (<-irrefl refl)
    ev (RightU v₁) (LeftU (PairU v₂ w₂)) (len-> len|right-v₁|>len|left-v₂w₂|) = len-> len|inj-right-v₁|>len|pair-inj-l-v₂-w₂| 
      where
        len|pair-inj-l-v₂-w₂|≡len|pair-v₂-w₂|+1 : length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₂) w₂))) ≡ suc (length (proj₁ (flat (PairU {pˡ} {r} {loc} v₂ w₂))))
        len|pair-inj-l-v₂-w₂|≡len|pair-v₂-w₂|+1 =
            begin
              length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₂) w₂)))
            ≡⟨⟩
              length (proj₁ (flat (inj-l v₂)) ++ (proj₁ (flat w₂))) 
            ≡⟨ length-++  (proj₁ (flat (inj-l v₂)))  ⟩
              length (proj₁ (flat (inj-l v₂))) + (length (proj₁ (flat w₂))) 
            ≡⟨ cong (_+  (length (proj₁ (flat w₂)))) ( len-|inj-l-u|≡len-|u|+1 v₂ )⟩
              suc (length (proj₁ (flat v₂))) + (length (proj₁ (flat w₂))) 
            ≡⟨⟩
              suc (length (proj₁ (flat v₂)) + (length (proj₁ (flat w₂))))
            ≡⟨ cong suc (sym (length-++ (proj₁ (flat v₂))) ) ⟩
              suc (length (proj₁ (flat (PairU {pˡ} {r} {loc} v₂ w₂))))
            ∎
      
        len|inj-right-v₁|>len|pair-inj-l-v₂-w₂| : length (proj₁ (flat (inj (RightU v₁)))) > length (proj₁ (flat (PairU {l} {r} {loc} (inj-l v₂) w₂)))
        len|inj-right-v₁|>len|pair-inj-l-v₂-w₂| rewrite len|pair-inj-l-v₂-w₂|≡len|pair-v₂-w₂|+1 | len-|inj-u|≡len-|u|+1 (RightU v₁) = Nat.s≤s len|right-v₁|>len|left-v₂w₂| 


>-inc-map-fuse-pdi-fst : ∀ { l r : RE } {ε∈l : ε∈ l } { loc : ℕ } { c : Char }
    → ( pdiˡ : PDInstance l c )
    → ( pdisʳ : List (PDInstance (l ● r ` loc) c ) )
    → >-Inc pdiˡ
    → All >-Inc pdisʳ
    -- we need to include the All Flat-[]-Fst-PDI  pdisʳ here
    → All Flat-[]-Fst-PDI  pdisʳ
    -------------------------------------------------------
    → All >-Inc (List.map (fuse {l ● r ` loc} {loc} {c} (pdinstance-fst {l} {r} {loc} {c} pdiˡ)) pdisʳ)
>-inc-map-fuse-pdi-fst {l} {r} {ε∈l} {loc} {c} pdiˡ [] >-inc-pdiˡ [] [] = []
>-inc-map-fuse-pdi-fst {l} {r} {ε∈l} {loc} {c} pdiˡ (pdiʳ ∷ pdisʳ) >-inc-pdiˡ (>-inc-pdiʳ ∷ >-inc-pdisʳ ) (fst-flat-[]-pdiʳ ∷ fst-flat-[]-pdisʳ) =
  >-inc-fuse-fst-pdi-flat-[]-fst-pdi  {l} {r} {ε∈l} {loc} {c}  pdiˡ pdiʳ >-inc-pdiˡ >-inc-pdiʳ fst-flat-[]-pdiʳ
  ∷ (>-inc-map-fuse-pdi-fst {l} {r} {ε∈l} {loc} {c}  pdiˡ pdisʳ >-inc-pdiˡ >-inc-pdisʳ fst-flat-[]-pdisʳ) 





>-inc-pdinstance-oplus-+● : ∀ { l+s r : RE } {ε∈l+s : ε∈ l+s } { loc : ℕ } { c : Char } 
    → ( pdisˡ : List (PDInstance l+s c) )
    → ( pdisʳ : List (PDInstance r c) )
    → All >-Inc pdisˡ
    → All >-Inc pdisʳ
    -----------------------------------------------------------------------------------------------------------------------
    → All >-Inc (pdinstance-oplus {l+s ● r ` loc} {loc} {c} (List.map (pdinstance-fst {l+s} {r} {loc} {c}) pdisˡ) (concatmap-pdinstance-snd {l+s} {r} {ε∈l+s} {loc} {c} pdisʳ))
>-inc-pdinstance-oplus-+● {l+s} {r} {ε∈l+s} {loc} {c} (pdiˡ ∷ pdisˡ) [] all->-inc-pdisˡ [] rewrite (concatmap-pdinstance-snd-[]≡[] {l+s} {r} {ε∈l+s} {loc} {c})  =  >-inc-map-fst (pdiˡ ∷ pdisˡ) all->-inc-pdisˡ 
>-inc-pdinstance-oplus-+● {l+s} {r} {ε∈l+s} {loc} {c} [] pdisʳ [] all->-inc-pdisʳ           =  >-inc-concatmap-pdinstance-snd pdisʳ all->-inc-pdisʳ
>-inc-pdinstance-oplus-+● {l+s} {r} {ε∈l+s} {loc} {c} (pdiˡ ∷ pdisˡ) (pdiʳ ∷ pdisʳ) ( >-inc-pdiˡ ∷ all->-inc-pdisˡ) (>-inc-pdiʳ ∷ all->-inc-pdisʳ)  -- = {!!}
  with mkAllEmptyU ε∈l+s in mkAllEmpty-eq | mkAllEmptyU-sound ε∈l+s 
... | []                 | _ =   Nullary.contradiction mkAllEmpty-eq (mkAllEmptyU≢[] {l+s} ε∈l+s) -- we need a contradiction here
... | e ∷ es             | flat-[]-e ∷ flat-[]-es =  >-inc-pdinstance-oplus-sub (pdiˡ ∷ pdisˡ) (pdiʳ ∷ pdisʳ) (>-inc-pdiˡ ∷ all->-inc-pdisˡ)  (>-inc-pdiʳ ∷ all->-inc-pdisʳ)  
  where
     >-inc-pdinstance-oplus-sub : ( psˡ : List (PDInstance l+s c) )
        → ( psʳ : List (PDInstance r c) ) -- problem, we should know that all the parse trees coming out from psʳ are having the empty fst.
        → All >-Inc psˡ
        → All >-Inc psʳ
        ---------------------------------------------------------------
        → All >-Inc (concatMap (λ pˡ₁ →  List.map (fuse  {l+s ● r ` loc} {loc} {c} pˡ₁) (concatMap (λ x → List.map (mk-snd-pdi x) psʳ) (zip-es-flat-[]-es {l+s} {ε∈l+s} (e ∷ es) (flat-[]-e ∷ flat-[]-es))))
           (List.map pdinstance-fst psˡ))        
     >-inc-pdinstance-oplus-sub  []         psʳ        [] _ = [] 
     >-inc-pdinstance-oplus-sub  (pˡ ∷ psˡ) []         (>-inc-pˡ ∷ all->-inc-psˡ) []
      rewrite concatmap-λx→[]-xs≡[] {∃[ e ](Flat-[] l+s e)} {(PDInstance (l+s ● r ` loc) c)} (zip-es-flat-[]-es {l+s} {ε∈l+s} (e ∷ es) (flat-[]-e ∷ flat-[]-es))
        | concatmap-λx→[]-xs≡[] {(PDInstance (l+s ● r ` loc) c)} {(PDInstance (l+s ● r ` loc) c)} (List.map pdinstance-fst psˡ) = []
     >-inc-pdinstance-oplus-sub  (pˡ ∷ psˡ) (pʳ ∷ psʳ) (>-inc-pˡ ∷ all->-inc-psˡ) (>-inc-pʳ ∷ all->-inc-psʳ) =  all-concat first rest 
      where    
        first : All >-Inc (List.map (fuse {l+s ● r ` loc} {loc} {c} (pdinstance-fst {l+s} {r} {loc} {c} pˡ)) (concatMap (λ x → List.map (mk-snd-pdi x) (pʳ ∷ psʳ)) (zip-es-flat-[]-es {l+s} {ε∈l+s} (e ∷ es) (flat-[]-e ∷ flat-[]-es)))) 
        first = 
              sub (zip-es-flat-[]-es {l+s} {ε∈l+s} (e ∷ es) (flat-[]-e ∷ flat-[]-es)) (pʳ ∷ psʳ) (>-inc-pʳ ∷ all->-inc-psʳ)
          where
            sub : ( es-flat-[]-es : List (∃[ e ](Flat-[] l+s e)) )
              → (qs : List (PDInstance r c))
              → All >-Inc qs
              → All >-Inc (List.map (fuse {l+s ● r ` loc} {loc} {c}  (pdinstance-fst {l+s} {r} {loc} {c} pˡ)) (concatMap (λ x → List.map (mk-snd-pdi x) qs) es-flat-[]-es))
            sub []                                  qs         >-inc-qs             = []
            sub ( (e , flat-[]-e) ∷ es-flat-[]-es ) []        []                    = sub es-flat-[]-es [] []
            sub ( (e , flat-[]-e) ∷ es-flat-[]-es ) (q ∷ qs ) (>-inc-q ∷ >-inc-qs ) = >-inc-map-fuse-pdi-fst  {l+s} {r} {ε∈l+s} {loc} {c}  pˡ (List.concatMap (λ x → List.map (mk-snd-pdi x) (q ∷ qs)) ((e , flat-[]-e) ∷ es-flat-[]-es))  >-inc-pˡ >-inc-concatmap-map-mk-snd-pdi-qs-es-flat-[]-es flat-[]-fst-concatmap-map-mk-snd-pdi-qs-es-flat-[]-es 
              where
                >-inc-concatmap-map-mk-snd-pdi-qs-es-flat-[]-es : All >-Inc (List.concatMap (λ x → List.map (mk-snd-pdi x) (q ∷ qs)) ((e , flat-[]-e) ∷ es-flat-[]-es))
                >-inc-concatmap-map-mk-snd-pdi-qs-es-flat-[]-es = >-inc-concatmap-pdinstance-snd-sub {l+s} {r} {ε∈l+s} {loc} {c} ((e , flat-[]-e) ∷ es-flat-[]-es) (q ∷ qs) (>-inc-q ∷ >-inc-qs )

                                          
                flat-[]-fst-concatmap-map-mk-snd-pdi-qs-es-flat-[]-es : All (Flat-[]-Fst-PDI {l+s} {r} {loc} {c})  (List.concatMap (λ x → List.map (mk-snd-pdi x) (q ∷ qs)) ((e , flat-[]-e) ∷ es-flat-[]-es))
                flat-[]-fst-concatmap-map-mk-snd-pdi-qs-es-flat-[]-es = flat-[]-fst-concatmap-pdinstance-snd-sub {l+s} {r} {ε∈l+s} {loc} {c}  ((e , flat-[]-e) ∷ es-flat-[]-es) (q ∷ qs) 
        rest : All >-Inc (concatMap (λ pˡ₁ → List.map (fuse pˡ₁)  (concatMap (λ x → List.map (mk-snd-pdi x) (pʳ ∷ psʳ)) (zip-es-flat-[]-es {l+s} {ε∈l+s} (e ∷ es) (flat-[]-e ∷ flat-[]-es)))) (List.map pdinstance-fst psˡ))
        rest =  >-inc-pdinstance-oplus-sub psˡ (pʳ ∷ psʳ) all->-inc-psˡ  (>-inc-pʳ ∷ all->-inc-psʳ)


-----------------------------------------------------------------------------
-- Sub Lemma 33.1 - 33.9 END
----------------------------------------------------------------------------

```


#### Main proof for Lemma 33

```agda

-- main lemma proof
pdU->-inc : ∀ { r : RE } { c : Char }
  → All (>-Inc {r} {c}) pdU[ r , c ]


pdUConcat->-inc : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
    → All (>-Inc {l ● r ` loc } {c}) (pdUConcat l r ε∈l loc c)


pdU->-inc {ε} {c} = []
pdU->-inc {$ c ` loc} {c'} with c Char.≟ c'
...  | no ¬c≡c' = []
...  | yes refl =  ( >-inc (λ { EmptyU EmptyU empty>empty →  Nullary.contradiction refl (>→¬≡ empty>empty)  } ) ) ∷ []

pdU->-inc {l + r ` loc} {c} =  >-inc-pdinstance-oplus-+ {l} {r} {loc} {c} pdU[ l , c ] pdU[ r , c ]  ind-hyp-l ind-hyp-r 
  where
    ind-hyp-l : All (>-Inc {l} {c}) pdU[ l , c ]
    ind-hyp-l = pdU->-inc {l} {c}
    
    ind-hyp-r : All (>-Inc {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU->-inc {r} {c}
    

pdU->-inc {r * ε∉r ` loc } {c} = all->-inc-map-star
  where
    ind-hyp-r : All (>-Inc {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU->-inc {r} {c}

    all->-inc-map-star : All (>-Inc {r * ε∉r ` loc} {c}) (List.map (pdinstance-star {r} {ε∉r} {loc} {c})  pdU[ r , c ])
    all->-inc-map-star  = >-inc-map-star pdU[ r , c ] ind-hyp-r

pdU->-inc {l ● r ` loc} {c} with ε∈? l
...                           | no ¬ε∈l = >-inc-map-fst pdU[ l , c ] ind-hyp-l
  where 
    ind-hyp-l : All (>-Inc {l} {c}) pdU[ l , c ]
    ind-hyp-l = pdU->-inc {l} {c}
    
pdU->-inc {l ● r ` loc} {c}  | yes ε∈l = pdUConcat->-inc   




{-# TERMINATING #-}
pdUConcat->-inc {ε} {r} {ε∈ε} {loc} {c} = all-concat all->-inc-pdis-inj-from-l-c all->-inc-concatmap-pdinstance-snd 
  where
    ind-hyp-l : All (>-Inc {ε} {c}) pdU[ ε , c ]
    ind-hyp-l = pdU->-inc {ε} {c}

    all->-inc-pdis-inj-from-l-c : All (>-Inc {ε ● r ` loc} {c}) (List.map (pdinstance-fst {ε} {r} {loc} {c}) pdU[ ε , c ])
    all->-inc-pdis-inj-from-l-c =  >-inc-map-fst pdU[ ε , c ] ind-hyp-l
    
    ind-hyp-r : All (>-Inc {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU->-inc {r} {c}

    all->-inc-concatmap-pdinstance-snd : All (>-Inc {ε ● r ` loc} {c}) (concatmap-pdinstance-snd {ε} {r} {ε∈ε} {loc} {c} pdU[ r , c ])
    all->-inc-concatmap-pdinstance-snd  = >-inc-concatmap-pdinstance-snd {ε} {r} {ε∈ε} {loc} {c} pdU[ r , c ] ind-hyp-r

pdUConcat->-inc { l * ε∉l ` loc₂ } {r} {ε∈*} {loc} {c} = all-concat all->-inc-pdis-inj-from-l-c all->-inc-concatmap-pdinstance-snd 
  where
    ind-hyp-l : All (>-Inc {l * ε∉l ` loc₂} {c}) pdU[ l * ε∉l ` loc₂ , c ]
    ind-hyp-l = pdU->-inc {l * ε∉l ` loc₂} {c}

    all->-inc-pdis-inj-from-l-c : All (>-Inc {(l * ε∉l ` loc₂) ● r ` loc} {c}) (List.map (pdinstance-fst {l * ε∉l ` loc₂} {r} {loc} {c}) pdU[ l * ε∉l ` loc₂ , c ])
    all->-inc-pdis-inj-from-l-c =  >-inc-map-fst pdU[ l * ε∉l ` loc₂ , c ] ind-hyp-l
    
    ind-hyp-r : All (>-Inc {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU->-inc {r} {c}

    all->-inc-concatmap-pdinstance-snd : All (>-Inc {(l * ε∉l ` loc₂) ● r ` loc} {c}) (concatmap-pdinstance-snd {l * ε∉l ` loc₂} {r} {ε∈*} {loc} {c}  pdU[ r , c ])
    all->-inc-concatmap-pdinstance-snd  = >-inc-concatmap-pdinstance-snd {l * ε∉l ` loc₂} {r} {ε∈*} {loc} {c}  pdU[ r , c ] ind-hyp-r

pdUConcat->-inc { l ● s ` loc₂ } {r} {ε∈l●s} {loc} {c} =  all-concat all->-inc-pdis-inj-from-l-c all->-inc-concatmap-pdinstance-snd 
  where
    ind-hyp-l : All (>-Inc {l ● s ` loc₂} {c}) pdU[ l ● s ` loc₂ , c ]
    ind-hyp-l = pdU->-inc {l ● s ` loc₂} {c}
    
    all->-inc-pdis-inj-from-l-c : All (>-Inc {(l ● s ` loc₂) ● r ` loc} {c}) (List.map (pdinstance-fst {l ● s ` loc₂} {r} {loc} {c}) pdU[ l ● s ` loc₂ , c ])
    all->-inc-pdis-inj-from-l-c =  >-inc-map-fst pdU[ l ● s ` loc₂ , c ] ind-hyp-l
    
    ind-hyp-r : All (>-Inc {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU->-inc {r} {c}

    all->-inc-concatmap-pdinstance-snd : All (>-Inc {(l ● s ` loc₂) ● r ` loc} {c}) (concatmap-pdinstance-snd {l ● s ` loc₂} {r} {ε∈l●s} {loc} {c}  pdU[ r , c ])
    all->-inc-concatmap-pdinstance-snd  = >-inc-concatmap-pdinstance-snd {l ● s ` loc₂} {r} {ε∈l●s} {loc} {c}  pdU[ r , c ] ind-hyp-r
  

pdUConcat->-inc { l + s ` loc₂ } {r} {ε∈l+s} {loc} {c} =  all->-inc-oplus-map-fst-concatmap-snd
  where

    ind-hyp-l : All (>-Inc {l} {c}) pdU[ l , c ]
    ind-hyp-l = pdU->-inc {l} {c}     

    ind-hyp-s : All (>-Inc {s} {c}) pdU[ s , c ]
    ind-hyp-s = pdU->-inc {s} {c}     

    ind-hyp-r : All (>-Inc {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU->-inc {r} {c}


    all->-inc-oplus-map-left-pdu-l-c-map-right-pdu-r-c : All (>-Inc {l + s ` loc₂} {c}) (pdinstance-oplus {l + s ` loc₂ } {loc₂} {c} (List.map pdinstance-left pdU[ l , c ]) (List.map pdinstance-right pdU[ s , c ]))
    all->-inc-oplus-map-left-pdu-l-c-map-right-pdu-r-c =  >-inc-pdinstance-oplus-+ {l} {s} {loc₂} {c} pdU[ l , c ] pdU[ s , c ]  ind-hyp-l ind-hyp-s  

    all->-inc-oplus-map-fst-concatmap-snd : All >-Inc (pdinstance-oplus (List.map pdinstance-fst (pdinstance-oplus (List.map pdinstance-left pdU[ l , c ]) (List.map pdinstance-right pdU[ s , c ])))
                                            (concatmap-pdinstance-snd {l + s ` loc₂} {r} {ε∈l+s} {loc} {c} pdU[ r , c ]))
    all->-inc-oplus-map-fst-concatmap-snd =
      >-inc-pdinstance-oplus-+● {l + s ` loc₂} {r} {ε∈l+s} {loc} {c}
                                (pdinstance-oplus (List.map pdinstance-left pdU[ l , c ]) (List.map pdinstance-right pdU[ s , c ]))
                                pdU[ r , c ]
                                all->-inc-oplus-map-left-pdu-l-c-map-right-pdu-r-c
                                ind-hyp-r 

```



### Definition 34: >-Strict increaseing PDInstance*

Let r be a non problematic regular expression.
Let w be a word.
Let pdi be a PDInstance* w.r.t r and w.
We say pdi is >-inc (strict increasing) iff,
  1. p be the partial derivative descendant inhabited in pdi, and
  2. inj is the injection function from parse tress of p to parse tress of r.
  3. for all parse trees p, u₁ and u₂ where p ⊢ u₁ > u₂
  Then r ⊢ inj u₁ > inj u₂

```agda

data *>-Inc : ∀ { r : RE } { w : List Char } → PDInstance* r w → Set where
  *>-inc : ∀ { p r : RE } { w : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → (proj₁ ( flat {r} (inj x ) ) ≡ w ++ (proj₁ (flat {p} x))) }
    → ( (u₁ : U p) → (u₂ : U p ) → p ⊢ u₁ > u₂ → r ⊢ inj u₁ > inj u₂ ) -- strict increasing evidence
    → *>-Inc {r} {w} (pdinstance* {p} {r} {w} inj sound-ev) 

```



### Lemma 35 : all pdinstance*'s from pdUMany[ r , w ] are >-strict increasing .

Let r be a non problematic regular expression.
Let w be a word.
Then for all pdi ∈ pdUMany[ r , w ], pdi is >-strict increasing. 


#### Sub Lemma 35.1 - 35.3 : *>-Inc is preserved inductively over pdinstance*'s operations

```agda
-----------------------------------------------------------------------------
-- Sub Lemma 35.1 - 35.3 BEGIN 
----------------------------------------------------------------------------
compose-pdi-with-*>-inc : { r d : RE } { pref : List Char } { c : Char }
                   → ( d→r : U d → U r )
                   → ( s-ev-d→r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
                   → (pdi : PDInstance d c)
                   → >-Inc pdi
                   → ( (x₁ : U d) → (x₂ : U d) → (d ⊢ x₁ > x₂) → r ⊢ d→r x₁ > d→r x₂ )
                   ---------------------------------------------------------------
                   → *>-Inc (compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d→r pdi)
compose-pdi-with-*>-inc {r} {d} {pref} {c} d→r s-ev-d→r pdi@(pdinstance {p} {d} {c}  p→d s-ev-p→d) (>-inc u₁→u₂→u₁>u₂→pd-u₁>pd-u₂ ) x₁→x₂→x₁>x₂→dr-x₁>dr-x₂ = *>-inc ev-*>-inc 
  where
    ev-*>-inc : (v₁ v₂ : U p)
      → p ⊢ v₁ > v₂
      → r ⊢ d→r (p→d v₁) > d→r (p→d v₂)
    ev-*>-inc v₁ v₂ v₁>v₂ = x₁→x₂→x₁>x₂→dr-x₁>dr-x₂ (p→d v₁) (p→d v₂) (u₁→u₂→u₁>u₂→pd-u₁>pd-u₂ v₁ v₂ v₁>v₂)   


advance-pdi*-with-c-*>-inc : ∀ { r : RE } { pref : List Char } { c : Char}
  → (pdi : PDInstance* r pref)
  → *>-Inc pdi
  ----------------------------------------------------------
  → All *>-Inc (advance-pdi*-with-c {r} {pref} {c} pdi)
advance-pdi*-with-c-*>-inc {r} {pref} {c} pdi@(pdinstance* {d} {r} {pref} d→r s-ev-d→r) (*>-inc u₁→u₂→u₁>u₂→dr-u₁>dr-u₂)= go pdU[ d , c ]  (pdU->-inc {d} {c}) 
  where
    go : ( pdis : List (PDInstance d c) )
       → All >-Inc pdis
       → All *>-Inc (List.map (compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d→r) pdis)
    go [] [] = []
    go (pdi ∷ pdis) (pdi->-inc ∷ all->-inc-pdis) = ( compose-pdi-with-*>-inc {r} {d} {pref} {c} d→r s-ev-d→r pdi pdi->-inc u₁→u₂→u₁>u₂→dr-u₁>dr-u₂ ) ∷ go pdis all->-inc-pdis 


concatmap-advance-pdi*-with-c-*>inc : ∀ { r : RE } { pref : List Char } { c : Char}
  → (pdis : List (PDInstance* r pref) )
  → All *>-Inc pdis
  ----------------------------------------------------------
  → All *>-Inc (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
concatmap-advance-pdi*-with-c-*>inc {r} {pref} {c} [] [] = []
concatmap-advance-pdi*-with-c-*>inc {r} {pref} {c} (pdi ∷ pdis) (pdi-*>-inc ∷ all-*>-inc-pdis) = all-concat all-*>-inc-advance-pdi*-with-c-pdi ind-hyp 

  where
    all-*>-inc-advance-pdi*-with-c-pdi : All *>-Inc (advance-pdi*-with-c {r} {pref} {c} pdi)
    all-*>-inc-advance-pdi*-with-c-pdi = advance-pdi*-with-c-*>-inc pdi pdi-*>-inc

    ind-hyp : All *>-Inc (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    ind-hyp = concatmap-advance-pdi*-with-c-*>inc {r} {pref} {c} pdis all-*>-inc-pdis

-----------------------------------------------------------------------------
-- Sub Lemma 35.1 - 35.3 END
----------------------------------------------------------------------------

```



#### Main proof for Lemma 35

```agda

pdUMany-aux-*>-inc : ∀ { r : RE } { pref : List Char} 
  → (suff : List Char )
  → (pdis : List (PDInstance* r pref))
  → All *>-Inc pdis
  ----------------------------------------------------
  → All *>-Inc (pdUMany-aux suff pdis)
pdUMany-aux-*>-inc {r} {pref} [] pdis all-*>-inc-pdis rewrite (++-identityʳ pref) = all-*>-inc-pdis
pdUMany-aux-*>-inc {r} {pref} ( c ∷ cs) pdis all-*>-inc-pdis = pdUMany-aux-*>-inc {r} {pref ∷ʳ c} cs (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis) concatmap-advance-pdi*-with-c-pdis-all-*>inc

  where
    concatmap-advance-pdi*-with-c-pdis-all-*>inc : All *>-Inc (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    concatmap-advance-pdi*-with-c-pdis-all-*>inc = concatmap-advance-pdi*-with-c-*>inc pdis all-*>-inc-pdis 



pdUMany-*>-inc : ∀ { r : RE } { w : List Char }
  → All (*>-Inc {r} {w}) pdUMany[ r  , w ]
pdUMany-*>-inc {r} {w} = pdUMany-aux-*>-inc w  [  ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ] (*>-inc ev-*>-inc  ∷ [] )
  where
    ev-*>-inc : (u₁ : U r)
      → (u₂ : U r)
      → r ⊢ u₁ > u₂
      --------------------------------
      → r ⊢ (λ u → u) u₁ > (λ u → u) u₂ 
    ev-*>-inc u₁ u₂ u₁>u₂ = u₁>u₂ 
  
```




Lemma : a posix parse tree must be flattened to the indexed word. 


```agda

⇒-member : ∀ { r : RE } { v : U r } { w : List Char} 
    → w , r ⇒ v
    → proj₁ (flat {r} v) ≡ w
⇒-member {ε}             {EmptyU}     {[]}      p₁                 = refl
⇒-member {$ c ` loc}     {LetterU .c} {.c ∷ []} (pc .{c} .{loc})   = refl
⇒-member {l ● r ` loc}   {PairU v u}  {w}       (ps {w₁} {w₂} .{w} .{l} .{r} .{loc} .{v} .{u} w≡w₁++w₂ w₁,l→v w₂,r→u longest-ev) = prf
  where
    ind-hyp-l : proj₁ (flat {l} v) ≡ w₁
    ind-hyp-l = ⇒-member w₁,l→v 
    ind-hyp-r : proj₁ (flat {r} u) ≡ w₂
    ind-hyp-r = ⇒-member w₂,r→u
    prf : proj₁ (flat (PairU {l} {r} {loc} v u)) ≡ w
    prf rewrite  ind-hyp-l |  ind-hyp-r = sym w≡w₁++w₂
⇒-member {l + r ` loc}   {LeftU v}  {w}       (p+l .{w} .{l} .{r} .{loc} .{v} w,l→v)       = ⇒-member w,l→v 
⇒-member {l + r ` loc}   {RightU v} {w}       (p+r .{w} .{l} .{r} .{loc} .{v} w,r→v ¬w∈⟦l⟧) = ⇒-member w,r→v 
⇒-member {r * ε∉r ` loc} {ListU []} {[]}      (p[] .{r} .{ε∉r} .{loc}) = refl 
⇒-member {r * ε∉r ` loc} {ListU (x ∷ xs)} {w} (p* {w₁} {w₂} .{w} .{r} .{ε∉r} .{loc} .{x} .{xs} w≡w₁++w₂ w₁,r→x w₂,r*→list-xs ¬w₁≡[] longest-ev) = prf
  where
    ind-hyp-x : proj₁ (flat {r} x) ≡ w₁
    ind-hyp-x = ⇒-member w₁,r→x
    ind-hyp-list-xs : proj₁ (flat {r * ε∉r ` loc} (ListU xs)) ≡ w₂
    ind-hyp-list-xs = ⇒-member w₂,r*→list-xs 
    prf : proj₁ (flat {r * ε∉r ` loc} (ListU (x ∷ xs))) ≡ w
    prf rewrite  ind-hyp-x |  ind-hyp-list-xs = sym w≡w₁++w₂

```

Lemma : a posix parse tree is the max value in posix ordering > 

```agda

⇒→>-max : ∀ { r : RE } { v : U r } { w : List Char} 
    → w , r ⇒ v
    → ( u : U r )
    → ¬ ( v ≡ u )
    → proj₁ (flat v) ≡ proj₁ (flat u) 
    ------------------
    → ( r ⊢ v > u )
⇒→>-max {ε}           {EmptyU}    {[]}      p₁          EmptyU      ¬empty≡empty       refl   = Nullary.contradiction refl ¬empty≡empty
⇒→>-max {$ c ` loc}   {LetterU _} .{c ∷ []} pc          (LetterU _) ¬letter-c≡letter-c refl = Nullary.contradiction refl ¬letter-c≡letter-c
⇒→>-max {l + r ` loc} {LeftU v}   {w}       (p+l w,l→v) (LeftU u)   ¬left-v≡left-u     |left-v|≡|left-u|  = len-≡  len|left-v|≡len|left-u| (choice-ll v>u )
  where
    len|left-v|≡len|left-u| : length (proj₁ (flat (LeftU {l} {r} {loc} v))) ≡ length (proj₁ (flat (LeftU {l} {r} {loc} u)))
    len|left-v|≡len|left-u| rewrite |left-v|≡|left-u| = refl

    ¬v≡u : ¬ v ≡ u
    ¬v≡u v≡u = ¬left-v≡left-u (cong LeftU v≡u) 

    v>u : l ⊢ v > u
    v>u = ⇒→>-max {l} {v} {w} w,l→v u ¬v≡u |left-v|≡|left-u|

⇒→>-max {l + r ` loc} {RightU v}   {w}       (p+r w,r→v ¬w∈⟦l⟧) (RightU u)   ¬right-v≡right-u     |right-v|≡|right-u|  = len-≡  len|right-v|≡len|right-u| (choice-rr v>u )
  where
    len|right-v|≡len|right-u| : length (proj₁ (flat (RightU {l} {r} {loc} v))) ≡ length (proj₁ (flat (RightU {l} {r} {loc} u)))
    len|right-v|≡len|right-u| rewrite |right-v|≡|right-u| = refl

    ¬v≡u : ¬ v ≡ u
    ¬v≡u v≡u = ¬right-v≡right-u (cong RightU v≡u) 

    v>u : r ⊢ v > u
    v>u = ⇒→>-max {r} {v} {w} w,r→v u ¬v≡u |right-v|≡|right-u|


⇒→>-max {l + r ` loc} {RightU v}   {w}       (p+r w,r→v ¬w∈⟦l⟧) (LeftU u)   ¬right-v≡left-u     |right-v|≡|left-u|  = Nullary.contradiction w∈⟦l⟧ ¬w∈⟦l⟧
  where
    |left-u|≡w : proj₁ (flat {l + r ` loc} (LeftU {l} {r} {loc} u)) ≡ w
    |left-u|≡w rewrite (sym  |right-v|≡|left-u| )  =  ⇒-member (p+r {w} {l} {r} {loc} {v}  w,r→v ¬w∈⟦l⟧)
    w∈⟦l⟧ : w ∈⟦ l ⟧
    w∈⟦l⟧ rewrite (sym |left-u|≡w) =  proj₂ (flat {l} u)  

⇒→>-max {l + r ` loc} {LeftU v}   {w}       (p+l w,l→v) (RightU u)   ¬left-v≡Right-u     |left-v|≡|right-u|  = len-≡  len|left-v|≡len|right-u| (choice-lr len|v|≥len|u| )
  where
    len|left-v|≡len|right-u| : length (proj₁ (flat (LeftU {l} {r} {loc} v))) ≡ length (proj₁ (flat (RightU {l} {r} {loc} u)))
    len|left-v|≡len|right-u| rewrite |left-v|≡|right-u| = refl

    len|v|≥len|u| : length (proj₁ (flat {l} v)) ≥ length (proj₁ (flat {r} u))
    len|v|≥len|u| rewrite |left-v|≡|right-u| = ≤-refl  


⇒→>-max {r * ε∉r ` loc} {ListU []} {[]}             (p[] .{r} .{ε∉r} .{loc}) (ListU []) ¬list-[]≡list-[] |list-[]|≡|list-[]| = Nullary.contradiction refl ¬list-[]≡list-[]

⇒→>-max {r * ε∉r ` loc} {ListU []} {[]}             (p[] .{r} .{ε∉r} .{loc}) (ListU (u ∷ us)) ¬list-[]≡list-u∷us |list-[]|≡|list-u∷us| =  Nullary.contradiction  (sym  |list-[]|≡|list-u∷us|)  (¬|list-u∷us|≡[] {r} {ε∉r} {loc} {u} {us})

⇒→>-max {r * ε∉r ` loc} {ListU (v ∷ vs)}  {w}  (p*  {w₁} {w₂} .{w} {r} {ε∉r} {loc} .{v} .{vs} w≡w₁++w₂ w₁,r→v w₂,r*→list-vs ¬w₁≡[] longest-ev) (ListU []) ¬list-v∷vs≡list-[] |list-v∷vs|≡|list-[]| =  Nullary.contradiction  |list-v∷vs|≡|list-[]| (¬|list-u∷us|≡[] {r} {ε∉r} {loc} {v} {vs}) 

⇒→>-max {r * ε∉r ` loc} {ListU (v ∷ vs)}  {w}  (p*  {w₁} {w₂} .{w} {r} {ε∉r} {loc} .{v} .{vs} w≡w₁++w₂ w₁,r→v w₂,r*→list-vs ¬w₁≡[] longest-ev) (ListU (u ∷ us)) ¬list-v∷vs≡list-u∷us |list-v∷vs|≡|list-u∷us| = len-≡ len|left-v∷vs|≡len|left-u∷us| list-v∷vs>ˡlist-u∷us 
  where
    len|left-v∷vs|≡len|left-u∷us| : length (proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ vs)))) ≡ length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ us))))
    len|left-v∷vs|≡len|left-u∷us| rewrite |list-v∷vs|≡|list-u∷us| = refl
    list-v∷vs>ˡlist-u∷us : (r * ε∉r ` loc) ⊢ ListU (v ∷ vs) >ⁱ ListU (u ∷ us)
    list-v∷vs>ˡlist-u∷us with length (proj₁ (flat v)) Nat.<? length (proj₁ (flat u))
    ... | yes len|v|<len|u| rewrite sym (⇒-member w₂,r*→list-vs) | sym (⇒-member w₁,r→v)
          = Nullary.contradiction anti-longest-ev  longest-ev 

        where
          anti-longest-ev-part1 : ∃[ w₅ ] ( ¬ w₅ ≡ [] ) ×
                                          ( (proj₁ (flat {r} v)) ++ w₅ ≡ (proj₁ (flat {r} u)) ) ×
                                          ( (proj₁ (flat {r * ε∉r ` loc} (ListU vs))) ≡ w₅ ++ (proj₁ (flat {r * ε∉r ` loc} (ListU us)))) 
          anti-longest-ev-part1 rewrite sym (⇒-member w₂,r*→list-vs)  = w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ {proj₁ (flat {r} v)} {proj₁ (flat {r * ε∉r ` loc} (ListU vs))} {proj₁ (flat {r} u)} {proj₁ (flat {r * ε∉r ` loc} (ListU us))}  |list-v∷vs|≡|list-u∷us|   len|v|<len|u|
          anti-longest-ev : ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) ×
                                            ( w₃ ++ w₄ ≡ proj₁ (flat {r * ε∉r ` loc} (ListU vs)) ) ×
                                            ( ( (proj₁ (flat {r} v)) ++ w₃ ) ∈⟦ r ⟧ ) ×
                                            ( w₄ ∈⟦ r * ε∉r ` loc ⟧ ) 
          anti-longest-ev = (proj₁ anti-longest-ev-part1 , ( (proj₁ (flat {r * ε∉r ` loc} (ListU us))) ,
                                      ( proj₁ (proj₂ anti-longest-ev-part1 ) ) ,
                                         ( sym (proj₂ (proj₂ (proj₂ anti-longest-ev-part1))) ,
                                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦r⟧  , proj₂ (flat { r * ε∉r ` loc}  (ListU us))   ) ) )
                          where
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦r⟧ : (Product.proj₁ (flat v) ++ Product.proj₁ anti-longest-ev-part1)  ∈⟦ r ⟧
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦r⟧ rewrite (proj₁ (proj₂ (proj₂  anti-longest-ev-part1 ))) =  proj₂ (flat {r} u) 
          
    ... | no ¬len|v|<len|u| with (¬m>n→n≡m⊎n>m ¬len|v|<len|u|)
    ...                      | inj₂ len|v|>len|u| = star-head (len-> len|v|>len|u|)
    ...                      | inj₁ len|v|≡len|u| with r ⊢ v ≟ u
    ...                                            | no ¬v≡u = star-head (⇒→>-max  w₁,r→v u ¬v≡u  (proj₁ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |list-v∷vs|≡|list-u∷us| len|v|≡len|u|)) )
    ...                                            | yes v≡u = star-tail v≡u (⇒→>-max w₂,r*→list-vs (ListU us)  ¬list-vs≡list-us  (proj₂ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |list-v∷vs|≡|list-u∷us| len|v|≡len|u|)))
                                                         where
                                                           ¬list-vs≡list-us : ¬ (ListU {r}  {ε∉r} {loc} vs) ≡ (ListU {r}  {ε∉r} {loc} us)
                                                           ¬list-vs≡list-us list-vs≡list-us =  ¬list-v∷vs≡list-u∷us ( Eq.cong₂ (λ x xs → ListU  {r}  {ε∉r} {loc} (x ∷ xs)) v≡u vs≡us )
                                                             where
                                                               vs≡us : vs ≡ us
                                                               vs≡us = inv-listU1 vs us list-vs≡list-us 


    
⇒→>-max {l ● r ` loc} {PairU {l} {r} {loc} v₁ v₂} {w}   (ps {w₁} {w₂} .{w} .{l} .{r} .{loc} .{v₁} .{v₂} w≡w₁++w₂ w₁,l→v₁ w₂,r→v₂ longest-ev) (PairU u₁ u₂) ¬pair-v₁v₂≡pair-u₁u₂ |pair-v₁v₂|≡|pair-u₁u₂| =
  len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| pair-v₁v₂>ˡpair-u₁u₂ 
  where
    len|pair-v₁v₂|≡len|pair-u₁u₂| : length (proj₁ (flat (PairU  {l} {r} {loc} v₁ v₂))) ≡ length (proj₁ (flat (PairU  {l} {r} {loc} u₁ u₂)))
    len|pair-v₁v₂|≡len|pair-u₁u₂| rewrite |pair-v₁v₂|≡|pair-u₁u₂|  =  refl 
    pair-v₁v₂>ˡpair-u₁u₂ : (l ● r ` loc) ⊢ PairU v₁ v₂ >ⁱ PairU u₁ u₂
    pair-v₁v₂>ˡpair-u₁u₂ with length (proj₁ (flat v₁)) Nat.<? length (proj₁ (flat u₁))
    ... | yes len|v₁|<len|u₁| rewrite sym (⇒-member w₂,r→v₂) | sym (⇒-member w₁,l→v₁) =  Nullary.contradiction anti-longest-ev  longest-ev 
        where
          anti-longest-ev-part1 : ∃[ w₅ ] ( ¬ w₅ ≡ [] ) ×
                                          ( (proj₁ (flat {l} v₁)) ++ w₅ ≡ (proj₁ (flat {l} u₁)) ) ×
                                          ( (proj₁ (flat {r} v₂)) ≡ w₅ ++ (proj₁ (flat {r} u₂))) 
          anti-longest-ev-part1 rewrite sym (⇒-member w₂,r→v₂)  = w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄  {proj₁ (flat {l} v₁)} {proj₁ (flat {r} v₂)} {proj₁ (flat {l} u₁)} {proj₁ (flat {r} u₂)} |pair-v₁v₂|≡|pair-u₁u₂|   len|v₁|<len|u₁|
          anti-longest-ev : ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) ×
                                            ( w₃ ++ w₄ ≡ proj₁ (flat {r} v₂) ) ×
                                            ( ( (proj₁ (flat {l} v₁)) ++ w₃ ) ∈⟦ l ⟧ ) ×
                                            ( w₄ ∈⟦ r ⟧ ) 
          anti-longest-ev = (proj₁ anti-longest-ev-part1 , ( (proj₁ (flat {r} u₂)) ,
                                      ( proj₁ (proj₂ anti-longest-ev-part1 ) ) ,
                                         ( sym (proj₂ (proj₂ (proj₂ anti-longest-ev-part1))) ,
                                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦l⟧  , proj₂ (flat {r}  u₂)   ) ) )
                          where
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦l⟧ : (Product.proj₁ (flat v₁) ++ Product.proj₁ anti-longest-ev-part1)  ∈⟦ l ⟧
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦l⟧ rewrite (proj₁ (proj₂ (proj₂  anti-longest-ev-part1 ))) =  proj₂ (flat {l} u₁) 
          
    
    ... | no ¬len|v₁|<len|u₁| with (¬m>n→n≡m⊎n>m ¬len|v₁|<len|u₁|)
    ...                        | inj₂ len|v₁|>len|u₁| = seq₁ (len-> len|v₁|>len|u₁|)
    ...                        | inj₁ len|v₁|≡len|u₁| with l ⊢ v₁ ≟ u₁
    ...                                                | no ¬v₁≡u₁ = seq₁ (⇒→>-max  w₁,l→v₁ u₁ ¬v₁≡u₁ (proj₁ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |pair-v₁v₂|≡|pair-u₁u₂| len|v₁|≡len|u₁|)))
    ...                                                | yes v₁≡u₁ = seq₂ v₁≡u₁ (⇒→>-max w₂,r→v₂ u₂  ¬v₂≡u₂ (proj₂ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |pair-v₁v₂|≡|pair-u₁u₂| len|v₁|≡len|u₁|)) )
                                                             where
                                                               ¬v₂≡u₂ : ¬ v₂ ≡ u₂
                                                               ¬v₂≡u₂ v₂≡u₂ = ¬pair-v₁v₂≡pair-u₁u₂ (Eq.cong₂ (λ x y → (PairU {l} {r} {loc} x y)) v₁≡u₁ v₂≡u₂) 

```


Lemma : the max value in the posix ordering > must be a posix parse tree.



```agda

postulate
  intersect-memberʳ : ∀ { l r : RE } { v : U r } 
    → proj₁ (flat {r} v) ∈⟦ l ⟧
    → ∃[ u ] proj₁ (flat {l} u) ∈⟦ l ⟧ 


>-max→⇒ :  ∀ { r : RE } { v : U r } 
  → ( ∀ ( u : U r ) → r ⊢ v > u )
  -----------------------------------
  → proj₁ (flat {r} v) , r ⇒ v

>-max→⇒ {ε}           {EmptyU}      max-ev = p₁
>-max→⇒ {$ c ` loc}   {LetterU .c}  max-ev = pc
>-max→⇒ {l + r ` loc} {LeftU v}     max-ev = p+l |v|,l→v
  where
    ∀u→v>u : ( u : U l ) → l ⊢ v > u
    ∀u→v>u u with max-ev (LeftU u)
    ... | len-> len|left-v|>len|left-u|                 = len-> len|left-v|>len|left-u|
    ... | len-≡ len|left-v|≡len|left-u| (choice-ll v>u) = v>u 
    |v|,l→v : proj₁ (flat {l} v) , l ⇒ v
    |v|,l→v = >-max→⇒  {l} {v} ∀u→v>u
>-max→⇒ {l + r ` loc} {RightU v}     max-ev = p+r |v|,r→v ¬|v|∈⟦l⟧ 
  where
    ∀u→v>u : ( u : U r ) → r ⊢ v > u
    ∀u→v>u u with max-ev (RightU u)
    ... | len-> len|right-v|>len|right-u|                 = len-> len|right-v|>len|right-u|
    ... | len-≡ len|right-v|≡len|right-u| (choice-rr v>u) = v>u 
  
    |v|,r→v : proj₁ (flat {r} v) , r ⇒ v
    |v|,r→v = >-max→⇒  {r} {v} ∀u→v>u
    
    ¬|v|∈⟦l⟧ : ¬ proj₁ (flat {r} v) ∈⟦ l ⟧
    ¬|v|∈⟦l⟧ |v|∈⟦l⟧ with intersect-memberʳ {l} {r} {v} |v|∈⟦l⟧
    ... |  u , proj₁flat-u∈⟦l⟧  = {!!} 



```
