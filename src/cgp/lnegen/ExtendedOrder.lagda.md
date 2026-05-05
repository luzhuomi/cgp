```agda
{-# OPTIONS --rewriting #-}
module cgp.lnegen.ExtendedOrder where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ;
  ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ; ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ;
  first ; ε∉r→¬first-r≡[] )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ∷-inj ; ¬∷≡[] ; inv-map-[] ; inv-concatMap-map-f-[] ; ¬≡[]→length>0 ) 


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )

import cgp.ParseTree as ParseTree
open ParseTree using (
  U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ;
  flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;
  flat-Uε≡[] ;
  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; unListU ; listU∘unListU ;
  u-of-r*-islist ; pair-≡ ; left-≡ ; right-≡ ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU ; ¬|list-u∷us|≡[] )

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ; mkAllEmptyU≢[] ; all-flat-[]-left ; all-flat-[]-right ; proj₁flat-v≡[]→ε∈r)

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ; 
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ; mkinjListSoundEv ;
  pdinstance-fst ; mkinjFst   ;
  pdinstance-snd ; mk-snd-pdi ; mkinjSnd ; 
  concatmap-pdinstance-snd ; zip-es-flat-[]-es  ;
  pdinstance-assoc; inv-assoc ;
  compose-pdi-with ; compose-pdi-with-soundEv
  ) 


import cgp.Recons as Recons
open Recons using ( Recons ; recons ;
  Recons* ; recons* ;
  inv-recons-left ;   inv-recons-right ; inv-recons-fst ; inv-recons-snd ; inv-recons-star ; inv-recons-assoc ; 
  inv-recons*-compose-pdi-with ; 
  ¬recons-right-from-pdinstance-left ; ¬recons-left-from-pdinstance-right ; ¬recons-[]-from-pdinstance-star 
  )


import cgp.lnegen.PartialDerivative as PartialDerivative
open PartialDerivative using (
  pdU[_,_] ; 
  pdUMany[_,_]; pdUMany-aux;
  advance-pdi*-with-c ; 
  parseAll[_,_] ; buildU ;
  pdi*-∃  ;
  recons-v→¬proj₁flat-v≡[] ) 


import cgp.lnegen.Order as LNEOrder
open LNEOrder using ( _⊢_>_ ; seq₁ ; seq₂ ;
  be ; bne ; lne ; choice-ll ; choice-lr ; choice-rr  ; star-head ; star-cons-nil ;
  >-sorted ; >-nil ; >-cons ; concat-sorted ; 
  mkAllEmptyU-sorted ;
  >-maybe ; >-nothing ; >-just ;
  _⊢_≅_ ; ≅-Preserve ; ≅-pres ; pdU-≅-preserve ;
  ≅-Preserve* ; ≅-pres* ; 
  mkAllEmptyU-≅ ; All-≅ ;  all-≅-nil ;  all-≅-cons ; All-≅→All ; 
  >-trans ; >-Inc-≅ ; >-inc ; 
  *>-Inc-≅  ; *>-inc ;
  concatmap-advance-pdi*-with-c-*>inc ;
  pdUMany-*>-inc )   


import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.Unit as Unit
open Unit using (⊤ ; tt)

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_  ; length ; inits )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalˡ ; ++-conicalʳ ;  ++-assoc )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)


import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map ; tabulate )

open import Data.List.Relation.Unary.Any using (Any; here; there ; map)

import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )



import Data.List.Membership.Propositional
open Data.List.Membership.Propositional using (_∈_)


import Relation.Nullary as Nullary 
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

open import Function using (_∘_ ; flip)
```


### Definition 36 : (Extended) left non-empty (LNE) ordering among PDInstances 

Let r be a non problematic regular expression.

Let c be a letter.

Let pdi₁ and pdi₂ be two partial derivative instances of r w.r.t c.

We say pdi₁ is "left non-empty" greater than pdi₂, r , c  ⊢ pdi₁ > pdi₂ iff
  for all parse trees u₁ u₂  of r, u₁ is constructible from pdi₁ and u₂ is constructibled from pdi₂ 
    then r ⊢ u₁ > u₂ 


```agda

infix 4 _,_⊢_∈_
data _,_⊢_∈_ : ∀ ( r : RE ) → ( c : Char ) → ( sf : List Char ) → PDInstance r c → Set where -- c is the leading character , sf is suffix
  ∈-pdi : ∀ { p r : RE } { c : Char } { sf : List Char }
    → sf ∈⟦ p ⟧ 
    → ( inj : U p → U r )
    → ( s-ev : ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) )
    → r , c ⊢ sf ∈ (pdinstance inj s-ev )

infix 4 _,_⊢_>_

data _,_⊢_>_ : ∀ ( r : RE ) → (c : Char ) → PDInstance r c → PDInstance r c → Set where
  >-pdi : ∀ { r : RE } { c : Char } 
    → ( pdi₁ : PDInstance r c )
    → ( pdi₂ : PDInstance r c )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r ) → (Recons u₁ pdi₁ ) → (Recons u₂ pdi₂) →  r ⊢ u₁ > u₂ )
    → r , c ⊢ pdi₁ > pdi₂




p-inhabit : ∀ { r : RE } { c : Char } → PDInstance r c → RE 
p-inhabit {r} {c} (pdinstance {p} {r} {c} _ _ ) = p

inj-inhabit : ∀ { r : RE } { c : Char } → (pdi : PDInstance r c) → ( U (p-inhabit pdi) → U r  )
inj-inhabit {r} {c} (pdinstance {p} {r} {c} inj _ ) = inj 

s-ev-inhabit : ∀ { r : RE } { c : Char } → (pdi : PDInstance r c) → ( ( u : U (p-inhabit pdi)) → proj₁ (flat ((inj-inhabit pdi) u)) ≡ c ∷ (proj₁ (flat u))   )
s-ev-inhabit {r} {c} (pdinstance {p} {r} {c} inj s-ev ) = s-ev


data _,_⊢_≥_ : ∀ ( r : RE ) → (c : Char ) → PDInstance r c → PDInstance r c → Set where
  ≥-pdi-= : ∀ { r  : RE } { c : Char }
    → ( pdi : PDInstance r c )
    → ( ( u₁ : U ( p-inhabit pdi ) )
        → ( u₂ : U ( p-inhabit pdi ) )
        → (p-inhabit pdi) ⊢ u₁ ≅ u₂ 
        → (p-inhabit pdi) ⊢ u₁ > u₂ 
        → ( r ⊢ (inj-inhabit pdi) u₁ ≅ (inj-inhabit pdi) u₂) × ( r ⊢ (inj-inhabit pdi) u₁ > (inj-inhabit pdi) u₂) )    
    → r ,  c  ⊢ pdi ≥ pdi 

  ≥-pdi-> : ∀ { r : RE } { c : Char }
    → ( pdi₁ : PDInstance r c )
    → ( pdi₂ : PDInstance r c )
    → ¬ (p-inhabit pdi₁ ≡ p-inhabit pdi₂)
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r ) → (Recons u₁ pdi₁ ) → (Recons u₂ pdi₂) →  r ⊢ u₁ > u₂ )
    → r , c ⊢ pdi₁ ≥ pdi₂


{- we don't need this? , we have not defined pdi-∃ 
>-pdi-trans : ∀ { r : RE } { c : Char } 
  → { pdi₁ : PDInstance r c }
  → { pdi₂ : PDInstance r c }
  → { pdi₃ : PDInstance r c }
  → r , c ⊢ pdi₁ > pdi₂
  → r , c ⊢ pdi₂ > pdi₃
  -------------------------------------------  
  → r , c ⊢ pdi₁ > pdi₃
>-pdi-trans {r} {c} {pdi₁} {pdi₂} {pdi₃} (>-pdi pdi₁ pdi₂  u₁→u₂→rec₁→rec₂→u₁>u₂)  (>-pdi .pdi₂ pdi₃ u₂→u₃→rec₂→rec₃→u₂>u₃)  = >-pdi pdi₁ pdi₃ >-ev 
  where
    >-ev : ( u₁ : U r )
          → ( u₃ : U r )
          → Recons u₁ pdi₁
          → Recons u₃ pdi₃
          ------------------------------
          → r ⊢ u₁ > u₃
    >-ev u₁ u₃ recons₁ recons₃ =
      let u₂-recons₂ = pdi-∃ pdi₂
      in >-trans (u₁→u₂→rec₁→rec₂→u₁>u₂ u₁ (proj₁ u₂-recons₂) recons₁ (proj₂ u₂-recons₂))
                  (u₂→u₃→rec₂→rec₃→u₂>u₃ (proj₁ u₂-recons₂) u₃ (proj₂ u₂-recons₂) recons₃)  -- where to get u₂ and recons₂ ?
-}

```


### Definition 37 : (Extended) left non-empty order (LNE) sortedness

```agda


data Ex>-maybe : ∀ { r : RE } { c : Char } ( pdi : PDInstance r c ) → ( mpdi : Maybe (PDInstance r c) ) → Set where
  ex>-nothing : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c } 
    ---------------------------
    → Ex>-maybe {r} {c} pdi nothing
  ex>-just : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c }
    → { pdi' : PDInstance r c }
    → r , c ⊢ pdi > pdi' 
    ----------------------------------
    → Ex>-maybe {r} {c} pdi (just pdi')

data Ex>-sorted : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) ) → Set where
  ex>-nil  : ∀ { r : RE } { c : Char } → Ex>-sorted {r} {c} []
  ex>-cons : ∀ { r : RE } { c : Char } 
    → { pdi : PDInstance r c }
    → { pdis : List (PDInstance r c) } 
    → Ex>-sorted  {r} {c} pdis 
    → Ex>-maybe {r} {c} pdi (head pdis)
    --------------------------------------
    → Ex>-sorted {r} {c} ( pdi ∷ pdis ) 


data Ex≥-maybe : ∀ { r : RE } { c : Char } ( pdi : PDInstance r c ) → ( mpdi : Maybe (PDInstance r c) ) → Set where
  ex≥-nothing : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c } 
    ---------------------------
    → Ex≥-maybe {r} {c} pdi nothing
  ex≥-just : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c }
    → { pdi' : PDInstance r c }
    → r , c ⊢ pdi ≥ pdi' 
    ----------------------------------
    → Ex≥-maybe {r} {c} pdi (just pdi')

data Ex≥-sorted : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) ) → Set where
  ex≥-nil  : ∀ { r : RE } { c : Char } → Ex≥-sorted {r} {c} []
  ex≥-cons : ∀ { r : RE } { c : Char } 
    → { pdi : PDInstance r c }
    → { pdis : List (PDInstance r c) } 
    → Ex≥-sorted  {r} {c} pdis 
    → Ex≥-maybe {r} {c} pdi (head pdis)
    --------------------------------------
    → Ex≥-sorted {r} {c} ( pdi ∷ pdis ) 


```



### Lemma 38: the list of pdinstances from pdU[ r , c] is extended LNE sorted. 


Let r be a non problematic regular expression.

Let c be a letter.

Then pdU[r , c] is LNE sorted. 



#### Sub Lemma 38.1 - 38.22 : Ex>-sortedness is preserved inductively over pdinstance operations.

```agda

-------------------------------------------------------------
-- Sub Lemma 38.1 - 38.22 BEGIN
-------------------------------------------------------------



left-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁  : PDInstance l c )
  → (pdi₂ : PDInstance l c )
  → l , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (l + r ` loc) , c ⊢ pdinstance-left pdi₁ > pdinstance-left pdi₂
left-ex-sorted {l} {r} {loc} {c} pdi₁ pdi₂ (>-pdi _ _ pdi₁>-pdi₂-ev ) = >-pdi left-pdi₁ left-pdi₂ ev
  where
    left-pdi₁ : PDInstance ( l + r ` loc ) c
    left-pdi₁ = pdinstance-left pdi₁
    left-pdi₂ : PDInstance ( l + r ` loc ) c    
    left-pdi₂ = pdinstance-left pdi₂    
 
    ev : ∀ ( u₁ : U  (l + r ` loc) )
          → ( u₂ : U  (l + r ` loc) )
          → ( Recons u₁ left-pdi₁ )
          → ( Recons u₂ left-pdi₂ )
          -------------------------
          → ( (l + r ` loc) ⊢ u₁ > u₂ )
    ev (LeftU v₁) (LeftU v₂)  recons-left-v₁-pdi-left recons-left-v₂-pdi-left =
             {-
             to make use of
              1) pdi₁>-pdi₂-ev : (u₃ u₄ : U l₁) → Recons u₃ pdi₁ → Recons u₄ pdi₂ → l₁ ⊢ u₃ > u₄
              we need to compute recons v pd₁ from recons (Left v) left-pdi₁
              2) then we have l ⊢ v > u , we can apply choice-ll rule to get l + r ` loc ⊢ LeftU v > LeftU u
             -}
             bne (¬≡[]→length>0 ¬proj₁flat-v₁≡[] ) (¬≡[]→length>0 ¬proj₁flat-v₂≡[]) (choice-ll (pdi₁>-pdi₂-ev v₁ v₂ recons-v₁-pdi₁ recons-v₂-pdi₂)) 
          where
            recons-v₁-pdi₁ : Recons v₁ pdi₁
            recons-v₁-pdi₁ = inv-recons-left {l} {r} {loc} v₁  pdi₁  recons-left-v₁-pdi-left
            recons-v₂-pdi₂ : Recons v₂ pdi₂            
            recons-v₂-pdi₂ = inv-recons-left {l} {r} {loc} v₂  pdi₂  recons-left-v₂-pdi-left
            ¬proj₁flat-v₁≡[] : ¬ (proj₁ (flat v₁) ≡ [])
            ¬proj₁flat-v₁≡[] = recons-v→¬proj₁flat-v≡[] v₁ pdi₁ recons-v₁-pdi₁
            ¬proj₁flat-v₂≡[] : ¬ (proj₁ (flat v₂) ≡ [])
            ¬proj₁flat-v₂≡[] = recons-v→¬proj₁flat-v≡[] v₂ pdi₂ recons-v₂-pdi₂


       
    ev (RightU v₁)  _          recons-right-v₁-pdi-left _  =  Nullary.contradiction recons-right-v₁-pdi-left (¬recons-right-from-pdinstance-left v₁ pdi₁ ) -- impossible cases
    ev (LeftU _)   (RightU v₂) _  recons-right-v₂-pdi-left =   Nullary.contradiction recons-right-v₂-pdi-left (¬recons-right-from-pdinstance-left v₂ pdi₂  )


right-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁ : PDInstance r c )
  → (pdi₂ : PDInstance r c )
  → r , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (l + r ` loc) , c ⊢ pdinstance-right pdi₁ > pdinstance-right pdi₂
right-ex-sorted {l} {r} {loc} {c} pdi₁ pdi₂ (>-pdi _ _ pdi₁>-pdi₂-ev ) = >-pdi right-pdi₁ right-pdi₂ ev
  where
    right-pdi₁ : PDInstance ( l + r ` loc ) c
    right-pdi₁ = pdinstance-right pdi₁
    right-pdi₂ : PDInstance ( l + r ` loc ) c    
    right-pdi₂ = pdinstance-right pdi₂    
 
    ev : ∀ ( u₁ : U  (l + r ` loc) )
          → ( u₂ : U  (l + r ` loc) )
          → ( Recons u₁ right-pdi₁ )
          → ( Recons u₂ right-pdi₂ )
          -------------------------
          → ( (l + r ` loc) ⊢ u₁ > u₂ )
    ev (RightU v₁) (RightU v₂)  recons-right-v₁-pdi-right recons-right-v₂-pdi-right =
      bne  (¬≡[]→length>0 ¬proj₁flat-v₁≡[] ) (¬≡[]→length>0 ¬proj₁flat-v₂≡[]) (choice-rr (pdi₁>-pdi₂-ev v₁ v₂ recons-v₁-pdi₁ recons-v₂-pdi₂) )  
        where
          recons-v₁-pdi₁ : Recons v₁ pdi₁
          recons-v₁-pdi₁ = inv-recons-right {l} {r} {loc} v₁  pdi₁  recons-right-v₁-pdi-right  
          recons-v₂-pdi₂ : Recons v₂ pdi₂            
          recons-v₂-pdi₂ = inv-recons-right {l} {r} {loc} v₂  pdi₂  recons-right-v₂-pdi-right 
          ¬proj₁flat-v₁≡[] : ¬ (proj₁ (flat v₁) ≡ [])
          ¬proj₁flat-v₁≡[] = recons-v→¬proj₁flat-v≡[] v₁ pdi₁ recons-v₁-pdi₁
          ¬proj₁flat-v₂≡[] : ¬ (proj₁ (flat v₂) ≡ [])
          ¬proj₁flat-v₂≡[] = recons-v→¬proj₁flat-v≡[] v₂ pdi₂ recons-v₂-pdi₂

       
    ev (LeftU v₁)  _             recons-left-v₁-pdi-right _  =  Nullary.contradiction recons-left-v₁-pdi-right (¬recons-left-from-pdinstance-right v₁ pdi₁ ) -- impossible cases
    ev (RightU _)  (LeftU v₂) _  recons-left-v₂-pdi-right =   Nullary.contradiction recons-left-v₂-pdi-right (¬recons-left-from-pdinstance-right v₂ pdi₂  )




-- the following look like can be combined polymorphically with map-leftU-sorted, map-rightU-sorted, map-leftU-rightU-sorted from Greedy.lagda.md
map-left-ex-sorted : ∀ { l r : RE }  { loc : ℕ } { c : Char } 
  → ( pdis : List (PDInstance l c ) )
  → Ex>-sorted {l} pdis
  → Ex>-sorted {l + r ` loc } (List.map pdinstance-left pdis)
map-left-ex-sorted []            ex>-nil = ex>-nil
map-left-ex-sorted ( pdi ∷ [] ) (ex>-cons ex>-nil (ex>-nothing) )
  = ex>-cons  ex>-nil (ex>-nothing)
map-left-ex-sorted ( pdi ∷ (pdi' ∷ pdis) ) (ex>-cons  ex>-sorted-pdis (ex>-just pdi>pdi'))
  = ex>-cons 
           (map-left-ex-sorted (pdi' ∷ pdis) ex>-sorted-pdis)
           (ex>-just (left-ex-sorted pdi pdi'  pdi>pdi'))



map-right-ex-sorted : ∀ { l r : RE }  { loc : ℕ } { c : Char } 
  → ( pdis : List (PDInstance r c ) )
  → Ex>-sorted {r} pdis
  → Ex>-sorted {l + r ` loc } (List.map pdinstance-right pdis)
map-right-ex-sorted []            ex>-nil = ex>-nil
map-right-ex-sorted ( pdi ∷ [] ) (ex>-cons ex>-nil ex>-nothing)
  = ex>-cons  ex>-nil ex>-nothing
map-right-ex-sorted ( pdi ∷ (pdi' ∷ pdis) ) (ex>-cons ex>-sorted-pdis (ex>-just pdi>pdi'))
  = ex>-cons 
           (map-right-ex-sorted (pdi' ∷ pdis) ex>-sorted-pdis)
           (ex>-just (right-ex-sorted pdi pdi'  pdi>pdi'))

map-left-right-ex-sorted : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( pdis  : List (PDInstance l c) )
  → ( pdis' : List (PDInstance r c) )
  → Ex>-sorted {l} pdis
  → Ex>-sorted {r} pdis'
  → Ex>-sorted {l + r ` loc } ((List.map pdinstance-left pdis) ++ (List.map pdinstance-right pdis'))
map-left-right-ex-sorted               []              pdis'  ex>-sorted-l-[]   ex>-sorted-r-pdis' = map-right-ex-sorted pdis' ex>-sorted-r-pdis'
map-left-right-ex-sorted {l} {r} {loc} pdis            []     ex>-sorted-l-pdis ex>-sorted-r-[] rewrite (cong (λ x → Ex>-sorted x) (++-identityʳ (List.map (pdinstance-left {l} {r} {loc}) pdis)))
  = map-left-ex-sorted  pdis ex>-sorted-l-pdis 
map-left-right-ex-sorted {l} {r} {loc} (pdi ∷ [])      (pdi' ∷ pdis')    ex>-sorted-l-pdis  ex>-sorted-r-pdis'
  = ex>-cons (map-right-ex-sorted (pdi' ∷ pdis') ex>-sorted-r-pdis') (ex>-just (>-pdi (pdinstance-left pdi) (pdinstance-right pdi')
    (λ { (LeftU v₁) (RightU v₂) recons-left-u-from-pdinstance-left   recons-right-u-from-pdinstance-right →
                let  recons-v₁-pdi = inv-recons-left {l} {r} {loc} v₁ pdi recons-left-u-from-pdinstance-left
                     recons-v₂-pdi' = inv-recons-right {l} {r} {loc} v₂ pdi' recons-right-u-from-pdinstance-right
                     ¬proj₁flat-v₁≡[] = recons-v→¬proj₁flat-v≡[] v₁ pdi recons-v₁-pdi
                     ¬proj₁flat-v₂≡[] = recons-v→¬proj₁flat-v≡[] v₂ pdi' recons-v₂-pdi' 
                in bne (¬≡[]→length>0 ¬proj₁flat-v₁≡[] ) (¬≡[]→length>0 ¬proj₁flat-v₂≡[] ) choice-lr 
        -- impossible cases
       ; (RightU v₁) _          recons-right-u-from-pdinstance-left  _              → Nullary.contradiction recons-right-u-from-pdinstance-left  (¬recons-right-from-pdinstance-left v₁ pdi )
       ; (LeftU v₁) (LeftU v₂)  _  recons-left-u-from-pdinstance-right              → Nullary.contradiction recons-left-u-from-pdinstance-right  (¬recons-left-from-pdinstance-right v₂ pdi' ) 
       }
    )))
map-left-right-ex-sorted {l} {r} {loc} (pdi₁ ∷ pdi₂ ∷ pdis)   (pdi' ∷ pdis') ex>-sorted-l-pdi₁pdi₂pdis ex>-sorted-r-pdipdis' with ex>-sorted-l-pdi₁pdi₂pdis
... | ex>-cons {l} ex>-sorted-pdi₂pdis (ex>-just (>-pdi _ _ pdi₁>pdi₂-ev) ) 
  = ex>-cons (map-left-right-ex-sorted (pdi₂ ∷ pdis) (pdi' ∷ pdis')   ex>-sorted-pdi₂pdis  ex>-sorted-r-pdipdis' ) ((ex>-just (>-pdi (pdinstance-left pdi₁) (pdinstance-left pdi₂)
    (λ { (LeftU v₁) (LeftU v₂)  recons-left-v1-from-pdinstance-left-pdi₁ recons-left-v2-from-pdinstance-left-pdi₂ →
         let recons-v₁-pdi₁ = inv-recons-left {l} {r} {loc} v₁  pdi₁  recons-left-v1-from-pdinstance-left-pdi₁
             recons-v₂-pdi₂ = inv-recons-left {l} {r} {loc} v₂  pdi₂  recons-left-v2-from-pdinstance-left-pdi₂
             ¬proj₁flat-v₁≡[] = recons-v→¬proj₁flat-v≡[] v₁ pdi₁ recons-v₁-pdi₁
             ¬proj₁flat-v₂≡[] = recons-v→¬proj₁flat-v≡[] v₂ pdi₂ recons-v₂-pdi₂  
         in bne (¬≡[]→length>0 ¬proj₁flat-v₁≡[] ) (¬≡[]→length>0 ¬proj₁flat-v₂≡[]) (choice-ll (pdi₁>pdi₂-ev v₁ v₂ recons-v₁-pdi₁ recons-v₂-pdi₂) ) 
        -- impossible cases         
       ; (RightU v₁)  _         recons-right-u-from-pdinstance-left-pdi₁ _ → Nullary.contradiction recons-right-u-from-pdinstance-left-pdi₁ ( ¬recons-right-from-pdinstance-left v₁ pdi₁ )
       ; (LeftU v₁) (RightU v₂) _ recons-right-u-from-pdinstance-left-pdi₂ → Nullary.contradiction recons-right-u-from-pdinstance-left-pdi₂ ( ¬recons-right-from-pdinstance-left v₂ pdi₂ )       
       }
    )))) 



star-ex-sorted : ∀ { r : RE }  { ε∉r : ε∉ r } {loc : ℕ} { c : Char } 
  → (pdi₁ : PDInstance r c )
  → (pdi₂ : PDInstance r c )
  → r , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (r * ε∉r ` loc) , c ⊢ pdinstance-star pdi₁ > pdinstance-star pdi₂
star-ex-sorted {r} {ε∉r} {loc} {c} pdi₁ pdi₂ (>-pdi _ _ pdi₁>-pdi₂-ev ) = >-pdi star-pdi₁ star-pdi₂ ev
  where
    star-pdi₁ : PDInstance ( r * ε∉r ` loc ) c
    star-pdi₁ = pdinstance-star pdi₁
    star-pdi₂ : PDInstance ( r * ε∉r ` loc ) c    
    star-pdi₂ = pdinstance-star pdi₂    
 
    ev : ∀ ( t₁ : U  (r * ε∉r ` loc) )
          → ( t₂ : U  (r * ε∉r ` loc) )
          → ( Recons t₁ star-pdi₁ )
          → ( Recons t₂ star-pdi₂ )
          -------------------------
          → ( (r * ε∉r ` loc) ⊢ t₁ > t₂ )
    ev (ListU []) _ recons-[]-star-pdi₁ _ = Nullary.contradiction  recons-[]-star-pdi₁ (¬recons-[]-from-pdinstance-star pdi₁)
    ev _ (ListU []) _ recons-[]-star-pdi₂ = Nullary.contradiction  recons-[]-star-pdi₂ (¬recons-[]-from-pdinstance-star pdi₂)
    ev (ListU (v₁ ∷ vs₁)) (ListU (v₂ ∷ vs₂)) recons-list-vvs₁-star-pdi₁ recons-list-vvs₂-star-pdi₂ =
      let recons-v₁-pdi₁ = inv-recons-star v₁ vs₁ pdi₁ recons-list-vvs₁-star-pdi₁ 
          recons-v₂-pdi₂ = inv-recons-star v₂ vs₂ pdi₂ recons-list-vvs₂-star-pdi₂
      in bne (¬≡[]→length>0 (¬|list-u∷us|≡[] {r} {ε∉r} {loc} {v₁} {vs₁} )) ((¬≡[]→length>0 (¬|list-u∷us|≡[] {r} {ε∉r} {loc} {v₂} {vs₂}))) (star-head (pdi₁>-pdi₂-ev v₁ v₂ recons-v₁-pdi₁ recons-v₂-pdi₂) )
      -- we only need to prove by I.H over the heads. why? because different pdinstances produce different parse tree.
  

map-star-ex-sorted : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
                     → ( pdis : List (PDInstance r c) )
                     → Ex>-sorted {r} pdis
                     → Ex>-sorted {r * ε∉r ` loc } (List.map pdinstance-star pdis)
map-star-ex-sorted {r} {ε∉r} {loc} {c} [] ex>-nil = ex>-nil
map-star-ex-sorted {r} {ε∉r} {loc} {c} (pdi ∷ [])  (ex>-cons ex>-nil ex>-nothing) = ex>-cons ex>-nil ex>-nothing
map-star-ex-sorted {r} {ε∉r} {loc} {c} (pdi₁ ∷ pdi₂ ∷ pdis)  (ex>-cons ex>-sorted-pdi2pdis (ex>-just pdi1>pdi2))
  = ex>-cons (map-star-ex-sorted (pdi₂ ∷ pdis) ex>-sorted-pdi2pdis)
             (ex>-just (star-ex-sorted pdi₁ pdi₂ pdi1>pdi2))



-- these two lemmas should be moved to Recons.lagda.md 
recons-u-pdi→|u|≡c∷w : ∀ { r : RE } { c : Char }
  → ( u : U r )
  → ( pdi : PDInstance r c )
  → Recons u pdi
  ------------------------
  → ∃[ w ] (proj₁ (flat u)) ≡ c ∷ w 
recons-u-pdi→|u|≡c∷w {r} {c} u (pdinstance inj sound-ev) (recons _ (w∈⟦p⟧ , inj∘unflat≡u)) =
  _ , trans (cong (proj₁ ∘ flat) (sym inj∘unflat≡u)) (sound-ev (unflat w∈⟦p⟧)) 


recons-u-pdi→¬|u|≡[] : ∀ { r : RE } { c : Char }
  → ( u : U r )
  → ( pdi : PDInstance r c )
  → Recons u pdi
  ------------------------
  → ¬ (proj₁ (flat u)) ≡ []  
recons-u-pdi→¬|u|≡[] {r} {c} u pdi recons-u-pdi = ev
  where
    |u|≡c∷w :  ∃[ w ] (proj₁ (flat u)) ≡ (c ∷ w) 
    |u|≡c∷w =  recons-u-pdi→|u|≡c∷w  u pdi recons-u-pdi
    ev :  ¬ (proj₁ (flat u)) ≡ []
    ev |u|≡[] rewrite (proj₂ |u|≡c∷w) = ¬∷≡[] |u|≡[] 
    



fst-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁ : PDInstance l c )
  → (pdi₂ : PDInstance l c )
  → l , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (l ● r ` loc) , c ⊢ pdinstance-fst pdi₁ > pdinstance-fst pdi₂
fst-ex-sorted {l} {r} {loc} {c} pdi₁ pdi₂ (>-pdi _ _ pdi₁>-pdi₂-ev ) = >-pdi fst-pdi₁ fst-pdi₂ ev
  where
    fst-pdi₁ : PDInstance ( l ● r ` loc ) c
    fst-pdi₁ = pdinstance-fst pdi₁
    fst-pdi₂ : PDInstance ( l ● r ` loc ) c    
    fst-pdi₂ = pdinstance-fst pdi₂    
 
    ev : ∀ ( t₁ : U  (l ● r ` loc) )
          → ( t₂ : U  (l ● r ` loc) )
          → ( Recons t₁ fst-pdi₁ )
          → ( Recons t₂ fst-pdi₂ )
          -------------------------
          → ( (l ● r ` loc) ⊢ t₁ > t₂ )
    ev (PairU u₁ v₁) (PairU u₂ v₂)  recons-pair-u₁v₁-pdi-fst recons-pair-u₂v₂-pdi-fst =
       let recons-u₁-pdi₁ = inv-recons-fst {l} {r} {loc} u₁ v₁ pdi₁  recons-pair-u₁v₁-pdi-fst 
           recons-u₂-pdi₂ = inv-recons-fst {l} {r} {loc} u₂ v₂ pdi₂  recons-pair-u₂v₂-pdi-fst
       in bne (¬≡[]→length>0 ¬|u₁v₁|≡[]) (¬≡[]→length>0 ¬|u₂v₂|≡[]) (seq₁ (pdi₁>-pdi₂-ev u₁ u₂  recons-u₁-pdi₁ recons-u₂-pdi₂) ) 
         where
           ¬|u₁v₁|≡[] : ¬ ( proj₁ (flat (PairU {l} {r} {loc} u₁ v₁)) ≡ [] )
           ¬|u₁v₁|≡[] = recons-u-pdi→¬|u|≡[] (PairU u₁ v₁) fst-pdi₁ recons-pair-u₁v₁-pdi-fst 
           ¬|u₂v₂|≡[] : ¬ ( proj₁ (flat (PairU {l} {r} {loc} u₂ v₂)) ≡ [] )
           ¬|u₂v₂|≡[] = recons-u-pdi→¬|u|≡[] (PairU u₂ v₂) fst-pdi₂ recons-pair-u₂v₂-pdi-fst 


map-fst-ex-sorted : ∀ { l r : RE } { loc : ℕ } { c : Char }
                    → ( pdis : List (PDInstance l c) )
                    → Ex>-sorted {l} pdis
                    → Ex>-sorted {l ● r ` loc } (List.map pdinstance-fst pdis)
map-fst-ex-sorted {l} {r} {loc} {c} [] ex>-nil = ex>-nil
map-fst-ex-sorted {l} {r} {loc} {c} (pdi ∷ [])              (ex>-cons ex>-nil ex>-nothing ) =
  ex>-cons  ex>-nil ex>-nothing 
map-fst-ex-sorted {l} {r} {loc} {c} (pdi₁  ∷ pdi₂ ∷ pdis ) (ex>-cons pdi₂pdis-sorted@(ex>-cons pdis-sorted pdi₂>head-pdis)  (ex>-just pdi₁>pdi₂ )) =
  ex>-cons (map-fst-ex-sorted {l} {r} {loc} {c}  (pdi₂ ∷  pdis) pdi₂pdis-sorted) (ex>-just (fst-ex-sorted {l} {r} pdi₁ pdi₂ pdi₁>pdi₂ ))



--------------------------------------------------------------------------------------------
-- sub lemma snd-ex-sorted and its sub sub lemmas BEGIN 
--------------------------------------------------------------------------------------------



mk-snd-pdi-fst-pair-≡ : ∀ { l r : RE } { loc : ℕ } { c : Char }
                      → ( pdi : PDInstance r c ) 
                      → ( e : U l ) -- empty parse tree from l
                      → ( flat-[]-e :  Flat-[] l e )
                      → ( u : U l )
                      → ( v : U r )                      
                      →  Recons (PairU {l} {r} {loc} u v) (mk-snd-pdi ( e , flat-[]-e ) pdi )
                      ----------------------------------------------
                      → u ≡ e 
mk-snd-pdi-fst-pair-≡ {l} {r} {loc} {c} pdi@(pdinstance inj s-ev) e (flat-[] {l} e proj₁∘flat-e≡[]) u v (recons {p} { l ● r ` loc } {c} {w} {injSnd} {injSnd-s} (PairU _ _) ( w∈⟦p⟧ , injSnd∘unflat-w∈⟦p⟧≡pair-u-v ) )  = proj₁ u≡e×v≡inj-unflat-w∈⟦p⟧                       
  where
    injSnd-unflat-w∈⟦p⟧≡pair-u-inj-unflat-w∈⟦p⟧ : mkinjSnd {l} {r} {p} {loc} inj u (unflat w∈⟦p⟧) ≡ PairU u (inj (unflat w∈⟦p⟧))
    injSnd-unflat-w∈⟦p⟧≡pair-u-inj-unflat-w∈⟦p⟧ =
      begin
        mkinjSnd {l} {r} {p} {loc} inj u (unflat w∈⟦p⟧)
      ≡⟨⟩
        PairU {l} {r} {loc} u (inj (unflat w∈⟦p⟧))
      ∎
    pair-u-v≡pair-e-inj-unflat-w∈⟦p⟧  : PairU u v ≡ PairU {l} {r} {loc} e (inj (unflat w∈⟦p⟧) )
    pair-u-v≡pair-e-inj-unflat-w∈⟦p⟧ =
      begin
        PairU u v
      ≡⟨ sym injSnd∘unflat-w∈⟦p⟧≡pair-u-v ⟩
        PairU e (inj (unflat w∈⟦p⟧) )
      ∎
    u≡e×v≡inj-unflat-w∈⟦p⟧ : (u ≡ e) × (v ≡ inj (unflat w∈⟦p⟧))
    u≡e×v≡inj-unflat-w∈⟦p⟧ = inv-pairU u v e (inj (unflat w∈⟦p⟧)) pair-u-v≡pair-e-inj-unflat-w∈⟦p⟧


-- main sub lemma :
-- pdinstances generated by pdinstance-snd is ex>-sorted.

pdinstance-snd-ex>-sorted : ∀ { l r : RE } { loc : ℕ } { c : Char }
                → (e-flat-[]-e : ∃[ e ] Flat-[] l e ) 
                → (pdis : List (PDInstance r c) )
                → Ex>-sorted {r} pdis 
                → Ex>-sorted { l ● r ` loc } (List.map (mk-snd-pdi {l} {r} {loc} {c}  e-flat-[]-e) pdis)
pdinstance-snd-ex>-sorted {l} {r} {loc} {c}  (e , flat-[]-e ) []            ex>-nil                                   = ex>-nil
pdinstance-snd-ex>-sorted {l} {r} {loc} {c}  (e , flat-[]-e ) (pdi ∷ [] ) (ex>-cons ex>-nil ex>-nothing)              = ex>-cons ex>-nil ex>-nothing

pdinstance-snd-ex>-sorted {l} {r} {loc} {c}  (e , flat-[]-e) (pdi₁ ∷ pdi₂ ∷ pdis ) (ex>-cons pdi₂pdis-ex>-sorted (ex>-just (>-pdi pdi₁ pdi₂ u₁→u₂→recons-u₁→recons-u₂→u₁>u₂)))  =
  ex>-cons (pdinstance-snd-ex>-sorted (e , flat-[]-e) (pdi₂ ∷ pdis) pdi₂pdis-ex>-sorted)
           (ex>-just (>-pdi (mk-snd-pdi (e , flat-[]-e) pdi₁)
                            (mk-snd-pdi (e , flat-[]-e) pdi₂)
                            (λ { (PairU e₁ u₁) (PairU e₂ u₂)
                                 recons-pair-e-u1 recons-pair-e-u2 
                                  → ev-> e₁ u₁ e₂ u₂ recons-pair-e-u1 recons-pair-e-u2  }  )) )

  where

     ev-> : (v₁ : U l )
          → (v₁' : U r )
          → (v₂ : U l )
          → (v₂' : U r )
          → Recons {l ● r ` loc} {c} (PairU v₁ v₁')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e ) pdi₁)
          → Recons {l ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e ) pdi₂ )
          --------------------------------------------------
          → (l ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂' 
     ev-> v₁ v₁' v₂ v₂' recons1 recons2
          = bne (¬≡[]→length>0 ¬|pair-v₁-v₁'|≡[]) (¬≡[]→length>0 ¬|pair-v₂-v₂'|≡[]) (seq₂ v₁≡v₂ v₁'>v₂')
          where
            ¬|pair-v₁-v₁'|≡[] : ¬ (proj₁ (flat (PairU {l} {r} {loc} v₁ v₁')) ≡ [])
            ¬|pair-v₁-v₁'|≡[] = recons-u-pdi→¬|u|≡[] (PairU v₁ v₁') (mk-snd-pdi (e , flat-[]-e) pdi₁) recons1
            ¬|pair-v₂-v₂'|≡[] : ¬ (proj₁ (flat (PairU {l} {r} {loc} v₂ v₂')) ≡ [])
            ¬|pair-v₂-v₂'|≡[] = recons-u-pdi→¬|u|≡[] (PairU v₂ v₂') (mk-snd-pdi (e , flat-[]-e) pdi₂) recons2
            v₁≡e : v₁ ≡ e
            v₁≡e = mk-snd-pdi-fst-pair-≡ pdi₁ e flat-[]-e v₁ v₁' recons1
            v₂≡e : v₂ ≡ e
            v₂≡e = mk-snd-pdi-fst-pair-≡ pdi₂ e flat-[]-e v₂ v₂' recons2
            v₁≡v₂ : v₁ ≡ v₂
            v₁≡v₂ rewrite v₁≡e | v₂≡e = refl
            recons1' :  Recons {l ● r ` loc} {c} (PairU e v₁')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e) pdi₁)
            recons1' rewrite cong (λ x → Recons {l ● r ` loc} {c} (PairU x v₁')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e ) pdi₁) ) (sym v₁≡e) = recons1
            recons2' :  Recons {l ● r ` loc} {c} (PairU e v₂')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e) pdi₂)
            recons2' rewrite cong (λ x → Recons {l ● r ` loc} {c} (PairU x v₂')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e ) pdi₂) ) (sym v₂≡e) = recons2
            recons-v₁' : Recons v₁' pdi₁
            recons-v₁' = inv-recons-snd {l} {r} {loc} {c}  e v₁' flat-[]-e pdi₁ recons1'
            recons-v₂' : Recons v₂' pdi₂
            recons-v₂' = inv-recons-snd {l} {r} {loc} {c}  e v₂' flat-[]-e pdi₂ recons2'
            v₁'>v₂' = u₁→u₂→recons-u₁→recons-u₂→u₁>u₂ v₁' v₂'  recons-v₁'  recons-v₂'



--------------------------------------------------------------------------------------------
-- sub lemma: pdinstance-snd-ex>-sorted END
--------------------------------------------------------------------------------------------



-- concatenation of two ex sorted lists of pdis are sorted if all the pdis from the first list are ex-> than the head of the 2nd list. 
concat-ex-sorted : ∀ { r : RE } { c }
    → ( pdis₁ : List ( PDInstance r c ))
    → ( pdis₂ : List ( PDInstance r c ))
    → Ex>-sorted { r } pdis₁
    → Ex>-sorted { r } pdis₂
    → All (λ pdi₁ → Ex>-maybe  {r} pdi₁ (head pdis₂)) pdis₁
    -------------------------------------------------------
    → Ex>-sorted { r } (pdis₁ ++ pdis₂)
concat-ex-sorted []                       pdis₂          ex>-nil                                       pdis₂-sorted     []                              = pdis₂-sorted
concat-ex-sorted pdis₁                    []             pdis₁-sorted                                  ex>-nil           _  rewrite (++-identityʳ pdis₁) = pdis₁-sorted
concat-ex-sorted (pdi₁ ∷ [])             (pdi₂ ∷ pdis₂) pdis₁-sorted                                  pdi₂pdis₂-sorted (ex>-just pdi₁>pdi₂  ∷ [])      = ex>-cons pdi₂pdis₂-sorted (ex>-just pdi₁>pdi₂) 
concat-ex-sorted (pdi₁ ∷ pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) (ex>-cons pdi₁'pdis₁-sorted pdi₁>head-pdis₁)  pdi₂pdis₂-sorted (ex>-just pdi₁>pdi₂  ∷ pxs)     = ex>-cons ind-hyp pdi₁>head-pdis₁
  where
    ind-hyp = concat-ex-sorted (pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) pdi₁'pdis₁-sorted  pdi₂pdis₂-sorted  pxs 




---------------------------------------------------------------------------------------------------
-- concatmap-pdinstance-snd-ex>-sorted and its sub lemma
--------------------------------------------------------------------------------------------------



pdinstance-snd-fst-all->concatmap-pdinstance-snd : ∀ { l r : RE } {ε∈l : ε∈ l } { loc : ℕ } { c : Char }
    → ( e  : U l )
    → ( flat-[]-e : Flat-[] l e )
    → ( es : List (U l) )
    → ( flat-[]-es : All ( Flat-[] l ) es )
    → ( e>-head-es : >-maybe e (head es))
    → ( es->-sorted : >-sorted es ) 
    → ( pdis : List (PDInstance r c ) )
    -----------------------------------------------------------------
    → All (λ pdi₁ → Ex>-maybe {l ● r ` loc } pdi₁ (head (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es))))
       (List.map (mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e)) pdis)
pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e (flat-[] e proj₁flat-e≡[]) [] [] >-nothing ex->-nil pdis = prf  (List.map (mk-snd-pdi (e , flat-[] e proj₁flat-e≡[])) pdis)
  where
    prf : (pdis : List (PDInstance (l ● r ` loc) c) )
          → All  (λ pdi₁ → Ex>-maybe pdi₁ nothing) pdis
    prf [] = []
    prf (pdi ∷ pdis) = ex>-nothing ∷ prf pdis
pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e₁ flat-[]-e₁  (e₂ ∷ es) (flat-[]-e₂ ∷ flat-[]-es) (>-just e₁>e₂) e₂es->sorted [] = [] 
pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e₁ flat-[]-e₁  (e₂ ∷ es) (flat-[]-e₂ ∷ flat-[]-es) (>-just e₁>e₂) e₂es->sorted (pdi ∷ pdis) = prf (pdi ∷ pdis)
  where
    prf : ( pdis' : List (PDInstance r c) )
          →  All (λ pdi₁ → Ex>-maybe pdi₁
                    (head
                      (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x (pdi ∷ pdis))
                                 ((e₂ , flat-[]-e₂) ∷ zip-es-flat-[]-es {l} {ε∈l}  es flat-[]-es))))
                    (List.map (mk-snd-pdi (e₁ , flat-[]-e₁)) pdis')
    prf [] = []
    prf (pdi'@(pdinstance {p} {r} {c}  inj' s-ev') ∷ pdis' ) = 
          ex>-just (>-pdi (mk-snd-pdi (e₁ , flat-[]-e₁) pdi')
                          (mk-snd-pdi (e₂ , flat-[]-e₂) pdi) λ { (PairU v₁ v₁') (PairU v₂ v₂') recons₁ recons₂ → ev-> v₁ v₁' v₂ v₂' recons₁ recons₂ } ) ∷ prf pdis'
          where
          ev-> : (v₁ : U l )
               → (v₁' : U r )
               → (v₂ : U l )
               → (v₂' : U r )
               → Recons {l ● r ` loc} {c} (PairU v₁ v₁')  ( mk-snd-pdi {l} {r} {loc} {c}  (e₁ , flat-[]-e₁ ) pdi')
               → Recons {l ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi {l} {r} {loc} {c}  (e₂ , flat-[]-e₂ ) pdi )
               --------------------------------------------------
               → (l ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂' 
          ev-> v₁ v₁' v₂ v₂' recons1 recons2 = bne (¬≡[]→length>0 ¬|pair-v₁-v₁'|≡[]) (¬≡[]→length>0 ¬|pair-v₂-v₂'|≡[]) (seq₁ v₁>v₂)
            where
              ¬|pair-v₁-v₁'|≡[] : ¬ (proj₁ (flat (PairU {l} {r} {loc} v₁ v₁')) ≡ [])
              ¬|pair-v₁-v₁'|≡[] = recons-u-pdi→¬|u|≡[] (PairU v₁ v₁') (mk-snd-pdi (e₁ , flat-[]-e₁) pdi') recons1
              ¬|pair-v₂-v₂'|≡[] : ¬ (proj₁ (flat (PairU {l} {r} {loc} v₂ v₂')) ≡ [])
              ¬|pair-v₂-v₂'|≡[] = recons-u-pdi→¬|u|≡[] (PairU v₂ v₂') (mk-snd-pdi (e₂ , flat-[]-e₂) pdi) recons2
              v₁≡e₁ : v₁ ≡ e₁
              v₁≡e₁ = mk-snd-pdi-fst-pair-≡ pdi' e₁ flat-[]-e₁ v₁ v₁' recons1
              v₂≡e₂ : v₂ ≡ e₂
              v₂≡e₂ = mk-snd-pdi-fst-pair-≡ pdi e₂ flat-[]-e₂ v₂ v₂' recons2
              v₁>v₂ : l ⊢ v₁ > v₂
              v₁>v₂ rewrite v₁≡e₁ | v₂≡e₂ = e₁>e₂ 
            


concatmap-pdinstance-snd-ex>-sorted-sub : ∀ { l r : RE } {ε∈l : ε∈ l } {loc : ℕ } { c : Char }
                                     → ( es : List (U l) )
                                     → ( flat-[]-es : All ( Flat-[] l ) es ) 
                                     → ( ex->-sorted : >-sorted es ) 
                                     → ( pdis : List (PDInstance r c ) )
                                     → Ex>-sorted {r} pdis
                                     ----------------------------------------------------------------
                                     → Ex>-sorted {l ● r ` loc} (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es))
concatmap-pdinstance-snd-ex>-sorted-sub {l} {r} {ε∈l} {loc} {c} []       []                        >-nil                          _    _              = ex>-nil
concatmap-pdinstance-snd-ex>-sorted-sub {l} {r} {ε∈l} {loc} {c} (e ∷ es) (flat-[]-e ∷ flat-[]-es)  (>-cons es->-sorted e>head-es) pdis pdis-ex>-sorted =
  concat-ex-sorted
    (List.map (mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e)) pdis)                                          -- ^ curr batch
    (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es)) -- ^ next bacth
    curr-sorted
    next-sorted
    (pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  e flat-[]-e es flat-[]-es e>head-es es->-sorted pdis ) 
  where
    curr-sorted : Ex>-sorted {l ● r ` loc} (List.map (mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e)) pdis)
    curr-sorted = pdinstance-snd-ex>-sorted {l} {r} {loc} {c} (e , flat-[]-e) pdis pdis-ex>-sorted
    next-sorted : Ex>-sorted {l ● r ` loc} (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es))
    next-sorted = concatmap-pdinstance-snd-ex>-sorted-sub {l} {r} {ε∈l} {loc} {c} es flat-[]-es es->-sorted pdis pdis-ex>-sorted 


-- pdinstances generated by concatmap-pdinstance-snd must be ex sorted. 
concatmap-pdinstance-snd-ex>-sorted : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
                                     → ( pdis : List (PDInstance r c ) )
                                     → Ex>-sorted {r} pdis
                                     → Ex>-sorted {l ● r ` loc } (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis)
concatmap-pdinstance-snd-ex>-sorted {l} {r} {ε∈l} {loc} {c} pdis ex>-sorted-pdis = concatmap-pdinstance-snd-ex>-sorted-sub {l} {r}  {ε∈l} {loc} {c}  es flat-[]-es es->-sorted pdis ex>-sorted-pdis
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l
    es->-sorted : >-sorted es
    es->-sorted = mkAllEmptyU-sorted {l} ε∈l 
    
---------------------------------------------------------------------------------------------------
-- concatmap-pdinstance-snd-ex>-sorted and its sub lemma END 
--------------------------------------------------------------------------------------------------
{-
-- we don't need assoc rule in lnegen
---------------------------------------------------------------------------------------------------
-- map-pdinstance-assoc-ex>-sorted and its sub lemma 
---------------------------------------------------------------------------------------------------

inv-assoc-> : ∀ { l s r : RE } {loc₁ loc₂ : ℕ }
          → { u₁ : U ( l ● (s ● r ` loc₂) ` loc₁) }
          → { u₂ : U ( l ● (s ● r ` loc₂) ` loc₁) }
          → (l ● (s ● r ` loc₂) ` loc₁) ⊢ u₁ > u₂
          -------------------------------------------------------------          
          → ((l ● s ` loc₁) ● r ` loc₂) ⊢ inv-assoc u₁ > inv-assoc u₂
inv-assoc-> {l} {s} {r} {loc₁} {loc₂} {PairU v₁ (PairU v₁' v₁'')} {PairU v₂ (PairU v₂' v₂'')} pair-v1-pair-v1'-v1''>pair-v2-pair-v2'-v2''
  with pair-v1-pair-v1'-v1''>pair-v2-pair-v2'-v2''
... | seq₁ v₁>v₂                          = seq₁ (seq₁ v₁>v₂)
... | seq₂ v₁≡v₂ (seq₁ v₁'>v₂')           = seq₁ (seq₂ v₁≡v₂ v₁'>v₂')
... | seq₂ v₁≡v₂ (seq₂ v₁'≡v₂' v₁''>v₂'') = seq₂ (pair-≡ v₁≡v₂ v₁'≡v₂') v₁''>v₂'' 


pdinstance-assoc-ex> : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
                       → ( pdi₁ : PDInstance (l ● (s ● r ` loc₂) ` loc₁) c )
                       → ( pdi₂ : PDInstance (l ● (s ● r ` loc₂) ` loc₁) c )                       
                       → (l ● (s ● r ` loc₂) ` loc₁) , c ⊢ pdi₁ > pdi₂
                       ------------------------------------------------------------
                       → (( l ● s ` loc₁) ● r ` loc₂) , c ⊢ (pdinstance-assoc pdi₁) > (pdinstance-assoc pdi₂)
pdinstance-assoc-ex> {l} {s} {r} {loc₁} {loc₂} {c} pdi₁ pdi₂ (>-pdi _ _  u₁→u₂→rec₁→rec₂→u₁>u₂ )
    = >-pdi (pdinstance-assoc pdi₁)
            (pdinstance-assoc pdi₂) 
            (λ { (PairU (PairU v₁ v₁') v₁'') (PairU (PairU v₂ v₂') v₂'') recons₁ recons₂ →
               (inv-assoc-> {l} {s} {r} {loc₁} {loc₂} ( u₁→u₂→rec₁→rec₂→u₁>u₂ (PairU v₁ (PairU v₁' v₁'')) (PairU v₂ (PairU v₂' v₂''))
                                                    (inv-recons-assoc v₁ v₁' v₁'' pdi₁ recons₁) (inv-recons-assoc v₂ v₂' v₂'' pdi₂ recons₂) ))   })
  

pdinstance-assoc-ex>-maybe : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
                             → ( pdi : PDInstance (l ● (s ● r ` loc₂) ` loc₁) c )
                             → ( pdis : List (PDInstance (l ● (s ● r ` loc₂) ` loc₁) c) )
                             → Ex>-maybe pdi (head pdis)
                             -------------------------------------------------------------
                             → Ex>-maybe (pdinstance-assoc pdi)
                                         (head (List.map pdinstance-assoc pdis))
pdinstance-assoc-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi [] ex>-nothing = ex>-nothing      
pdinstance-assoc-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi₁ (pdi₂ ∷ pdis) (ex>-just pdi₁>pdi₂) = ex>-just (pdinstance-assoc-ex> {l} {s} {r} {loc₁} {loc₂} {c} pdi₁ pdi₂ pdi₁>pdi₂ )

map-pdinstance-assoc-ex>-sorted : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
                                → ( pdis : List (PDInstance (l ● (s ● r ` loc₂) ` loc₁) c) )
                                → Ex>-sorted {l ● (s ● r ` loc₂) ` loc₁} pdis
                                ---------------------------------------------------------------
                                → Ex>-sorted {(l ● s ` loc₁) ● r ` loc₂} (List.map pdinstance-assoc pdis)
map-pdinstance-assoc-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} [] ex>-nil = ex>-nil
map-pdinstance-assoc-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} (pdi ∷ pdis) (ex>-cons pdis-ex>-sorted pdi>head-pdis) = ex>-cons (map-pdinstance-assoc-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} pdis pdis-ex>-sorted) (pdinstance-assoc-ex>-maybe  {l} {s} {r} {loc₁} {loc₂} {c} pdi pdis pdi>head-pdis)


-}

{-
-- we don't ned pdUConcat 
------------------------------------------------------------------------------------------
-- aux lemmas for the pdUConcat l * case. 
-- the parse tree generated by  pdi : PDInstance (r * ε∉r ` loc₁) c must be a consU
pdinstance-r*-is-cons : ∀ { r : RE } {ε∉r : ε∉ r } {loc : ℕ } { c : Char }
  → ( pdi : PDInstance (r * ε∉r ` loc ) c )
  → ( u : U (r * ε∉r ` loc) )
  → Recons u  pdi
  -------------------------------------
  → ∃[ x ] ∃[ xs ] u ≡ (ListU (x ∷ xs ))
pdinstance-r*-is-cons {r} {ε∉r} {loc} {c} (pdinstance inj s-ev) u (recons {p} {r * ε∉r ` loc } {c} {w} u' ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡u )) = prf
  where
    prf :  ∃[ x ] ∃[ xs ] u ≡ (ListU (x ∷ xs ))
    prf with u-of-r*-islist u
    ... | inj₂ ex-u≡list-x::xs = ex-u≡list-x::xs
    ... | inj₁ u≡list-[] = Nullary.contradiction  c∷w≡[] Word.¬c∷w≡[] 
      where
        proj₁-flat-u≡[] : ( proj₁ (flat u)) ≡ [] 
        proj₁-flat-u≡[] =
          begin
            proj₁ (flat u)
          ≡⟨ cong (λ x → proj₁ ( flat x ) ) u≡list-[] ⟩
            proj₁ (flat (ListU {r} {ε∉r} {loc} []))
          ≡⟨⟩
            []
          ∎
          
        proj₁-flat-u≡cw : (proj₁ (flat u)) ≡ (c ∷ proj₁ (flat (unflat w∈⟦p⟧)))
        proj₁-flat-u≡cw = 
          begin
            proj₁ (flat u)
          ≡⟨ cong (λ x → proj₁ (flat x) ) (sym inj-unflat-w∈⟦p⟧≡u) ⟩
            proj₁ (flat (inj (unflat w∈⟦p⟧) ) )
          ≡⟨ s-ev  (unflat w∈⟦p⟧) ⟩ 
           c ∷ proj₁ (flat ( unflat w∈⟦p⟧ ) )
          ∎
        c∷w≡[] :  (c ∷ proj₁ (flat (unflat w∈⟦p⟧))) ≡ []
        c∷w≡[] =
          begin
            (c ∷ proj₁ (flat (unflat w∈⟦p⟧)))
          ≡⟨ sym  proj₁-flat-u≡cw ⟩
            (proj₁ (flat u))
          ≡⟨ proj₁-flat-u≡[] ⟩
            []
          ∎ 
            

-- the first of the pair from pdi : PDInstance (l * ε∉l ` loc₁) c must be a consU
pdinstance-fst-pair-l*-is-cons : ∀ { l r : RE } {ε∉l : ε∉ l} { loc₁ loc₂ : ℕ } { c : Char }
                      → ( pdi : PDInstance (l * ε∉l ` loc₁) c )
                      → ( u : U (l * ε∉l ` loc₁) )
                      → ( v : U r )                       
                      → Recons (PairU {(l * ε∉l ` loc₁)} {r} {loc₂} u v) (pdinstance-fst pdi)
                      -------------------------------------------------------
                      → ∃[ x ] ∃[ xs ] u ≡ (ListU (x ∷ xs) )
pdinstance-fst-pair-l*-is-cons {l} {r} {ε∉l} {loc₁} {loc₂} {c} pdi (ListU us) v rec = pdinstance-r*-is-cons pdi (ListU us) recons-list-us
  where
    recons-list-us : Recons (ListU us) pdi 
    recons-list-us = inv-recons-fst {l * ε∉l ` loc₁} {r} {loc₂} {c} (ListU us) v pdi rec

-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------

-------------------------------------------------------------
-- Sub Lemma 38.1 - 38.22 END 
-------------------------------------------------------------
-} 


```

#### Main Proof for Lemma 38

```agda
-- these lemma should be moved to partial derivatives 
pdinstance-snd-[]≡[] : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( x : ∃[ e ] (Flat-[] l e ) )
    ---------------------------------
    → pdinstance-snd {l} {r} {loc} {c} x [] ≡ []
pdinstance-snd-[]≡[] {l} {r} {loc} {c} x =
  begin
    pdinstance-snd {l} {r} {loc} {c} x []
  ≡⟨⟩
    List.map (mk-snd-pdi x) []
  ≡⟨⟩
    []
  ∎ 


concatmap-pdinstance-snd-[]≡[] : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
    →  concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} [] ≡ []

concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c} = prf 
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l
    zs : List ( ∃[ e ] (Flat-[] l e) ) 
    zs = zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es
    -- induction over the list of empty parse trees and the flat-[] properties 
    ind : ( ys : List ( ∃[ e ] (Flat-[] l e) ) )
      → List.foldr _++_ [] (List.map (λ x → pdinstance-snd {l} {r} {loc} {c} x []) ys) ≡ []
    ind []          = refl
    ind ( y ∷ ys ) = ind ys

    prf :  concatmap-pdinstance-snd [] ≡ [] 
    prf =
      begin
        concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} []
      ≡⟨⟩
        concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x []) zs
      ≡⟨⟩ 
        List.foldr _++_ [] (List.map (λ x → pdinstance-snd {l} {r} {loc} {c} x []) zs)
      ≡⟨ ind zs ⟩
        []
      ∎



-- main lemma: 
pdU-sorted : ∀ { r : RE } { c : Char }
  → Ex>-sorted {r} {c} pdU[ r , c ]


pdU-sorted {ε} {c} = ex>-nil
pdU-sorted {$ c ` loc } {c'} with c Char.≟ c'
...                           | no _ = ex>-nil 
...                           | yes refl = ex>-cons ex>-nil ex>-nothing 
  where
    -- duplicated from PartialDerivativeParseTree
    pdi : PDInstance ($ c ` loc) c
    pdi = pdinstance {ε} {$ c ` loc} {c}
                     (λ u → LetterU {loc} c)
                          (λ EmptyU →                 -- ^ soudness ev
                             begin
                               [ c ]
                             ≡⟨⟩
                               c ∷ []
                             ≡⟨ cong ( λ x → ( c ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                               c ∷ (proj₁ (flat EmptyU))
                             ∎)
                             
pdU-sorted {l + r ` loc } {c} =  map-left-right-ex-sorted pdU[ l , c ] pdU[ r , c ] ind-hyp-l ind-hyp-r 
  where
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c}
    ind-hyp-r : Ex>-sorted pdU[ r , c ]
    ind-hyp-r = pdU-sorted {r} {c}
pdU-sorted {l * ε∉l ` loc } {c} =  map-star-ex-sorted pdU[ l , c ] ind-hyp-l
  where 
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c}

pdU-sorted {l ● r ` loc } {c} with ε∈? l
...  | no ¬ε∈l = map-fst-ex-sorted {l} {r} {loc} {c}  pdU[ l , c ] ind-hyp-l
  where
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c}
...  | yes ε∈l = concat-ex-sorted {l ● r ` loc} {c}
                    (List.map pdinstance-fst pdU[ l , c ])
                    (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ])
                    map-pdinstance-fst-ex>sorted
                    concatmap-pdinstance-snd-is-ex>-sorted
                    (all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd pdU[ l , c ] pdU[ r , c ]) 
  where
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c}
    
    ind-hyp-r : Ex>-sorted pdU[ r , c ]
    ind-hyp-r = pdU-sorted {r} {c}

    -- we need to concat the following two, but we need to know all fst in map-pdinstance-fst-ex>sorted  >  concatmap-pdinstance-snd-ex>-sorted
    map-pdinstance-fst-ex>sorted : Ex>-sorted { l ● r ` loc } (List.map pdinstance-fst  pdU[ l , c ] )
    map-pdinstance-fst-ex>sorted = map-fst-ex-sorted pdU[ l , c ] ind-hyp-l 

    concatmap-pdinstance-snd-is-ex>-sorted : Ex>-sorted { l ● r ` loc } (concatmap-pdinstance-snd { l } {r} {ε∈l} {loc} {c} pdU[ r , c ])
    concatmap-pdinstance-snd-is-ex>-sorted = concatmap-pdinstance-snd-ex>-sorted {l} {r} {ε∈l} {loc} {c}  pdU[ r , c ] ind-hyp-r 


    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd :
         (pdis : List (PDInstance l c ))
      →  (pdis' : List (PDInstance r c))
      →  All (λ pdi → Ex>-maybe { l ● r ` loc } pdi (head (concatmap-pdinstance-snd { l } {r} {ε∈l} {loc} {c} pdis'))) (List.map
      (pdinstance-fst {l} {r} {loc} {c}) pdis )
    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd [] _ = []
    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd (pdi ∷ pdis) [] rewrite ( concatmap-pdinstance-snd-[]≡[] {l } {r} {ε∈l} {loc} {c} )  = prf (pdi ∷ pdis) 
      where
        prf : (pdis' : List (PDInstance l c))
          → All (λ pdi₁ → Ex>-maybe pdi₁ nothing)  (List.map ( pdinstance-fst  {l} {r} {loc} {c} ) pdis' )
        prf [] = []
        prf (pdi' ∷ pdis') = ex>-nothing ∷ prf pdis'       
    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd (pdi ∷ pdis) (pdi'@(pdinstance inj' s-ev') ∷ pdis')
       with zip-es-flat-[]-es {l} {ε∈l}  (mkAllEmptyU ε∈l) (mkAllEmptyU-sound {l} (ε∈l)) in eq 
    ... | []                                  =  Nullary.contradiction (PartialDerivative.zip-es-flat-[]-es≡[]→es≡[] {l} {ε∈l}  (mkAllEmptyU ε∈l) (mkAllEmptyU-sound {l} ε∈l) eq) (mkAllEmptyU≢[] ε∈l) 
    ... | ( e , flat-[] _ proj₁flat-e≡[] )  ∷ es-flat-[]-es =  ind (pdi ∷ pdis) 
      where 
        ind : ( pdis : List (PDInstance l c ) )
          → All (λ pdi → Ex>-maybe pdi
                (just (mk-snd-pdi {l} {r} {loc} {c} (e , flat-[] e proj₁flat-e≡[]) pdi')))
                      (List.map pdinstance-fst pdis)
        ind [] = []
        ind ( pdi@(pdinstance inj s-ev) ∷ pdis ) =  ex>-just (>-pdi (pdinstance-fst {l} {r} {loc} {c} (pdinstance inj s-ev)) (mk-snd-pdi (e , flat-[] e proj₁flat-e≡[]) pdi') λ { ( PairU v₁ v₁') (PairU v₂ v₂') r₁ r₂  → ev->  v₁ v₁' v₂ v₂' r₁ r₂  } ) ∷ ind pdis
          where 
            ev-> : (v₁ : U l )
              → (v₁' : U r )
              → (v₂ : U l )
              → (v₂' : U r )
              → Recons {l ● r ` loc} {c} (PairU v₁ v₁')  ( pdinstance-fst {l} {r} {loc} {c} ( pdinstance inj s-ev ) )
              → Recons {l ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi (e , flat-[] e proj₁flat-e≡[]) (pdinstance inj' s-ev') )
              --------------------------------------------------
              → (l ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂'
            ev-> v₁ v₁' v₂ v₂' recons1 recons2 =
              bne (¬≡[]→length>0 ¬|pair-v₁-v₁'|≡[]) (¬≡[]→length>0 ¬|pair-v₂-v₂'|≡[]) (seq₁ v₁>v₂)
              where
                recons-v₁-pdi : Recons v₁ pdi
                recons-v₁-pdi = inv-recons-fst {l} {r} {loc} v₁ v₁' pdi recons1
                ¬|v₁|≡[] : ¬ (proj₁ (flat v₁) ≡ [])
                ¬|v₁|≡[] = recons-v→¬proj₁flat-v≡[] v₁ pdi recons-v₁-pdi
                v₂≡e : v₂ ≡ e
                v₂≡e = mk-snd-pdi-fst-pair-≡ pdi' e (flat-[] e proj₁flat-e≡[]) v₂ v₂' recons2
                |v₂|≡[] : proj₁ (flat v₂) ≡ []
                |v₂|≡[] = trans (cong (proj₁ ∘ flat) v₂≡e) proj₁flat-e≡[]
                v₁>v₂ : l ⊢ v₁ > v₂
                v₁>v₂ = lne (¬≡[]→length>0 ¬|v₁|≡[]) (cong List.length |v₂|≡[])
                ¬|pair-v₁-v₁'|≡[] = recons-v→¬proj₁flat-v≡[] (PairU v₁ v₁') (pdinstance-fst (pdinstance inj s-ev)) recons1
                ¬|pair-v₂-v₂'|≡[] = recons-v→¬proj₁flat-v≡[] (PairU v₂ v₂') (mk-snd-pdi (e , flat-[] e proj₁flat-e≡[]) (pdinstance inj' s-ev')) recons2 


              
```



### Definition 39 : (Extended) LNE ordering among PDInstance*'s 

Let r be a non problematic regular expression.

Let w be a word.

Let pdi₁ and pdi₂ be two partial derivative descendant instances of r w.r.t w.

We say pdi₁ is LNE greater than pdi₂, r , w  ⊢* pdi₁ > pdi₂ iff
  for all parse trees u₁ u₂  of r, u₁ is constructable from pdi₁ and u₂ is constructabled from pdi₂ 
    then r ⊢ u₁ > u₂ 

```agda

-- a suffice is a member of a pd inhabiting in a pdinstance
infix 4 _,_⊢*_∈_
data _,_⊢*_∈_ : ∀ ( r : RE ) → ( pf : List Char ) → ( sf : List Char ) → PDInstance* r pf → Set where -- pf is prefix , sf is suffix
  *∈-pdi : ∀ { p r : RE } { pf : List Char } { sf : List Char }
    → sf ∈⟦ p ⟧ 
    → ( inj : U p → U r )
    → ( s-ev : ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ pf ++ ( proj₁ (flat {p} u) )) )
    → r , pf ⊢* sf ∈ (pdinstance* inj s-ev )

infix 4 _,_⊢*_>_
data _,_⊢*_>_ : ∀ ( r : RE ) → ( pf : List Char ) → PDInstance* r pf → PDInstance* r pf → Set where -- pf is prefix
  *>-pdi : ∀ { r : RE } { pf : List Char } 
    → ( pdi₁ : PDInstance* r pf )
    → ( pdi₂ : PDInstance* r pf )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r ) → (Recons* u₁ pdi₁ ) → (Recons* u₂ pdi₂) → r ⊢ u₁ > u₂ )
    → r , pf  ⊢* pdi₁ > pdi₂ 
  -- shall we add a special case where pf ≡ [] ? if that's the case we should have ≥ instead of >


*>-pdi-trans : ∀ { r : RE }  { pf : List Char } 
  → { pdi₁ : PDInstance* r pf }
  → { pdi₂ : PDInstance* r pf }
  → { pdi₃ : PDInstance* r pf }
  → r , pf   ⊢* pdi₁ > pdi₂
  → r , pf   ⊢* pdi₂ > pdi₃
  -------------------------------------------
  → r , pf  ⊢* pdi₁ > pdi₃
*>-pdi-trans {r} {pf} {pdi₁} {pdi₂} {pdi₃} (*>-pdi .{r} .{pf} pdi₁ pdi₂ u₁>u₂-ev)  (*>-pdi .{r} .{pf} .(pdi₂) pdi₃ u₂>u₃-ev)  = *>-pdi pdi₁ pdi₃  *>-ev

  where
    *>-ev : ( u₁ : U r )
          → ( u₃ : U r )
          → Recons* u₁ pdi₁
          → Recons* u₃ pdi₃
          ------------------------------
          → r ⊢ u₁ > u₃
    *>-ev u₁ u₃ recons₁ recons₃  =
      let u₂-recons₂ = pdi*-∃  {r} {pf} pdi₂
      in  >-trans (u₁>u₂-ev u₁ (proj₁ u₂-recons₂) recons₁ (proj₂ u₂-recons₂) )
                  (u₂>u₃-ev (proj₁ u₂-recons₂) u₃ (proj₂ u₂-recons₂) recons₃ ) 

```

### Definition 40 : (Extended) LNE sortedness among pdinstance*'s 

```agda
data Ex*>-maybe : ∀ { r : RE } { pf : List Char } → ( pdi : PDInstance* r pf ) → ( mpdi : Maybe (PDInstance* r pf) ) → Set where
  ex*>-nothing : ∀ { r : RE } { pf : List Char } 
    → { pdi : PDInstance* r pf }
    ---------------------------
    → Ex*>-maybe {r} {pf} pdi nothing
  ex*>-just : ∀ { r : RE } { pf : List Char } 
    → { pdi : PDInstance* r pf }
    → { pdi' : PDInstance* r pf }
    → r , pf  ⊢* pdi > pdi'
    ----------------------------------
    → Ex*>-maybe {r} {pf} pdi (just pdi')

{-
data Ex*>-first : ∀ { r : RE } { pf sf : List Char } → ( pdi : PDInstance* r pf ) → ( r , pf ⊢* sf ∈ pdi ) → ( pdis : List (PDInstance* r pf ) ) → Set where
  ex*>-first-nil : ∀ { r : RE } { pf sf : List Char }
    → { pdi : PDInstance* r pf }
    → { sf∈pdi : ( r , pf ⊢* sf ∈ pdi ) }
    ---------------------------
    → Ex*>-first {r} {pf} {sf} pdi sf∈pdi []
  ex*>-first-skip : ∀ { r : RE } { pf sf : List Char }
    → { pdi : PDInstance* r pf }
    → { pdi' : PDInstance* r pf }
    → { pdis : List (PDInstance* r pf) }
    → { sf∈pdi : ( r , pf ⊢* sf ∈ pdi ) }
    → ¬ ( r , pf ⊢* sf ∈ pdi' )
    → Ex*>-first {r} {pf} {sf} pdi sf∈pdi pdis
    ----------------------------------------------------
    → Ex*>-first {r} {pf} {sf} pdi sf∈pdi (pdi' ∷ pdis)
  ex*>-first-cons : ∀ { r : RE } { pf sf : List Char }
    → { pdi : PDInstance* r pf }
    → { pdi' : PDInstance* r pf }
    → { pdis : List (PDInstance* r pf) }
    → { sf∈pdi : ( r , pf ⊢* sf ∈ pdi ) }
    → ( r , pf ⊢* sf ∈ pdi' )
    → r , pf  ⊢* pdi > pdi'
    ----------------------------------------------------
    → Ex*>-first {r} {pf} {sf} pdi sf∈pdi (pdi' ∷ pdis)
-} 

data Ex*>-sorted : ∀ { r : RE } { w : List Char } ( pdis : List (PDInstance* r w) ) → Set where
  ex*>-nil  : ∀ { r : RE } { w : List Char } → Ex*>-sorted {r} {w} []
  ex*>-cons : ∀ { r : RE } { w : List Char } 
    → { pdi : PDInstance* r w }
    → { pdis : List (PDInstance* r w) } 
    → Ex*>-sorted {r} {w} pdis 
    → Ex*>-maybe {r} {w} pdi (head pdis)
    --------------------------------------
    → Ex*>-sorted {r} {w} ( pdi ∷ pdis )

{-
data Ex*>-weak-first : ∀ { r : RE } { pf sf : List Char } → ( pdi : PDInstance* r pf ) → ( pdis : List (PDInstance* r pf ) ) → Set where
  ex*>-weak-nonmember : ∀ { r : RE } { pf sf : List Char }
    → ( pdi : PDInstance* r pf )
    → ( pdis : List (PDInstance* r pf ) )
    → ¬ ( r , pf ⊢* sf ∈ pdi )
    ----------------------------------
    → Ex*>-weak-first {r} {pf} {sf} pdi pdis
  ex*>-weak-member : ∀ { r : RE } { pf sf : List Char }
    → ( pdi : PDInstance* r pf )
    → ( pdis : List (PDInstance* r pf ) )
    → ( sf∈pdi : r , pf ⊢* sf ∈ pdi )
    → Ex*>-first {r} {pf} {sf} pdi sf∈pdi pdis
    ----------------------------------
    → Ex*>-weak-first {r} {pf} {sf} pdi pdis
-}     


```


```agda
p-inhabit* : ∀ { r : RE } { pf : List Char } → PDInstance* r pf → RE 
p-inhabit* {r} {pf} (pdinstance* {p} {r} {pf} _ _ ) = p

inj-inhabit* : ∀ { r : RE } { pf : List Char } → (pdi : PDInstance* r pf) → ( U (p-inhabit* pdi) → U r  )
inj-inhabit* {r} {pf} (pdinstance* {p} {r} {pf} inj _ ) = inj 

s-ev-inhabit* : ∀ { r : RE } { pf : List Char } → (pdi : PDInstance* r pf) → ( ( u : U (p-inhabit* pdi)) → proj₁ (flat ((inj-inhabit* pdi) u)) ≡ pf ++ (proj₁ (flat u))   )
s-ev-inhabit* {r} {pf} (pdinstance* {p} {r} {pf} inj s-ev ) = s-ev



data _,_⊢*_≥_ : ∀ ( r : RE ) → ( pf : List Char ) → PDInstance* r pf → PDInstance* r pf → Set where
  *≥-pdi-[] : ∀ { r : RE }
    → r , [] ⊢* pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ≥ pdinstance* {r} {r} (λ u → u) (λ u → refl)

  -- do we need to do the same for ≥-pdi? 
  *≥-pdi-= : ∀ { r : RE } { c : Char } { pf : List Char } 
    → ( pdi : PDInstance* r ( c ∷ pf ) )
    → ( 
        ( u₁ : U ( p-inhabit* pdi ) )
        → ( u₂ : U ( p-inhabit* pdi ) )
        → ( (p-inhabit* pdi) ⊢ u₁ ≅ u₂ )
        → ( (p-inhabit* pdi) ⊢ u₁ > u₂ )
        → ( ( r ⊢ (inj-inhabit* pdi) u₁ ≅ (inj-inhabit* pdi) u₂) × ( r ⊢ (inj-inhabit* pdi) u₁ > (inj-inhabit* pdi) u₂) ) )  
    → r , ( c ∷ pf )  ⊢* pdi ≥ pdi 


  *≥-pdi-> : ∀ { r : RE } { c : Char } { pf : List Char } 
    → ( pdi₁ : PDInstance* r ( c ∷ pf ) )
    → ( pdi₂ : PDInstance* r ( c ∷ pf ) )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r ) → (Recons* u₁ pdi₁ ) → (Recons* u₂ pdi₂) → r ⊢ u₁ > u₂ )
    → r , ( c ∷ pf )  ⊢* pdi₁ ≥  pdi₂ 



```
```agda
*≥-pdi-trans : ∀ { r : RE }  { pf : List Char } 
  → { pdi₁ : PDInstance* r pf }
  → { pdi₂ : PDInstance* r pf }
  → { pdi₃ : PDInstance* r pf }
  → r , pf   ⊢* pdi₁ ≥ pdi₂
  → r , pf   ⊢* pdi₂ ≥ pdi₃
  -------------------------------------------
  → r , pf  ⊢* pdi₁ ≥  pdi₃
*≥-pdi-trans {r} {[]}  *≥-pdi-[] *≥-pdi-[] = *≥-pdi-[]

*≥-pdi-trans {r} { c ∷ pf } (*≥-pdi-> pdi₁ pdi₂  u₁>u₂-ev ) (*≥-pdi-> .pdi₂ pdi₃ u₂>u₃-ev ) = *≥-pdi-> pdi₁ pdi₃ *>-ev 
  where
    *>-ev : ( u₁ : U r )
          → ( u₃ : U r )
          → Recons* u₁ pdi₁
          → Recons* u₃ pdi₃
          ------------------------------
          → r ⊢ u₁ > u₃
    *>-ev u₁ u₃ recons₁ recons₃  =
      let u₂-recons₂ = pdi*-∃  {r} {c ∷ pf} pdi₂
      in  >-trans (u₁>u₂-ev u₁ (proj₁ u₂-recons₂) recons₁ (proj₂ u₂-recons₂) )
                  (u₂>u₃-ev (proj₁ u₂-recons₂) u₃ (proj₂ u₂-recons₂) recons₃ )     


``` 

```agda
data Ex*≥-maybe : ∀ { r : RE } { pf : List Char } → ( pdi : PDInstance* r pf ) → ( mpdi : Maybe (PDInstance* r pf) ) → Set where
  ex*≥-nothing : ∀ { r : RE } { pf : List Char } 
    → { pdi : PDInstance* r pf }
    ---------------------------
    → Ex*≥-maybe {r} {pf} pdi nothing
  ex*≥-just : ∀ { r : RE } { pf : List Char } 
    → { pdi : PDInstance* r pf }
    → { pdi' : PDInstance* r pf }
    → r , pf  ⊢* pdi ≥ pdi'
    ----------------------------------
    → Ex*≥-maybe {r} {pf} pdi (just pdi')



data Ex*≥-sorted : ∀ { r : RE } { w : List Char } ( pdis : List (PDInstance* r w) ) → Set where
  ex*≥-nil  : ∀ { r : RE } { w : List Char } → Ex*≥-sorted {r} {w} []
  ex*≥-cons : ∀ { r : RE } { w : List Char } 
    → { pdi : PDInstance* r w }
    → { pdis : List (PDInstance* r w) } 
    → Ex*≥-sorted {r} {w} pdis 
    → Ex*≥-maybe {r} {w} pdi (head pdis)
    --------------------------------------
    → Ex*≥-sorted {r} {w} ( pdi ∷ pdis )

```



### Lemma 41: the list of pdinstance*'s from pdUMany[ r , c] is extended LNE sorted. 


Let r be a non problematic regular expression.

Let w be a word.

Then pdUMany[r , w] is extended LNE sorted.


#### Sub Lemma 41.1 - 41.6 : Ex*>-sortedness is inductively preserved over pdinstance*'s operations 



```agda

-------------------------------------------------------------
-- Sub Lemma 41.1 - 41.6 BEGIN
-------------------------------------------------------------

-- perhaps we need to define a decidability check r , pf ⊢* sf ∈? pdi which give us (yes (r , pf ⊢* sf ∈ pdi)) or (no ¬ (r , pf ⊢* sf ∈ pdi))


-- Ex*>-first-cast : The `Ex*>-first` data type carries a proof `sf∈pdi` that the reference pdi accepts `sf`.
-- However, the constructors of `Ex*>-first` never inspect this proof (they only check whether subsequent pdis accept `sf`).
-- Hence, the same `Ex*>-first` witness can be reused with any other proof `sf∈pdi₂` for the same `pdi` and `sf`.
-- This lemma performs that "cast" by structural recursion over the witness.
{-
Ex*>-first-cast : ∀ { r : RE } { pf sf : List Char }
  → { pdi : PDInstance* r pf }
  → { sf∈pdi₁ sf∈pdi₂ : r , pf ⊢* sf ∈ pdi }
  → { pdis : List (PDInstance* r pf) }
  → Ex*>-first pdi sf∈pdi₁ pdis
  → Ex*>-first pdi sf∈pdi₂ pdis
Ex*>-first-cast {r} {pf} {sf} {pdi} {sf∈pdi₁} {sf∈pdi₂} {[]} ex*>-first-nil = ex*>-first-nil
Ex*>-first-cast {r} {pf} {sf} {pdi} {sf∈pdi₁} {sf∈pdi₂} {pdi' ∷ pdis} (ex*>-first-skip ¬sf∈pdi' first) = ex*>-first-skip ¬sf∈pdi' (Ex*>-first-cast first)
Ex*>-first-cast {r} {pf} {sf} {pdi} {sf∈pdi₁} {sf∈pdi₂} {pdi' ∷ pdis} (ex*>-first-cons sf∈pdi' pdi>pdi') = ex*>-first-cons sf∈pdi' pdi>pdi'
-}

-- Ex*>-first-++ : If `pdi` is "first" among `pdis₁` (i.e. every pdi before the first accepting one is skipped),
-- and also "first" among `pdis₂`, then it is "first" among the concatenation `pdis₁ ++ pdis₂`.
-- The key insight is that the first accepting pdi in `pdis₁ ++ pdis₂` is either:
--   1) The first accepting pdi found in `pdis₁` (terminal, via `ex*>-first-cons`), or
--   2) If `pdis₁` has no accepting pdis, then the first accepting pdi of `pdis₂`.
{-
Ex*>-first-++ : ∀ { r : RE } { pf sf : List Char }
  → { pdi : PDInstance* r pf }
  → { sf∈pdi : r , pf ⊢* sf ∈ pdi }
  → { pdis₁ pdis₂ : List (PDInstance* r pf) }
  → Ex*>-first pdi sf∈pdi pdis₁
  → Ex*>-first pdi sf∈pdi pdis₂
  → Ex*>-first pdi sf∈pdi (pdis₁ ++ pdis₂)
Ex*>-first-++ {r} {pf} {sf} {pdi} {sf∈pdi} {[]} {pdis₂} ex*>-first-nil first-pdis₂ = first-pdis₂
Ex*>-first-++ {r} {pf} {sf} {pdi} {sf∈pdi} {pdi' ∷ pdis₁'} {pdis₂} (ex*>-first-skip ¬sf∈pdi' first-pdis₁') first-pdis₂ =
  ex*>-first-skip ¬sf∈pdi' (Ex*>-first-++ first-pdis₁' first-pdis₂)
Ex*>-first-++ {r} {pf} {sf} {pdi} {sf∈pdi} {pdi' ∷ pdis₁'} {pdis₂} (ex*>-first-cons sf∈pdi' pdi>pdi') first-pdis₂ =
  ex*>-first-cons sf∈pdi' pdi>pdi'
-} 

concat-ex*-sorted : ∀ { r : RE } { w : List Char }
    → ( pdis₁ : List ( PDInstance* r w ))
    → ( pdis₂ : List ( PDInstance* r w ))
    → Ex*>-sorted { r } { w } pdis₁
    → Ex*>-sorted { r } {w} pdis₂
    → All (λ pdi₁ → Ex*>-maybe  {r} pdi₁ (head pdis₂)) pdis₁
    -------------------------------------------------------
    → Ex*>-sorted { r } {w} (pdis₁ ++ pdis₂)
concat-ex*-sorted []                       pdis₂          ex*>-nil                                       pdis₂-sorted     []                              = pdis₂-sorted
concat-ex*-sorted pdis₁                    []             pdis₁-sorted                                  ex*>-nil           _  rewrite (++-identityʳ pdis₁) = pdis₁-sorted
concat-ex*-sorted (pdi₁ ∷ [])             (pdi₂ ∷ pdis₂) pdis₁-sorted                                  pdi₂pdis₂-sorted (ex*>-just pdi₁>pdi₂  ∷ [])      = ex*>-cons pdi₂pdis₂-sorted (ex*>-just pdi₁>pdi₂) 
concat-ex*-sorted (pdi₁ ∷ pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) (ex*>-cons pdi₁'pdis₁-sorted pdi₁>head-pdis₁)  pdi₂pdis₂-sorted (ex*>-just pdi₁>pdi₂  ∷ pxs)     = ex*>-cons ind-hyp pdi₁>head-pdis₁
  where
    ind-hyp = concat-ex*-sorted (pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) pdi₁'pdis₁-sorted  pdi₂pdis₂-sorted  pxs


concat-ex*≥-sorted : ∀ { r : RE } { w : List Char }
    → ( pdis₁ : List ( PDInstance* r w ))
    → ( pdis₂ : List ( PDInstance* r w ))
    → Ex*≥-sorted { r } { w } pdis₁
    → Ex*≥-sorted { r } {w} pdis₂
    → All (λ pdi₁ → Ex*≥-maybe  {r} pdi₁ (head pdis₂)) pdis₁
    -------------------------------------------------------
    → Ex*≥-sorted { r } {w} (pdis₁ ++ pdis₂)
concat-ex*≥-sorted []                       pdis₂          ex*≥-nil                                       pdis₂-sorted     []                              = pdis₂-sorted
concat-ex*≥-sorted pdis₁                    []             pdis₁-sorted                                  ex*≥-nil           _  rewrite (++-identityʳ pdis₁) = pdis₁-sorted
concat-ex*≥-sorted (pdi₁ ∷ [])             (pdi₂ ∷ pdis₂) pdis₁-sorted                                  pdi₂pdis₂-sorted (ex*≥-just pdi₁≥pdi₂  ∷ [])      = ex*≥-cons pdi₂pdis₂-sorted (ex*≥-just pdi₁≥pdi₂) 
concat-ex*≥-sorted (pdi₁ ∷ pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) (ex*≥-cons pdi₁'pdis₁-sorted pdi₁≥head-pdis₁)  pdi₂pdis₂-sorted (ex*≥-just pdi₁≥pdi₂  ∷ pxs)     = ex*≥-cons ind-hyp pdi₁≥head-pdis₁
  where
    ind-hyp = concat-ex*≥-sorted (pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) pdi₁'pdis₁-sorted  pdi₂pdis₂-sorted  pxs
{-
The below does not work

Counterexample: d = ($a ● $c) + ($a ● $d)
In pdU[d, a], there are two pdis:
1. pdi₁ from the left branch ($a ● $c):  
   Reconstructs v₁ = LeftU (PairU (LetterU a) (LetterU c)) with flat v₁ = [a, c].
2. pdi₂ from the right branch ($a ● $d):  
   Reconstructs v₂ = RightU (PairU (LetterU a) (LetterU d)) with flat v₂ = [a, d].
Since pdU-sorted puts all left pdis before right pdis, pdi₁ > pdi₂ holds in Ex>-sorted (via choice-lr).
Now in compose-pdi-with-ex*>-head-map-compose-pdi-with, d→r is the injection from the outer pdinstance* (say the identity for simplicity). We need to show r ⊢ v₁ > v₂. We know d ⊢ v₁ > v₂ via choice-lr.
But d→r-inc-ev (from *>-Inc-≅) has type:
(v₁ v₂ : U d) → d ⊢ v₁ ≅ v₂ → d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂
For d = l + r, ≅ is +⊢≅ which requires equal flat words. Since [a, c] ≢ [a, d], we have d ⊢ v₁ ≢ v₂. Therefore the ≅ premise is false, and d→r-inc-ev cannot be applied.
Why *>-Inc-≅ is too strong here
The problem is that *>-Inc-≅ requires ≅ between arbitrary trees from different pdis in pdU[d,c]. But pdis in pdU[d,c] can have different source REs and reconstruct trees with different flat words. There is no guarantee they are ≅.
What about *>-Inc?
*>-Inc (without the ≅ premise) does hold for every pdinstance* in pdUMany[r,w]. Looking at the proofs in Order.lagda.md:
- pdinstance-left/right: left-mono / right-mono preserve > directly.
- pdinstance-fst: uses seq₁ with length proofs from injFstSnd — never needs ≅.
- pdinstance-star: uses star-head with length proofs from mkinjListSoundEv — never needs ≅.
- mk-snd-pdi: uses seq₂ with refl on the fixed empty tree — never needs ≅.
- inv-assoc: preserves > by reassociating seq₁/seq₂.
All the >-Inc-≅ lemmas in Order.lagda.md actually only use the > evidence; the ≅ evidence is never used meaningfully. They could be rewritten as >-Inc lemmas trivially.
Options to fix the hole
1. Use *>-Inc (recommended): Define *>-Inc without ≅, prove all pdi operations satisfy it, thread it through pdUMany-*>-inc, and change compose-pdi-with-ex*>-head-map-compose-pdi-with to take *>-Inc evidence for d→r.
2. Restructure the proof: Instead of parameterizing by a generic d→r-inc-ev, prove directly inside advance-pdi*-with-c-sorted that for the specific d→r from the current pdinstance*, > is preserved for trees from pdU[d,c]. But this essentially rebuilds the *>-Inc proof inline.
Would you like me to implement option 1? It requires adding *>-Inc and >-Inc definitions + lemmas to Order.lagda.md and adjusting the call sites in ExtendedOrder.lagda.md.


-}

{-
PDInstance-descendant : ∀ {r c} → PDInstance r c → RE
PDInstance-descendant (pdinstance {p} inj s-ev) = p

PDInstance-accepts-sf : ∀ {r c} → PDInstance r c → List Char → Set
PDInstance-accepts-sf pdi sf = sf ∈⟦ PDInstance-descendant pdi ⟧

Maybe-PDInstance-accepts-sf : ∀ {r c} → Maybe (PDInstance r c) → List Char → Set
Maybe-PDInstance-accepts-sf nothing sf = ⊤
Maybe-PDInstance-accepts-sf (just pdi) sf = PDInstance-accepts-sf pdi sf

compose-pdi-with-∈ : ∀ { d r : RE } { pf : List Char } { c : Char } { sf : List Char }
  → ( d→r : U d → U r )
  → ( s-ev-d→r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pf ++ ( proj₁ (flat {d} v) )) )
  → ( pdi : PDInstance d c )
  → PDInstance-accepts-sf pdi sf
  → r , pf ∷ʳ c ⊢* sf ∈ compose-pdi-with d→r s-ev-d→r pdi
compose-pdi-with-∈ {pf = pf} {c = c} d→r s-ev-d→r (pdinstance p→d s-ev-p→d) sf∈p = *∈-pdi {pf = pf ∷ʳ c} sf∈p (λ x → d→r (p→d x)) (compose-pdi-with-soundEv d→r s-ev-d→r p→d s-ev-p→d)
-}


{-
Kenny:
In `lnegen/ExtendedOrder.lagda.md`, the premise `>-inc-d→r` in lemmas `map-compose-pdi-with-sorted` and `compose-pdi-with-ex*>-head-map-compose-pdi-with`, can we add back `d ⊢ v₁ ≅ v₂`? i.e. `( >-inc-d→r :  (v₁ v₂ : U d) → d ⊢ v₁ ≅ v₂ → d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂ )` instead of `( >-inc-d→r :  (v₁ v₂ : U d) → d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂ )`?

Kimi:
No — we cannot add it back. It would make compose-pdi-with-ex*>-head-map-compose-pdi-with unprovable. Here is a concrete counterexample.
The counterexample
Take d = l ● r where:
- l = $a + ($a ● $b) (non-problematic, both branches have first-char a)
- r = $b + ε (accepts ε, so ε∈r)
- c = 'a'
Then pdU[l, 'a'] contains two pdis:
1. pdiₗ₁ with descendant ε (from the left $a branch)
2. pdiₗ₂ with descendant $b (from the right $a ● $b branch)
In pdU[d, 'a'] with ε∈l, both appear as fst pdis:
- pdi₁ = pdinstance-fst pdiₗ₁ with descendant ε ● r. Its reconstructions are v₁ = PairU (LetterU 'a') v₁' for any v₁' : U r.
- pdi₂ = pdinstance-fst pdiₗ₂ with descendant $b ● r. Its reconstructions are v₂ = PairU (PairU (LetterU 'a') (LetterU 'b')) v₂' for any v₂' : U r.
Because pdU-sorted puts all left-branch pdis before right-branch pdis, pdi₁ and pdi₂ are adjacent in Ex>-sorted, so d ⊢ v₁ > v₂ holds for all reconstructions.
Now pick:
- v₁' = LeftU (LetterU 'b') (the $b branch of r), so flat v₁' = "b"
- v₂' = RightU EmptyU (the ε branch of r), so flat v₂' = []
Then:
- flat v₁ = flat (LetterU 'a') ++ flat v₁' = "a" ++ "b" = "ab"
- flat v₂ = flat (PairU (LetterU 'a') (LetterU 'b')) ++ flat v₂' = "ab" ++ [] = "ab"
So flat v₁ ≡ flat v₂, but:
- l ⊢ LetterU 'a' ≢ PairU (LetterU 'a') (LetterU 'b') because their flat words differ ("a" vs "ab")
- Therefore l ● r ⊢ v₁ ≢ v₂ by ●⊢≅ — the ≅ relation requires component-wise ≅, which fails.
Why this matters for ex*>-ev
In compose-pdi-with-ex*>-head-map-compose-pdi-with, the ex*>-ev function is invoked with exactly these v₁ and v₂. It would need to call:
>-inc-d→r v₁ v₂ (d ⊢ v₁ ≅ v₂) (d ⊢ v₁ > v₂)
But d ⊢ v₁ ≅ v₂ is false in this case. There is no way to construct it from the available hypotheses.
The fix that already works
The current proof avoids this entirely because >-inc-d→r has type:
(v₁ v₂ : U d) → d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂
And d ⊢ v₁ > v₂ is already given directly by pdi₁>pdi₂ (via Ex>-maybe). The ≅ premise is simply not needed.
If your downstream code currently requires *>-Inc-≅, the right fix is to change it to use *>-Inc (without ≅). The file's own comments note that all the >-inc lemmas in Order.lagda.md can be rewritten to use only >, and doing so is exactly what makes this proof go through.
Would you like me to proceed with updating the downstream commented lemmas to use *>-Inc instead?


Kenny:

The above counter example is flaw, e.g.
1) ε∉l
2) v₁ and v₂ are not parse trees of d, but
  u₁ = PairU (LeftU (LetterU 'a')) v₁' ; and 
  u₂ = PairU (RightU (PairU (LetterU 'a') (LetterU 'b'))) v₂'
  are.
3) the counter example still applies
>-inc-d→r u₁ u₂ as ¬ ( d ⊢ u₁ ≅ u₂ )
4) in general, we can't apply d ⊢ _ ≅ _  where d is the top level regex (non partial derivative) .
-}

compose-pdi-with-ex*>-head-map-compose-pdi-with : ∀ { d r : RE } { pref : List Char} { c : Char }
  → ( d→r : U d → U r ) -- a part of a pdi*
  → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) ) -- a part of a pdi* 
  → ( >-inc-d→r :  (v₁ v₂ : U d) →  d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂ ) -- strict inc evidence for d→r for that pdi*
  -- in what situation, we don't have d ⊢ v₁ ≅ v₂?  only when d ≡ r ?
  -- we need d to be a strict descendant, i.e. d ∈ pdUMany [ r , w ] where w is not [] 
  → ( pdi : PDInstance d c ) 
  → ( pdis : List (PDInstance d c) )
  → Ex>-maybe pdi (head pdis)
  -------------------------------------------------------------------------------------------------
  → Ex*>-maybe (compose-pdi-with d→r s-ev-d-r pdi) (head (List.map (compose-pdi-with d→r s-ev-d-r) pdis))
compose-pdi-with-ex*>-head-map-compose-pdi-with {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r pdi []  ex>-nothing = ex*>-nothing   
compose-pdi-with-ex*>-head-map-compose-pdi-with {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r
  pdi₁@(pdinstance {p₁} {d} {c} p₁→d s-ev-p₁-d)
  (pdi₂@(pdinstance {p₂} {d} {c} p₂→d s-ev-p₂-d) ∷ pdis )
  (ex>-just pdi₁>pdi₂@(>-pdi _ _ u₁→u₂→rec₁→rec₂→u₁>u₂ ) ) = ex*>-just (*>-pdi -- u₁ and u₂ of U d
                             {r} {pref ∷ʳ c}
                             (compose-pdi-with d→r s-ev-d-r pdi₁)
                             (compose-pdi-with d→r s-ev-d-r pdi₂) -- from the same pdinstance* 
                             ex*>-ev ) 
  where
            -- 1) from inv-recons*-compose-pdi-with we note that
            -- u₁ is reconstructable from pdinstance* d→r s-ev-d-r
            -- u₂ is reconstructable from pdinstance* d→r s-ev-d-r
            --   same pdinstance* but different w∈⟦d⟧
            -- 2) all pdinstance*s must be *>-inc , namely
            --    v1 v2 : d →  d ⊢ v1 > v2 → d→r v₁ > d→r v₂
            --  if can we show u₁ = d→r v₁ and u₂ = d→ r v₂ ? 

    ex*>-ev : ∀ (u₁ u₂ : U r )
      → Recons* u₁ (compose-pdi-with d→r s-ev-d-r (pdinstance p₁→d s-ev-p₁-d))
      → Recons* u₂ (compose-pdi-with d→r s-ev-d-r (pdinstance p₂→d s-ev-p₂-d))
      ----------------------------------------------------------------------------
      → r ⊢ u₁ > u₂
    ex*>-ev u₁ u₂
            rec*₁@(recons* .{p₁} .{r} {w₁} {pref++c} u₁ ( w₁∈⟦p₁⟧ , d→r∘p₁→d-unflat-w₁∈⟦p₁⟧≡u₁ ) )
            rec*₂@(recons* .{p₂} .{r} {w₂} .{pref++c}  u₂ ( w₂∈⟦p₂⟧ , d→r∘p₁→d-unflat-w₂∈⟦p₂⟧≡u₂ ) ) 
            with inv-recons*-compose-pdi-with u₁ pdi₁ d→r s-ev-d-r rec*₁     | inv-recons*-compose-pdi-with u₂ pdi₂ d→r s-ev-d-r rec*₂             
    ... | recons* .{d} .{r} {cw₁} .{pref} .u₁ ( cw₁∈⟦d⟧ , d→r-unflat-cw₁∈⟦d⟧≡u₁ ) | recons* .{d} .{r} {cw₂} .{pref} .u₂ ( cw₂∈⟦d⟧ , d→r-unflat-cw₂∈⟦d⟧≡u₂ ) 
            rewrite sym d→r∘p₁→d-unflat-w₁∈⟦p₁⟧≡u₁ | sym  d→r∘p₁→d-unflat-w₂∈⟦p₂⟧≡u₂ = 
                >-inc-d→r (p₁→d (unflat w₁∈⟦p₁⟧) ) (p₂→d (unflat w₂∈⟦p₂⟧)  )
                  (u₁→u₂→rec₁→rec₂→u₁>u₂ (p₁→d (unflat w₁∈⟦p₁⟧))
                                                                                               (p₂→d (unflat w₂∈⟦p₂⟧))
                                                                                               (recons (p₁→d (unflat w₁∈⟦p₁⟧)) (w₁∈⟦p₁⟧ , refl))
                                                                                               (recons (p₂→d (unflat w₂∈⟦p₂⟧)) (w₂∈⟦p₂⟧ , refl)))


compose-pdi-with-ex*≥-head-map-compose-pdi-with : ∀ { d r : RE } { pref : List Char} { c : Char }
  → ( d→r : U d → U r ) -- a part of a pdi*
  → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) ) -- a part of a pdi* 
  → ( >-inc-d→r :  (v₁ v₂ : U d) →  d ⊢ v₁ ≅ v₂ → d ⊢ v₁ > v₂ → ( r ⊢ d→r v₁ ≅ d→r v₂ × r ⊢ d→r v₁ > d→r v₂ ) ) -- strict inc evidence for d→r for that pdi*
  -- in what situation, we don't have d ⊢ v₁ ≅ v₂?  only when d ≡ r ?
  -- we need d to be a strict descendant, i.e. d ∈ pdUMany [ r , w ] where w is not [] 
  → ( pdi : PDInstance d c )
  → ( >-Inc-≅ pdi ) 
  → ( pdis : List (PDInstance d c) )
  → Ex>-maybe pdi (head pdis)
  -------------------------------------------------------------------------------------------------
  → Ex*≥-maybe (compose-pdi-with d→r s-ev-d-r pdi) (head (List.map (compose-pdi-with d→r s-ev-d-r) pdis))
compose-pdi-with-ex*≥-head-map-compose-pdi-with {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r pdi (>-inc u₁→u₂→u₁≅u₂→in₁u₁≅in₁u₂) []  ex>-nothing = ex*≥-nothing   
compose-pdi-with-ex*≥-head-map-compose-pdi-with {d} {r} {x ∷ pref} {c} d→r s-ev-d-r >-inc-d→r
  pdi₁@(pdinstance {p₁} {d} {c} p₁→d s-ev-p₁-d) (>-inc u₁→u₂→u₁≅u₂→p₁→du₁≅p₁→du₂)
  (pdi₂@(pdinstance {p₂} {d} {c} p₂→d s-ev-p₂-d) ∷ pdis )
  {- p₁→d u₁ > p₂→d u₂?
     p₁→d u₁ ≅ p₂→d u₂?
     but ¬ p₁ ≡ p₂
     we dont have u₁ ≅ u₂ 
  -}
  (ex>-just pdi₁>pdi₂@(>-pdi _ _ u₁→u₂→rec₁→rec₂→u₁>u₂ ) ) = ex*≥-just (*≥-pdi->  -- u₁ and u₂ of U d
                             {r} {x} { pref  ∷ʳ c}
                             (compose-pdi-with d→r s-ev-d-r pdi₁)
                             (compose-pdi-with d→r s-ev-d-r pdi₂)

                             ex*>-ev ) 
  where
            -- 1) from inv-recons*-compose-pdi-with we note that
            -- u₁ is reconstructable from pdinstance* d→r s-ev-d-r
            -- u₂ is reconstructable from pdinstance* d→r s-ev-d-r
            --   same pdinstance* but different w∈⟦d⟧
            -- 2) all pdinstance*s must be *>-inc , namely
            --    v1 v2 : d →  d ⊢ v1 > v2 → d→r v₁ > d→r v₂
            --  if can we show u₁ = d→r v₁ and u₂ = d→ r v₂ ? 

    ex*>-ev : ∀ (u₁ u₂ : U r )
      → Recons* u₁ (compose-pdi-with d→r s-ev-d-r (pdinstance p₁→d s-ev-p₁-d))
      → Recons* u₂ (compose-pdi-with d→r s-ev-d-r (pdinstance p₂→d s-ev-p₂-d))
      ----------------------------------------------------------------------------
      → r ⊢ u₁ > u₂
    ex*>-ev u₁ u₂
            rec*₁@(recons* .{p₁} .{r} {w₁} {pref++c} u₁ ( w₁∈⟦p₁⟧ , d→r∘p₁→d-unflat-w₁∈⟦p₁⟧≡u₁ ) )
            rec*₂@(recons* .{p₂} .{r} {w₂} .{pref++c}  u₂ ( w₂∈⟦p₂⟧ , d→r∘p₁→d-unflat-w₂∈⟦p₂⟧≡u₂ ) ) 
            with inv-recons*-compose-pdi-with u₁ pdi₁ d→r s-ev-d-r rec*₁     | inv-recons*-compose-pdi-with u₂ pdi₂ d→r s-ev-d-r rec*₂             
    ... | recons* .{d} .{r} {cw₁} .{x ∷ pref} .u₁ ( cw₁∈⟦d⟧ , d→r-unflat-cw₁∈⟦d⟧≡u₁ ) | recons* .{d} .{r} {cw₂} .{x ∷ pref} .u₂ ( cw₂∈⟦d⟧ , d→r-unflat-cw₂∈⟦d⟧≡u₂ ) 
            rewrite sym d→r∘p₁→d-unflat-w₁∈⟦p₁⟧≡u₁ | sym  d→r∘p₁→d-unflat-w₂∈⟦p₂⟧≡u₂ = 
                proj₂ (  >-inc-d→r (p₁→d (unflat w₁∈⟦p₁⟧) ) (p₂→d (unflat w₂∈⟦p₂⟧)  )
                  {!!}  -- this hole requires  d ⊢ p₁→d (unflat w₁∈⟦p₁⟧) ≅ p₂→d (unflat w₂∈⟦p₂⟧)
                  -- when d = a* ● a* 
                  --      p₁ = (ε ● a*) ● a* and p₂ = ε ● a*
                  --      w₁ = [] and w₂ = [] 
                  -- unflat []∈⟦p₁⟧ --> PairU (PairU EmptyU (ListU [])) (ListU [])
                  -- unflat []∈⟦p₂⟧ --> PairU EmptyU (ListU [])
                  -- p₁→d ∘ unflat []∈⟦p₁⟧ --> PairU (PairU (ListU (LetterU 'a' ∷ [])) (ListU []))                (ListU [])
                  -- p₂→d ∘ unflat []∈⟦p₂⟧ --> PairU (PairU (ListU [])                 (ListU (Letter 'a' ∷ []))) (ListU [])
                  -- we don't have d ⊢ p₁→d (unflat w₁∈⟦p₁⟧) ≅ p₂→d (unflat w₂∈⟦p₂⟧)!!!
                  -- we need a special coercion for this case!!
                  -- what is the relationship between p₁ and p₂ and d? this happens only d has an alternative branch in the shape r ● t and ε∈ r. 
                  (u₁→u₂→rec₁→rec₂→u₁>u₂ (p₁→d (unflat w₁∈⟦p₁⟧))
                                                                                               (p₂→d (unflat w₂∈⟦p₂⟧))
                                                                                               (recons (p₁→d (unflat w₁∈⟦p₁⟧)) (w₁∈⟦p₁⟧ , refl))
                                                                                               (recons (p₂→d (unflat w₂∈⟦p₂⟧)) (w₂∈⟦p₂⟧ , refl))) )




map-compose-pdi-with-sorted : ∀ { d r : RE } { pref : List Char} { c : Char }
  → ( d→r : U d → U r )
  → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → ( >-inc-d→r :  (v₁ v₂ : U d) → d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂ ) -- strict inc evidence for d→r  
  → ( pdis : List (PDInstance d c) )
  → Ex>-sorted pdis
  -------------------------------------------------------------
  → Ex*>-sorted {r}  (List.map (compose-pdi-with d→r s-ev-d-r) pdis )
map-compose-pdi-with-sorted {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r [] ex>-nil = ex*>-nil
map-compose-pdi-with-sorted {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r (pdi ∷ pdis)  (ex>-cons pdis-sorted pdi>head-pdis) =
  ex*>-cons ind-hyp
  (compose-pdi-with-ex*>-head-map-compose-pdi-with d→r s-ev-d-r >-inc-d→r pdi pdis pdi>head-pdis)
  where
    ind-hyp : Ex*>-sorted {r}  (List.map (compose-pdi-with d→r s-ev-d-r) pdis )
    ind-hyp = map-compose-pdi-with-sorted {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r pdis pdis-sorted 

-- adance-pdi*-with-c is collapsing the pdinstances vertically via composition 
-- need
advance-pdi*-with-c-sorted : ∀ { r : RE } { pref : List Char} { c : Char }
  → (pdi : PDInstance* r pref)
  → *>-Inc-≅ pdi -- do we need ≅-Preserve* pdi? 
  ----------------------------------------------------------
  → Ex*>-sorted (advance-pdi*-with-c {r} {pref} {c} pdi)
advance-pdi*-with-c-sorted {r} {pref} {c} pdi@(pdinstance* {d} {r} {pref} d→r s-ev-d-r) (*>-inc d→r-inc-ev) 
  with pdU[ d , c ]                        | pdU-sorted { d } {c}                      | pdU-≅-preserve {d} {c} -- we should use pdU-≅-preserve {d} {c} here 
... | []                                   | _                                         | _ = ex*>-nil
... | pdi₁@(pdinstance in₁ s-ev₁) ∷ pdis₁  | ex>-cons ex>-sorted-pdis₁ pdi₁>head-pdis₁ | (≅-pres u₁→u₂→u₁≅u₂→in₁u₁≅in₁u₂) ∷ ≅-pres-pdis₁   =
  ex*>-cons (map-compose-pdi-with-sorted d→r s-ev-d-r
                                         {!!} -- d→r-inc-ev
                                         pdis₁ ex>-sorted-pdis₁)
                                               (compose-pdi-with-ex*>-head-map-compose-pdi-with d→r s-ev-d-r
                                                 {!!} -- d→r-inc-ev -- d→r-inc-ev
                                                   pdi₁ pdis₁ pdi₁>head-pdis₁  )



{- 
advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c : ∀ { r : RE } { pref : List Char } { c : Char }
  → ( pdi :  PDInstance* r pref )
  → ( pdis : List (PDInstance* r pref ) )
  → Ex*>-sorted pdis
  → Ex*>-maybe pdi (head pdis)
  --------------------------------------------------------------------------
  → All (λ pdi₁ → Ex*>-maybe pdi₁ (head (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis))) (advance-pdi*-with-c {r} {pref} {c} pdi)
advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c {r}  {pref} {c} pdi [] ex*>-nil ex*>-nothing = prf (advance-pdi*-with-c {r} {pref} {c} pdi)
  where
    prf : (pdis : List (PDInstance* r  ( pref ∷ʳ c ) ) )
          → All  (λ pdi₁ → Ex*>-maybe pdi₁ nothing) pdis
    prf [] = []
    prf (pdi ∷ pdis) = ex*>-nothing ∷ prf pdis
advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c {r}  {pref} {c}
  pdi₁@(pdinstance* {d₁} {r} d₁→r s-ev-d₁r)
  (pdi₂@(pdinstance* {d₂} {r} d₂→r s-ev-d₂r) ∷ pdis) (ex*>-cons pdis-*>sorted pdi₂>head-pdis) (ex*>-just pdi₁>pdi₂@(*>-pdi .pdi₁ .pdi₂ u₁→u₂→rec₁→rec₂→u₁>u₂))
  with pdU[ d₂ , c ]
... | [] =  advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c {r}  {pref} {c}  pdi₁ pdis pdis-*>sorted (pdi₁>head pdis pdi₂>head-pdis) 
  where
    pdi₁>head : ( pdis : List (PDInstance* r pref) )
        →  Ex*>-maybe pdi₂ (head pdis) 
        →  Ex*>-maybe pdi₁ (head pdis)
    pdi₁>head [] ex*>-nothing = ex*>-nothing
    pdi₁>head (pdi₃ ∷ pdis) (ex*>-just pdi₂>pdi₃) = ex*>-just (*>-pdi-trans {r} {pref} {pdi₁} {pdi₂} {pdi₃} pdi₁>pdi₂ pdi₂>pdi₃)
... | pdi₂' ∷ pdis₂' = go pdU[ d₁ , c ] 
  where
      go : ( pdis₁' : List ( PDInstance d₁ c ) )
        → All ( λ pdi' → Ex*>-maybe pdi' (head
                ((List.map (compose-pdi-with d₂→r s-ev-d₂r) (pdi₂' ∷ pdis₂')) ++ (List.foldr _++_ [] (List.map advance-pdi*-with-c pdis))))) (List.map (compose-pdi-with d₁→r s-ev-d₁r) pdis₁')
      go [] = []
      go (pdi₁' ∷ pdis₁' ) = (ex*>-just (*>-pdi (compose-pdi-with d₁→r s-ev-d₁r pdi₁') (compose-pdi-with d₂→r s-ev-d₂r pdi₂') ev->)) ∷ (go pdis₁')
        where
          ev-> : ( u₁ : U r)
               → ( u₂ : U r)
               → ( Recons* u₁ (compose-pdi-with d₁→r s-ev-d₁r pdi₁') )
               → ( Recons* u₂ (compose-pdi-with d₂→r s-ev-d₂r pdi₂') ) 
               → r ⊢ u₁ > u₂
          ev-> u₁ u₂ recons₁ recons₂ = u₁→u₂→rec₁→rec₂→u₁>u₂ u₁ u₂ (inv-recons*-compose-pdi-with u₁ pdi₁' d₁→r s-ev-d₁r recons₁) (inv-recons*-compose-pdi-with u₂ pdi₂' d₂→r s-ev-d₂r recons₂)  
        

concatmap-advance-pdi*-with-c-sorted : ∀ { r : RE } { pref : List Char } { c : Char }
  → (pdis : List (PDInstance* r pref) )
  → Ex*>-sorted pdis
  → All *>-Inc pdis
  -------------------------------------------------------------------------------------
  → Ex*>-sorted (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
concatmap-advance-pdi*-with-c-sorted {r}  {pref} {c} [] ex*>-nil []  = ex*>-nil
concatmap-advance-pdi*-with-c-sorted {r}  {pref} {c} (pdi ∷ pdis) (ex*>-cons pdis-ex*>-sorted pdi>head-pdis) (*>-inc-pdi ∷ *>-inc-pdis ) = concat-ex*-sorted (advance-pdi*-with-c {r} {pref} {c} pdi) (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis) advance-pdi*-with-c-pdi-sorted ind-hyp advance-pdi*-with-c-pdi-all>head-ind-hyp
  where
    advance-pdi*-with-c-pdi-sorted : Ex*>-sorted (advance-pdi*-with-c {r} {pref} {c} pdi)
    advance-pdi*-with-c-pdi-sorted = advance-pdi*-with-c-sorted pdi *>-inc-pdi

    ind-hyp : Ex*>-sorted (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    ind-hyp = concatmap-advance-pdi*-with-c-sorted {r}  {pref} {c} pdis pdis-ex*>-sorted *>-inc-pdis

    advance-pdi*-with-c-pdi-all>head-ind-hyp : All (λ pdi₁ → Ex*>-maybe pdi₁ (head (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis))) (advance-pdi*-with-c pdi)
    advance-pdi*-with-c-pdi-all>head-ind-hyp =  advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c {r}  {pref} {c}  pdi pdis pdis-ex*>-sorted pdi>head-pdis


-------------------------------------------------------------
-- Sub Lemma 41.1 - 41.6 BEGIN
-------------------------------------------------------------
-}
 ```
 
#### Main proof for Lemma 41
 
```agda 
{-
pdUMany-aux-sorted : ∀ { r : RE }  { pref : List Char }
  → ( c : Char )
  → ( cs : List Char )
  → ( pdis : List (PDInstance* r pref ) )
  → Ex*>-sorted pdis
  → All *>-Inc pdis -- we need to thread through *>-Inc for all the sub lemmas so that we can use it in compose-pdi-with-ex*>-head-map-compose-pdi-with 
  -------------------------------------------------------
  → Ex*>-sorted (pdUMany-aux (c ∷ cs) pdis)
pdUMany-aux-sorted {r}  {pref} c [] pdis pdis-ex*>-sorted *>-inc-pdis  rewrite (++-identityʳ (pref ∷ʳ c) )   = concatmap-advance-pdi*-with-c-pdis-sorted
  where
    concatmap-advance-pdi*-with-c-pdis-sorted : Ex*>-sorted (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    concatmap-advance-pdi*-with-c-pdis-sorted = concatmap-advance-pdi*-with-c-sorted {r}  {pref} {c} pdis pdis-ex*>-sorted *>-inc-pdis 
-- pdis-ex*>-sorted
pdUMany-aux-sorted {r}  {pref} c (d ∷ cs) pdis pdis-ex*>-sorted *>-inc-pdis =
  pdUMany-aux-sorted {r}  {pref ∷ʳ c} d cs (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis) concatmap-advance-pdi*-with-c-pdis-sorted (concatmap-advance-pdi*-with-c-*>inc pdis *>-inc-pdis)
  where
    concatmap-advance-pdi*-with-c-pdis-sorted : Ex*>-sorted (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    concatmap-advance-pdi*-with-c-pdis-sorted = concatmap-advance-pdi*-with-c-sorted {r}  {pref} {c} pdis pdis-ex*>-sorted *>-inc-pdis 


  
pdUMany-sorted : ∀ { r : RE } { w : List Char }
  → Ex*>-sorted {r} {w} pdUMany[ r , w ]
pdUMany-sorted {r} {[]} = ex*>-cons ex*>-nil ex*>-nothing
pdUMany-sorted {r} {c ∷ cs} = pdUMany-aux-sorted {r}  {[]} c cs [  ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ] (ex*>-cons ex*>-nil ex*>-nothing)  pdUMany-*>-inc
-}
 ```
 
### Theorem 42 : ParseAll is LNE sorted
 
 
### Aux lemmas 
```agda
{-
map-inj-sorted : ∀ { p r : RE }
  → ( us : List ( U p ) )
  → ( inj : U p → U r )
  → ( (u₁ : U p) → (u₂ : U p) → p ⊢ u₁ > u₂ → r ⊢ inj u₁ > inj u₂ )
  → >-sorted {p} us
  ---------------------------------
  → >-sorted {r} (List.map inj us)
map-inj-sorted {p} {r} [] inj >-inc-ev >-nil = >-nil
map-inj-sorted {p} {r} (u ∷ []) inj >-inc-ev (>-cons >-nil >-nothing)  = >-cons >-nil >-nothing
map-inj-sorted {p} {r} (u₁ ∷ (u₂ ∷  us)) inj >-inc-ev (>-cons u₂us-sorted (>-just u₁>u₂) )  = >-cons ind-hyp (>-just (>-inc-ev u₁ u₂ u₁>u₂))
  where
    ind-hyp : >-sorted {r} (List.map inj (u₂ ∷ us))
    ind-hyp = map-inj-sorted {p} {r} (u₂ ∷ us) inj >-inc-ev u₂us-sorted 



-- this lemma is similar to advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c
buildU-all>head-concatmap-buildU : ∀ { p r : RE } { pref : List Char } { ε∈p } 
  → ( p→r : U p → U r )  -- buildU is inlined into map p→r (mkAllEmptyU ε∈p) 
  → ( s-ev-p-r : ∀ ( u : U p ) → ( proj₁ ( flat {r} (p→r u) ) ≡ pref ++ ( proj₁ (flat {p} u) )) ) -- ^ soundness evidence of the inject function  
  → ( pdis : List (PDInstance* r pref ) )
  → Ex*>-sorted pdis
  → Ex*>-maybe (pdinstance* p→r s-ev-p-r)  (head pdis)
  -------------------------------------------------------------------------------------------
  → All (λ u₁ → >-maybe  u₁ (head (concatMap (buildU {r} {pref}) pdis)) )
       (List.map p→r (mkAllEmptyU ε∈p))
buildU-all>head-concatmap-buildU {p} {r} {pref} {ε∈p} p→r s-ev-p-r [] ex*>-nil ex*>-nothing = prf (List.map p→r (mkAllEmptyU ε∈p))
  where
    prf : ( us : List (U r)) →   All (λ u₁ → >-maybe u₁ nothing) us 
    prf [] = []
    prf (u ∷ us )  = >-nothing ∷ prf us 
buildU-all>head-concatmap-buildU {p} {r} {pref} {ε∈p} p→r s-ev-p-r
  (pdi₂@(pdinstance* {p₂} {r} p₂→r s-ev-p₂-r) ∷ pdis) (ex*>-cons pdis-sorted pdi₂>head-pdis) (ex*>-just pdi₁>pdi₂@(*>-pdi pdi₁ pdi₂  u₁→u₂→r₁→r₂→u₁>u₂)) with ε∈? p₂
  
... | no ¬ε∈p₂ = buildU-all>head-concatmap-buildU {p} {r} {pref} {ε∈p} p→r s-ev-p-r pdis pdis-sorted (pdi₁>head pdis pdi₂>head-pdis)
  where
    pdi₁>head : ( pdis : List (PDInstance* r pref) )
        →  Ex*>-maybe pdi₂ (head pdis) 
        →  Ex*>-maybe pdi₁ (head pdis)
    pdi₁>head [] ex*>-nothing = ex*>-nothing
    pdi₁>head (pdi₃ ∷ pdis) (ex*>-just pdi₂>pdi₃) = ex*>-just (*>-pdi-trans {r} {pref} {pdi₁} {pdi₂} {pdi₃} pdi₁>pdi₂ pdi₂>pdi₃)    

... | yes ε∈p₂ with mkAllEmptyU ε∈p₂ in eq
...               | [] = Nullary.contradiction eq (mkAllEmptyU≢[]  ε∈p₂)
...               | v ∷ vs = go (mkAllEmptyU ε∈p)
  where
    go : ( us : List (U p) )
      →  All (λ u₁ → >-maybe u₁ (just (p₂→r v))) (List.map p→r us )
    go [] = []
    go ( u ∷ us ) = >-just (u₁→u₂→r₁→r₂→u₁>u₂ (p→r u) (p₂→r v) rec*₁ rec*₂ ) ∷ go us
      where
        rec*₁ : Recons* (p→r u) (pdinstance* p→r s-ev-p-r)
        rec*₁ with flat u in flat-u-eq 
        ... | w , w∈p = recons* {p} {r} (p→r u) (w∈p , cong (λ x → p→r x ) unflat-w∈p≡u)
          where
            unflat-w∈p≡u : unflat w∈p ≡ u
            unflat-w∈p≡u =
              begin
                unflat w∈p
              ≡⟨ cong (λ x → unflat (proj₂ x)) (sym flat-u-eq)  ⟩
                unflat (proj₂ (flat u))
              ≡⟨ unflat∘proj₂∘flat ⟩
                u 
              ∎
        rec*₂ : Recons* (p₂→r v) (pdinstance* p₂→r s-ev-p₂-r)
        rec*₂ with flat v in flat-v-eq 
        ... | w , w∈p₂ = recons* {p₂} {r} (p₂→r v) (w∈p₂ , cong (λ x → p₂→r x ) unflat-w∈p₂≡v)
          where
            unflat-w∈p₂≡v : unflat w∈p₂ ≡ v
            unflat-w∈p₂≡v =
              begin
                unflat w∈p₂
              ≡⟨ cong (λ x → unflat (proj₂ x)) (sym flat-v-eq)  ⟩
                unflat (proj₂ (flat v))
              ≡⟨ unflat∘proj₂∘flat ⟩
                v 
              ∎              
              
  
concatMap-buildU-sorted : ∀ { r : RE } { w : List Char }
  → ( pdis : List (PDInstance* r w) )
  → Ex*>-sorted pdis
  → All *>-Inc pdis
  → >-sorted {r} (concatMap buildU pdis)
concatMap-buildU-sorted {r} {w} [] ex*>-nil [] = >-nil
concatMap-buildU-sorted {r} {w} (pdi@(pdinstance* {p} {r} inj s-ev) ∷ []) (ex*>-cons ex*>-nil ex*>-nothing) ((*>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) ∷ []) with ε∈? p
... | no _ = >-nil
... | yes ε∈p rewrite (++-identityʳ (List.map inj (mkAllEmptyU ε∈p))) =  map-inj-sorted (mkAllEmptyU ε∈p) inj u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ (mkAllEmptyU-sorted ε∈p)  
concatMap-buildU-sorted {r} {w} (pdi₁@(pdinstance* {p₁} {r} p₁→r s-ev₁ ) ∷ ( pdi₂@(pdinstance* {p₂} {r} p₂→r s-ev₂ ) ∷ pdis ) ) (ex*>-cons pdi₂pdis-sorted (ex*>-just pdi₁>pdi₂)) 
  (inc₁@(*>-inc u₁→u₂→u₁>u₂→p₁→r-u₁>p₁→r-u₂) ∷ ( inc₂@(*>-inc u₁→u₂→u₁>u₂→p₂→r-u₁>p₂→r-u₂) ∷ *>-inc-pdis ) ) with ε∈? p₁
... | no _  = concatMap-buildU-sorted {r} {w} (pdi₂ ∷ pdis)  pdi₂pdis-sorted (inc₂ ∷ *>-inc-pdis)
... | yes ε∈p₁ = concat-sorted ( List.map p₁→r (mkAllEmptyU ε∈p₁))  (concatMap buildU (pdi₂ ∷ pdis)) us₁-sorted ind-hyp map-p₁→r-mkAllEmptyU-ε∈p₁-all>head-concatMap-buildU-pdi₂pdis  
  where
    ind-hyp : >-sorted {r} (concatMap buildU (pdi₂ ∷ pdis))
    ind-hyp = concatMap-buildU-sorted {r} {w} (pdi₂ ∷ pdis)  pdi₂pdis-sorted (inc₂ ∷ *>-inc-pdis)

    us₁-sorted : >-sorted ( List.map p₁→r (mkAllEmptyU ε∈p₁) )
    us₁-sorted =  map-inj-sorted (mkAllEmptyU ε∈p₁) p₁→r  u₁→u₂→u₁>u₂→p₁→r-u₁>p₁→r-u₂ (mkAllEmptyU-sorted ε∈p₁)

    map-p₁→r-mkAllEmptyU-ε∈p₁-all>head-concatMap-buildU-pdi₂pdis : All (λ u₁ → >-maybe u₁ (head (concatMap buildU (pdinstance* p₂→r s-ev₂ ∷ pdis))))
                                                                                          (List.map p₁→r (mkAllEmptyU ε∈p₁))
    map-p₁→r-mkAllEmptyU-ε∈p₁-all>head-concatMap-buildU-pdi₂pdis = buildU-all>head-concatmap-buildU p₁→r s-ev₁ (pdi₂ ∷ pdis) pdi₂pdis-sorted  (ex*>-just pdi₁>pdi₂) 
-}
```
 
#### Main proof for Theorem 42 
```agda
{-
parseAll-is-lne-sorted : ∀ { r : RE } { w : List Char }
  →  >-sorted {r} (parseAll[ r , w ])
parseAll-is-lne-sorted {r} {w} = concatMap-buildU-sorted pdUMany[ r , w ] pdUMany-sorted  pdUMany-*>-inc
-}
```

