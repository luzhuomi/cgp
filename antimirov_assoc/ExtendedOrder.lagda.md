```agda
{-# OPTIONS --rewriting #-}
module cgp.antimirov_assoc.ExtendedOrder where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ;
  ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ; ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ;
  first ; ε∉r→¬first-r≡[] )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ∷-inj ; ¬∷≡[] ; inv-map-[] ; inv-concatMap-map-f-[] ) 


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )


import cgp.ParseTree as ParseTree
open ParseTree using (
  U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ;
  flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;
  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; unListU ; listU∘unListU ;
  u-of-r*-islist ; pair-≡ ; left-≡ ; right-≡ ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU)

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ; mkAllEmptyU≢[] ; all-flat-[]-left ; all-flat-[]-right )


import cgp.antimirov_assoc.PartialDerivative as PartialDerivative
open PartialDerivative using (
  pdU[_,_] ; PDInstance ; pdinstance ;
  pdinstance-left ; pdinstance-right; pdinstance-fst ;
  mkinjFst ;  pdinstance-snd ; concatmap-pdinstance-snd ;
  zip-es-flat-[]-es ; mk-snd-pdi ; mkinjSnd ;
  pdinstance-star ; mkinjList ; flat-Uε≡[];
  pdUMany[_,_]; pdUMany-aux;  PDInstance* ; pdinstance* ;
  advance-pdi*-with-c ; compose-pdi-with ; 
  Recons ; recons ;
  Recons* ; recons* ;
  parseAll[_,_] ; buildU ;
  inv-recons-left ;   inv-recons-right ; inv-recons-fst ; inv-recons-snd ; inv-recons-star ;
  inv-recons*-compose-pdi-with ; 
  ¬recons-right-from-pdinstance-left ; ¬recons-left-from-pdinstance-right ; ¬recons-[]-from-pdinstance-star ;
  pdi*-∃  ;
  recons-v→¬proj₁flat-v≡[] ) 


import cgp.antimirov_assoc.Order as AntimirovOrder
open AntimirovOrder using ( _⊢_>_ ; seq₁ ; seq₂ ;
  choice-ll-bothempty ; choice-ll-notempty; choice-ll-empty ;
  choice-rr-bothempty ; choice-rr-notempty; choice-rr-empty ;
  choice-lr-bothempty ; choice-lr-notempty ; choice-lr-empty ;
  choice-rl-empty ; star-head ; star-cons-nil ;
  >-sorted ; >-nil ; >-cons ; concat-sorted ; 
  mkAllEmptyU-sorted ;
  >-maybe ; >-nothing ; >-just ; 
  >-trans ; *>-Inc ; *>-inc ;
  concatmap-advance-pdi*-with-c-*>inc ;
  pdUMany-*>-inc )   


import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_  )

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


### Definition 36 : (Extended) greedy ordering among PDInstances 

Let r be a non problematic regular expression.

Let c be a letter.

Let pdi₁ and pdi₂ be two partial derivative instances of r w.r.t c.

We say pdi₁ is greedier than pdi₂, r , c  ⊢ pdi₁ > pdi₂ iff
  for all parse trees u₁ u₂  of r, u₁ is constructable from pdi₁ and u₂ is constructabled from pdi₂ 
    then r ⊢ u₁ > u₂ 


```agda

data _,_⊢_>_ : ∀ ( r : RE ) → (c : Char ) → PDInstance r c → PDInstance r c → Set where
  >-pdi : ∀ { r : RE } { c : Char }
    → ( pdi₁ : PDInstance r c )
    → ( pdi₂ : PDInstance r c )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r ) → (Recons u₁ pdi₁ ) → (Recons u₂ pdi₂) → ( r ⊢ u₁ > u₂) )
    → r , c ⊢ pdi₁ > pdi₂


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


### Definition 37 : (Extended) greedy order sortedness

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
```



### Lemma 38: the list of pdinstances from pdU[ r , c] is extended greedily sorted. 


Let r be a non problematic regular expression.

Let c be a letter.

Then pdU[r , c] is extended greedily sorted. 



#### Sub Lemma 38.1 - 38.25 : Ex>-sortedness is preserved inductively over pdinstance operations.

```agda
-------------------------------------------------------------
-- Sub Lemma 38.1 - 38.25 BEGIN
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
             choice-ll-notempty  ¬proj₁flat-v₁≡[]  ¬proj₁flat-v₂≡[]  (pdi₁>-pdi₂-ev v₁ v₂  recons-v₁-pdi₁ recons-v₂-pdi₂)
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
       choice-rr-notempty ¬proj₁flat-v₁≡[] ¬proj₁flat-v₂≡[]  (pdi₁>-pdi₂-ev v₁ v₂  recons-v₁-pdi₁ recons-v₂-pdi₂)
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
                in choice-lr-notempty ¬proj₁flat-v₁≡[] ¬proj₁flat-v₂≡[] 
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
         in choice-ll-notempty ¬proj₁flat-v₁≡[] ¬proj₁flat-v₂≡[]  ( pdi₁>pdi₂-ev v₁ v₂ recons-v₁-pdi₁ recons-v₂-pdi₂ )
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
      in star-head (pdi₁>-pdi₂-ev v₁ v₂ recons-v₁-pdi₁ recons-v₂-pdi₂)

  

map-star-ex-sorted : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
                     → ( pdis : List (PDInstance r c) )
                     → Ex>-sorted {r} pdis
                     → Ex>-sorted {r * ε∉r ` loc } (List.map pdinstance-star pdis)
map-star-ex-sorted {r} {ε∉r} {loc} {c} [] ex>-nil = ex>-nil
map-star-ex-sorted {r} {ε∉r} {loc} {c} (pdi ∷ [])  (ex>-cons ex>-nil ex>-nothing) = ex>-cons ex>-nil ex>-nothing
map-star-ex-sorted {r} {ε∉r} {loc} {c} (pdi₁ ∷ pdi₂ ∷ pdis)  (ex>-cons ex>-sorted-pdi2pdis (ex>-just pdi1>pdi2))
  = ex>-cons (map-star-ex-sorted (pdi₂ ∷ pdis) ex>-sorted-pdi2pdis)
             (ex>-just (star-ex-sorted pdi₁ pdi₂ pdi1>pdi2))






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
    ev (PairU u₁ v₁) (PairU u₂ v₂)  recons-pair-u₁v₁-pdi-fst recons-pair-u₁v₂-pdi-fst =
       let recons-u₁-pdi₁ = inv-recons-fst {l} {r} {loc} u₁ v₁ pdi₁  recons-pair-u₁v₁-pdi-fst 
           recons-u₂-pdi₂ = inv-recons-fst {l} {r} {loc} u₂ v₂ pdi₂  recons-pair-u₁v₂-pdi-fst
       in seq₁ (pdi₁>-pdi₂-ev u₁ u₂  recons-u₁-pdi₁ recons-u₂-pdi₂) 




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
          =  seq₂ v₁≡v₂ v₁'>v₂' 
          where
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
          ev-> v₁ v₁' v₂ v₂' recons1 recons2 = seq₁ v₁>v₂
            where
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

---------------------------------------------------------------------------------------------------
-- map-pdinstance-assoc-ex>-sorted and its sub lemma 
---------------------------------------------------------------------------------------------------
{- 
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


---------------------------------------------------------------------------------------------------
-- map-pdinstance-assoc-ex>-sorted and its sub lemma 
---------------------------------------------------------------------------------------------------

inv-dist-> : ∀ { l s r : RE } {loc₁ loc₂ : ℕ }
             → { u₁ : U (( l ● r ` loc₂) + ( s ● r ` loc₂ ) ` loc₁)  }
             → { u₂ : U (( l ● r ` loc₂) + ( s ● r ` loc₂ ) ` loc₁)  }
             → (( l ● r ` loc₂) + ( s ● r ` loc₂ ) ` loc₁ ) ⊢ u₁ > u₂
             -------------------------------------------------------------          
             → (( l + s ` loc₁) ● r ` loc₂)  ⊢ inv-dist u₁ > inv-dist u₂ 
inv-dist-> {l} {s} {r} {loc₁} {loc₂} {LeftU (PairU v₁ v₁')} {LeftU (PairU v₂ v₂')} (choice-ll (seq₁ v₁>v₂)) = seq₁ (choice-ll v₁>v₂)
inv-dist-> {l} {s} {r} {loc₁} {loc₂} {LeftU (PairU v₁ v₁')} {LeftU (PairU v₂ v₂')} (choice-ll (seq₂ v₁≡v₂ v₁'>v₂')) = seq₂ (left-≡ v₁≡v₂) v₁'>v₂'
inv-dist-> {l} {s} {r} {loc₁} {loc₂} {RightU (PairU v₁ v₁')} {RightU (PairU v₂ v₂')} (choice-rr (seq₁ v₁>v₂)) = seq₁ (choice-rr v₁>v₂)
inv-dist-> {l} {s} {r} {loc₁} {loc₂} {RightU (PairU v₁ v₁')} {RightU (PairU v₂ v₂')} (choice-rr (seq₂ v₁≡v₂ v₁'>v₂')) = seq₂ (right-≡ v₁≡v₂) v₁'>v₂'
inv-dist-> {l} {s} {r} {loc₁} {loc₂} {LeftU (PairU v₁ v₁')} {RightU (PairU v₂ v₂')} choice-lr = seq₁ choice-lr
-- the RightU vs LeftU case is not required, it leads to λ() automatically


inv-dist-right-> : ∀ { l s r : RE } {loc₁ loc₂ : ℕ }  { v₁ v₁' : U s } { v₂ v₂' : U r } 
   → (s ● r ` loc₂) ⊢ PairU v₁ v₂ > PairU v₁' v₂'
   -----------------------------------------------------------------------------
   → ((l + s ` loc₁) ● r ` loc₂) ⊢ PairU (RightU v₁) v₂ > PairU (RightU v₁') v₂'
inv-dist-right->  {l} {s} {r} {loc₁} {loc₂} {v₁} {v₁'} {v₂} {v₂'} (seq₁ v₁>v₁') = seq₁ (choice-rr v₁>v₁')
inv-dist-right->  {l} {s} {r} {loc₁} {loc₂} {v₁} {v₁'} {v₂} {v₂'} (seq₂ v₁≡v₁' v₂>v₂') = seq₂ (right-≡ v₁≡v₁')  v₂>v₂'


dist-left-right-ex>-maybe : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
  → ( pdi : ( PDInstance ( l ● r ` loc₂ ) c ))
  → ( pdis : ( List (PDInstance ( s ● r ` loc₂ ) c ) ))
  -----------------------------------------------------------------------------------------------------------------------
  → Ex>-maybe (pdinstance-dist {l} {s} {r} {loc₁} {loc₂} {c} (pdinstance-left pdi))  (head (List.map pdinstance-dist (List.map pdinstance-right pdis)))
dist-left-right-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi [] = ex>-nothing
dist-left-right-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdiˡ (pdiʳ ∷ pdisʳ)  = ex>-just (>-pdi (pdinstance-dist (pdinstance-left pdiˡ)) (pdinstance-dist (pdinstance-right pdiʳ)) ev->)
  where
    ev-> : (u₁ u₂ : U ((l + s ` loc₁) ● r ` loc₂))
         → Recons u₁ (pdinstance-dist (pdinstance-left pdiˡ))
         → Recons u₂ (pdinstance-dist (pdinstance-right pdiʳ))
         → ((l + s ` loc₁) ● r ` loc₂) ⊢ u₁ > u₂
    ev-> (PairU (LeftU v₁) v₂) (PairU (RightU v₁') v₂') recons₁ recons₂ = seq₁ choice-lr
    ev-> (PairU (RightU v₁) v₂) _ recons₁ _ =  Nullary.contradiction recons₁ (¬recons-pair-right-from-pdinstance-dist-left  v₁ v₂ pdiˡ)
    ev-> _ (PairU (LeftU v₁') v₂') _ recons₂  =  Nullary.contradiction recons₂ (¬recons-pair-left-from-pdinstance-dist-right  v₁' v₂' pdiʳ)      
    

dist-right-ex>-maybe : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
  → ( pdi : ( PDInstance ( s ● r ` loc₂ ) c ))
  → ( pdis : ( List (PDInstance ( s ● r ` loc₂ ) c ) ))
  → Ex>-maybe (pdinstance-right { l ● r ` loc₂} { s ● r ` loc₂} {loc₁} {c}  pdi) (head (List.map pdinstance-right pdis))
  --------------------------------------------------
  → Ex>-maybe (pdinstance-dist  {l} {s} {r} {loc₁} {loc₂} {c} (pdinstance-right pdi))
    (head (List.map pdinstance-dist (List.map pdinstance-right pdis)))
dist-right-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi [] ex>-nothing = ex>-nothing
dist-right-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi₁ (pdi₂ ∷ pdis) (ex>-just (>-pdi _ _ u₁→u₂→r₁→r₂→u₁>u₂)) = ex>-just (>-pdi (pdinstance-dist (pdinstance-right pdi₁)) (pdinstance-dist (pdinstance-right pdi₂)) ev->)
  where
    ev-> : (u₁ u₂ : U ((l + s ` loc₁) ● r ` loc₂))
         → Recons u₁ (pdinstance-dist (pdinstance-right pdi₁))
         → Recons u₂ (pdinstance-dist (pdinstance-right pdi₂))
         → ((l + s ` loc₁) ● r ` loc₂) ⊢ u₁ > u₂
    ev-> (PairU (RightU v₁) v₂) (PairU (RightU v₁') v₂') recons₁ recons₂ = inv-dist-right->  pair-v₁-v₂>pair-v₁'-v₂'
      where
        right-pair-v₁-v₂>right-pair-v₁'-v₂' :  ((l ● r ` loc₂) + s ● r ` loc₂ ` loc₁) ⊢ RightU (PairU v₁ v₂) > RightU (PairU v₁' v₂')
        right-pair-v₁-v₂>right-pair-v₁'-v₂' =  
                                u₁→u₂→r₁→r₂→u₁>u₂ (RightU (PairU v₁ v₂)) (RightU (PairU v₁' v₂')) (inv-recons-dist-right v₁ v₂ pdi₁ recons₁) (inv-recons-dist-right v₁' v₂' pdi₂ recons₂)
        pair-v₁-v₂>pair-v₁'-v₂' :  s ● r ` loc₂ ⊢ PairU v₁ v₂ > PairU v₁' v₂'
        pair-v₁-v₂>pair-v₁'-v₂' with right-pair-v₁-v₂>right-pair-v₁'-v₂'
        ...                       | choice-rr ev = ev 
    ev-> (PairU (LeftU v₁) v₂) _ recons₁ _    =  Nullary.contradiction recons₁ (¬recons-pair-left-from-pdinstance-dist-right  v₁ v₂ pdi₁)      
    ev-> _ (PairU (LeftU v₁') v₂') _ recons₂  =  Nullary.contradiction recons₂ (¬recons-pair-left-from-pdinstance-dist-right  v₁' v₂' pdi₂)      
  


map-dist-right-ex>-sorted : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
                            → ( pdis : List (PDInstance ( s ● r ` loc₂ ) c ) )
                            → Ex>-sorted {( l ● r ` loc₂) + ( s ● r ` loc₂) ` loc₁ } (List.map pdinstance-right pdis)
                            ---------------------------------------------------------------
                            → Ex>-sorted { (l + s ` loc₁) ● r ` loc₂} (List.map pdinstance-dist (List.map pdinstance-right pdis))
map-dist-right-ex>-sorted   {l} {s} {r} {loc₁} {loc₂} {c} []     ex>-nil = ex>-nil
map-dist-right-ex>-sorted   {l} {s} {r} {loc₁} {loc₂} {c} (pdi ∷ pdis) (ex>-cons pdis-ex>-sorted pdi>head-pdis) = ex>-cons (map-dist-right-ex>-sorted pdis pdis-ex>-sorted) (dist-right-ex>-maybe pdi pdis pdi>head-pdis) 



map-dist-left++right-ex>-sorted : ∀ {l s r : RE } { loc₁ loc₂ : ℕ } { c : Char }
                         → ( pdisˡ : (List (PDInstance  (l ● r ` loc₂) c) )) 
                         → Ex>-sorted {( l ● r ` loc₂) + ( s ● r ` loc₂) ` loc₁ } (List.map pdinstance-left pdisˡ)
                         → ( pdisʳ : (List (PDInstance  (s ● r ` loc₂) c) )) 
                         → Ex>-sorted {( l ● r ` loc₂) + ( s ● r ` loc₂) ` loc₁ } (List.map pdinstance-right pdisʳ)                         
                         ---------------------------------------------------------------
                         → Ex>-sorted { (l + s ` loc₁) ● r ` loc₂} (List.map pdinstance-dist ((List.map pdinstance-left pdisˡ) ++ (List.map pdinstance-right pdisʳ ) ))
map-dist-left++right-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} [] ex>-nil pdisʳ map-right-pdisʳ-ex>-sorted rewrite cong (λ x →  Ex>-sorted (List.map (pdinstance-dist {l} {s} {r} {loc₁} {loc₂} {c}) x)) (++-identityˡ (List.map pdinstance-right pdisʳ))  =
  map-dist-right-ex>-sorted pdisʳ map-right-pdisʳ-ex>-sorted
map-dist-left++right-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} (pdiˡ ∷ []) (ex>-cons ex->nil ex->-nothing) pdisʳ map-right-pdisʳ-ex>-sorted =
  ex>-cons (map-dist-left++right-ex>-sorted [] ex->nil pdisʳ map-right-pdisʳ-ex>-sorted)
    (dist-left-right-ex>-maybe pdiˡ pdisʳ) 
             
map-dist-left++right-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} (pdiˡ ∷ (pdiˡ' ∷ pdisˡ)  ) (ex>-cons pdiˡ'pdis-ex->sorted (ex>-just (>-pdi _ _  u₁→u₂→r₁→r₂→u₁>u₂ )))  pdisʳ map-right-pdisʳ-ex>-sorted =
  ex>-cons (map-dist-left++right-ex>-sorted (pdiˡ' ∷ pdisˡ) pdiˡ'pdis-ex->sorted pdisʳ map-right-pdisʳ-ex>-sorted)
    (ex>-just (>-pdi (pdinstance-dist (pdinstance-left pdiˡ))
                     (pdinstance-dist (pdinstance-left pdiˡ')) ev-> ))
    where
      ev->  : (u₁ u₂ : U ((l + s ` loc₁) ● r ` loc₂))
            → Recons u₁ (pdinstance-dist (pdinstance-left pdiˡ))
            → Recons u₂ (pdinstance-dist (pdinstance-left pdiˡ'))
            -------------------------------------------------
            → ((l + s ` loc₁) ● r ` loc₂) ⊢ u₁ > u₂
      ev-> (PairU (LeftU v₁) v₃) (PairU (LeftU v₁') v₃') recons₁ recons₂ =
        inv-dist-> {l} {s} {r} {loc₁} {loc₂} {LeftU (PairU v₁ v₃)} {LeftU (PairU v₁' v₃')}
          (u₁→u₂→r₁→r₂→u₁>u₂ (LeftU (PairU v₁ v₃)) (LeftU (PairU v₁' v₃')) (inv-recons-dist-left v₁ v₃ pdiˡ recons₁) (inv-recons-dist-left v₁' v₃' pdiˡ' recons₂) )
      ev-> (PairU (RightU v₂) v₃) _ recons₁ _   = Nullary.contradiction recons₁ (¬recons-pair-right-from-pdinstance-dist-left v₂ v₃ pdiˡ)   -- need to create a contradiction
      ev-> _ (PairU (RightU v₂') v₃') _ recons₂ = Nullary.contradiction recons₂ (¬recons-pair-right-from-pdinstance-dist-left v₂' v₃' pdiˡ')   -- need to create a contradiction

---------------------------------------------------------------------------------------------------
-- map-pdinstance-dist-ex>-sorted and its sub lemma END 

-}


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
-- Sub Lemma 38.1 - 38.25 END 
-------------------------------------------------------------

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

postulate
  ¬zip-es-flat-[]-es≡[] : ∀ { l  : RE } {ε∈l : ε∈ l }
    → ¬ ( zip-es-flat-[]-es {l} {ε∈l} (mkAllEmptyU ε∈l) (mkAllEmptyU-sound ε∈l) )≡ []


-- parse tree can be flattened to [] implies RE is nullable. 
proj₁flat-v≡[]→ε∈r : ∀ { r : RE } { v : U r }
    → (proj₁ (flat v)) ≡ []
    -------------------------
    → ε∈ r
proj₁flat-v≡[]→ε∈r {ε} {EmptyU} proj₁flat-v≡[] = ε∈ε 
proj₁flat-v≡[]→ε∈r {$ c ` loc } {LetterU _} = λ()
proj₁flat-v≡[]→ε∈r {r * ε∉r ` loc } {ListU _} proj₁flat-v≡[] = ε∈* 
proj₁flat-v≡[]→ε∈r {l + r  ` loc } {LeftU v} proj₁flat-v≡[] with ε∈? r
... | yes ε∈r = ε∈ ε∈l + ε∈r 
  where
    ε∈l : ε∈ l 
    ε∈l = proj₁flat-v≡[]→ε∈r {l} {v} proj₁flat-v≡[]
... | no ¬ε∈r = ε∈ ε∈l <+ (¬ε∈r→ε∉r ¬ε∈r)
  where
    ε∈l : ε∈ l 
    ε∈l = proj₁flat-v≡[]→ε∈r {l} {v} proj₁flat-v≡[]
proj₁flat-v≡[]→ε∈r {l + r  ` loc } {RightU v} proj₁flat-v≡[] with ε∈? l
... | yes ε∈l = ε∈ ε∈l + ε∈r 
  where
    ε∈r : ε∈ r 
    ε∈r = proj₁flat-v≡[]→ε∈r {r} {v} proj₁flat-v≡[]
... | no ¬ε∈l = ε∈ (¬ε∈r→ε∉r ¬ε∈l) +> ε∈r 
  where
    ε∈r : ε∈ r 
    ε∈r = proj₁flat-v≡[]→ε∈r {r} {v} proj₁flat-v≡[]
proj₁flat-v≡[]→ε∈r {l ● r  ` loc } {PairU v u} proj₁flat-pair-v-u≡[] = ε∈ ε∈l ● ε∈r
  where
    ε∈l : ε∈ l
    ε∈l = proj₁flat-v≡[]→ε∈r {l} {v} (++-conicalˡ (proj₁ (flat v)) (proj₁ (flat u)) proj₁flat-pair-v-u≡[])
    ε∈r : ε∈ r
    ε∈r = proj₁flat-v≡[]→ε∈r {r} {u} (++-conicalʳ (proj₁ (flat v)) (proj₁ (flat u)) proj₁flat-pair-v-u≡[])
    
{-
|∷|>|[]| : ∀ { r : RE } { ε∈r : ε∈ r } { c : Char } { cs : List Char } 
    → ( u v : U r )
    → ( proj₁ (flat u) ≡ c ∷ cs )
    → ( proj₁ (flat v) ≡ [] )
    ------------------------------
    → r ⊢ u > v 
|∷|>|[]| {ε} {ε∈ε} {c} {cs} EmptyU EmptyU = λ()
|∷|>|[]| {r * ε∉r ` loc } {ε∈*} {c} {cs} (ListU (u ∷ us)) (ListU []) proj₁flat-list-u∷us≡c∷cs proj₁flat-list-[]≡[] = star-cons-nil 
|∷|>|[]| {r * ε∉r ` loc } {ε∈*} {c} {cs} (ListU (u ∷ us)) (ListU (v ∷ vs)) proj₁flat-list-u∷us≡c∷cs proj₁flat-list-v-vs≡[] = Nullary.contradiction proj₁flat-list-v-vs≡[] ¬proj₁-flat-list-v-vs≡[] 
  where
    bar : proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ vs))) ≡ proj₁ (flat v) ++ proj₁ (flat (ListU {r} {ε∉r} {loc} vs))
    bar =
      begin
        proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ vs)))
      ≡⟨⟩
        proj₁ (flat v) ++ proj₁ (flat (ListU {r} {ε∉r} {loc} vs))
      ∎ 
    ¬proj₁-flat-list-v-vs≡[] : ¬ (proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ vs))) ≡ [] )
    ¬proj₁-flat-list-v-vs≡[] proj₁-flat-list-v-vs≡[] rewrite bar = (ε∉r→¬ε∈r ε∉r) ( proj₁flat-v≡[]→ε∈r proj₁-flat-v≡[]) 
      where
        proj₁-flat-v≡[] : proj₁ (flat v) ≡ []
        proj₁-flat-v≡[] = ++-conicalˡ ( proj₁ (flat v)) ( proj₁ (flat (ListU {r} {ε∉r} {loc} vs)))  proj₁-flat-list-v-vs≡[]
|∷|>|[]| {l + r ` loc } {ε∈ ε∈l + ε∈r } {c} {cs} (LeftU u) (LeftU v) proj₁flat-left-u≡c∷cs   proj₁flat-left-v≡[] = choice-ll-empty ¬proj₁flat-u≡[]  proj₁flat-left-v≡[] 
  where
    ¬proj₁flat-u≡[] : ¬ (proj₁ (flat u) ≡ [])
    ¬proj₁flat-u≡[] rewrite proj₁flat-left-u≡c∷cs = λ proj₁flat-u≡[] → ¬∷≡[] proj₁flat-u≡[] 
|∷|>|[]| {l + r ` loc } {ε∈ ε∈l + ε∈r } {c} {cs} (LeftU u) (RightU v) proj₁flat-left-u≡c∷cs   proj₁flat-right-v≡[] = choice-lr-empty ¬proj₁flat-u≡[]  proj₁flat-right-v≡[] 
  where
    ¬proj₁flat-u≡[] : ¬ (proj₁ (flat u) ≡ [])
    ¬proj₁flat-u≡[] rewrite proj₁flat-left-u≡c∷cs = λ proj₁flat-u≡[] → ¬∷≡[] proj₁flat-u≡[] 
|∷|>|[]| {l + r ` loc } {ε∈ ε∈l + ε∈r } {c} {cs} (RightU u) (RightU v) proj₁flat-right-u≡c∷cs   proj₁flat-right-v≡[] = choice-rr-empty ¬proj₁flat-u≡[]  proj₁flat-right-v≡[] 
  where
    ¬proj₁flat-u≡[] : ¬ (proj₁ (flat u) ≡ [])
    ¬proj₁flat-u≡[] rewrite proj₁flat-right-u≡c∷cs = λ proj₁flat-u≡[] → ¬∷≡[] proj₁flat-u≡[] 
|∷|>|[]| {l + r ` loc } {ε∈ ε∈l + ε∈r } {c} {cs} (RightU u) (LeftU v) proj₁flat-right-u≡c∷cs   proj₁flat-left-v≡[] = choice-rl-empty ¬proj₁flat-u≡[]  proj₁flat-left-v≡[] 
  where
    ¬proj₁flat-u≡[] : ¬ (proj₁ (flat u) ≡ [])
    ¬proj₁flat-u≡[] rewrite proj₁flat-right-u≡c∷cs = λ proj₁flat-u≡[] → ¬∷≡[] proj₁flat-u≡[]
|∷|>|[]| {l + r ` loc } {ε∈ ε∈l <+ ε∉r } {c} {cs} (RightU u) (LeftU v) proj₁flat-right-u≡c∷cs   proj₁flat-left-v≡[] = choice-rl-empty ¬proj₁flat-u≡[]  proj₁flat-left-v≡[] 
  where
    ¬proj₁flat-u≡[] : ¬ (proj₁ (flat u) ≡ [])
    ¬proj₁flat-u≡[] rewrite proj₁flat-right-u≡c∷cs = λ proj₁flat-u≡[] → ¬∷≡[] proj₁flat-u≡[]
|∷|>|[]| {l + r ` loc } {ε∈ ε∈l <+ ε∉r } {c} {cs} (LeftU u) (LeftU v) proj₁flat-left-u≡c∷cs   proj₁flat-left-v≡[] = choice-ll-empty ¬proj₁flat-u≡[]  proj₁flat-left-v≡[] 
  where
    ¬proj₁flat-u≡[] : ¬ (proj₁ (flat u) ≡ [])
    ¬proj₁flat-u≡[] rewrite proj₁flat-left-u≡c∷cs = λ proj₁flat-u≡[] → ¬∷≡[] proj₁flat-u≡[]
|∷|>|[]| {l + r ` loc } {ε∈ ε∈l <+ ε∉r } {c} {cs} u (RightU v) proj₁flat-u≡c∷cs   proj₁flat-right-v≡[] = Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-right-v≡[]) (ε∉r→¬ε∈r ε∉r) 

|∷|>|[]| {l + r ` loc } {ε∈ ε∉l +> ε∈r } {c} {cs} (LeftU u) (RightU v) proj₁flat-left-u≡c∷cs   proj₁flat-right-v≡[] = choice-lr-empty ¬proj₁flat-u≡[]  proj₁flat-right-v≡[] 
  where
    ¬proj₁flat-u≡[] : ¬ (proj₁ (flat u) ≡ [])
    ¬proj₁flat-u≡[] rewrite proj₁flat-left-u≡c∷cs = λ proj₁flat-u≡[] → ¬∷≡[] proj₁flat-u≡[] 
|∷|>|[]| {l + r ` loc } {ε∈ ε∉l +> ε∈r } {c} {cs} (RightU u) (RightU v) proj₁flat-right-u≡c∷cs   proj₁flat-right-v≡[] = choice-rr-empty ¬proj₁flat-u≡[]  proj₁flat-right-v≡[] 
  where
    ¬proj₁flat-u≡[] : ¬ (proj₁ (flat u) ≡ [])
    ¬proj₁flat-u≡[] rewrite proj₁flat-right-u≡c∷cs = λ proj₁flat-u≡[] → ¬∷≡[] proj₁flat-u≡[] 
|∷|>|[]| {l + r ` loc } {ε∈ ε∉l +> ε∈r } {c} {cs} u (LeftU v) proj₁flat-u≡c∷cs   proj₁flat-left-v≡[] = Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-left-v≡[]) (ε∉r→¬ε∈r ε∉l) 
|∷|>|[]| {l ● r ` loc } {ε∈ ε∈l ● ε∈r } {c} {cs} (PairU u₁ u₂) (PairU v₁ v₂) proj₁flat-pair-u₁u₂≡c∷cs proj₁flat-pair-v₁v₂≡[] = {!!}
  -- how to guarantee either u₁ > v₁ or u₁ ≡ v₁ ? 
  -- can't guarantee. here is the counter example 
  -- u = PairU (RightU EmptyU) (ListU (LetterU a) ∷ [])
  -- v = PairU (LeftU EmptyU)  (ListU [] )
  -- u < v!!!
  -- is it because we need assoc rule for ( r ● s ) ● t ---> r ● (s ● t) ?
-}

all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd : ∀ { l r : RE } {loc : ℕ } { ε∈l : ε∈ l } { c : Char }
      →  (pdis : List (PDInstance l c ))
      →  (pdis' : List (PDInstance r c))
      →  ( pdis ≡  pdU[ l , c ] )   -- added this to create a contradiction for the ε case. 
      →  ( pdis' ≡ pdU[ r , c ] )
      →  All (λ pdi → Ex>-maybe { l ● r ` loc } pdi (head (concatmap-pdinstance-snd  {l} {r} {ε∈l} {loc} {c} pdis')))
             (List.map (pdinstance-fst {l} {r} {loc} {c}) pdis )
all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd [] _ _ _ = []
all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd {l} {r} {loc} {ε∈l} {c}  (pdi ∷ pdis) [] _ _  rewrite ( concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c} )  = prf (pdi ∷ pdis)
  where
    prf : (pdis' : List (PDInstance l c))
          → All (λ pdi₁ → Ex>-maybe pdi₁ nothing)  (List.map ( pdinstance-fst  {l} {r} {loc} {c} ) pdis' )
    prf [] = []
    prf (pdi' ∷ pdis') = ex>-nothing ∷ prf pdis' 


all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd {ε} {r} {loc} {ε∈ε} {c}  (pdiˡ ∷ pdisˡ) (pdiʳ ∷ pdisʳ) pdiˡ∷pdisˡ≡[] _  =  Nullary.contradiction pdiˡ∷pdisˡ≡[] Utils.¬∷≡[] -- how to create a contradiction? 

all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd {s ● t ` loc' } {r} {loc} {ε∈ ε∈s ● ε∈t} {c}  (pdiˡ@(pdinstance inj s-ev) ∷ pdisˡ) (pdiʳ ∷ pdisʳ) _  _  = {!!}  -- it seems that this case can't be proven. we need to get rid of it using assoc? we should find the counter example which satisfies the < order but not produceable by the current pdU

all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd {s * ε∉s ` loc' } {r} {loc} {ε∈*} {c} (pdiˡ ∷ pdisˡ) (pdiʳ ∷ pdisʳ) _ _  =  ind (pdiˡ ∷ pdisˡ)
  where
    ind : ( pdis : List (PDInstance (s * ε∉s ` loc') c ) )
      → All (λ pdi → Ex>-maybe pdi (just (mk-snd-pdi {s * ε∉s ` loc'} {r} {loc} {c}  (ListU [] , flat-[] (ListU []) refl) pdiʳ)))
           (List.map pdinstance-fst pdis)
    ind [] = []
    ind (pdi ∷ pdis) = (ex>-just (>-pdi (pdinstance-fst pdi) (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl) pdiʳ) λ { ( PairU v₁ v₁') (PairU v₂ v₂') r₁ r₂  → ev->  v₁ v₁' v₂ v₂' r₁ r₂  } )) ∷ ind pdis
      where
      ev-> : (v₁ : U (s * ε∉s ` loc') )
           → (v₁' : U r )
           → (v₂ : U (s * ε∉s ` loc') )
           → (v₂' : U r )
           → Recons {(s * ε∉s ` loc') ● r ` loc} {c} (PairU v₁ v₁')  ( pdinstance-fst {(s * ε∉s ` loc')} {r} {loc} {c} pdi )
           → Recons {(s * ε∉s ` loc') ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi {(s * ε∉s ` loc')} {r} {loc} {c}  (ListU [] ,  flat-[] (ListU []) refl) pdiʳ )
           --------------------------------------------------
           → ((s * ε∉s ` loc') ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂'
      ev-> v₁ v₁' v₂ v₂' recons1 recons2  = seq₁ v₁>v₂
        where 
          v₂≡list-[] : v₂ ≡ (ListU [])
          v₂≡list-[] = mk-snd-pdi-fst-pair-≡ pdiʳ (ListU []) (flat-[] (ListU []) refl)  v₂ v₂' recons2
          v₁-is-cons : ∃[ x ] ∃[ xs ] (v₁ ≡ ListU (x ∷ xs))
          v₁-is-cons = pdinstance-fst-pair-l*-is-cons pdi v₁ v₁' recons1
          x  = proj₁ v₁-is-cons
          xs = proj₁ (proj₂ v₁-is-cons)
          v₁≡list-x-xs = proj₂ (proj₂ v₁-is-cons)
          list-x-xs>e : (s * ε∉s ` loc') ⊢ ListU (x ∷ xs) > (ListU []) 
          list-x-xs>e = star-cons-nil
          v₁>v₂ : (s * ε∉s ` loc') ⊢ v₁ > v₂
          v₁>v₂ rewrite  v₁≡list-x-xs | v₂≡list-[] = list-x-xs>e
all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd {s + t ` loc' } {r} {loc} {ε∈ ε∈s + ε∈t } {c} (pdiˡ ∷ pdisˡ) (pdiʳ@(pdinstance injʳ s-evʳ) ∷ pdisʳ) _ _ 
  with zip-es-flat-[]-es {s + t ` loc'} {ε∈ ε∈s + ε∈t}  (mkAllEmptyU (ε∈ ε∈s + ε∈t)) (mkAllEmptyU-sound {s + t ` loc'} (ε∈ ε∈s + ε∈t)) in eq 
... | []                                  =  Nullary.contradiction (PartialDerivative.zip-es-flat-[]-es≡[]→es≡[] {s + t ` loc'} {ε∈ ε∈s + ε∈t}  (mkAllEmptyU (ε∈ ε∈s + ε∈t)) (mkAllEmptyU-sound {s + t ` loc'} (ε∈ ε∈s + ε∈t)) eq) (mkAllEmptyU≢[] (ε∈ ε∈s + ε∈t)) 
... | ( e , flat-[] _ proj₁flat-e≡[] )  ∷ es-flat-[]-es  =  ind (pdiˡ ∷ pdisˡ) 

  where 
    ind : ( pdis : List (PDInstance (s + t ` loc') c ) )
      → All (λ pdi → Ex>-maybe pdi
         (just (mk-snd-pdi {s + t ` loc' } {r} {loc} {c} (e , flat-[] e proj₁flat-e≡[]) pdiʳ)))
            (List.map pdinstance-fst pdis)
    ind [] = []
    ind ( pdi@(pdinstance inj s-ev) ∷ pdis ) =  ex>-just (>-pdi (pdinstance-fst {s + t ` loc'} {r} {loc} {c} (pdinstance inj s-ev)) (mk-snd-pdi (e , flat-[] e proj₁flat-e≡[]) pdiʳ) λ { ( PairU v₁ v₁') (PairU v₂ v₂') r₁ r₂  → ev->  v₁ v₁' v₂ v₂' r₁ r₂  } ) ∷ ind pdis
      where 
        ev-> : (v₁ : U (s + t ` loc') )
           → (v₁' : U r )
           → (v₂ : U (s + t ` loc') )
           → (v₂' : U r )
           → Recons {(s + t ` loc') ● r ` loc} {c} (PairU v₁ v₁')  ( pdinstance-fst {s + t ` loc'} {r} {loc} {c} ( pdinstance inj s-ev ) )
           → Recons {(s + t ` loc') ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi (e , flat-[] e proj₁flat-e≡[]) (pdinstance injʳ s-evʳ) )
           --------------------------------------------------
           → ((s + t ` loc') ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂'
        ev-> (LeftU u₁) v₁' (LeftU u₂) v₂' (recons .(PairU (LeftU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-left-u₁-v₁')) (recons .(PairU (LeftU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' = seq₁ (choice-ll-empty ¬proj₁flatleftu₁≡[] proj₁flatleftu₂≡[] )
          where
            pair-left-u₁-v₁'≡pair-inj-v₃-v₃' : PairU (LeftU u₁) v₁' ≡  PairU (inj v₃) v₃' 
            pair-left-u₁-v₁'≡pair-inj-v₃-v₃' =
              begin
                PairU (LeftU u₁) v₁'
              ≡⟨ sym inj-unflat-w∈⟦p₁●r⟧≡pair-left-u₁-v₁' ⟩
                mkinjFst inj (PairU v₃ v₃')
              ≡⟨⟩
                PairU (inj v₃) v₃' 
              ∎ 
            left-u₁≡inj-v₃ : LeftU {s} {t} {loc'} u₁ ≡  inj v₃
            left-u₁≡inj-v₃ = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (LeftU u₁) v₁' (inj v₃) v₃'  pair-left-u₁-v₁'≡pair-inj-v₃-v₃' )

            ¬proj₁flatleftu₁≡[] : ¬ proj₁ (flat (LeftU {s} {t} {loc'} u₁)) ≡ []
            ¬proj₁flatleftu₁≡[] rewrite cong (λ x → proj₁ (flat x )) left-u₁≡inj-v₃ | s-ev v₃ =   λ proj₁flat-inj-v₃≡[] →  Utils.¬∷≡[]  proj₁flat-inj-v₃≡[]  


            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (LeftU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (LeftU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            left-u₂≡e : LeftU {s} {t} {loc'} u₂ ≡ e
            left-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (LeftU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatleftu₂≡[] : proj₁ (flat (LeftU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatleftu₂≡[] rewrite cong (λ x → proj₁ (flat x )) left-u₂≡e  = proj₁flat-e≡[]

        ev-> (LeftU u₁) v₁' (RightU u₂) v₂' (recons .(PairU (LeftU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-left-u₁-v₁')) (recons .(PairU (RightU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' = seq₁ (choice-lr-empty ¬proj₁flatleftu₁≡[] proj₁flatrightu₂≡[] )
          where
            pair-left-u₁-v₁'≡pair-inj-v₃-v₃' : PairU (LeftU u₁) v₁' ≡  PairU (inj v₃) v₃' 
            pair-left-u₁-v₁'≡pair-inj-v₃-v₃' =
              begin
                PairU (LeftU u₁) v₁'
              ≡⟨ sym inj-unflat-w∈⟦p₁●r⟧≡pair-left-u₁-v₁' ⟩
                mkinjFst inj (PairU v₃ v₃')
              ≡⟨⟩
                PairU (inj v₃) v₃' 
              ∎ 
            left-u₁≡inj-v₃ : LeftU {s} {t} {loc'} u₁ ≡  inj v₃
            left-u₁≡inj-v₃ = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (LeftU u₁) v₁' (inj v₃) v₃'  pair-left-u₁-v₁'≡pair-inj-v₃-v₃' )

            ¬proj₁flatleftu₁≡[] : ¬ proj₁ (flat (LeftU {s} {t} {loc'} u₁)) ≡ []
            ¬proj₁flatleftu₁≡[] rewrite cong (λ x → proj₁ (flat x )) left-u₁≡inj-v₃ | s-ev v₃ =   λ proj₁flat-inj-v₃≡[] →  Utils.¬∷≡[]  proj₁flat-inj-v₃≡[]  


            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (RightU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (RightU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            right-u₂≡e : RightU {s} {t} {loc'} u₂ ≡ e
            right-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (RightU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatrightu₂≡[] : proj₁ (flat (RightU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatrightu₂≡[] rewrite cong (λ x → proj₁ (flat x )) right-u₂≡e  = proj₁flat-e≡[]

        ev-> (RightU u₁) v₁' (LeftU u₂) v₂' (recons .(PairU (RightU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-right-u₁-v₁')) (recons .(PairU (LeftU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' = seq₁ (choice-rl-empty ¬proj₁flatrightu₁≡[] proj₁flatleftu₂≡[] )
          where
            pair-right-u₁-v₁'≡pair-inj-v₃-v₃' : PairU (RightU u₁) v₁' ≡  PairU (inj v₃) v₃' 
            pair-right-u₁-v₁'≡pair-inj-v₃-v₃' =
              begin
                PairU (RightU u₁) v₁'
              ≡⟨ sym inj-unflat-w∈⟦p₁●r⟧≡pair-right-u₁-v₁' ⟩
                mkinjFst inj (PairU v₃ v₃')
              ≡⟨⟩
                PairU (inj v₃) v₃' 
              ∎ 
            right-u₁≡inj-v₃ : RightU {s} {t} {loc'} u₁ ≡  inj v₃
            right-u₁≡inj-v₃ = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (RightU u₁) v₁' (inj v₃) v₃'  pair-right-u₁-v₁'≡pair-inj-v₃-v₃' )

            ¬proj₁flatrightu₁≡[] : ¬ proj₁ (flat (RightU {s} {t} {loc'} u₁)) ≡ []
            ¬proj₁flatrightu₁≡[] rewrite cong (λ x → proj₁ (flat x )) right-u₁≡inj-v₃ | s-ev v₃ =   λ proj₁flat-inj-v₃≡[] →  Utils.¬∷≡[]  proj₁flat-inj-v₃≡[]  


            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (LeftU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (LeftU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            left-u₂≡e : LeftU {s} {t} {loc'} u₂ ≡ e
            left-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (LeftU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatleftu₂≡[] : proj₁ (flat (LeftU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatleftu₂≡[] rewrite cong (λ x → proj₁ (flat x )) left-u₂≡e  = proj₁flat-e≡[]

        ev-> (RightU u₁) v₁' (RightU u₂) v₂' (recons .(PairU (RightU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-right-u₁-v₁')) (recons .(PairU (RightU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' = seq₁ (choice-rr-empty ¬proj₁flatrightu₁≡[] proj₁flatrightu₂≡[] )
          where
            pair-right-u₁-v₁'≡pair-inj-v₃-v₃' : PairU (RightU u₁) v₁' ≡  PairU (inj v₃) v₃' 
            pair-right-u₁-v₁'≡pair-inj-v₃-v₃' =
              begin
                PairU (RightU u₁) v₁'
              ≡⟨ sym inj-unflat-w∈⟦p₁●r⟧≡pair-right-u₁-v₁' ⟩
                mkinjFst inj (PairU v₃ v₃')
              ≡⟨⟩
                PairU (inj v₃) v₃' 
              ∎ 
            right-u₁≡inj-v₃ : RightU {s} {t} {loc'} u₁ ≡  inj v₃
            right-u₁≡inj-v₃ = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (RightU u₁) v₁' (inj v₃) v₃'  pair-right-u₁-v₁'≡pair-inj-v₃-v₃' )

            ¬proj₁flatrightu₁≡[] : ¬ proj₁ (flat (RightU {s} {t} {loc'} u₁)) ≡ []
            ¬proj₁flatrightu₁≡[] rewrite cong (λ x → proj₁ (flat x )) right-u₁≡inj-v₃ | s-ev v₃ =   λ proj₁flat-inj-v₃≡[] →  Utils.¬∷≡[]  proj₁flat-inj-v₃≡[]  

            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (RightU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (RightU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            right-u₂≡e : RightU {s} {t} {loc'} u₂ ≡ e
            right-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (RightU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatrightu₂≡[] : proj₁ (flat (RightU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatrightu₂≡[] rewrite cong (λ x → proj₁ (flat x )) right-u₂≡e  = proj₁flat-e≡[]


all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd {s + t ` loc' } {r} {loc} {ε∈ ε∈s <+ ε∉t } {c} (pdiˡ ∷ pdisˡ) (pdiʳ@(pdinstance injʳ s-evʳ) ∷ pdisʳ) _ _ 
  with zip-es-flat-[]-es {s + t ` loc'}  {ε∈ ε∈s <+ ε∉t }  (mkAllEmptyU (ε∈ ε∈s <+ ε∉t)) (mkAllEmptyU-sound {s + t ` loc'}  (ε∈ ε∈s <+ ε∉t) ) in eq 
... | []                                  =  Nullary.contradiction (PartialDerivative.zip-es-flat-[]-es≡[]→es≡[] {s + t ` loc'} {ε∈ ε∈s <+ ε∉t }   (mkAllEmptyU (ε∈ ε∈s <+ ε∉t )) (mkAllEmptyU-sound {s + t ` loc'} (ε∈ ε∈s <+ ε∉t)) eq) (mkAllEmptyU≢[] (ε∈ ε∈s <+ ε∉t)) 
... | ( e , flat-[] _ proj₁flat-e≡[] )  ∷ es-flat-[]-es  =  ind (pdiˡ ∷ pdisˡ) 

  where 
    ind : ( pdis : List (PDInstance (s + t ` loc') c ) )
      → All (λ pdi → Ex>-maybe pdi
         (just (mk-snd-pdi {s + t ` loc' } {r} {loc} {c} (e , flat-[] e proj₁flat-e≡[]) pdiʳ)))
            (List.map pdinstance-fst pdis)
    ind [] = []
    ind ( pdi@(pdinstance inj s-ev) ∷ pdis ) =  ex>-just (>-pdi (pdinstance-fst {s + t ` loc'} {r} {loc} {c} (pdinstance inj s-ev)) (mk-snd-pdi (e , flat-[] e proj₁flat-e≡[]) pdiʳ) λ { ( PairU v₁ v₁') (PairU v₂ v₂') r₁ r₂  → ev->  v₁ v₁' v₂ v₂' r₁ r₂  } ) ∷ ind pdis
      where 
        ev-> : (v₁ : U (s + t ` loc') )
           → (v₁' : U r )
           → (v₂ : U (s + t ` loc') )
           → (v₂' : U r )
           → Recons {(s + t ` loc') ● r ` loc} {c} (PairU v₁ v₁')  ( pdinstance-fst {s + t ` loc'} {r} {loc} {c} ( pdinstance inj s-ev ) )
           → Recons {(s + t ` loc') ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi (e , flat-[] e proj₁flat-e≡[]) (pdinstance injʳ s-evʳ) )
           --------------------------------------------------
           → ((s + t ` loc') ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂'
        ev->  (LeftU u₁) v₁' (LeftU u₂) v₂' (recons .(PairU (LeftU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-left-u₁-v₁')) (recons .(PairU (LeftU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' = seq₁ (choice-ll-empty ¬proj₁flatleftu₁≡[] proj₁flatleftu₂≡[] )
          where
            pair-left-u₁-v₁'≡pair-inj-v₃-v₃' : PairU (LeftU u₁) v₁' ≡  PairU (inj v₃) v₃' 
            pair-left-u₁-v₁'≡pair-inj-v₃-v₃' =
              begin
                PairU (LeftU u₁) v₁'
              ≡⟨ sym inj-unflat-w∈⟦p₁●r⟧≡pair-left-u₁-v₁' ⟩
                mkinjFst inj (PairU v₃ v₃')
              ≡⟨⟩
                PairU (inj v₃) v₃' 
              ∎ 
            left-u₁≡inj-v₃ : LeftU {s} {t} {loc'} u₁ ≡  inj v₃
            left-u₁≡inj-v₃ = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (LeftU u₁) v₁' (inj v₃) v₃'  pair-left-u₁-v₁'≡pair-inj-v₃-v₃' )

            ¬proj₁flatleftu₁≡[] : ¬ proj₁ (flat (LeftU {s} {t} {loc'} u₁)) ≡ []
            ¬proj₁flatleftu₁≡[] rewrite cong (λ x → proj₁ (flat x )) left-u₁≡inj-v₃ | s-ev v₃ =   λ proj₁flat-inj-v₃≡[] →  Utils.¬∷≡[]  proj₁flat-inj-v₃≡[]  


            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (LeftU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (LeftU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            left-u₂≡e : LeftU {s} {t} {loc'} u₂ ≡ e
            left-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (LeftU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatleftu₂≡[] : proj₁ (flat (LeftU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatleftu₂≡[] rewrite cong (λ x → proj₁ (flat x )) left-u₂≡e  = proj₁flat-e≡[]
            
        ev-> (LeftU u₁) v₁' (RightU u₂) v₂' (recons .(PairU (LeftU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-left-u₁-v₁')) (recons .(PairU (RightU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' = Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flatrightu₂≡[] ) (ε∉r→¬ε∈r ε∉t) 
          where

            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (RightU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (RightU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            right-u₂≡e : RightU {s} {t} {loc'} u₂ ≡ e
            right-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (RightU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)

            proj₁flatrightu₂≡[] : proj₁ (flat (RightU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatrightu₂≡[] rewrite cong (λ x → proj₁ (flat x )) right-u₂≡e  = proj₁flat-e≡[]

            
        ev-> (RightU u₁) v₁' (LeftU u₂) v₂' (recons .(PairU (RightU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-right-u₁-v₁')) (recons .(PairU (LeftU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' = seq₁ (choice-rl-empty ¬proj₁flatrightu₁≡[] proj₁flatleftu₂≡[] )
          where
            pair-right-u₁-v₁'≡pair-inj-v₃-v₃' : PairU (RightU u₁) v₁' ≡  PairU (inj v₃) v₃' 
            pair-right-u₁-v₁'≡pair-inj-v₃-v₃' =
              begin
                PairU (RightU u₁) v₁'
              ≡⟨ sym inj-unflat-w∈⟦p₁●r⟧≡pair-right-u₁-v₁' ⟩
                mkinjFst inj (PairU v₃ v₃')
              ≡⟨⟩
                PairU (inj v₃) v₃' 
              ∎ 
            right-u₁≡inj-v₃ : RightU {s} {t} {loc'} u₁ ≡  inj v₃
            right-u₁≡inj-v₃ = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (RightU u₁) v₁' (inj v₃) v₃'  pair-right-u₁-v₁'≡pair-inj-v₃-v₃' )

            ¬proj₁flatrightu₁≡[] : ¬ proj₁ (flat (RightU {s} {t} {loc'} u₁)) ≡ []
            ¬proj₁flatrightu₁≡[] rewrite cong (λ x → proj₁ (flat x )) right-u₁≡inj-v₃ | s-ev v₃ =   λ proj₁flat-inj-v₃≡[] →  Utils.¬∷≡[]  proj₁flat-inj-v₃≡[]  


            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (LeftU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (LeftU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            left-u₂≡e : LeftU {s} {t} {loc'} u₂ ≡ e
            left-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (LeftU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatleftu₂≡[] : proj₁ (flat (LeftU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatleftu₂≡[] rewrite cong (λ x → proj₁ (flat x )) left-u₂≡e  = proj₁flat-e≡[]

        ev-> (RightU u₁) v₁' (RightU u₂) v₂' (recons .(PairU (RightU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-right-u₁-v₁')) (recons .(PairU (RightU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' =  Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flatrightu₂≡[] ) (ε∉r→¬ε∈r ε∉t)  
          where
          
            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (RightU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (RightU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            right-u₂≡e : RightU {s} {t} {loc'} u₂ ≡ e
            right-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (RightU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatrightu₂≡[] : proj₁ (flat (RightU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatrightu₂≡[] rewrite cong (λ x → proj₁ (flat x )) right-u₂≡e  = proj₁flat-e≡[]



all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd {s + t ` loc' } {r} {loc} {ε∈ ε∉s +> ε∈t } {c} (pdiˡ ∷ pdisˡ) (pdiʳ@(pdinstance injʳ s-evʳ) ∷ pdisʳ) _ _ 
  with zip-es-flat-[]-es {s + t ` loc'} {ε∈ ε∉s +> ε∈t}  (mkAllEmptyU (ε∈ ε∉s +> ε∈t)) (mkAllEmptyU-sound {s + t ` loc'} (ε∈ ε∉s +> ε∈t)) in eq 
... | []                                  =  Nullary.contradiction (PartialDerivative.zip-es-flat-[]-es≡[]→es≡[] {s + t ` loc'} {ε∈ ε∉s +> ε∈t}  (mkAllEmptyU (ε∈ ε∉s +> ε∈t)) (mkAllEmptyU-sound {s + t ` loc'} (ε∈ ε∉s +> ε∈t)) eq) (mkAllEmptyU≢[] (ε∈ ε∉s +> ε∈t)) 
... | ( e , flat-[] _ proj₁flat-e≡[] )  ∷ es-flat-[]-es  =  ind (pdiˡ ∷ pdisˡ) 

  where 
    ind : ( pdis : List (PDInstance (s + t ` loc') c ) )
      → All (λ pdi → Ex>-maybe pdi
         (just (mk-snd-pdi {s + t ` loc' } {r} {loc} {c} (e , flat-[] e proj₁flat-e≡[]) pdiʳ)))
            (List.map pdinstance-fst pdis)
    ind [] = []
    ind ( pdi@(pdinstance inj s-ev) ∷ pdis ) =  ex>-just (>-pdi (pdinstance-fst {s + t ` loc'} {r} {loc} {c} (pdinstance inj s-ev)) (mk-snd-pdi (e , flat-[] e proj₁flat-e≡[]) pdiʳ) λ { ( PairU v₁ v₁') (PairU v₂ v₂') r₁ r₂  → ev->  v₁ v₁' v₂ v₂' r₁ r₂  } ) ∷ ind pdis
      where 
        ev-> : (v₁ : U (s + t ` loc') )
           → (v₁' : U r )
           → (v₂ : U (s + t ` loc') )
           → (v₂' : U r )
           → Recons {(s + t ` loc') ● r ` loc} {c} (PairU v₁ v₁')  ( pdinstance-fst {s + t ` loc'} {r} {loc} {c} ( pdinstance inj s-ev ) )
           → Recons {(s + t ` loc') ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi (e , flat-[] e proj₁flat-e≡[]) (pdinstance injʳ s-evʳ) )
           --------------------------------------------------
           → ((s + t ` loc') ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂'
        ev-> (LeftU u₁) v₁' (LeftU u₂) v₂' (recons .(PairU (LeftU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-left-u₁-v₁')) (recons .(PairU (LeftU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' =  Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flatleftu₂≡[] ) (ε∉r→¬ε∈r ε∉s) 
          where
            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (LeftU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (LeftU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            left-u₂≡e : LeftU {s} {t} {loc'} u₂ ≡ e
            left-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (LeftU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatleftu₂≡[] : proj₁ (flat (LeftU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatleftu₂≡[] rewrite cong (λ x → proj₁ (flat x )) left-u₂≡e  = proj₁flat-e≡[]

        ev-> (LeftU u₁) v₁' (RightU u₂) v₂' (recons .(PairU (LeftU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-left-u₁-v₁')) (recons .(PairU (RightU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' = seq₁ (choice-lr-empty ¬proj₁flatleftu₁≡[] proj₁flatrightu₂≡[] )
          where
            pair-left-u₁-v₁'≡pair-inj-v₃-v₃' : PairU (LeftU u₁) v₁' ≡  PairU (inj v₃) v₃' 
            pair-left-u₁-v₁'≡pair-inj-v₃-v₃' =
              begin
                PairU (LeftU u₁) v₁'
              ≡⟨ sym inj-unflat-w∈⟦p₁●r⟧≡pair-left-u₁-v₁' ⟩
                mkinjFst inj (PairU v₃ v₃')
              ≡⟨⟩
                PairU (inj v₃) v₃' 
              ∎ 
            left-u₁≡inj-v₃ : LeftU {s} {t} {loc'} u₁ ≡  inj v₃
            left-u₁≡inj-v₃ = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (LeftU u₁) v₁' (inj v₃) v₃'  pair-left-u₁-v₁'≡pair-inj-v₃-v₃' )

            ¬proj₁flatleftu₁≡[] : ¬ proj₁ (flat (LeftU {s} {t} {loc'} u₁)) ≡ []
            ¬proj₁flatleftu₁≡[] rewrite cong (λ x → proj₁ (flat x )) left-u₁≡inj-v₃ | s-ev v₃ =   λ proj₁flat-inj-v₃≡[] →  Utils.¬∷≡[]  proj₁flat-inj-v₃≡[]  


            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (RightU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (RightU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            right-u₂≡e : RightU {s} {t} {loc'} u₂ ≡ e
            right-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (RightU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatrightu₂≡[] : proj₁ (flat (RightU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatrightu₂≡[] rewrite cong (λ x → proj₁ (flat x )) right-u₂≡e  = proj₁flat-e≡[]

        ev-> (RightU u₁) v₁' (LeftU u₂) v₂' (recons .(PairU (RightU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-right-u₁-v₁')) (recons .(PairU (LeftU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' =  Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flatleftu₂≡[] ) (ε∉r→¬ε∈r ε∉s) 
          where

            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (LeftU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (LeftU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-left-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            left-u₂≡e : LeftU {s} {t} {loc'} u₂ ≡ e
            left-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (LeftU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-left-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatleftu₂≡[] : proj₁ (flat (LeftU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatleftu₂≡[] rewrite cong (λ x → proj₁ (flat x )) left-u₂≡e  = proj₁flat-e≡[]

        ev-> (RightU u₁) v₁' (RightU u₂) v₂' (recons .(PairU (RightU u₁) v₁') (w∈⟦p₁●r⟧ , inj-unflat-w∈⟦p₁●r⟧≡pair-right-u₁-v₁')) (recons .(PairU (RightU u₂) v₂') (w∈⟦p₂⟧ , mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂')) with unflat w∈⟦p₁●r⟧
        ... | PairU v₃ v₃' = seq₁ (choice-rr-empty ¬proj₁flatrightu₁≡[] proj₁flatrightu₂≡[] )
          where
            pair-right-u₁-v₁'≡pair-inj-v₃-v₃' : PairU (RightU u₁) v₁' ≡  PairU (inj v₃) v₃' 
            pair-right-u₁-v₁'≡pair-inj-v₃-v₃' =
              begin
                PairU (RightU u₁) v₁'
              ≡⟨ sym inj-unflat-w∈⟦p₁●r⟧≡pair-right-u₁-v₁' ⟩
                mkinjFst inj (PairU v₃ v₃')
              ≡⟨⟩
                PairU (inj v₃) v₃' 
              ∎ 
            right-u₁≡inj-v₃ : RightU {s} {t} {loc'} u₁ ≡  inj v₃
            right-u₁≡inj-v₃ = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (RightU u₁) v₁' (inj v₃) v₃'  pair-right-u₁-v₁'≡pair-inj-v₃-v₃' )

            ¬proj₁flatrightu₁≡[] : ¬ proj₁ (flat (RightU {s} {t} {loc'} u₁)) ≡ []
            ¬proj₁flatrightu₁≡[] rewrite cong (λ x → proj₁ (flat x )) right-u₁≡inj-v₃ | s-ev v₃ =   λ proj₁flat-inj-v₃≡[] →  Utils.¬∷≡[]  proj₁flat-inj-v₃≡[]  

            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ : PairU (RightU u₂) v₂' ≡ PairU e (injʳ  (unflat w∈⟦p₂⟧))
            pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧ =
              begin
                PairU (RightU u₂) v₂'
              ≡⟨ sym mkinjSnd-injʳ-e-unflat-w∈⟦p₂⟧≡pair-right-u₂-v₂' ⟩
                 mkinjSnd injʳ e (unflat w∈⟦p₂⟧)
              ≡⟨⟩
                PairU e (injʳ  (unflat w∈⟦p₂⟧))
              ∎ 
            right-u₂≡e : RightU {s} {t} {loc'} u₂ ≡ e
            right-u₂≡e = proj₁ ( inv-pairU {s + t ` loc'} {r} {loc} (RightU u₂) v₂' e  (injʳ (unflat w∈⟦p₂⟧)) pair-right-u₂-v₂'≡pair-e-inj-unflat-w∈⟦p₂⟧)
            proj₁flatrightu₂≡[] : proj₁ (flat (RightU {s} {t} {loc'} u₂)) ≡ []
            proj₁flatrightu₂≡[] rewrite cong (λ x → proj₁ (flat x )) right-u₂≡e  = proj₁flat-e≡[]


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
...  | yes ε∈l = 
  concat-ex-sorted { l ● r ` loc } {c}
    (List.map pdinstance-fst pdU[ l , c ])
    (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ])
    map-pdinstance-fst-ex>sorted
    concatmap-pdinstance-snd-is-ex>-sorted
    (all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd pdU[ l , c ]  pdU[ r , c ] refl refl )
  where
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c}
    
    ind-hyp-r : Ex>-sorted pdU[ r , c ]
    ind-hyp-r = pdU-sorted {r} {c}

    -- we need to concat the following two, but we need to know all fst in map-pdinstance-fst-ex>sorted  >  concatmap-pdinstance-snd-ex>-sorted
    map-pdinstance-fst-ex>sorted : Ex>-sorted { l ● r ` loc } (List.map pdinstance-fst  pdU[ l , c ] )
    map-pdinstance-fst-ex>sorted = map-fst-ex-sorted pdU[ l , c ] ind-hyp-l 

    concatmap-pdinstance-snd-is-ex>-sorted : Ex>-sorted { l  ● r ` loc } (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ])
    concatmap-pdinstance-snd-is-ex>-sorted = concatmap-pdinstance-snd-ex>-sorted {l} {r} {ε∈l} {loc} {c}  pdU[ r , c ] ind-hyp-r 

{-
    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd :
         (pdis : List (PDInstance l c ))
      →  (pdis' : List (PDInstance r c))
      →  All (λ pdi → Ex>-maybe { l ● r ` loc } pdi (head (concatmap-pdinstance-snd  {l} {r} {ε∈l} {loc} {c} pdis')))
             (List.map (pdinstance-fst {l} {r} {loc} {c}) pdis )
    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd [] _ = []
    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd (pdi ∷ pdis) [] rewrite ( concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c} )
      = prf (pdi ∷ pdis)
        where
          prf : (pdis' : List (PDInstance l c))
              → All (λ pdi₁ → Ex>-maybe pdi₁ nothing)  (List.map ( pdinstance-fst  {l} {r} {loc} {c} ) pdis' )
          prf [] = []
          prf (pdi' ∷ pdis') = ex>-nothing ∷ prf pdis' 

    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd (pdi ∷ pdis) (pdi' ∷ pdis')
      with concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  (pdi' ∷ pdis') in concatmap-pd-snd-eq 
    ... | ( pdi₂@(pdinstance p→l●r₂ s-ev₂) ∷ pdis₂ ) = ind (pdi ∷ pdis)
        where
          ind : ( pdis₀ : List (PDInstance l c) )
              → All (λ pdi₁ → Ex>-maybe pdi₁ (just (pdinstance p→l●r₂ s-ev₂)))
                (List.map pdinstance-fst pdis₀)
          ind []              = []
          ind (pdi₀@(pdinstance p→l₀ s-ev₀) ∷ pdis₀) with pdinstance-fst {l} {r} {loc} pdi₀ -- pdi₀ is pdi from the parent scope
          ... | pdi₁@(pdinstance p→l●r₁ s-ev₁) = ex>-just (>-pdi pdi₁ (pdinstance p→l●r₂ s-ev₂) ev) ∷ (ind pdis₀)
            where
              ev : (u₁ u₂ : U (l ● r ` loc)) →
                   Recons u₁ (pdinstance p→l●r₁ s-ev₁) →
                   Recons u₂ (pdinstance p→l●r₂ s-ev₂) → (l ● r ` loc) ⊢ u₁ > u₂
              ev (PairU v₁ s₁) (PairU v₂ s₂)
                 recons₁@(recons _ ( w∈⟦p₁⟧ , inj-unflat-w∈⟦p₁⟧≡pair-v₁s₁ ))
                 recons₂@(recons _ ( w∈⟦p₂⟧ , inj-unflat-w∈⟦p₂⟧≡pair-v₂s₂ )) =  {!!}


              {-

              ev-> : (v₁ : U l )
                   → (v₁' : U r )
                   → (v₂ : U l )
                   → (v₂' : U r )
                   → Recons {l ● r ` loc} {c} (PairU v₁ v₁')  ( pdinstance-fst {l} {r} {loc} {c}  pdi₀ )
                   → Recons {l ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi {l} {r} {loc} {c}  (ListU [] ,  flat-[] (ListU []) refl) pdi' )
                   --------------------------------------------------
                   → ((l * ε∉l ` loc₂) ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂'
              ev-> v₁ v₁' v₂ v₂' recons1 recons2  = seq₁ v₁>v₂
                where 
                  v₂≡list-[] : v₂ ≡ (ListU [])
                  v₂≡list-[] = mk-snd-pdi-fst-pair-≡ pdi' (ListU []) (flat-[] (ListU []) refl)  v₂ v₂' recons2
                  v₁-is-cons : ∃[ x ] ∃[ xs ] (v₁ ≡ ListU (x ∷ xs))
                  v₁-is-cons = pdinstance-fst-pair-l*-is-cons pdi v₁ v₁' recons1
                  x  = proj₁ v₁-is-cons
                  xs = proj₁ (proj₂ v₁-is-cons)
                  v₁≡list-x-xs = proj₂ (proj₂ v₁-is-cons)
                  list-x-xs>e : (l * ε∉l ` loc₂) ⊢ ListU (x ∷ xs) > (ListU []) 
                  list-x-xs>e = star-cons-nil
                  v₁>v₂ : (l * ε∉l ` loc₂) ⊢ v₁ > v₂
                  v₁>v₂ rewrite  v₁≡list-x-xs | v₂≡list-[] = list-x-xs>e
              -}


    ... | [] with inv-concatMap-map-f-[] {xs = (zip-es-flat-[]-es {l} {ε∈l} (mkAllEmptyU ε∈l) (mkAllEmptyU-sound ε∈l)) }
                                         {ys =  (pdi' ∷ pdis')} 
                                         concatmap-pd-snd-eq
    ...       |  inj₁ zip-es-flat-[]-es≡[] = Nullary.contradiction zip-es-flat-[]-es≡[] ¬zip-es-flat-[]-es≡[]
    ...       |  inj₂ pdi'∷pdis'≡[]        = Nullary.contradiction pdi'∷pdis'≡[] ¬∷≡[] 
    -}

{-
Goal: All (λ pdi₁ → Ex>-maybe pdi₁ (just (pdinstance inj s-ev)))
      (pdinstance-fst pdi ∷ List.map pdinstance-fst pdis)
————————————————————————————————————————————————————————————
pdi₂  : PDInstance (l ● r ` loc) c
pdi₂  = pdinstance inj s-ev
pdis  : List (PDInstance l c)
pdi   : PDInstance l c
concatmap-pd-snd-eq
      : List.foldr _++_ []
        (List.map (λ x → mk-snd-pdi x pdi' ∷ List.map (mk-snd-pdi x) pdis')
         (zip-es-flat-[]-es (mkAllEmptyU ε∈l) (mkAllEmptyU-sound ε∈l)))
        ≡ pdinstance inj s-ev ∷ pdis₂
pdis₂ : List (PDInstance (l ● r ` loc) c)
s-ev  : (u : U p) →
        Product.proj₁ (flat (inj u)) ≡ c ∷ Product.proj₁ (flat u)
inj   : U p → U (l ● r ` loc)
p     : RE   (not in scope)
pdis' : List (PDInstance r c)
pdi'  : PDInstance r c
c     : Char
loc   : ℕ
r     : RE
ε∈l   : ε∈ l
l     : RE

we need to make use of the fact that all parse trees pdi₁ = PairU v' u' produced by concatmap-pdinstance-snd has an empty v.
all the parse trees PairU v u produced by pdinstance-fst has a non empty v.

do we need this?
forall parse tree v and u. |v| != [] and |u| = [], r |- v > u 

then we can show that PairU v u > PairU v' u' via seq₁ (v > v') 

-}
       
```



### Definition 39 : (Extended) greedy ordering among PDInstance*'s 

Let r be a non problematic regular expression.

Let w be a word.

Let pdi₁ and pdi₂ be two partial derivative descendant instances of r w.r.t w.

We say pdi₁ is greedier than pdi₂, r , w  ⊢* pdi₁ > pdi₂ iff
  for all parse trees u₁ u₂  of r, u₁ is constructable from pdi₁ and u₂ is constructabled from pdi₂ 
    then r ⊢ u₁ > u₂ 

```agda

data _,_⊢*_>_ : ∀ ( r : RE ) → (w : List Char ) → PDInstance* r w → PDInstance* r w → Set where
  *>-pdi : ∀ { r : RE } { w : List Char }
    → ( pdi₁ : PDInstance* r w )
    → ( pdi₂ : PDInstance* r w )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r ) → (Recons* u₁ pdi₁ ) → (Recons* u₂ pdi₂) → ( r ⊢ u₁ > u₂) )
    → r , w ⊢* pdi₁ > pdi₂ 

-- transitivity of *>-pdi 
*>-pdi-trans : ∀ { r : RE }  { pref : List Char } 
  → { pdi₁ : PDInstance* r pref }
  → { pdi₂ : PDInstance* r pref }
  → { pdi₃ : PDInstance* r pref }
  → r , pref ⊢* pdi₁ > pdi₂
  → r , pref ⊢* pdi₂ > pdi₃
  -------------------------------------------  
  → r , pref ⊢* pdi₁ > pdi₃ 
*>-pdi-trans {r} {pref}  {pdi₁} {pdi₂} {pdi₃} (*>-pdi pdi₁ pdi₂ u₁→u₂→rec₁→rec₂→u₁>u₂)  (*>-pdi .pdi₂ pdi₃ u₂→u₃→rec₂→rec₃→u₂>u₃)  = *>-pdi pdi₁ pdi₃ *>-ev
  
  where
    *>-ev : ( u₁ : U r )
          → ( u₃ : U r )
          → Recons* u₁ pdi₁
          → Recons* u₃ pdi₃
          ------------------------------
          → r ⊢ u₁ > u₃
    *>-ev u₁ u₃ recons₁ recons₃ =
      let u₂-recons₂ = pdi*-∃  {r} {pref} pdi₂ 
      in  >-trans (u₁→u₂→rec₁→rec₂→u₁>u₂ u₁ (proj₁ u₂-recons₂) recons₁ (proj₂ u₂-recons₂))
                  (u₂→u₃→rec₂→rec₃→u₂>u₃ (proj₁ u₂-recons₂) u₃ (proj₂ u₂-recons₂) recons₃)  -- where to get u₂ and recons₂ ?

```

### Definition 40 : (Extended) greedy order sortedness among pdinstance*'s 

```agda

data Ex*>-maybe : ∀ { r : RE } { w : List Char } ( pdi : PDInstance* r w ) → ( mpdi : Maybe (PDInstance* r w) ) → Set where
  ex*>-nothing : ∀ { r : RE } { w : List Char }
    → { pdi : PDInstance* r w } 
    ---------------------------
    → Ex*>-maybe {r} {w} pdi nothing
  ex*>-just : ∀ { r : RE } { w : List Char }
    → { pdi : PDInstance* r w }
    → { pdi' : PDInstance* r w }
    → r , w ⊢* pdi > pdi' 
    ----------------------------------
    → Ex*>-maybe {r} {w} pdi (just pdi')

data Ex*>-sorted : ∀ { r : RE } { w : List Char } ( pdis : List (PDInstance* r w) ) → Set where
  ex*>-nil  : ∀ { r : RE } { w : List Char } → Ex*>-sorted {r} {w} []
  ex*>-cons : ∀ { r : RE } { w : List Char } 
    → { pdi : PDInstance* r w }
    → { pdis : List (PDInstance* r w) } 
    → Ex*>-sorted  {r} {w} pdis 
    → Ex*>-maybe {r} {w} pdi (head pdis)
    --------------------------------------
    → Ex*>-sorted {r} {w} ( pdi ∷ pdis ) 
```


### Lemma 41: the list of pdinstance*'s from pdUMany[ r , c] is extended greedily sorted. 


Let r be a non problematic regular expression.

Let w be a word.

Then pdUMany[r , w] is extended greedily sorted.


#### Sub Lemma 41.1 - 41.x : Ex*>-sortedness is inductively preserved over pdinstance*'s operations 

```agda
-------------------------------------------------------------
-- Sub Lemma 41.1 - 41.6 BEGIN
-------------------------------------------------------------
-- TODO: can we define a "polymoprhic" version of concat-ex-sorted and concat-ex*-sorted? 
-- concatenation of two ex sorted lists of pdis are sorted if all the pdis from the first list are ex-> than the head of the 2nd list. 
concat-ex*-sorted : ∀ { r : RE } { w : List Char }
    → ( pdis₁ : List ( PDInstance* r w ))
    → ( pdis₂ : List ( PDInstance* r w ))
    → Ex*>-sorted { r } pdis₁
    → Ex*>-sorted { r } pdis₂
    → All (λ pdi₁ → Ex*>-maybe  {r} pdi₁ (head pdis₂)) pdis₁
    -------------------------------------------------------
    → Ex*>-sorted { r } (pdis₁ ++ pdis₂)
concat-ex*-sorted []                       pdis₂          ex*>-nil                                       pdis₂-sorted     []                              = pdis₂-sorted
concat-ex*-sorted pdis₁                    []             pdis₁-sorted                                  ex*>-nil           _  rewrite (++-identityʳ pdis₁) = pdis₁-sorted
concat-ex*-sorted (pdi₁ ∷ [])             (pdi₂ ∷ pdis₂) pdis₁-sorted                                  pdi₂pdis₂-sorted (ex*>-just pdi₁>pdi₂  ∷ [])      = ex*>-cons pdi₂pdis₂-sorted (ex*>-just pdi₁>pdi₂) 
concat-ex*-sorted (pdi₁ ∷ pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) (ex*>-cons pdi₁'pdis₁-sorted pdi₁>head-pdis₁)  pdi₂pdis₂-sorted (ex*>-just pdi₁>pdi₂  ∷ pxs)     = ex*>-cons ind-hyp pdi₁>head-pdis₁
  where
    ind-hyp = concat-ex*-sorted (pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) pdi₁'pdis₁-sorted  pdi₂pdis₂-sorted  pxs 



compose-pdi-with-ex*>-head-map-compose-pdi-with : ∀ { d r : RE } { pref : List Char} { c : Char }
  → ( d→r : U d → U r )
  → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → ( >-inc-d→r :  (v₁ v₂ : U d) → d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂ ) -- strict inc evidence for d→r
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
            --    v1 v2 : d,  d |- v1 > v2 → d→r v₁ > d→r v₂
            --  if can we show u₁ = d→r v₁ and u₂ = d→ r v₂ ? 

    ex*>-ev : ∀ (u₁ u₂ : U r )
      → Recons* u₁ (compose-pdi-with d→r s-ev-d-r (pdinstance p₁→d s-ev-p₁-d))
      → Recons* u₂ (compose-pdi-with d→r s-ev-d-r (pdinstance p₂→d s-ev-p₂-d))
      ----------------------------------------------------------------------------
      → r ⊢ u₁ > u₂
    ex*>-ev u₁ u₂
            rec*₁@(recons* {- {p₁} {r} {w₁} {pref++c} -} u₁ ( w₁∈⟦p₁⟧ , d→r∘p₁→d-unflat-w₁∈⟦p₁⟧≡u₁ ) )
            rec*₂@(recons* {- {p₂} {r} {w₂} {pref++c} -} u₂ ( w₂∈⟦p₂⟧ , d→r∘p₁→d-unflat-w₂∈⟦p₂⟧≡u₂ ) )
            with inv-recons*-compose-pdi-with u₁ pdi₁ d→r s-ev-d-r rec*₁     | inv-recons*-compose-pdi-with u₂ pdi₂ d→r s-ev-d-r rec*₂             
    ... | recons* {d} {r} {cw₁} {pref} u₁ ( cw₁∈⟦d⟧ , d→r-unflat-cw₁∈⟦d⟧≡u₁ ) | recons* {d} {r} {cw₂} {pref} u₂ ( cw₂∈⟦d⟧ , d→r-unflat-cw₂∈⟦d⟧≡u₂ ) 
            rewrite sym d→r∘p₁→d-unflat-w₁∈⟦p₁⟧≡u₁ | sym  d→r∘p₁→d-unflat-w₂∈⟦p₂⟧≡u₂ = 
                >-inc-d→r (p₁→d (unflat w₁∈⟦p₁⟧) ) (p₂→d (unflat w₂∈⟦p₂⟧)  )  (u₁→u₂→rec₁→rec₂→u₁>u₂ (p₁→d (unflat w₁∈⟦p₁⟧))
                                                                                               (p₂→d (unflat w₂∈⟦p₂⟧))
                                                                                               (recons (p₁→d (unflat w₁∈⟦p₁⟧)) (w₁∈⟦p₁⟧ , refl))
                                                                                               (recons (p₂→d (unflat w₂∈⟦p₂⟧)) (w₂∈⟦p₂⟧ , refl)))
          

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


-- need
advance-pdi*-with-c-sorted : ∀ { r : RE } { pref : List Char} { c : Char }
  → (pdi : PDInstance* r pref)
  → *>-Inc pdi 
  ----------------------------------------------------------
  → Ex*>-sorted (advance-pdi*-with-c {r} {pref} {c} pdi)
advance-pdi*-with-c-sorted {r} {pref} {c} pdi@(pdinstance* {d} {r} {pref} d→r s-ev-d-r) (*>-inc d→r-inc-ev) 
  with pdU[ d , c ]    | pdU-sorted { d } {c} 
... | []               | _                                          = ex*>-nil
... | (pdi₁ ∷ pdis₁ ) | ex>-cons ex>-sorted-pdis₁ pdi₁>head-pdis₁  = ex*>-cons (map-compose-pdi-with-sorted d→r s-ev-d-r d→r-inc-ev pdis₁ ex>-sorted-pdis₁)
                                                                               (compose-pdi-with-ex*>-head-map-compose-pdi-with d→r s-ev-d-r d→r-inc-ev pdi₁ pdis₁ pdi₁>head-pdis₁  )





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

```

#### Main proof for Lemma 41

```agda 

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


```

### Theorem 42 : ParseAll is greedily sorted


### Aux lemmas 
```agda
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
```

#### Main proof for Theorem 42 
```agda
parseAll-is-greedy : ∀ { r : RE } { w : List Char }
  →  >-sorted {r} (parseAll[ r , w ])
parseAll-is-greedy {r} {w} = concatMap-buildU-sorted pdUMany[ r , w ] pdUMany-sorted  pdUMany-*>-inc 
```

