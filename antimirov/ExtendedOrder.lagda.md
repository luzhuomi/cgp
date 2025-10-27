```agda
{-# OPTIONS --rewriting #-}
module cgp.antimirov.ExtendedOrder where

import cgp.RE as RE
open RE using (RE; ϕ ; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ε∉ϕ ; ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star )

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] )


import cgp.antimirov.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; PDInstance ; pdinstance ; pdinstance-left ; pdinstance-right;   pdinstance-fst ; mkinjFst ;  pdinstance-snd ; concatmap-pdinstance-snd ; map-mk-snd-pdi ; mk-snd-pdi ; mkinjSnd ; pdinstance-star ; mkinjList ; flat-Uε≡[]; pdUMany[_,_];  PDInstance* ; pdinstance*  ; Recons ; recons  ) 


import cgp.antimirov.Order as AntimirovOrder
open AntimirovOrder using ( _⊢_>_ ; seq₁ ; seq₂ ; choice-ll ; choice-rr ; choice-lr ) 


import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_  )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

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


### Definition 34 : (Extended) greedy ordering among PDInstances 

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
```


### Definition 35 : (Extended) greedy order sortedness

```agda

data Ex>-maybe : ∀ { r : RE } { c : Char } ( pdi : PDInstance r c ) → ( mpdi : Maybe (PDInstance r c) ) → Set where
  ex>-nothing : ∀ { r : RE } { c : Char }
    → ( pdi : PDInstance r c )
    ---------------------------
    → Ex>-maybe {r} {c} pdi nothing
  ex>-just : ∀ { r : RE } { c : Char }
    → ( pdi : PDInstance r c )
    → ( pdi' : PDInstance r c )
    → r , c ⊢ pdi > pdi' 
    ----------------------------------
    → Ex>-maybe {r} {c} pdi (just pdi')

data Ex>-sorted : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) ) → Set where
  ex>-nil  : ∀ { r : RE } { c : Char } → Ex>-sorted {r} {c} []
  ex>-cons : ∀ { r : RE } { c : Char } 
    → ( pdi : PDInstance r c )
    → ( pdis : List (PDInstance r c) )
    → ( Ex>-sorted  {r} {c} pdis)
    → Ex>-maybe {r} {c} pdi (head pdis)
    --------------------------------------
    → Ex>-sorted {r} {c} ( pdi ∷ pdis ) 
```



### Lemma 36: pdinstances from pdU[ r , c] is extended greedily ordered. 


Let r be a non problematic regular expression.

Let c be a letter.

Then pdU[r , c] is extended greedily sorted. 

```agda

-- aux lemma

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

-- these should be moved to ParseTree

LeftU≢RightU : ∀ { l r : RE } {loc : ℕ }
  → (u : U l)
  → (v : U r)
  → (LeftU {l} {r} {loc} u) ≢ (RightU {l} {r} {loc} v)
LeftU≢RightU {l} {r} {loc} u v = λ()


inv-leftU : ∀ { l r : RE } { loc : ℕ }
  → ( u : U l )
  → ( v : U l )  
  → ( LeftU {l} {r} {loc} u ≡ LeftU {l} {r} v )
  ----------------------------------------------
  → u ≡ v
inv-leftU _ _ refl = refl   


RightU≢LeftU : ∀ { l r : RE } {loc : ℕ }
  → (u : U r)
  → (v : U l)
  → (RightU {l} {r} {loc} u) ≢ (LeftU {l} {r} {loc} v)
RightU≢LeftU {l} {r} {loc} u v = λ()


inv-rightU : ∀ { l r : RE } { loc : ℕ }
  → ( u : U r )
  → ( v : U r )  
  → ( RightU {l} {r} {loc} u ≡ RightU {l} {r} v )
  ----------------------------------------------
  → u ≡ v
inv-rightU _ _ refl = refl   

inv-pairU : ∀ { l r : RE } { loc : ℕ }
  → ( u : U l )
  → ( v : U r )
  → ( u' : U l )
  → ( v' : U r )  
  → ( PairU {l} {r} {loc} u v  ≡ PairU {l} {r} {loc} u' v' )
  ---------------------------------------------------------
  → u ≡ u' × v ≡ v'
inv-pairU _ _ _ _ refl = refl , refl   

-- these should be moved to PartialDerivativeParseTree 

inv-recons-left : ∀ { l r : RE } { loc : ℕ } { c : Char } 
    → ( u : U l ) 
    → ( pdi : PDInstance l c )
    → Recons (LeftU {l} {r} {loc} u) (pdinstance-left pdi )
    ---------------------------------------------------------
    → Recons u pdi
inv-recons-left {l} {r} {loc} {c} u (pdinstance {p} {l} {c} inj s-ev) (recons (LeftU u') ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡LeftU-u ))
  = recons u (w∈⟦p⟧ , inv-leftU (inj (unflat w∈⟦p⟧)) u inj-unflat-w∈⟦p⟧≡LeftU-u) 

inv-recons-right : ∀ { l r : RE } { loc : ℕ } { c : Char } 
    → ( u : U r ) 
    → ( pdi : PDInstance r c )
    → Recons (RightU {l} {r} {loc} u) (pdinstance-right pdi )
    ---------------------------------------------------------
    → Recons u pdi
inv-recons-right {l} {r} {loc} {c} u (pdinstance {p} {r} {c} inj s-ev) (recons (RightU u') ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡RightU-u ))
  = recons u (w∈⟦p⟧ , inv-rightU (inj (unflat w∈⟦p⟧)) u inj-unflat-w∈⟦p⟧≡RightU-u)


inv-recons-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( u : U l )
    → ( v : U r )  
    → ( pdi : PDInstance l c )
    → Recons (PairU {l} {r} {loc} u v) (pdinstance-fst pdi )
    -------------------------------------------------------- 
    → Recons u pdi
inv-recons-fst {l} {r} {loc} {c} u v (pdinstance {p} {l} {c} inj s-ev)
  (recons {p ● r ` loc} {l ● r ` loc} {c} {w'} {inj'} {s-ev'} (PairU u' v') ( _●_⧺_  {xs} {ys} {w'} {p} {r} {loc} xs∈⟦p⟧  ys∈⟦r⟧ xs++ys≡w'  , inj-unflat-w'∈⟦p●r⟧≡PairU-u-v ))
  = recons {p} {l} {c} {xs} {inj} {s-ev}  u (xs∈⟦p⟧  , proj₁ inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r⟧≡v ) 
    where 
      inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r⟧≡v : ( inj (unflat xs∈⟦p⟧) ≡ u ) × ( unflat ys∈⟦r⟧ ≡ v )
      inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r⟧≡v = inv-pairU (inj (unflat xs∈⟦p⟧)) (unflat ys∈⟦r⟧) u v inj-unflat-w'∈⟦p●r⟧≡PairU-u-v


-- A RightU parse tree cannot be reconstructed from a pdinstance-left created pdisntance
¬recons-right-from-pdinstance-left : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( u : U r ) 
  → ( pdi : PDInstance l c )
    ------------------------------------------------------------
  → ¬ (Recons (RightU {l} {r} {loc} u) (pdinstance-left pdi ))
¬recons-right-from-pdinstance-left {l} {r} {loc} {c} u pdi@(pdinstance {p} {l} inj s-ev) (recons {p'} {l + r ` loc } {c} {w} {inj'} {s-ev'} (RightU u) ( w∈⟦p'⟧ , inj∘unflat≡rightu-u ) )
  = (LeftU≢RightU {l} {r} {loc} (inj (unflat w∈⟦p'⟧)) u)  inj∘unflat≡rightu-u 


-- A LeftU parse tree cannot be reconstructed from a pdinstance-right created pdisntance
¬recons-left-from-pdinstance-right : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( u : U l ) 
  → ( pdi : PDInstance r c )
    ------------------------------------------------------------
  → ¬ (Recons (LeftU {l} {r} {loc} u) (pdinstance-right pdi ))
¬recons-left-from-pdinstance-right {l} {r} {loc} {c} u pdi@(pdinstance {p} {r} inj s-ev) (recons {p'} {l + r ` loc } {c} {w} {inj'} {s-ev'} (LeftU u) ( w∈⟦p'⟧ , inj∘unflat≡leftu-u ) )
  = (RightU≢LeftU {l} {r} {loc} (inj (unflat w∈⟦p'⟧)) u) inj∘unflat≡leftu-u



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
       let recons-v₁-pdi₁ = inv-recons-left {l} {r} {loc} v₁  pdi₁  recons-left-v₁-pdi-left 
           recons-v₂-pdi₂ = inv-recons-left {l} {r} {loc} v₂  pdi₂  recons-left-v₂-pdi-left
       in choice-ll (pdi₁>-pdi₂-ev v₁ v₂  recons-v₁-pdi₁ recons-v₂-pdi₂) 
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
       let recons-v₁-pdi₁ = inv-recons-right {l} {r} {loc} v₁  pdi₁  recons-right-v₁-pdi-right 
           recons-v₂-pdi₂ = inv-recons-right {l} {r} {loc} v₂  pdi₂  recons-right-v₂-pdi-right
       in choice-rr (pdi₁>-pdi₂-ev v₁ v₂  recons-v₁-pdi₁ recons-v₂-pdi₂) 
    ev (LeftU v₁)  _             recons-left-v₁-pdi-right _  =  Nullary.contradiction recons-left-v₁-pdi-right (¬recons-left-from-pdinstance-right v₁ pdi₁ ) -- impossible cases
    ev (RightU _)  (LeftU v₂) _  recons-left-v₂-pdi-right =   Nullary.contradiction recons-left-v₂-pdi-right (¬recons-left-from-pdinstance-right v₂ pdi₂  )




-- the following look like can be combined polymorphically with map-leftU-sorted, map-rightU-sorted, map-leftU-rightU-sorted from Greedy.lagda.md
map-left-ex-sorted : ∀ { l r : RE }  { loc : ℕ } { c : Char } 
  → ( pdis : List (PDInstance l c ) )
  → Ex>-sorted {l} pdis
  → Ex>-sorted {l + r ` loc } (List.map pdinstance-left pdis)
map-left-ex-sorted []            ex>-nil = ex>-nil
map-left-ex-sorted ( pdi ∷ [] ) (ex>-cons _ _  ex>-nil (ex>-nothing _) )
  = ex>-cons (pdinstance-left pdi) (List.map pdinstance-left []) ex>-nil (ex>-nothing (pdinstance-left pdi))
map-left-ex-sorted ( pdi ∷ (pdi' ∷ pdis) ) (ex>-cons _ _  ex>-sorted-pdis (ex>-just pdi pdi' pdi>pdi'))
  = ex>-cons (pdinstance-left pdi)
           (List.map pdinstance-left (pdi' ∷ pdis))
           (map-left-ex-sorted (pdi' ∷ pdis) ex>-sorted-pdis)
           (ex>-just (pdinstance-left pdi) (pdinstance-left pdi') (left-ex-sorted pdi pdi'  pdi>pdi'))



map-right-ex-sorted : ∀ { l r : RE }  { loc : ℕ } { c : Char } 
  → ( pdis : List (PDInstance r c ) )
  → Ex>-sorted {r} pdis
  → Ex>-sorted {l + r ` loc } (List.map pdinstance-right pdis)
map-right-ex-sorted []            ex>-nil = ex>-nil
map-right-ex-sorted ( pdi ∷ [] ) (ex>-cons _ _  ex>-nil (ex>-nothing u) )
  = ex>-cons (pdinstance-right pdi) (List.map pdinstance-right []) ex>-nil (ex>-nothing (pdinstance-right pdi))
map-right-ex-sorted ( pdi ∷ (pdi' ∷ pdis) ) (ex>-cons _ _  ex>-sorted-pdis (ex>-just pdi pdi' pdi>pdi'))
  = ex>-cons (pdinstance-right pdi)
           (List.map pdinstance-right (pdi' ∷ pdis))
           (map-right-ex-sorted (pdi' ∷ pdis) ex>-sorted-pdis)
           (ex>-just (pdinstance-right pdi) (pdinstance-right pdi') (right-ex-sorted pdi pdi'  pdi>pdi'))

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
  = ex>-cons (pdinstance-left pdi) (List.map pdinstance-left [] ++ List.map pdinstance-right (pdi' ∷ pdis')) (map-right-ex-sorted (pdi' ∷ pdis') ex>-sorted-r-pdis') (ex>-just (pdinstance-left pdi) (pdinstance-right pdi') (>-pdi (pdinstance-left pdi) (pdinstance-right pdi')
    (λ { (LeftU v₁) (RightU v₂) recons-left-u-from-pdinstance-left   recons-right-u-from-pdinstance-right → choice-lr
        -- impossible cases
       ; (RightU v₁) _          recons-right-u-from-pdinstance-left  _              → Nullary.contradiction recons-right-u-from-pdinstance-left  (¬recons-right-from-pdinstance-left v₁ pdi )
       ; (LeftU v₁) (LeftU v₂)  _  recons-left-u-from-pdinstance-right              → Nullary.contradiction recons-left-u-from-pdinstance-right  (¬recons-left-from-pdinstance-right v₂ pdi' ) 
       }
    )))
map-left-right-ex-sorted {l} {r} {loc} (pdi₁ ∷ pdi₂ ∷ pdis)   (pdi' ∷ pdis') ex>-sorted-l-pdi₁pdi₂pdis ex>-sorted-r-pdipdis' with ex>-sorted-l-pdi₁pdi₂pdis
... | ex>-cons {l} _ _ ex>-sorted-pdi₂pdis (ex>-just pdi₁ pdi₂ (>-pdi _ _ pdi₁>pdi₂-ev) ) 
  = ex>-cons (pdinstance-left pdi₁) (List.map pdinstance-left (pdi₂ ∷ pdis) ++ List.map pdinstance-right (pdi' ∷ pdis')) (map-left-right-ex-sorted (pdi₂ ∷ pdis) (pdi' ∷ pdis')   ex>-sorted-pdi₂pdis  ex>-sorted-r-pdipdis' ) ((ex>-just (pdinstance-left pdi₁) (pdinstance-left pdi₂) (>-pdi (pdinstance-left pdi₁) (pdinstance-left pdi₂)
    (λ { (LeftU v₁) (LeftU v₂)  recons-left-v1-from-pdinstance-left-pdi₁ recons-left-v2-from-pdinstance-left-pdi₂ →
         let recons-v₁-pdi₁ = inv-recons-left {l} {r} {loc} v₁  pdi₁  recons-left-v1-from-pdinstance-left-pdi₁
             recons-v₂-pdi₂ = inv-recons-left {l} {r} {loc} v₂  pdi₂  recons-left-v2-from-pdinstance-left-pdi₂
         in choice-ll ( pdi₁>pdi₂-ev v₁ v₂ recons-v₁-pdi₁ recons-v₂-pdi₂ )
        -- impossible cases         
       ; (RightU v₁)  _         recons-right-u-from-pdinstance-left-pdi₁ _ → Nullary.contradiction recons-right-u-from-pdinstance-left-pdi₁ ( ¬recons-right-from-pdinstance-left v₁ pdi₁ )
       ; (LeftU v₁) (RightU v₂) _ recons-right-u-from-pdinstance-left-pdi₂ → Nullary.contradiction recons-right-u-from-pdinstance-left-pdi₂ ( ¬recons-right-from-pdinstance-left v₂ pdi₂ )       
       }
    )))) 




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
map-fst-ex-sorted {l} {r} {loc} {c} (pdi ∷ [])              (ex>-cons _ _ ex>-nil (ex>-nothing _)) =
  ex>-cons (pdinstance-fst pdi) (List.map pdinstance-fst []) ex>-nil (ex>-nothing (pdinstance-fst pdi))
map-fst-ex-sorted {l} {r} {loc} {c} (pdi₁  ∷ pdi₂ ∷ pdis ) (ex>-cons _ _ pdi₂pdis-sorted@(ex>-cons _ _ pdis-sorted pdi₂>head-pdis)  (ex>-just _ _ pdi₁>pdi₂ )) =
  ex>-cons (pdinstance-fst pdi₁) (List.map pdinstance-fst (pdi₂ ∷ pdis)) (map-fst-ex-sorted {l} {r} {loc} {c}  (pdi₂ ∷  pdis) pdi₂pdis-sorted) (ex>-just (pdinstance-fst pdi₁) (pdinstance-fst pdi₂) (fst-ex-sorted {l} {r} pdi₁ pdi₂ pdi₁>pdi₂ ))



postulate 
  concatmap-pdinstance-snd-ex-sorted : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
                                      → ( pdis : List (PDInstance r c ) )
                                      → Ex>-sorted {r} pdis
                                      → Ex>-sorted {l ● r ` loc } (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis)

-- similiar to map-left-right-ex-sorted, can we generalize them?
map-fst-snd-ex-sorted : ∀ { l r : RE } { ε∈l : ε∈ l } { loc } { c : Char }
                        → ( pdis : List (PDInstance l c ) )
                        → ( pdis' : List (PDInstance r c ) )
                        → Ex>-sorted {l} pdis
                        → Ex>-sorted {r} pdis'
                        → Ex>-sorted {l ● r ` loc } ((List.map pdinstance-fst pdis) ++ (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis'))                        
map-fst-snd-ex-sorted                      []              pdis'  ex>-sorted-fst-[]    ex>-sorted-snd-pdis' = concatmap-pdinstance-snd-ex-sorted pdis' ex>-sorted-snd-pdis'
map-fst-snd-ex-sorted {l} {r} {ε∈l} {loc} pdis            []     ex>-sorted-fst-pdis ex->-sorted-snd-[] rewrite (cong (λ x → Ex>-sorted x) (++-identityʳ (List.map (pdinstance-fst {l} {r} {loc}) pdis)))
  = map-fst-ex-sorted pdis ex>-sorted-fst-pdis
map-fst-snd-ex-sorted {l} {r} {ε∈l} {loc} (pdi ∷ [])     (pdi' ∷ pdis')   ex>-sorted-fst-pdis ex>-sorted-snd-pdis' 
  = ex>-cons (pdinstance-fst pdi) (List.map pdinstance-fst [] ++ concatmap-pdinstance-snd (pdi' ∷ pdis') ) (concatmap-pdinstance-snd-ex-sorted (pdi' ∷ pdis') ex>-sorted-snd-pdis' ) {!!} -- how to show non empty parse tree of l is greedier than empty parse tree of l? 
map-fst-snd-ex-sorted {l} {r} {ε∈l} {loc} (pdi₁ ∷ pdi₂ ∷ pdis)     (pdi' ∷ pdis')   ex>-sorted-fst-pdi₁pdi₂pdis ex>-sorted-snd-pdis' with ex>-sorted-fst-pdi₁pdi₂pdis
... | ex>-cons {l} _ _ ex>-sorted-pdi₂pdis (ex>-just pdi₁ pdi₂ (>-pdi _ _ pdi₁>pdi₂-ev) )
  = ex>-cons (pdinstance-fst pdi₁) {!!}  {!!} {!!}


pdU-sorted : ∀ { r : RE } { c : Char }
  → Ex>-sorted {r} {c} pdU[ r , c ]
pdU-sorted {ϕ} {c} = ex>-nil
pdU-sorted {ε} {c} = ex>-nil
pdU-sorted {$ c ` loc } {c'} with c Char.≟ c'
...                           | no _ = ex>-nil 
...                           | yes refl = ex>-cons pdi [] ex>-nil (ex>-nothing pdi) 
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

pdU-sorted {l ● r ` loc } {c} with ε∈? l
...  | no ¬ε∈l = map-fst-ex-sorted {l} {r} {loc} {c}  pdU[ l , c ] ind-hyp-l
  where
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c}
...  | yes ε∈l = map-fst-snd-ex-sorted pdU[ l , c ] pdU[ r , c ] ind-hyp-l ind-hyp-r 
  where
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c} 

    ind-hyp-r : Ex>-sorted pdU[ r , c ]
    ind-hyp-r = pdU-sorted {r} {c}

  -- e.g. (ε + a) . (a + ε)
  --  pd[ (ε + a) . (a + ε) , a ] =
  --      [ ε . (a + ε ) ,  ε    ]

  --  w = "a"
  --  the parse trees     [ (RightU a) . (RightU EmptyU) , (LeftU EmptyU) . (LeftU a) ]

  --  but (LeftU EmptyU) > (RightU a)
```
