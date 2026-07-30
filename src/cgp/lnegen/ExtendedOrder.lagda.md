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
  >-trans ;
  >-maybe ; >-just ; >-nothing   )   


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


U-inhabited : ∀ (r : RE) → U r
U-inhabited ε = EmptyU
U-inhabited ($ c ` loc) = LetterU c
U-inhabited (l + r ` loc) = LeftU (U-inhabited l)
U-inhabited (l ● r ` loc) = PairU (U-inhabited l) (U-inhabited r)
U-inhabited (r * nε ` loc) = ListU []

pdi-∃ : ∀ {r c} (pdi : PDInstance r c) → ∃[ u ] Recons u pdi
pdi-∃ (pdinstance {p} {r} {c} inj sound-ev) =
  let u-p : U p
      u-p = U-inhabited p
      w = proj₁ (flat u-p)
      w∈p = proj₂ (flat u-p)
      u = inj (unflat w∈p)
  in u , recons u (w∈p , refl)

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
                  (u₂→u₃→rec₂→rec₃→u₂>u₃ (proj₁ u₂-recons₂) u₃ (proj₂ u₂-recons₂) recons₃)

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


### Note:  Antimirov's PD does not produce parse trees sorted in lne order. refer to "ParseAll is not sorted" in `Inc.lagda.md`

