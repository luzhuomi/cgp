```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.ExtendedOrder where

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
  flat-Uε≡[] ;
  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; unListU ; listU∘unListU ;
  u-of-r*-islist ; pair-≡ ; left-≡ ; right-≡ ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU)

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ; mkAllEmptyU≢[] ; all-flat-[]-left ; all-flat-[]-right ; proj₁flat-v≡[]→ε∈r)

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ; 
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst   ;
  pdinstance-snd ; mk-snd-pdi ; mkinjSnd ; 
  concatmap-pdinstance-snd ; zip-es-flat-[]-es  ;
  pdinstance-assoc; inv-assoc ;
  compose-pdi-with   
  ) 


import cgp.Recons as Recons
open Recons using ( Recons ; recons ;
  Recons* ; recons* ;
  inv-recons-left ;   inv-recons-right ; inv-recons-fst ; inv-recons-snd ; inv-recons-star ; inv-recons-assoc ; 
  inv-recons*-compose-pdi-with ; 
  ¬recons-right-from-pdinstance-left ; ¬recons-left-from-pdinstance-right ; ¬recons-[]-from-pdinstance-star 
  )


import cgp.posix.PartialDerivative as PartialDerivative
open PartialDerivative using (
  pdU[_,_] ; pdUConcat ;
  pdUMany[_,_]; pdUMany-aux;
  advance-pdi*-with-c ; 
  parseAll[_,_] ; buildU ;
  pdi*-∃
  -- ;
  -- recons-v→¬proj₁flat-v≡[]
  )


import cgp.posix.Order as PosixOrder
open PosixOrder using ( _⊢_>_ ; len-≡ ; len-> ; 
  _⊢_>ⁱ_ ; seq₁ ; seq₂ ;
  choice-ll ; choice-rr ;
  choice-lr ;
  choice-rl ; star-head ; star-cons-nil ;
  >-sorted ; >-nil ; >-cons ; concat-sorted ; 
  mkAllEmptyU-sorted ;
  >-maybe ; >-nothing ; >-just ; 
  >-trans ; *>-Inc ; *>-inc ;
  concatmap-advance-pdi*-with-c-*>inc ;
  pdUMany-*>-inc )   



import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _≥_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ )


import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length  )

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


### Definition 36 : (Extended) POSIX ordering among PDInstances 

Let r be a non problematic regular expression.

Let c be a letter.

Let pdi₁ and pdi₂ be two partial derivative instances of r w.r.t c.

We say pdi₁ is "posix" greater than pdi₂, r , c  ⊢ pdi₁ > pdi₂ iff
  for all parse trees u₁ u₂  of r, |u₁| ≥ |u₂|, u₁ is constructible from pdi₁ and u₂ is constructibled from pdi₂ 
    then r ⊢ u₁ > u₂ ?


.


```agda
{-
trying to define a > among Recons r c, but it 
 does not work
data Rec> : { r : RE } { c : Char } { u₁ u₂ : U r } { p₁ p₂ : PDInstance r c }
  → Recons u₁ p₁ → Recons u₂ p₂ → Set where
  rec> : ∀ { r p₁ p₂ : RE } { c : Char } { w₁ w₂ : List Char } { inj1 : U p₁ → U r }
    { inj2 : U p₂ → U r  }
    { s-ev₁ : ∀ ( x : U p₁ ) → ( proj₁ ( flat {r} (inj1 x) ) ≡ c ∷ ( proj₁ (flat {p₁} x) )) }
    { s-ev₂ : ∀ ( x : U p₂ ) → ( proj₁ ( flat {r} (inj2 x) ) ≡ c ∷ ( proj₁ (flat {p₂} x) )) }
    → ( u₁ u₂ : U r )
    → ( c-ev₁ : ∃[ w₁∈⟦p₁⟧ ] ( (inj1 (unflat {p₁} {w₁}  w₁∈⟦p₁⟧)) ≡ u₁ ) )
    → ( c-ev₂ : ∃[ w₂∈⟦p₂⟧ ] ( (inj2 (unflat {p₂} {w₂}  w₂∈⟦p₂⟧)) ≡ u₂ ) )
    -- but p₁ and p₂ are not the same! we can compare unflat w₁∈⟦p₁⟧ and unflat w₂∈⟦p₂⟧
    ------------------------------------
    → Rec> (Recons.recons {p₁} {r} {c} {w₁} {inj1} {s-ev₁} u₁ c-ev₁) (Recons.recons {p₂} {r} {c} {w₂} {inj2} {s-ev₂} u₂ c-ev₂)
-}    
  

{-
data _,_⊢_>_ : ∀ ( r : RE ) → (c : Char ) → PDInstance r c → PDInstance r c → Set where
  >-pdi : ∀ { r : RE } { c : Char }
    → ( pdi₁ : PDInstance r c )
    → ( pdi₂ : PDInstance r c )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r )
      → length (proj₁ (flat u₁)) ≥ length (proj₁ (flat u₂))
      → (Recons u₁ pdi₁ ) → (Recons u₂ pdi₂) → ( r ⊢ u₁ > u₂) )
    → r , c ⊢ pdi₁ > pdi₂
-}

-- if we index the relation with a word, hence, we fix the suffix and the leading character c

-- we need a weaker variant of Recons



data WeakRecons : { r : RE } { c : Char } → ( w : List Char ) → ( u : U r ) → ( PDInstance r c )  → Set where -- how to put ( v : U p )?
  wrecons : ∀ { p r : RE } { c : Char } { w : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → (u : U r)
    → ∃[ w∈⟦p⟧ ] ( (inj (unflat {p} {w}  w∈⟦p⟧)) ≡ u )    -- the completeness property.
    → WeakRecons {r} {c} w u (pdinstance {p} {r} {c} inj sound-ev) -- <- the input PDI obj


data _,_,_⊢_>_ : ∀ ( r : RE ) → (c : Char ) →  (w : List Char ) → PDInstance r c → PDInstance r c → Set where
  >-pdi : ∀ { r : RE } { c : Char } { w : List Char } 
    → ( pdi₁ : PDInstance r c )
    → ( pdi₂ : PDInstance r c )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r )
      → proj₁ (flat u₁) ≡ c ∷ w 
      → proj₁ (flat u₂) ≡ c ∷ w 
      → (WeakRecons w u₁ pdi₁ ) → (WeakRecons w u₂ pdi₂) → ( r ⊢ u₁ > u₂) ) -- we need to expose pd parse trees v₁ and v₂ and v₁ > v₂ here.
    → r , c , w  ⊢ pdi₁ > pdi₂


```




### Definition 37 : (Extended) POSIX order sortedness

```agda
{-
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
-}


data Ex>-maybe : ∀ { r : RE } { c : Char } { w : List Char }  ( pdi : PDInstance r c ) → ( mpdi : Maybe (PDInstance r c) ) → Set where
  ex>-nothing : ∀ { r : RE } { c : Char } { w : List Char }
    → { pdi : PDInstance r c } 
    ---------------------------
    → Ex>-maybe {r} {c} {w} pdi nothing
  ex>-just : ∀ { r : RE } { c : Char } { w : List Char }
    → { pdi : PDInstance r c }
    → { pdi' : PDInstance r c }
    → r , c , w  ⊢ pdi > pdi' 
    ----------------------------------
    → Ex>-maybe {r} {c} {w} pdi (just pdi')


data Ex>-sorted : ∀ { r : RE } { c : Char } { w : List Char } ( pdis : List (PDInstance r c) ) → Set where
  ex>-nil  : ∀ { r : RE } { c : Char } { w : List Char } → Ex>-sorted {r} {c} {w} []
  ex>-cons : ∀ { r : RE } { c : Char } { w : List Char } 
    → { pdi : PDInstance r c }
    → { pdis : List (PDInstance r c) } 
    → Ex>-sorted  {r} {c} {w} pdis 
    → Ex>-maybe {r} {c} {w} pdi (head pdis)
    --------------------------------------
    → Ex>-sorted {r} {c} {w} ( pdi ∷ pdis )


```




### Lemma 38: the list of pdinstances from pdU[ r , c] is extended POSIX-> sorted. 


Let r be a non problematic regular expression.

Let c be a letter.

Then pdU[r , c] is LNE sorted. 




#### Sub Lemma 38.1 - 38.22 : Ex>-sortedness is preserved inductively over pdinstance operations.

```agda
{-
-------------------------------------------------------------
-- Sub Lemma 38.1 - 38.22 BEGIN
-------------------------------------------------------------

import Relation.Binary.Definitions
open  Relation.Binary.Definitions using (
  Tri ; tri< ; tri≈ ; tri> ) 


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
          → length (proj₁ (flat u₁)) ≥ length (proj₁ (flat u₂))
          → ( Recons u₁ left-pdi₁ )
          → ( Recons u₂ left-pdi₂ )
          -------------------------
          → ( (l + r ` loc) ⊢ u₁ > u₂ )
    ev (LeftU v₁) (LeftU v₂) len|left-v₁|≥len|left-v₂| recons-left-v₁-pdi-left recons-left-v₂-pdi-left with (Nat.<-cmp (length (proj₁ (flat (LeftU {l} {r} {loc} v₁)))) (length (proj₁ (flat (LeftU  {l} {r} {loc}  v₂)) )))
    ... | tri< len|left-v₁|<len|left-v₂| _ _ = Nullary.contradiction  len|left-v₁|≥len|left-v₂| ( <⇒≱ len|left-v₁|<len|left-v₂| )
    ... | tri> _ _ len|left-v₁|>len|left-v₂| = len-> len|left-v₁|>len|left-v₂|  
    ... | tri≈ _ len|left-v₁|≡len|left-v₂| _ = 
             len-≡ len|left-v₁|≡len|left-v₂| (choice-ll (pdi₁>-pdi₂-ev v₁ v₂ (≤-reflexive ( sym len|left-v₁|≡len|left-v₂|) ) recons-v₁-pdi₁ recons-v₂-pdi₂))
          where
            recons-v₁-pdi₁ : Recons v₁ pdi₁
            recons-v₁-pdi₁ = inv-recons-left {l} {r} {loc} v₁  pdi₁  recons-left-v₁-pdi-left
            recons-v₂-pdi₂ : Recons v₂ pdi₂            
            recons-v₂-pdi₂ = inv-recons-left {l} {r} {loc} v₂  pdi₂  recons-left-v₂-pdi-left
    ev (RightU v₁)  _        _  recons-right-v₁-pdi-left _  =  Nullary.contradiction recons-right-v₁-pdi-left (¬recons-right-from-pdinstance-left v₁ pdi₁ ) -- impossible cases
    ev (LeftU _)   (RightU v₂) _  _ recons-right-v₂-pdi-left =   Nullary.contradiction recons-right-v₂-pdi-left (¬recons-right-from-pdinstance-left v₂ pdi₂  )



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
          → length (proj₁ (flat u₁)) ≥ length (proj₁ (flat u₂))
          → ( Recons u₁ right-pdi₁ )
          → ( Recons u₂ right-pdi₂ )
          -------------------------
          → ( (l + r ` loc) ⊢ u₁ > u₂ )
    ev (RightU v₁) (RightU v₂)  len|right-v₁|≥len|right-v₂|  recons-right-v₁-pdi-right recons-right-v₂-pdi-right with (Nat.<-cmp (length (proj₁ (flat (RightU {l} {r} {loc} v₁)))) (length (proj₁ (flat (RightU  {l} {r} {loc}  v₂)) )))
    ... | tri< len|right-v₁|<len|right-v₂| _ _ = Nullary.contradiction  len|right-v₁|≥len|right-v₂| ( <⇒≱ len|right-v₁|<len|right-v₂| )
    ... | tri> _ _ len|right-v₁|>len|right-v₂| = len-> len|right-v₁|>len|right-v₂|  
    ... | tri≈ _ len|right-v₁|≡len|right-v₂| _ =
      len-≡ len|right-v₁|≡len|right-v₂| (choice-rr (pdi₁>-pdi₂-ev v₁ v₂  (≤-reflexive ( sym len|right-v₁|≡len|right-v₂|) ) recons-v₁-pdi₁ recons-v₂-pdi₂))
          where
            recons-v₁-pdi₁ : Recons v₁ pdi₁
            recons-v₁-pdi₁ = inv-recons-right {l} {r} {loc} v₁  pdi₁  recons-right-v₁-pdi-right  
            recons-v₂-pdi₂ : Recons v₂ pdi₂            
            recons-v₂-pdi₂ = inv-recons-right {l} {r} {loc} v₂  pdi₂  recons-right-v₂-pdi-right 

       
    ev (LeftU v₁)  _          _   recons-left-v₁-pdi-right _  =  Nullary.contradiction recons-left-v₁-pdi-right (¬recons-left-from-pdinstance-right v₁ pdi₁ ) -- impossible cases
    ev (RightU _)  (LeftU v₂) _  _  recons-left-v₂-pdi-right =   Nullary.contradiction recons-left-v₂-pdi-right (¬recons-left-from-pdinstance-right v₂ pdi₂  )



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
  = ex>-cons (map-right-ex-sorted (pdi' ∷ pdis') ex>-sorted-r-pdis') (ex>-just (>-pdi (pdinstance-left pdi) (pdinstance-right pdi') ev ))
    where
      ev : (u₁ u₂ : U (l + r ` loc))
        → length (proj₁ (flat u₁)) ≥ length (proj₁ (flat u₂))
        → Recons u₁ (pdinstance-left pdi)
        → Recons u₂ (pdinstance-right pdi')
        → (l + r ` loc) ⊢ u₁ > u₂
      ev (LeftU v₁) (RightU v₂) len|left-v₁|≥len|right-v₂| recons-left-u-from-pdinstance-left   recons-right-u-from-pdinstance-right with (Nat.<-cmp (length (proj₁ (flat v₁))) (length (proj₁ (flat v₂))))
      ... | tri< len|left-v₁|<len|right-v₂| _ _ = Nullary.contradiction  len|left-v₁|≥len|right-v₂| ( <⇒≱ len|left-v₁|<len|right-v₂|)
      ... | tri> _ _ len|left-v₁|>len|right-v₂| = len-> len|left-v₁|>len|right-v₂|
      ... | tri≈ _ len|left-v₁|≡len|right-v₂| _  = 
            let  recons-v₁-pdi = inv-recons-left {l} {r} {loc} v₁ pdi recons-left-u-from-pdinstance-left
                 recons-v₂-pdi' = inv-recons-right {l} {r} {loc} v₂ pdi' recons-right-u-from-pdinstance-right
            in len-≡ len|left-v₁|≡len|right-v₂| (choice-lr len|left-v₁|≥len|right-v₂|)
      ev (RightU v₁) _         _ recons-right-u-from-pdinstance-left  _              = Nullary.contradiction recons-right-u-from-pdinstance-left  (¬recons-right-from-pdinstance-left v₁ pdi )
      ev (LeftU v₁) (LeftU v₂) _ _  recons-left-u-from-pdinstance-right              = Nullary.contradiction recons-left-u-from-pdinstance-right  (¬recons-left-from-pdinstance-right v₂ pdi' ) 
map-left-right-ex-sorted {l} {r} {loc} (pdi₁ ∷ pdi₂ ∷ pdis)   (pdi' ∷ pdis') ex>-sorted-l-pdi₁pdi₂pdis ex>-sorted-r-pdipdis' with ex>-sorted-l-pdi₁pdi₂pdis
... | ex>-cons {l} ex>-sorted-pdi₂pdis (ex>-just (>-pdi _ _ pdi₁>pdi₂-ev) ) 
  = ex>-cons (map-left-right-ex-sorted (pdi₂ ∷ pdis) (pdi' ∷ pdis')   ex>-sorted-pdi₂pdis  ex>-sorted-r-pdipdis' ) (ex>-just (>-pdi (pdinstance-left pdi₁) (pdinstance-left pdi₂) ev ))
    where
      ev : (u₁ u₂ : U (l + r ` loc))
        → length (proj₁ (flat u₁)) ≥  length (proj₁ (flat u₂))
        → Recons u₁ (pdinstance-left pdi₁)
        → Recons u₂ (pdinstance-left pdi₂)
        → (l + r ` loc) ⊢ u₁ > u₂
      ev (LeftU v₁) (LeftU v₂) len|left-v₁|≥len|left-v₂|  recons-left-v1-from-pdinstance-left-pdi₁ recons-left-v2-from-pdinstance-left-pdi₂ with (Nat.<-cmp (length (proj₁ (flat v₁))) (length (proj₁ (flat v₂))))
      ... | tri< len|left-v₁|<len|left-v₂| _ _ = Nullary.contradiction  len|left-v₁|≥len|left-v₂| ( <⇒≱ len|left-v₁|<len|left-v₂|)
      ... | tri> _ _ len|left-v₁|>len|left-v₂| = len-> len|left-v₁|>len|left-v₂|
      ... | tri≈ _ len|left-v₁|≡len|left-v₂| _  = 

          let recons-v₁-pdi₁ = inv-recons-left {l} {r} {loc} v₁  pdi₁  recons-left-v1-from-pdinstance-left-pdi₁
              recons-v₂-pdi₂ = inv-recons-left {l} {r} {loc} v₂  pdi₂  recons-left-v2-from-pdinstance-left-pdi₂
          in len-≡ len|left-v₁|≡len|left-v₂| (choice-ll  (pdi₁>pdi₂-ev v₁ v₂ len|left-v₁|≥len|left-v₂|  recons-v₁-pdi₁ recons-v₂-pdi₂ ))
          -- impossible cases         
      ev (RightU v₁)  _        _  recons-right-u-from-pdinstance-left-pdi₁ _ = Nullary.contradiction recons-right-u-from-pdinstance-left-pdi₁ ( ¬recons-right-from-pdinstance-left v₁ pdi₁ )
      ev (LeftU v₁) (RightU v₂) _ _ recons-right-u-from-pdinstance-left-pdi₂ = Nullary.contradiction recons-right-u-from-pdinstance-left-pdi₂ ( ¬recons-right-from-pdinstance-left v₂ pdi₂ )       



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
          → length (proj₁ (flat t₁)) ≥  length (proj₁ (flat t₂))
          -- w : List Char
          -- proj₁ (flat t₁) ≡ c ∷ w 
          -- proj₁ (flat t₂) ≡ c ∷ w
          
          → ( Recons t₁ star-pdi₁ )
          → ( Recons t₂ star-pdi₂ )
          -------------------------
          → ( (r * ε∉r ` loc) ⊢ t₁ > t₂ )
    ev (ListU []) _ _ recons-[]-star-pdi₁ _ = Nullary.contradiction  recons-[]-star-pdi₁ (¬recons-[]-from-pdinstance-star pdi₁)
    ev _ (ListU []) _ _ recons-[]-star-pdi₂ = Nullary.contradiction  recons-[]-star-pdi₂ (¬recons-[]-from-pdinstance-star pdi₂)
    ev (ListU (v₁ ∷ vs₁)) (ListU (v₂ ∷ vs₂)) len|list-v₁vs₁|≥len|list-v₂vs₂| recons-list-vvs₁-star-pdi₁ recons-list-vvs₂-star-pdi₂ with (Nat.<-cmp (length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (v₁ ∷ vs₁) )))) (length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (v₂ ∷ vs₂))))))
    ... | tri< len|list-v₁vs₁|<len|list-v₂vs₂| _ _ =  Nullary.contradiction  len|list-v₁vs₁|≥len|list-v₂vs₂| ( <⇒≱ len|list-v₁vs₁|<len|list-v₂vs₂| ) 
    ... | tri> _ _ len|list-v₁vs₁|>len|list-v₂vs₂| = len-> len|list-v₁vs₁|>len|list-v₂vs₂|
    ... | tri≈ _ len|list-v₁vs₁|≡len|list-v₂vs₂|  _ = 
      let recons-v₁-pdi₁ = inv-recons-star v₁ vs₁ pdi₁ recons-list-vvs₁-star-pdi₁ 
          recons-v₂-pdi₂ = inv-recons-star v₂ vs₂ pdi₂ recons-list-vvs₂-star-pdi₂
      in len-≡  len|list-v₁vs₁|≡len|list-v₂vs₂| (star-head (pdi₁>-pdi₂-ev v₁ v₂ {!!}  recons-v₁-pdi₁ recons-v₂-pdi₂))
        -- we need  len|v₁|≥len|v₂|
        {-
        how to create a contradiction when len|v₁|<len|v₂|?
         attempt 1: len|v₁|<len|v₂| => r ⊢ v₂ > v₁
                                    => r* ⊢ list v₂∷vs₂ >ⁱ list v₁∷vs₁
                                    => r* ⊢ list v₂∷vs₂ > list v₁∷vs₁
                                    => len|v₂∷vs₂| ≥ len|v₁∷vs₁|
                                    no contradiction found

         attempt 2 or it is not possible for r* to have more than 1 oplus partial derivative? 
            the only possible case of introducing ++ is r ≡ l ● s for some l where ε∈ l, l cannot
         hm.. seems not

         attempt 3 let's index the >-pdi relation with a specific word.

         case 1 |v₁|≡|v₂| By I.H. >-pdi
         case 2 |v₂| is a prefix of |v₁| seq₁ (len->  ... )
         case 3 |v₁| is a prefix of |v₂| we need a contradiction?
           
           v₂ > v₁?
             the problem is the same?
               that is we should use the premise r , c ⊢ pdi₁ > pdi₂
               to create a contradiction, but we could not.

               The issue is in the Recons definition, it is only required that there exists a suffix word w∈⟦p⟧
                 such that (inj₁ (unflat {p₁} {w}  w∈⟦p₁⟧)) ≡ v₁
                 (inj₂ (unflat {p₂} {w}  w∈⟦p₁⟧)) ≡ v₂
                 

data Recons : { r : RE } { c : Char } → ( u : U r ) → ( PDInstance r c )  → Set where
  recons : ∀ { p r : RE } { c : Char } { w : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → (u : U r)
    → ∃[ w∈⟦p⟧ ] ( (inj (unflat {p} {w}  w∈⟦p⟧)) ≡ u )    -- the completeness property.
    → Recons {r} {c} u (pdinstance {p} {r} {c} inj sound-ev) -- <- the input PDI obj

         
        -}
        
-}


star-ex-sorted : ∀ { r : RE }  { ε∉r : ε∉ r } {loc : ℕ} { c : Char } { w₁ w₂ w  : List Char } 
  → w₁ ++ w₂ ≡ w 
  → (pdi₁ : PDInstance r c )
  → (pdi₂ : PDInstance r c )
  → r , c , w₁ ⊢ pdi₁ > pdi₂
  -------------------------------------------------
  → (r * ε∉r ` loc) , c , w  ⊢ pdinstance-star pdi₁ > pdinstance-star pdi₂
star-ex-sorted {r} {ε∉r} {loc} {c} {w₁} {w₂} {w} w₁++w₂≡w pdi₁ pdi₂ (>-pdi _ _ pdi₁>-pdi₂-ev ) = >-pdi star-pdi₁ star-pdi₂ ev 
  where
    star-pdi₁ : PDInstance ( r * ε∉r ` loc ) c
    star-pdi₁ = pdinstance-star pdi₁
    star-pdi₂ : PDInstance ( r * ε∉r ` loc ) c    
    star-pdi₂ = pdinstance-star pdi₂    

    ev : ∀ ( t₁ : U  (r * ε∉r ` loc) )
         → ( t₂ : U  (r * ε∉r ` loc) )
         → proj₁ (flat t₁) ≡ c ∷ w 
         → proj₁ (flat t₂) ≡ c ∷ w
         → WeakRecons w t₁ star-pdi₁ 
         → WeakRecons w t₂ star-pdi₂ 
         -------------------------
         → ( (r * ε∉r ` loc) ⊢ t₁ > t₂ )
    ev (ListU []) _ |list-[]|≡c∷w _ recons-[]-star-pdi₁ _ = Nullary.contradiction (sym |list-[]|≡c∷w) ¬∷≡[]
    ev _ (ListU []) _ |list-[]|≡c∷w _ recons-[]-star-pdi₂ = Nullary.contradiction (sym |list-[]|≡c∷w) ¬∷≡[]
    ev (ListU (v₁ ∷ vs₁)) (ListU (v₂ ∷ vs₂)) |list-v₁∷vs₁|≡c∷w |list-v₂∷vs₂|≡c∷w recons-list-vvs₁-star-pdi₁ recons-list-vvs₂-star-pdi₂ = {!!}
          -- len|v₁|>len|v₂|, -- straight forward
          -- len|v₁|≡len|v₂|  -- apply IH
          -- len|v₁|<len|v₂|
          -- how do we know that the underlying partial derivative parse trees (PairU v₁' vs₁) and (PairU v₂' vs₂) len|v₁'|≥|len|v₂'|? do we also enforce > between them?
          -- we can't, they are parse trees of two differen types, p₁ ≢ p₂
          -- hence we can't define > among them
    

```
