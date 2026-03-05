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
  pdU[_,_] ; -- pdUConcat ;
  pdinstance-oplus ; 
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
  

-- what if in addition, we know that p from pdi₁ and pdi₂ are identitcal? weak-singleton

data _,_⊢_>_ : ∀ ( r : RE ) → (c : Char ) → PDInstance r c → PDInstance r c → Set where
  >-pdi : ∀ { r : RE } { c : Char }
    → ( pdi₁ : PDInstance r c ) 
    → ( pdi₂ : PDInstance r c )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r )
      → length (proj₁ (flat u₁)) ≥ length (proj₁ (flat u₂))
        -- this premise is problematic? it weakens the >-pdi relation compared to the greedy and lne order 
        -- w/o this, we can't prove left-ex-sort and right-ex-sort refer to (**)
        -- can we still create a contradiction w/o this to prove (**)?
        -- even if we could do it for left-ex-sort and right-ex-sort, how about star-ex-sort? 

      → (Recons u₁ pdi₁ ) → (Recons u₂ pdi₂) → ( r ⊢ u₁ > u₂) )
    → r , c ⊢ pdi₁ > pdi₂

{-
data _,_⊢_>>_ : ∀ ( r : RE ) → ( c : Char ) → PDInstance r c → PDInstance r c → Set where
  >>-pdi-r* : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
    → ( pdi₁ : PDInstance (r * ε∉r ` loc) c )
    → ( pdi₂ : PDInstance (r * ε∉r ` loc) c )
    → ( ∀ (u₁ : U ( r * ε∉r ` loc) ) → ( u₂ : U (r * ε∉r ` loc) )
      → length (proj₁ (flat u₁)) ≥ length
        -- how to get the heads and tails? 
-} 
-- if we index the relation with a word, hence, we fix the suffix and the leading character c

-- we need a weaker variant of Recons

{-

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

-}
```




### Definition 37 : (Extended) POSIX order sortedness

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

{-

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

-}
```




### Lemma 38: the list of pdinstances from pdU[ r , c] is extended POSIX-> sorted. 


Let r be a non problematic regular expression.

Let c be a letter.

Then pdU[r , c] is LNE sorted. 




#### Sub Lemma 38.1 - 38.22 : Ex>-sortedness is preserved inductively over pdinstance operations.

```agda

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
    ... | tri< len|left-v₁|<len|left-v₂| _ _ = Nullary.contradiction  len|left-v₁|≥len|left-v₂| ( <⇒≱ len|left-v₁|<len|left-v₂| )  -- (**)
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
    ... | tri< len|right-v₁|<len|right-v₂| _ _ = Nullary.contradiction  len|right-v₁|≥len|right-v₂| ( <⇒≱ len|right-v₁|<len|right-v₂| )  -- (**) 
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

         can we find a counter example such that
            Recons (ListU (v₁ ∷ vs₁)) (pdinstance-star pdi₁) and 
            Recons (ListU (v₂ ∷ vs₂)) (pdinstance-star pdi₂) and 
            pdi₁ > pdi₂ and 
            len|v₁|<len|v₂| ?

         counter example:
           r = (a* ● (a* ● a)) *

           p₁ = ( ε ● ( a* ● ( a* ● a ) ) )   from pdi₁               
           p₂ = ( ε ● ( a* ● a ) )           from pdi₂ 

           our goal is to show pdinstance-star pdi₁ > pdinstance-star pdi₂
           
           from the premise
            (a* ● (a* ● a)) , a ⊢ pdi₁ > pdi₂
              evidence function
               ∀ (v₁ v₂ : U (a* ● (a* ● a)))
                → len|v₁|≥len|v₂|
                → Recons v₁ pdi₁  -- injecting a back to some pd parse tree
                → Recons v₂ pdi₂  -- injecting a back to some pd parse tree 
                → (a* ● (a* ● a)) ⊢ v₁ > v₂

              note that the v₁ and v₂ below do not meet the premise of the evidence function above. hence it does not violate the evidence for pdi₁ > pdi₂    

            we may find v₁' = ( Emp , ( [] , ( [] , a ) ))
                        v₂' = ( Emp , ( [ a ] , a ) )

                        
                        v₁  = ( [a], ([], a ))
                        v₂ =  ( [a], ([a], a))

                        vs₁ = [a]
                        vs₂ = []

                        v₁ ∷ vs₁ has type U (a* ● (a* ● a)) *
                        v₂ ∷ vs₂ has type U (a* ● (a* ● a)) *
                        
                        |u₁| = |v₁ ∷ vs₁| ≡ [ a , a , a ]
                        |u₂| = |v₂ ∷ vs₂| ≡ [ a , a , a ]
                        |v₁| ≡ [a , a]
                        |v₂| ≡ [a, a, a]

                        we don't have |v₁|≥|v₂| 

                        the question is ... how can v₁ ∷ vs₁ and v₂ ∷ vs₂ be constructed from
                        pdinstance-star pdi₁ and pdinstance-star pdi₂?

                         v₁'vs₁ = Pair ( Emp , ( [] , ( [] , a ) )) vs₁
                         v₂'vs₂ = Pair ( Emp , ( [ a ] , a ) ) vs₂

                         the partial derivative in  pdinstance-star pdi₁ is p₁ ● r
                         and the parital derivative in pdinstance-star pdi₂ is p₂ ●r

                         pdinstances are unique prior ε ● r ≡ r simplification.
                         lne and greedy partial derivative construction gives us the
                         condition, that the > is preserved across pdinstances in ordered.
                         this is not the case in the current POSIX attempt.
                         
                        ### these are craps
                        hm... the premise       length (proj₁ (flat u₁)) ≥ length (proj₁ (flat u₂)) is not sufficient (not strong enough) to show ⊢ u₁ > u₂, (note that from posix/Order.lagda.md, we have shown that >→len|≥| and len|>|→> but not len|≥|→>
                        i.e. u₁ ≡ ListU v₁ ∷ vs₁ and u₂ ≡ ListU v₂ ∷ vs₂
                        we should follow a bit of the shape of r? only for r* and r ● s?
                    
                        one possiblity is to type index the _,_⊢_>_ relation

                        with different sub cases of r. HOwever, that would requires use to
                          pattern match pdi₁ > pdi₂ into sub cases.
                        ### these are craps :END 


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
        
{-


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
    
-}

```

```agda
private 
  variable
    ℓ : Agda.Primitive.Level
    
data NilSingleton { A : Set ℓ } : List A → Set ℓ where
  isNil :  NilSingleton []
  isSingleton :  ( x : A ) → NilSingleton  (x ∷ [])


map-NilOrSingleton : ∀ { A B : Set } { f : A → B } { xs : List A }
  → NilSingleton xs
  ------------------------------
  → NilSingleton (List.map f xs)
map-NilOrSingleton {A} {B} {f} {[]} isNil = isNil
map-NilOrSingleton {A} {B} {f} {x ∷ []} (isSingleton .(x)) = isSingleton (f x) 

oplus-NilOrSingleton : ∀ { r : RE } { loc : ℕ } { c : Char }
  → ( pdis₁ : List (PDInstance r c ) )
  → ( pdis₂ : List (PDInstance r c ) )
  → NilSingleton pdis₁
  → NilSingleton pdis₂
  --------------------------------------------------------------
  → NilSingleton (pdinstance-oplus {r} {loc} {c} pdis₁ pdis₂)
oplus-NilOrSingleton {r} {loc} {c} [] pdis₂ isNil nilsingleton-pdis₂          = nilsingleton-pdis₂
oplus-NilOrSingleton {r} {loc} {c} (pdi₁ ∷ []) [] (isSingleton .(pdi₁)) isNil = isSingleton pdi₁
oplus-NilOrSingleton {r} {loc} {c} (pdi₁ ∷ []) (pdi₂ ∷ []) (isSingleton .(pdi₁)) (isSingleton .(pdi₂)) = isSingleton (PartialDerivative.fuse pdi₁ pdi₂) 


pdinstance-snd-NilOrSingleton : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( es-flat-[]-es : ∃[ e ] (Flat-[] l e ) )
  → ( pdis : List (PDInstance r c ) )
  → NilSingleton pdis
  --------------------------------------------------------------
  → NilSingleton (pdinstance-snd {l} {r} {loc} {c} es-flat-[]-es pdis)
pdinstance-snd-NilOrSingleton = {!!}   
  


concatmap-pdinstance-snd-NilOrSingleton : { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c  : Char }
  → ( pdis : List (PDInstance r c ) )
  → NilSingleton pdis
  ----------------------------------------------------------------------
  → NilSingleton (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis)
concatmap-pdinstance-snd-NilOrSingleton {l} {r} {ε∈l} {loc} {c} [] isNil   rewrite PosixOrder.concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c} =  isNil
concatmap-pdinstance-snd-NilOrSingleton {l} {r} {ε∈l} {loc} {c} (pdi ∷ []) (isSingleton .(pdi)) = sub e-flat-es
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l
    e-flat-es :  List ( ∃[ e ] (Flat-[] l e) )
    e-flat-es = zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es
    sub : (xs :  List ( ∃[ e ] (Flat-[] l e) )) →  NilSingleton (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x (pdi ∷ [])) xs)
    sub [] = isNil 
    sub (x ∷ xs) = {!!}  -- mkAllEmptyU is not singleton? hence  (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis) is not singleton
    -- can we nail down a counter example ?

    -- since Singleton is not guanranteed by pdU operations.
    -- we define a weaker property.
    -- all the partial derivative descendants in posix PDU must be sharing the same p, the partial derivative expression is the same.



    


pdU-NilOrSingleton : ∀ { r : RE } { c : Char }
  → NilSingleton pdU[ r  , c ]
pdU-NilOrSingleton {ε} {c} = isNil
pdU-NilOrSingleton {$ c ` loc} {c₁} with c Char.≟ c₁
... | no ¬c≡c₁ = isNil
... | yes c≡c₁ rewrite c≡c₁ = isSingleton
                              ( pdinstance {ε} {$ c₁ ` loc} {c₁} -- copied from PartialDerivative 
                                                 (λ u → LetterU {loc} c₁)
                                                 (λ EmptyU →                 -- ^ soundness ev
                                                   begin
                                                     [ c₁ ]
                                                    ≡⟨⟩
                                                     c₁ ∷ []
                                                    ≡⟨ cong ( λ x → ( c₁ ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                                                     c₁ ∷ (proj₁ (flat EmptyU))
                                                    ∎) )
pdU-NilOrSingleton {l + r ` loc} {c} = oplus-NilOrSingleton (List.map pdinstance-left pdU[ l , c ]) (List.map pdinstance-right pdU[ r , c ]) (map-NilOrSingleton ind-hyp-l) (map-NilOrSingleton ind-hyp-r)
  where
    ind-hyp-l :  NilSingleton pdU[ l  , c ]
    ind-hyp-l = pdU-NilOrSingleton {l} {c}
    ind-hyp-r :  NilSingleton pdU[ r  , c ]
    ind-hyp-r = pdU-NilOrSingleton {r} {c}    
    
pdU-NilOrSingleton {l ● r ` loc} {c} with ε∈? l
... | no ¬ε∈l = map-NilOrSingleton (pdU-NilOrSingleton {l} {c})
... | yes ε∈l = oplus-NilOrSingleton (List.map pdinstance-fst pdU[ l , c ]) ( concatmap-pdinstance-snd {l} {r} {ε∈l}   {loc} {c} pdU[ r , c ] ) (map-NilOrSingleton ind-hyp-l) (concatmap-pdinstance-snd-NilOrSingleton pdU[ r , c ] ind-hyp-r) 
  where
    ind-hyp-l :  NilSingleton pdU[ l  , c ]
    ind-hyp-l = pdU-NilOrSingleton {l} {c}
    ind-hyp-r :  NilSingleton pdU[ r  , c ]
    ind-hyp-r = pdU-NilOrSingleton {r} {c}
pdU-NilOrSingleton {r * ε∉r ` loc} {c} = map-NilOrSingleton ind-hyp-r
  where 
    ind-hyp-r :  NilSingleton pdU[ r  , c ]
    ind-hyp-r = pdU-NilOrSingleton {r} {c}




concatmap-advance-pdi*-with-c-NilOrSingleton : ∀ { r : RE } { pref : List Char } { c : Char }
  → (pdis : List (PDInstance* r pref))
  → NilSingleton pdis
  --------------------------------------
  → NilSingleton (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
concatmap-advance-pdi*-with-c-NilOrSingleton {r} {pref} {c} [] isNil = isNil
concatmap-advance-pdi*-with-c-NilOrSingleton {r} {pref} {c} (pdi@(pdinstance* {p} {r} {w} inj s-ev) ∷ []) (isSingleton .(pdi)) with pdU[ p , c ] | pdU-NilOrSingleton {p} {c} 
... | []         | isNil = isNil
... | qdi ∷ []  | isSingleton .(qdi) =  isSingleton (compose-pdi-with inj s-ev qdi)
  

pdUMany-aux-NilOrSingleton : ∀ { r : RE } { pref : List Char }
  → ( c : Char)
  → ( cs : List Char )
  → ( pdis : List (PDInstance*  r pref ) )
  → NilSingleton pdis
  -----------------------------------------
  → NilSingleton (pdUMany-aux (c ∷ cs) pdis)
pdUMany-aux-NilOrSingleton {r} {pref} c [] pdis nilorsingleton-pdis rewrite (++-identityʳ (pref ∷ʳ c) ) =  concatmap-advance-pdi*-with-c-NilOrSingleton pdis nilorsingleton-pdis
pdUMany-aux-NilOrSingleton {r} {pref} c (d ∷ cs) pdis nilorsingleton-pdis = pdUMany-aux-NilOrSingleton {r} {pref ∷ʳ c} d cs (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis) ( concatmap-advance-pdi*-with-c-NilOrSingleton pdis nilorsingleton-pdis ) 

pdUMany-NilOrSingleton : ∀ { r : RE } { w : List Char }
  → NilSingleton (pdUMany[ r , w ])
pdUMany-NilOrSingleton {r} {[]} = isSingleton
                                    (pdinstance* PartialDerivative.injId PartialDerivative.injId-sound)
pdUMany-NilOrSingleton {r} {c ∷ cs}  =  pdUMany-aux-NilOrSingleton {r} {[]} c cs  [ ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ] (isSingleton (pdinstance* (λ u → u) (λ u → refl)))    


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



concatMap-buildU-sorted : ∀ { r : RE } { w : List Char }
  → ( pdis : List (PDInstance* r w ) )
  → NilSingleton pdis
  → All *>-Inc pdis
  → >-sorted {r} (concatMap buildU pdis)
concatMap-buildU-sorted {r} {w} [] isNil [] =  >-nil
concatMap-buildU-sorted {r} {w} ((pdi@(pdinstance* {p} {r} inj s-ev)) ∷ []) (isSingleton .(pdi)) ((*>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) ∷ [])  with ε∈? p
... | no _ = >-nil
... | yes  ε∈p rewrite (++-identityʳ (List.map inj (mkAllEmptyU ε∈p))) =  map-inj-sorted (mkAllEmptyU ε∈p) inj u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ (mkAllEmptyU-sorted ε∈p)


parseAll-is-posix-sorted : ∀ { r : RE } { w : List Char }
  →  >-sorted {r} (parseAll[ r , w ])
parseAll-is-posix-sorted {r} {w} = concatMap-buildU-sorted pdUMany[ r , w ] pdUMany-NilOrSingleton pdUMany-*>-inc 

```

