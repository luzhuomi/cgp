This module contains the implementation of regular expression parsing algorithm by adapting Antimriov's original partial derivative operation with ... ?

```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.PartialDerivative where

import cgp.RE as RE
open RE using (RE ; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ;  ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ; first ;  ε∉r→¬first-r≡[]  )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ; flat-Uε≡[] ;   inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU;  unListU ; listU∘unListU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU  )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ;
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ;
  pdinstance-fst ;
  concatmap-pdinstance-snd ; 
  pdinstance-assoc ;
  compose-pdi-with 
  ) 

import cgp.Recons as Recons
open Recons using ( Recons ; recons ; 
  any-recons-left ; any-recons-right ;
  any-recons-fst ; any-recons-star ;
  any-recons-pdinstance-snd ;
  any-recons-concatmap-pdinstance-snd ;
  any-recons-assoc ;
  Recons* ; recons* ;
  compose-pdi-with-can-recons*
  )


import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; Flat-[] ; flat-[] ;  mkAllEmptyU≢[] )


import cgp.Utils as Utils
open Utils using (any-right-concat; any-left-concat ; all-concat ;  ∷-inj ; ¬∷≡[] ; inv-map-[] ; inv-concatMap-map-f-[]  )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_  )

import Data.List.Properties
open Data.List.Properties using ( ++-assoc  ; ++-identityʳ ; ++-identityˡ ; {-  unfold-reverse ; -} ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing ; map ; _>>=_  ) 

import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)

import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map)
open import Data.List.Relation.Unary.Any using (Any; here; there ; map)
import Data.List.Membership.Propositional
open Data.List.Membership.Propositional using (_∈_)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

import Relation.Nullary as Nullary 
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

open import Function using (_∘_ ; flip)

```

### Definition 15: Partial Derivative

We recall the partial derivative operaiton from [3]

pd(ϕ, ℓ) = {}   pd(ε, ℓ) = {}    pd(ℓ, ℓ) = {ε}    pd(ℓ', ℓ) = {}

pd(r₁ ● r₂ , ℓ ) = { r₁' ● r₂ ∣ r₁' ∈ pd( r₁ , ℓ ) } ∪ {  r₂' ∣ ε ∈ r₁ ∧ r₂' ∈ pd( r₂ , ℓ ) }

pd(r₁ + r₂ , ℓ ) = pd( r₁ , ℓ ) ∪ pd( r₂ , ℓ  )

pd(r* , ℓ ) = pd( r' ● r* ∣ r' ∈ pd( r , ℓ ) )


In parsing algorithm implementation, we replace { } by list [], ∪ by ++.
Since sets are unordered but lists are ordered, fixing an order means implementing a particular matching policy.

To enforce the posix ordering, we encode { } by singleton list, i.e Maybe. ∪ by ⊕

[] ⊕ [ r ] = [ r ]
[ r ] ⊕ [] = [ r ]
[ s ] ⊕ [ t ] = [ s + t ]




### A question: is ⊕ necessary? how does ⊕ give us posix ordering? can we enforce posix order without using ⊕ ?

Observation: the difference between ⊕ and ++ is that ⊕ merges two partial derivatives into a single partial derivative,
hence subsequently the use of r' ∈ pd( r , ℓ ) in the ● case and * case, we are dealing with just one r' instead of a sequence of r'.

### An Example

r = (a + b + a ● b)*                                        
w = ab


#### Using lne

Recall in lne parsing, we specialize the pd( r₁ ● r₂ , ℓ ) case as follows,

pd( r₁ ● r₂ , ℓ ) ｜ ¬ ε ∈ r₁ = { r₁' ● r₂ ∣ r₁' ∈ pd( r₁ , ℓ ) } 
pd( r₁ ● r₂ , ℓ ) ｜ ε ∈ r₁   =
  if r₁ ≡ s ● t
  then pd( s ● ( t ● r₂ ) )                -- (1)
  else { r₁' ● r₂ ∣ r₁' ∈ pd( r₁ , ℓ ) } ∪ pd( r₂ , ℓ )

Apply it to the above running example 

pd( r , a ) = [ r' ● r | r' ∈ pd( ( a + b) + a ● b, a ) ]
            = [ ε ● r , ε ● b ● r ]
            ∵ pd( (a + b) + a ● b, a ) =
              pd( a , a ) ++ pd( b , a ) ++ pd( a ● b , a ) =
              [ ε ] ++ [] ++ [ ε ● b ]
concatMap (λ x → pd( x , b )) [ ε ● r , ε ● b ● r ] = pd( ε ● r , b ) ++ pd( ε ● b ● r , b )
                                            = [ ε ● r ] ++ [ ε ● r ]  -- the first r has been unrolled again (in its 3rd iteration), while the 2nd r is stillin its 2nd iteration

#### Using ⊕ to replace all ++ 

i.e. the following two cases are replaced

pd(r₁ ● r₂ , ℓ ) = [ r₁' ● r₂ ∣ r₁' ∈ pd( r₁ , ℓ ) ]  ⊕ [  r₂' ∣ ε ∈ r₁ ∧ r₂' ∈ pd( r₂ , ℓ ) ] -- (1) 

pd(r₁ + r₂ , ℓ ) = pd( r₁ , ℓ ) ⊕ pd( r₂ , ℓ  ) -- (2)

we replace all ++ by ⊕, we don't apply associativity rule, so that the structure of the overall regular expression is respect. 

Apply the above to the running example 

pd( r , a ) = [ r' ● r | r' ∈ pd( ( a + b) + a ● b, a ) ]
            = [ ( ε + ε ● b ) ● r ]
            ∵ pd( (a + b) + a ● b, a ) =
              pd( a , a ) ⊕ pd( b , a ) ⊕ pd( a ● b , a ) =
              [ ε ] ⊕ []  ⊕ [ ε ● b ] = 
              [ ε + ε ● b ]
              
concatMap (λ x →  pd( x , b ) [ ( ε + ε ● b ) ● r ] = pd( ( ε + ε ● b ) ● r , b )
                                            = ( map ( λ p → p ● r ) pd( ε + ε ● b , b ) ) ⊕ pd( r , b ) 
                                            = (( map ( λ p → p ● r ) pd( ε , b ) ) ⊕ pd( ε ● b , b )) ⊕ pd( r , b )
                                            = (( map ( λ p → p ● r ) [ ε ] ) ⊕  pd( r , b )
                                            = [ ε ● r ] ⊕ pd( r , b ) -- the left r is not touched, i.e. still in the 2nd iteration.
                                            = [ ε ● r ] ⊕ [ ε ● r ]   -- the right r is in the 3nd iteration. thanks to the lne policy by default 
                                            

### An example 

ps  = let a₁ = $ 'a' ` 1
          b₂ = $ 'b' ` 2
          a+b = a₁ + b₂ ` 3 
          a₄ = $ 'a' ` 4
          b₅ = $ 'b' ` 5
          a●b = a₄ ● b₅ ` 6
          r = ( a+b + a●b ` 7 ) * (ε∉ (ε∉ ε∉$ + ε∉$ ) + (ε∉fst ε∉$) ) ` 8 
      in pd( r , 'a') >>= (λ p → pd( p , 'b') )


ps should be

just
((ε ●
  ((($ 'a' ` 1) + $ 'b' ` 2 ` 3) + ($ 'a' ` 4) ● $ 'b' ` 5 ` 6 ` 7) *
  ε∉ ε∉ ε∉$ + ε∉$ + ε∉fst ε∉$ ` 8
  ` 8)
 +
 ε ●
 ((($ 'a' ` 1) + $ 'b' ` 2 ` 3) + ($ 'a' ` 4) ● $ 'b' ` 5 ` 6 ` 7) *
 ε∉ ε∉ ε∉$ + ε∉$ + ε∉fst ε∉$ ` 8
 ` 8
 ` 8)


### a safe variant implementation of posix : using ⊕ only at + case, use ++ in the ● case.

In this variant, we do not replace the ++ in the r₁ ● r₂ case by ⊕, we only apply ⊕ to the +  case.

pd(r₁ + r₂ , ℓ ) = pd( r₁ , ℓ ) ⊕ pd( r₂ , ℓ  )

pd[ r , a ] = [ r' ● r | r' ∈ pd[ ( a + b) + a ● b, a ] ]
            = [ ( ε + ε ● b ) ● r ]
            ∵ pd[ (a + b) + a ● b, a ] =  
              pd[ a , a ] ⊕ pd[ b , a ] ⊕ pd[ a ● b , a ] =
              [ ε ] ⊕ []  ⊕ [ ε ● b ] = 
              [ ε + ε ● b ]

concatMap pd[ _ , b ] [ ( ε + ε ● b ) ● r ] = pd[ ( ε + ε ● b ) ● r , b ]
                                            = pdConcat ( ε + ε ● b ) r b
                                            = ( map ( λ p → p ● r ) pd[ ε + ε ● b , b ] ) ++ pd[ r , b ] -- not using ⊕ here
                                            = ( map ( λ p → p ● r ) pd[ ε , b ] ⊕  pd[ ε ● b , b ]) ++ pd[ r , b ]
                                            = ( map ( λ p → p ● r ) [ ε ] ) ++ pd[ r , b ]
                                            = [ ε ● r ] ++ pd[ r , b ] -- the left r is not touched, i.e. still in the 2nd iteration.
                                            = [ ε ● r , ε ● r ]        -- the right r is in the 3rd iteration. thanks to the lne policy by default 


```agda
-- a version that use list (mostly singleton) to implement { }
-- and ⊕ to replace the ∪ in the + case.

_⊕_`_ : List RE → List RE → ℕ →  List RE
_⊕_`_ [] rs loc = rs
_⊕_`_ rs [] loc = rs
_⊕_`_ rs ts loc = concatMap ( λ r → List.map (λ t → (r + t ` loc)) ts ) rs 


pd[_,_] : RE →  Char → List RE
pdConcat : ( l : RE ) → ( r : RE ) → ( ε∈l : ε∈ l ) → ( loc : ℕ ) → ( c : Char ) → List RE

pd[ ε , c ]    = []
pd[ $ c ` loc  , c' ] with c Char.≟ c'
...                      | yes refl = [ ε ] 
...                      | no  _    = [] 
pd[ l ● r ` loc , c ] with ε∈? l
...                      | yes ε∈l  = pdConcat  l r ε∈l loc c
...                      | no ¬ε∈l  = List.map (λ l' → l' ● r ` loc ) pd[ l , c ]
pd[ l + r ` loc , c ]               = pd[ l , c ] ⊕  pd[ r , c ] ` loc 
pd[ r * nε ` loc , c ]              = List.map (λ r' → r' ● ( r * nε ` loc ) ` loc ) pd[ r , c ]
{-# TERMINATING #-}
-- it seems to me that the ⊕ in pdConcat cases is unnecessary.
pdConcat ε  r  ε∈ε loc c  = pd[ r  , c ]
pdConcat (l * ε∉l ` loc₂ ) r ε∈*             loc c = (List.map (λ l' → l' ● r ` loc ) pd[ l * ε∉l ` loc₂ , c ] ) ++ pd[ r , c ]
-- we don't apply assoc rule to rewrite (l ● s ) ● r into l ● (s ● r), so that we can retain the structure left-most-longest property globally
pdConcat (l ● s ` loc₂ )   r (ε∈ ε∈l ● ε∈s)  loc c = (List.map (λ p → p ● r ` loc ) pd[ l ● s ` loc₂ , c ]) ++ pd[ r , c ]  
pdConcat (l + s ` loc₂ )   r (ε∈l+s)         loc c = (List.map (λ p → p ● r ` loc ) pd[ l + s ` loc₂ , c ]) ++ pd[ r , c ]

```

#### Note : a possible simple algorithm

the above cases for pdConcat can be combined into one
for the ease of reusing the sub lemmas from lne and greedy parsing, let's keep the above for the time being.

pdConcat l  r (ε∈l)         loc c = (List.map (λ p → p ● r ` loc ) pd[ l , c ]) ++ pd[ r , c ]


```agda

ps  = let a₁ = $ 'a' ` 1
          b₂ = $ 'b' ` 2
          a+b = a₁ + b₂ ` 3 
          a₄ = $ 'a' ` 4
          b₅ = $ 'b' ` 5
          a●b = a₄ ● b₅ ` 6
          r = ( a+b + a●b ` 7 ) * (ε∉ (ε∉ ε∉$ + ε∉$ ) + (ε∉fst ε∉$) ) ` 8 
      in concatMap (λ p → pd[ p , 'b'] ) pd[ r , 'a']

```
ps should be

((ε ●
  ((($ 'a' ` 1) + $ 'b' ` 2 ` 3) + ($ 'a' ` 4) ● $ 'b' ` 5 ` 6 ` 7) *
  ε∉ ε∉ ε∉$ + ε∉$ + ε∉fst ε∉$ ` 8
  ` 8)
 +
 ε ●
 ((($ 'a' ` 1) + $ 'b' ` 2 ` 3) + ($ 'a' ` 4) ● $ 'b' ` 5 ` 6 ` 7) *
 ε∉ ε∉ ε∉$ + ε∉$ + ε∉fst ε∉$ ` 8
 ` 8
 ` 7)
∷ []


### pdU definition 


Note that the pdU function (at its sub functions) operates over the List functor instead of Maybe.
The reason is that one partial derivative instance might be associated with more than one coercion functions.
This is because there might be more than one empty parse trees given the partial derivative is nullable. 

### Example

r = ( ε + ε ) ● a 
pd[ r , a ] = [ ε ]

mkAllEmpty ( ε + ε ) = [ LeftU EmptyU , RightU EmptyU ]

for simplicity, we omit the soundness evidence

pdi[ r , a ] = concatMap (λ e → pdinstance-snd e  pd[ a , a ] )  [ LeftU EmptyU , RightU EmptyU ] 
             = concatMap (λ e → pdinstance-snd e  [ pdinstance {ε} {a} (λ _ → a ) ] )  [ LeftU EmptyU , RightU EmptyU ]
             = concatMap (λ e → map (mk-snd-pdi e)  [ pdinstance {ε} {a} (λ _ → a ) ] )  [ LeftU EmptyU , RightU EmptyU ]
             = [ pdinstance {ε} {r} (λ u → PairU (LeftU EmptyU) ((λ _ →  a) u) ) ,
                 pdinstance {ε} {r} (λ u → PairU (RightU EmptyU) ((λ _ →  a) u) ) ]


overall we still need to operate over a list of pdinstances instead of maybe pdinstance. 

```agda
-- ^ applying parse tree constructors to coercion records (namely, the injection function and the soundness evidence)

{-
fuse : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → PDInstance (l + r ` loc) c
  → PDInstance (l + r ` loc) c
  → PDInstance (l + r ` loc) c
fuse {l} {r} {loc} {c} (pdinstance {pˡ} {l+r} {_} inj-l s-ev-l) (pdinstance {pᵣ} {l+r} {_} inj-r s-ev-r) = 
        (pdinstance {pˡ + pᵣ ` loc} {l+r} {c} inj sound-ev )
     where
       inj : U (pˡ + pᵣ ` loc ) → U ( l + r ` loc )
       inj (LeftU v₁) = inj-l v₁
       inj (RightU v₂) = inj-r v₂ 
       sound-ev : (u : U (pˡ + pᵣ ` loc)) 
                   → proj₁ (flat (inj u))  ≡ c ∷ proj₁ (flat u)
       sound-ev (LeftU v₁) = s-ev-l v₁
       sound-ev (RightU v₂) = s-ev-r v₂


pdinstance-oplus : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → List (PDInstance (l + r ` loc) c)
  → List (PDInstance (l + r ` loc) c)
  → List (PDInstance (l + r ` loc) c)
pdinstance-oplus {l} {r} {loc} {c} []     pdis  = pdis
pdinstance-oplus {l} {r} {loc} {c} pdis   []    = pdis
pdinstance-oplus {l} {r} {loc} {c} pdisˡ  pdisᵣ =  concatMap (λ pdiˡ → List.map (fuse pdiˡ) pdisᵣ) pdisˡ
-}


fuse : ∀ { r : RE } { loc : ℕ } { c : Char } 
  → PDInstance r c
  → PDInstance r c
  → PDInstance r c
fuse {r} {loc} {c} (pdinstance {pˡ} {r} {_} inj-l s-ev-l) (pdinstance {pʳ} {r} {_} inj-r s-ev-r) = 
        (pdinstance {pˡ + pʳ ` loc} {r} {c} inj sound-ev )
     where
       inj : U (pˡ + pʳ ` loc ) → U r
       inj (LeftU v₁) = inj-l v₁
       inj (RightU v₂) = inj-r v₂ 
       sound-ev : (u : U (pˡ + pʳ ` loc)) 
                   → proj₁ (flat (inj u))  ≡ c ∷ proj₁ (flat u)
       sound-ev (LeftU v₁) = s-ev-l v₁
       sound-ev (RightU v₂) = s-ev-r v₂


pdinstance-oplus : ∀ { r : RE } { loc : ℕ } { c : Char }
  → List (PDInstance r c)
  → List (PDInstance r c)
  → List (PDInstance r c)
pdinstance-oplus {r} {loc} {c} []     pdisʳ  = pdisʳ
pdinstance-oplus {r} {loc} {c} pdisˡ  []     = pdisˡ
pdinstance-oplus {r} {loc} {c} pdisˡ  pdisʳ  =  concatMap (λ pdiˡ → List.map (fuse {r} {loc} {c}  pdiˡ) pdisʳ) pdisˡ 

 

      


---------------------------------------------------------------------------------------------------
-- pdU[_,_] and pdUConcat

pdU[_,_] : ( r : RE ) → ( c : Char ) → List (PDInstance r c)
pdUConcat : ( l r : RE ) → ( ε∈l : ε∈ l ) → ( loc : ℕ ) → ( c : Char ) → List (PDInstance (l ● r ` loc ) c)


pdU[ ε , c ] = []
pdU[ $ c ` loc , c' ] with c Char.≟ c'
...                     | yes refl = [ ( pdinstance {ε} {$ c ` loc} {c}
                                                 (λ u → LetterU {loc} c)
                                                 (λ EmptyU →                 -- ^ soundness ev
                                                   begin
                                                     [ c ]
                                                    ≡⟨⟩
                                                     c ∷ []
                                                    ≡⟨ cong ( λ x → ( c ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                                                     c ∷ (proj₁ (flat EmptyU))
                                                    ∎) ) ]
...                     | no _    =  []
pdU[ l + r ` loc , c ]  =
  pdinstance-oplus -- oplus is needed, otherwise posix is violated, refer to posix-test-r₁ example below
    { l + r ` loc } {loc} {c} 
    ( List.map pdinstance-left pdU[ l , c ] )
    ( List.map pdinstance-right pdU[ r , c ])
pdU[ r * nε ` loc , c ] =
  List.map pdinstance-star pdU[ r , c ]
pdU[ l ● r ` loc , c ] with ε∈? l
...                       | no ¬ε∈l = List.map pdinstance-fst  pdU[ l , c ]
...                       | yes ε∈l = pdUConcat l r ε∈l loc c 

{-# TERMINATING #-}
pdUConcat ε r ε∈ε loc c                    = concatmap-pdinstance-snd {ε}              {r} {ε∈ε}   {loc} {c} pdU[ r , c ]
pdUConcat (l * ε∉l ` loc₁)  r ε∈*   loc₂ c =
  ( List.map pdinstance-fst pdU[ (l * ε∉l ` loc₁) , c ] )
  ++ -- no need oplus?  seems so, because of  ε∉l 
  concatmap-pdinstance-snd {l * ε∉l ` loc₁} {r} {ε∈*}   {loc₂} {c} pdU[ r , c ]
pdUConcat (l ● s ` loc₁)    r ε∈l●s loc₂ c =
  -- to implement posix, we need to retain the structure, we don't apply assoc rule. 
  -- List.map pdinstance-assoc pdU[ ( l ● ( s ● r ` loc₂ ) ` loc₁ ) , c ]
  ( List.map pdinstance-fst pdU[ (l ● s ` loc₁) , c ] )
  ++ -- no need oplus ? 
   concatmap-pdinstance-snd {l ● s ` loc₁}   {r} {ε∈l●s} {loc₂} {c} pdU[ r , c ]

pdUConcat (l + s ` loc₁)    r ε∈l+s loc₂ c =
  {-
  ( List.map pdinstance-fst pdU[ (l + s ` loc₁) , c ] )
  ++ 
   concatmap-pdinstance-snd {l + s ` loc₁}   {r} {ε∈l+s} {loc₂} {c} pdU[ r , c ]
  -}
  -- oplus is needed, otherwise posix is violated , refer to refer to posix-test-r₂ example below
  pdinstance-oplus
    { ( l + s ` loc₁ ) ● r ` loc₂ }  {loc₂} {c}
    ( List.map pdinstance-fst pdU[ (l + s ` loc₁) , c ] )
    ( concatmap-pdinstance-snd {l + s ` loc₁}   {r} {ε∈l+s} {loc₂} {c} pdU[ r , c ] )
```


### Lemma 17: pdU[_,_] is sound.

Let r be a non problematic regular expression.
Let c be a letter.
Let p be a partial derivative of r w.r.t c, i.e. p ∈ pd[r , c]
Let f be the injection function from parse tree of p to parse tree of r.
Let u be a parse tree of p, then |(f u)| = c ∷ | u |, where (f u) is a parse tree of r.
( in agda terms,  proj₁ (flat {r} (f u)) ≡ c ∷ (proj₁ (flat {p} u)) ). 


The proof is given as part of the PDInstance being computed. 


### Definition 18 (Reconstructability):
Let r be a non problematic regular expression.
Let c be a character.
Let u be a parse tree of r.
Let pdi be a partial derivative (instance) of r w.r.t c,
such that pdi = { p , inj , sound-ev }
  where
    1. p is the partial derivative instance of p/c;
    2. inj is the injection function from parse tree of p back to parse tree of r;
    3. sound-ev is the soundness evidence pdi
Then we say pdi is u-reconstructable w.r.t c iff there exists a word w ∈ ⟦p⟧ such that inj (unflat w∈p) ≡ u.


definition of Recons is moved to Recons.lagda.md



### Lemma 19: pdU[_,_] is complete. 

Let r be a non problematic regular expression.
Let c be a letter.
Let u be a parse tree of r such that (flat u) = c ∷ w for some word w.      
Then there exists a partial derivative instance, pdi ∈ pdU[r,c] , such that
pdi is u-reconstruable w.r.t c.



To prove Lemma 19, we need to prove some sub lemmas. 
The sub lemmas (properties of pdinstance-reconstructabilities) are found in Recons.lagda.md. 



```agda
any-recons-oplus-left : ∀ { r : RE } { loc : ℕ } { c : Char } { w : List Char } { u : U r }
    → ( pdisˡ : List (PDInstance r c))
    → ( pdisʳ : List (PDInstance r c)) 
    → Any (Recons {r} {c} u) pdisˡ
    → Any (Recons {r} {c} u) (pdinstance-oplus {r} {loc} {c} pdisˡ pdisʳ)
any-recons-oplus-left {r} {loc} {c} {w} {u} []              pdisʳ any-recons-left-pdis = Nullary.contradiction any-recons-left-pdis ¬Any[]
any-recons-oplus-left {r} {loc} {c} {w} {u} (pdiˡ ∷ pdisˡ) []    any-recons-left-pdis = any-recons-left-pdis
any-recons-oplus-left {r} {loc} {c} {w} {u} (pdiˡ ∷ pdisˡ) (pdiʳ ∷ pdisʳ)  any-recons-left-pdis = prf  (pdiˡ ∷ pdisˡ) any-recons-left-pdis 
  where
    prf : ∀ ( pdis : List (PDInstance r c))
          → Any (Recons {r} {c} u) pdis
          → Any (Recons u) (concatMap (λ x → List.map (fuse {r} {loc} {c} x) (pdiʳ ∷ pdisʳ)) pdis)
    prf []  any-recons-left-pdis =  Nullary.contradiction any-recons-left-pdis ¬Any[]
    prf ( pdi ∷ pdis ) (there pxs) = any-right-concat ind-hyp  
      where
        ind-hyp :  Any (Recons u) (concatMap (λ x → List.map (fuse {r} {loc} {c} x) (pdiʳ ∷ pdisʳ)) pdis)
        ind-hyp = prf pdis pxs
    prf ( pdi ∷ pdis ) (here (recons {p} {r} {c} {w} {inj} {s-ev} u ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡u ) )) = any-left-concat (sub-prf pdiʳ pdisʳ)
      where
        sub-prf : (pdiʳ : (PDInstance r c))
            → (pdisʳ : List (PDInstance r c))
            → Any (Recons u) (List.map (fuse {r} {loc} {c} (pdinstance inj s-ev)) (pdiʳ ∷ pdisʳ))
        sub-prf (pdinstance {pʳ} {r} {_} injᵣ s-evᵣ) pdisʳ = here (recons { p + pʳ ` loc } {r} {c} {w} u ((pʳ +L w∈⟦p⟧) , inj-unflat-w∈⟦p⟧≡u) ) 


any-recons-oplus-right : ∀ { r : RE } { loc : ℕ } { c : Char } { w : List Char } { u : U r }
    → ( pdisˡ : List (PDInstance r c))
    → ( pdisʳ : List (PDInstance r c)) 
    → Any (Recons {r} {c} u) pdisʳ
    → Any (Recons {r} {c} u) (pdinstance-oplus {r} {loc} {c} pdisˡ pdisʳ)
any-recons-oplus-right {r} {loc} {c} {w} {u} pdisˡ  []             any-recons-right-pdis = Nullary.contradiction any-recons-right-pdis ¬Any[]
any-recons-oplus-right {r} {loc} {c} {w} {u} []     (pdiʳ ∷ pdisʳ) any-recons-right-pdis = any-recons-right-pdis 
any-recons-oplus-right {r} {loc} {c} {w} {u} (pdiˡ@(pdinstance {pˡ} {r} {_} injˡ s-ev-l) ∷ pdisˡ) (pdiʳ ∷ pdisʳ)  any-recons-right-pdis = prf  (pdiʳ ∷ pdisʳ) any-recons-right-pdis
  where 
    prf : ∀ ( pdis : List (PDInstance r c))
          → Any (Recons {r} {c} u) pdis
          → Any (Recons u) (concatMap (λ x → List.map (fuse {r} {loc} {c} x) pdis) ((pdinstance {pˡ} {r} {c} injˡ s-ev-l) ∷ pdisˡ))
    prf pdis  any-recons-right-pdis  = any-left-concat (sub-prf  pdis  any-recons-right-pdis )
      where
        sub-prf : ∀ ( pdis : List (PDInstance r c))
          → Any (Recons {r} {c} u) pdis
          → Any (Recons u) (List.map (fuse {r} {loc} {c} (pdinstance injˡ s-ev-l)) pdis)
        sub-prf [] any-recons-right-pdis =  Nullary.contradiction any-recons-right-pdis ¬Any[]
        sub-prf (pdi ∷ pdis) (there pxs) = there (sub-prf pdis pxs)
        sub-prf (pdi ∷ pdis) (here (recons {p} {r} {_} {w} {inj-r} {s-ev-r} _ ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡u ) )) =
          here (recons { pˡ + p ` loc } {r} {c} {w}  u ( (pˡ +R w∈⟦p⟧)  , inj-unflat-w∈⟦p⟧≡u )) 
```

#### Main proof for Lemma 19

it only defers from the lne parsing in the "l + r" choice case of pdU (thanks to the use of ⊕ ), the rest of the cases are the same


```agda
pdU-complete : ∀ { r : RE  } { c : Char } { w : List Char }
  → ( u : U r )  
  → ( proj₁ (flat {r} u) ≡ c ∷ w )
  → Any (Recons {r} {c} u) pdU[ r , c ]

pdUConcat-complete : ∀ { l s : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char } { w : List Char }
    → ( u : U l )
    → ( v : U s ) 
    → ( proj₁ (flat { l ● s ` loc } (PairU u v)) ≡ c ∷ w )
    → Any (Recons { l ● s ` loc } (PairU u v)) (pdUConcat l s ε∈l loc c)

pdU-complete {ε}           {c}  {w} EmptyU = λ()
pdU-complete {$ c ` loc}   {c'} {w} (LetterU _) with c Char.≟ c'
...                                              | yes refl with w    
...                                                           |  []  = λ proj1-flat-u≡[] →  here (recons (LetterU c) (ε , refl))
pdU-complete {$ c ` loc}   {c'} {w} (LetterU c₂) | no  ¬c≡c'  = λ c∷[]≡c'w →  Nullary.contradiction (proj₁ (∷-inj c∷[]≡c'w)) ¬c≡c' 
pdU-complete {l + s ` loc} {c}  {w} (LeftU u)  proj1-flat-leftu≡cw = any-recons-oplus-left {l + s ` loc } {loc} {c} {w} {LeftU u} (List.map pdinstance-left pdU[ l , c ]) (List.map pdinstance-right pdU[ s , c ]) ys 
  where
    xs : Any (Recons {l} {c} u) pdU[ l , c ]
    xs =  pdU-complete {l} {c} u proj1-flat-leftu≡cw
    ys : Any (Recons { l + s ` loc} {c} (LeftU u)) (List.map pdinstance-left pdU[ l , c ])
    ys =  any-recons-left {l} {s} {loc} {c}  {w} {u} pdU[ l , c ]  xs
pdU-complete {l + s ` loc} {c}  {w} (RightU u)  proj1-flat-rightu≡cw = any-recons-oplus-right {l + s ` loc} {loc} {c} {w} {RightU u} (List.map pdinstance-left pdU[ l , c ]) (List.map pdinstance-right pdU[ s , c ]) ys
  where
    xs : Any (Recons {s} {c} u) pdU[ s , c ]
    xs =  pdU-complete {s} {c} u proj1-flat-rightu≡cw
    ys : Any (Recons { l + s ` loc} {c} (RightU u)) (List.map pdinstance-right pdU[ s , c ])
    ys =  any-recons-right {l} {s} {loc} {c}  {w} {u} pdU[ s , c ]  xs
pdU-complete {l * ε∉l ` loc} {c} {w} (ListU (u ∷ us)) proj1-flat-u∷us≡cw  = bs
  where
    e1-e2-e3 : ∃[ xs ] ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs ) × ( proj₁ (flat (ListU us)) ≡ ys ) × ( xs ++ ys ≡ w ) 
    e1-e2-e3 = inv-flat-star {l} {ε∉l} {loc} {u} {us} {c} {w} proj1-flat-u∷us≡cw   
    xs               = proj₁ e1-e2-e3
    proj1-flat-u≡cxs = proj₁ (proj₂ (proj₂ e1-e2-e3))
    as : Any (Recons {l} {c} u) pdU[ l , c ] 
    as = pdU-complete {l} {c} {xs} u proj1-flat-u≡cxs 
    bs : Any (Recons {l * ε∉l ` loc } {c} (ListU (u ∷ us))) (List.map pdinstance-star pdU[ l , c ])
    bs = any-recons-star {l} {ε∉l} {loc} {c} {w} {u} {us} pdU[ l , c ] as     
pdU-complete {l ● s ` loc} {c}  {w} (PairU u v) proj1-flat-pair-u-v≡cw with ε∈? l   
pdU-complete {l ● s ` loc} {c}  {w} (PairU u v) proj1-flat-pair-u-v≡cw    | no ¬ε∈l  =  ys
  where
    e1-e2-e3 : ∃[ cs ] ∃[ cs' ] (proj₁ (flat u) ≡ c ∷ cs) × (proj₁ (flat v) ≡ cs') × ( cs ++ cs' ≡ w )
    e1-e2-e3 = inv-flat-pair-fst {l} {s} {¬ε∈l} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw
    e1 : ∃[ cs ] (proj₁ (flat u) ≡ c ∷ cs)
    e1 = ( proj₁ e1-e2-e3 , ( proj₁ ∘ proj₂ ∘ proj₂ ) e1-e2-e3 )
    xs : Any (Recons {l} {c} u) pdU[ l , c ]
    xs  = pdU-complete {l} {c} {proj₁ e1} u (proj₂ e1)   
    ys : Any (Recons { l ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l , c ])
    ys = any-recons-fst {l} {s} {loc} {c} {w} {u} {v} pdU[ l , c ] xs 
 
pdU-complete {l ● s ` loc} {c}  {w} (PairU u v) proj1-flat-pair-u-v≡cw       | yes ε∈l  =  pdUConcat-complete {l} {s} {ε∈l} {loc} {c} {w} u v  proj1-flat-pair-u-v≡cw


{-# TERMINATING #-}    
pdUConcat-complete {ε} {s} {ε∈ε} {loc} {c} {w} u@EmptyU v proj1-flat-pair-u-v≡cw  = prove e1-e2-e3 
  where
    e1-e2-e3 :  ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) 
              ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) ) 
    e1-e2-e3 = inv-flat-pair-snd {ε} {s} {ε∈ε} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw 
    prove : ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) )
           → Any (Recons {ε ● s ` loc} {c} (PairU u v)) (List.map (pdinstance-fst {ε} {s} {loc} {c}) pdU[ ε , c ] ++ (concatmap-pdinstance-snd {ε} {s} {ε∈ε} {loc} {c} pdU[ s , c ])) 
    prove (inj₂ ( xs , ys , proj1-flat-u≡cxs , proj1-flat-v≡ys , refl ) )  = any-left-concat bs
      where 
        as : Any (Recons {ε} {c} u) pdU[ ε , c ]
        as = pdU-complete {ε} {c} {xs} u proj1-flat-u≡cxs   
        bs : Any (Recons { ε ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ ε , c ])
        bs = any-recons-fst {ε} {s} {loc} {c} {w} {u} {v} pdU[ ε , c ] as 
    prove (inj₁ ( ys , proj1-flat-u≡[] , proj1-flat-v≡cys , refl ) ) = any-right-concat {PDInstance (ε ● s ` loc) c} {(Recons { ε ● s ` loc} {c} (PairU u v))} {(List.map pdinstance-fst pdU[ ε , c ])}  bs
      where 
        as : Any (Recons {s} {c} v) pdU[ s , c ] 
        as = pdU-complete {s} {c} {ys} v proj1-flat-v≡cys
        bs : Any (Recons { ε ● s ` loc} {c} (PairU u v)) (concatmap-pdinstance-snd {ε} {s} {ε∈ε} {loc} {c} pdU[ s , c ]) 
        bs = any-recons-concatmap-pdinstance-snd {ε} {s} {ε∈ε} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdU[ s , c ] as


pdUConcat-complete {l * ε∉l ` loc₁} {s} {ε∈*} {loc} {c} {w} u@(ListU us) v proj1-flat-pair-u-v≡cw  = prove e1-e2-e3 
  where
    e1-e2-e3 :  ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) 
              ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) ) 
    e1-e2-e3 = inv-flat-pair-snd {l * ε∉l ` loc₁} {s} {ε∈*} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw 
    prove : ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) )
           → Any (Recons {(l * ε∉l ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l * ε∉l ` loc₁ , c ] ++ (concatmap-pdinstance-snd  {l * ε∉l ` loc₁} {s} {ε∈*} {loc} {c}   pdU[ s , c ])) 
    prove (inj₂ ( xs , ys , proj1-flat-u≡cxs , proj1-flat-v≡ys , refl ) )  = any-left-concat bs
      where 
        as : Any (Recons {l * ε∉l ` loc₁} {c} u) pdU[ l * ε∉l ` loc₁ , c ]
        as = pdU-complete {l * ε∉l ` loc₁} {c} {xs} u proj1-flat-u≡cxs   
        bs : Any (Recons { (l * ε∉l ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l * ε∉l ` loc₁ , c ])
        bs = any-recons-fst {l * ε∉l ` loc₁} {s} {loc} {c} {w} {u} {v} pdU[ l * ε∉l ` loc₁ , c ] as 
    prove (inj₁ ( ys , proj1-flat-u≡[] , proj1-flat-v≡cys , refl ) ) = any-right-concat  {PDInstance ( (l * ε∉l ` loc₁) ● s ` loc) c} {(Recons { (l * ε∉l ` loc₁)  ● s ` loc} {c} (PairU u v))} {(List.map pdinstance-fst pdU[ l * ε∉l ` loc₁ , c ])}  bs
      where 
        as : Any (Recons {s} {c} v) pdU[ s , c ] 
        as = pdU-complete {s} {c} {ys} v proj1-flat-v≡cys
        bs : Any (Recons { (l * ε∉l ` loc₁) ● s ` loc} {c} (PairU u v)) (concatmap-pdinstance-snd {l * ε∉l ` loc₁} {s} {ε∈*} {loc} {c} pdU[ s , c ]) 
        bs = any-recons-concatmap-pdinstance-snd {l * ε∉l ` loc₁} {s} {ε∈*} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdU[ s , c ] as
{-
pdUConcat-complete {l ● t ` loc₁} {s} {ε∈l●t} {loc} {c} {w} u@(PairU u₁ u₂) v proj1-flat-pair-u-v≡cw  = any-recons-assoc {l} {t} {s} {loc₁} {loc} {c} {w} {u₁} {u₂} {v}  pdU[ l ● (t ● s ` loc) ` loc₁ , c ] xs  
  where
    proj₁-flat-pair-u₁-pair-u₂-v≡cw : proj₁ (flat (PairU {l} { t ● s ` loc } {loc₁} u₁ (PairU u₂ v))) ≡ c ∷ w
    proj₁-flat-pair-u₁-pair-u₂-v≡cw with flat u₁   | flat u₂     | flat v
    ... | w₁ , w₁∈⟦l⟧ | w₂ , w₂∈⟦t⟧  | w₃ , w₃∈⟦s⟧ rewrite ++-assoc w₁ w₂ w₃ = proj1-flat-pair-u-v≡cw
    
    xs : Any (Recons {l ● (t ● s ` loc) ` loc₁} {c} (PairU u₁ (PairU u₂ v))) pdU[ l ● (t ● s ` loc) ` loc₁ , c ]
    xs  = pdU-complete {l ● (t ● s ` loc) ` loc₁} {c} {w}  (PairU u₁ (PairU u₂ v)) proj₁-flat-pair-u₁-pair-u₂-v≡cw 
-}
pdUConcat-complete {l ● t ` loc₁} {s} {ε∈l●t} {loc} {c} {w} u@(PairU u₁ u₂) v proj1-flat-pair-u-v≡cw  = prove e1-e2-e3
  where
    e1-e2-e3 :  ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) 
              ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) ) 
    e1-e2-e3 = inv-flat-pair-snd {l ● t ` loc₁} {s} {ε∈l●t} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw 
    prove : ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) )
           → Any (Recons {(l ● t ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l ● t ` loc₁ , c ] ++ (concatmap-pdinstance-snd  {l ● t ` loc₁} {s} {ε∈l●t} {loc} {c}   pdU[ s , c ])) 
    prove (inj₂ ( xs , ys , proj1-flat-u≡cxs , proj1-flat-v≡ys , refl ) )  = any-left-concat bs
      where 
        as : Any (Recons {l ● t ` loc₁} {c} u) pdU[ l ● t ` loc₁ , c ]
        as = pdU-complete {l ● t ` loc₁} {c} {xs} u proj1-flat-u≡cxs   
        bs : Any (Recons { (l ● t ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l ● t ` loc₁ , c ])
        bs = any-recons-fst {l ● t ` loc₁} {s} {loc} {c} {w} {u} {v} pdU[ l ● t ` loc₁ , c ] as 
    prove (inj₁ ( ys , proj1-flat-u≡[] , proj1-flat-v≡cys , refl ) ) = any-right-concat  {PDInstance ( (l ● t ` loc₁) ● s ` loc) c} {(Recons { (l ● t ` loc₁)  ● s ` loc} {c} (PairU u v))} {(List.map pdinstance-fst pdU[ l ● t ` loc₁ , c ])}  bs
      where 
        as : Any (Recons {s} {c} v) pdU[ s , c ] 
        as = pdU-complete {s} {c} {ys} v proj1-flat-v≡cys
        bs : Any (Recons { (l ● t ` loc₁) ● s ` loc} {c} (PairU u v)) (concatmap-pdinstance-snd {l ● t ` loc₁} {s} {ε∈l●t} {loc} {c} pdU[ s , c ]) 
        bs = any-recons-concatmap-pdinstance-snd {l ● t ` loc₁} {s} {ε∈l●t} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdU[ s , c ] as
{-
-- the version not using oplus 
pdUConcat-complete {l + t ` loc₁} {s} {ε∈l+t} {loc} {c} {w} u v proj1-flat-pair-u-v≡cw  = prove e1-e2-e3 
  where
    e1-e2-e3 :  ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) 
              ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) ) 
    e1-e2-e3 = inv-flat-pair-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw 
    prove : ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) )
           → Any (Recons {(l + t ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l + t ` loc₁ , c ] ++ (concatmap-pdinstance-snd  {l + t ` loc₁} {s} {ε∈l+t} {loc} {c}   pdU[ s , c ])) 
    prove (inj₂ ( xs , ys , proj1-flat-u≡cxs , proj1-flat-v≡ys , refl ) )  = any-left-concat bs
      where 
        as : Any (Recons {l + t ` loc₁} {c} u) pdU[ l + t ` loc₁ , c ]
        as = pdU-complete {l + t ` loc₁} {c} {xs} u proj1-flat-u≡cxs   
        bs : Any (Recons { (l + t ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l + t ` loc₁ , c ])
        bs = any-recons-fst {l + t ` loc₁} {s} {loc} {c} {w} {u} {v} pdU[ l + t ` loc₁ , c ] as 
    prove (inj₁ ( ys , proj1-flat-u≡[] , proj1-flat-v≡cys , refl ) ) = any-right-concat  {PDInstance ( (l + t ` loc₁) ● s ` loc) c} {(Recons { (l + t ` loc₁)  ● s ` loc} {c} (PairU u v))} {(List.map pdinstance-fst pdU[ l + t ` loc₁ , c ])}  bs
      where 
        as : Any (Recons {s} {c} v) pdU[ s , c ] 
        as = pdU-complete {s} {c} {ys} v proj1-flat-v≡cys
        bs : Any (Recons { (l + t ` loc₁) ● s ` loc} {c} (PairU u v)) (concatmap-pdinstance-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {c} pdU[ s , c ]) 
        bs = any-recons-concatmap-pdinstance-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdU[ s , c ] as
-}
pdUConcat-complete  {l + t ` loc₁} {s} {ε∈l+t} {loc} {c} {w} u v proj1-flat-pair-u-v≡cw  = prove e1-e2-e3 
  where
    e1-e2-e3 :  ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) 
              ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) ) 
    e1-e2-e3 = inv-flat-pair-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw 
    prove : ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) )
           → Any (Recons {(l + t ` loc₁) ● s ` loc} {c} (PairU u v))
                         (pdinstance-oplus  {(l + t ` loc₁) ● s ` loc} {loc} (List.map pdinstance-fst
                                                     (pdinstance-oplus {l + t ` loc₁} {loc₁} (List.map pdinstance-left pdU[ l , c ])
                                                                                             (List.map pdinstance-right pdU[ t , c ])))
                                           (concatmap-pdinstance-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {c}  pdU[ s , c ]))
    prove (inj₂ ( xs , ys , proj1-flat-u≡cxs , proj1-flat-v≡ys , refl ) ) =
      any-recons-oplus-left {(l + t ` loc₁) ● s ` loc} {loc} {c} {w} {PairU u v}
                            (List.map pdinstance-fst
                                      (pdinstance-oplus {l + t ` loc₁} {loc₁} (List.map pdinstance-left pdU[ l , c ])
                                                                              (List.map pdinstance-right pdU[ t , c ])))
                            (concatmap-pdinstance-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {c}  pdU[ s , c ]) bs
      where 
        as : Any (Recons {l + t ` loc₁} {c} u) pdU[ l + t ` loc₁ , c ]
        as = pdU-complete {l + t ` loc₁} {c} {xs} u proj1-flat-u≡cxs   
        bs : Any (Recons { (l + t ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l + t ` loc₁ , c ])
        bs = any-recons-fst {l + t ` loc₁} {s} {loc} {c} {w} {u} {v} pdU[ l + t ` loc₁ , c ] as 
    prove (inj₁ ( ys , proj1-flat-u≡[] , proj1-flat-v≡cys , refl ) ) =
      any-recons-oplus-right {(l + t ` loc₁) ● s ` loc} {loc} {c} {w} {PairU u v}
                            (List.map pdinstance-fst
                                      (pdinstance-oplus {l + t ` loc₁} {loc₁} (List.map pdinstance-left pdU[ l , c ])
                                                                              (List.map pdinstance-right pdU[ t , c ])))
                            (concatmap-pdinstance-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {c}  pdU[ s , c ]) bs 
      where 
        as : Any (Recons {s} {c} v) pdU[ s , c ] 
        as = pdU-complete {s} {c} {ys} v proj1-flat-v≡cys
        bs : Any (Recons { (l + t ` loc₁) ● s ` loc} {c} (PairU u v)) (concatmap-pdinstance-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {c} pdU[ s , c ]) 
        bs = any-recons-concatmap-pdinstance-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdU[ s , c ] as    
```

### Definition 20: Many steps Partial deriviatves with coercion functions `pdUMany[ r , w ]` and `PDInstance*`


For the ease of establishing the completeness proof of `pdUMany[ r , w ]`, we introduce
a data type `PDInstance*` (similar to `PDInstance`) to record the partial derivative descendant, the prefix of `w` which has been consumed
so far, the injection function and the soundness evidence.

As we collect the prefix, we make use of the snoc `∷ʳ` operation (which is a short hand for `λ xs x → xs ++ [ x ]`).
And the prefix is used as the index of the dependent datatype. 


One caveat of Agda is that it *does not automatically register* that ` xs ∷ʳ x ++ ys ` is equivalent to ` xs ++ ( x ∷ ys ) `. It has to be explicitly
"taught" that the equivalence holds with the library function `∷ʳ-++`.

Though this can be done manually as and when Agda complains about that the equivalence is not met, it gets trickier as the rewriting take place "implicitly".

For example, it is hard to manually prove that, which is 

pdUMany-aux≡ : ∀ {r : RE} {pref : List Char} {c : Char} {cs : Char} { pdis : List ( PDInstance* r pref ) }
  → pdUMany-aux {r} {pref} (c ∷ cs) pdis ≡  pdUMany-aux {r} {pref ∷ʳ c} cs ( concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis )


Simply because Agda can't find unify the type of the left-hand-side of the equivalence relation of type `List (PDInstance* r ( pref ++ cs ∷ cs ))` with
the right hand side `List (PDInstance* r ( pref ∷ʳ c ++ cs ) )`.

Hence using a global automatic rewriting language extension help to address this issue.


```agda 

import cgp.Rewriting  -- import ∷ʳ-++ rewriting rule

-- the result type for pdUMany, a variant of PDInstance


```


```agda

---------------------------------------------------------------------------------------------------------
-- A helper function  for pdUMany-aux then pdUMany 
-- compose-pdi-with : copmose a PDInstance with the "downstream" PDinstance* injection and soundness evidence



-- helper functions for pdUMany-aux then pdUMany                   
-- advance-pdi*-with-c : advance a PDInstance* with a character c (by consuming it with pdU) and return a list of PDInstance*
advance-pdi*-with-c : ∀ { r : RE } { pref : List Char } { c : Char }
                     → PDInstance* r pref
                     → List (PDInstance* r (pref ∷ʳ c ))
advance-pdi*-with-c {r} {pref} {c} (pdinstance* {d} {r} {pref} d→r s-ev-d-r) =
  List.map (compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d-r ) pdU[ d , c ] 

-- pdUMany's helper function 
pdUMany-aux :  ∀ { r : RE }
                 {pref : List Char}
               → (suff : List Char) 
               → List (PDInstance* r pref)
               → List (PDInstance* r (pref ++ suff ) )
pdUMany-aux {r} {pref} [] pdis rewrite (++-identityʳ pref) =  pdis
pdUMany-aux {r} {pref} (c ∷ cs) pdis {- rewrite (cong (λ x → List (PDInstance* r x )) (sym (∷ʳ-++ pref c cs))) -}  =  -- the rewrite is no longer needed thanks to the REWRITE ∷ʳ-++  pragma 
                pdUMany-aux {r} {pref ∷ʳ c} cs (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)



injId : ∀ { r : RE } → U r  → U r 
injId u = u

injId-sound : ∀ { r : RE } → ( u : U r ) → proj₁  (flat {r} (injId u)) ≡ proj₁ (flat {r} u)
injId-sound u = refl 

pdUMany[_,_] : ( r : RE ) → ( cs : List Char ) → List (PDInstance* r cs )
pdUMany[ r , cs ]         =
   pdUMany-aux {r} {[]} cs [  ( pdinstance* {r} {r} {[]} injId injId-sound ) ]


```

### Lemma 21 : pdUMany[ r , w ] is sound

Let r  be a non problematic regular expresion.
Let w be a word.
Let p be a partial derivative descendant of r w.r.t c, i.e. p ∈ proj₁ (proj₂ pdUMany[ r , w ] )
Let f be the injection function from parse tree of o to parse tree of r.
Let u be a parse tree of p, then |(f u)| = w ++ | u |, where (f u) is a parse tree of r.


The proof is given as part of the PDInstance* being computed. 


### Definition 22 (Parse Tree Reconstructability of PD Descendants):

Let r be a non problematic regular expression.
Let pref be a word,
LEt u be a parse tree of r.
Let pdi be a partial derivative descendant (instance) of r w.r.t. prefix pref,
such that pdi = { p , inj , sound-ev }
  where
    1. p is the partial derivative descendant instance of r / pref
    2. inj is the injection function from the parse tree of p back to the parse tree of r;
    3. sound-ev is the soundness evidence pdi
Then we say pdi is prefix reconstructable w.r.t. pre iff there exists a word w ∈⟦p⟧ such that inj (unflat w∈⟦p⟧) ≡ u.

```agda

-------------------------------------------------------------------------------------------------------------
-- Sub Lemma 23.1 - 23.3 BEGIN 
-------------------------------------------------------------------------------------------------------------



-- TODO the following lemma can be simplified.
-- compose-pdi-with-can-recons*  is moved to Recons.lagda.md


-- any-advance-pdi*-with-c : search for reconstructable pd Instance from (List.map (compose-pdi-with {r} {d}  {pref} {c} d→r-inj s-ev-d-r ) pdU [d , c]
any-advance-pdi*-with-c : ∀ { r : RE } { pref : List Char } { c : Char } { cs : List Char }
    → ( u : U r )
    → ( proj₁ (flat {r} u) ≡ pref ++ ( c ∷ cs ))
    → ( pdi : PDInstance* r pref )
    → Recons* {r} {pref} u pdi
    → Any (Recons* {r} {pref ∷ʳ c} u) (advance-pdi*-with-c {r} {pref} {c} pdi)  
any-advance-pdi*-with-c {r} {pref} {c} {cs} u proj1-flat-u≡pref++ccs (pdinstance* {d} {r} {pref} d→r s-ev-d-r) (recons* {d} {r} {ccs} {pref} {d→r} {s-ev-d-r} u' ( ccs∈⟦d⟧ , d→r-unflat-ccs∈⟦d⟧≡u )) = find pdU[ d , c ] any-recons-pdu-d-c  
  where 
      proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++c∷cs : proj₁ (flat (d→r (unflat ccs∈⟦d⟧ ))) ≡ pref ++ c ∷ cs
      proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++c∷cs =
        begin
          proj₁ (flat (d→r (unflat ccs∈⟦d⟧ )))
        ≡⟨ cong (λ x → (proj₁ (flat x))) d→r-unflat-ccs∈⟦d⟧≡u ⟩
          proj₁ (flat u)
        ≡⟨ proj1-flat-u≡pref++ccs ⟩
          pref ++ c ∷ cs
        ∎
      proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++proj1-flat-unflat=ccs∈⟦d⟧ : proj₁ (flat (d→r (unflat ccs∈⟦d⟧))) ≡ pref ++ proj₁ (flat (unflat ccs∈⟦d⟧))
      proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++proj1-flat-unflat=ccs∈⟦d⟧ = s-ev-d-r (unflat ccs∈⟦d⟧)
      pref++proj-1-flat-unflat-ccs∈⟦d⟧≡pref++ccs : pref ++ proj₁ (flat (unflat ccs∈⟦d⟧)) ≡ pref ++ c ∷ cs
      pref++proj-1-flat-unflat-ccs∈⟦d⟧≡pref++ccs = Eq.trans (sym proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++proj1-flat-unflat=ccs∈⟦d⟧)  proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++c∷cs
      proj1-flat-unflat-ccs∈⟦d⟧≡ccs : proj₁ (flat (unflat ccs∈⟦d⟧)) ≡ c ∷ cs 
      proj1-flat-unflat-ccs∈⟦d⟧≡ccs =  ++-cancelˡ pref  (proj₁ (flat (unflat ccs∈⟦d⟧))) (c ∷ cs) pref++proj-1-flat-unflat-ccs∈⟦d⟧≡pref++ccs

      -- : U d can be reconstructed based on pdU completenes 
      any-recons-pdu-d-c : Any (Recons {d} {c} (unflat ccs∈⟦d⟧)) pdU[ d , c ]
      any-recons-pdu-d-c =  pdU-complete {d} {c} {cs} (unflat ccs∈⟦d⟧) proj1-flat-unflat-ccs∈⟦d⟧≡ccs

      find : ∀ (pdis : List (PDInstance d c)) → Any (Recons {d} {c} (unflat ccs∈⟦d⟧)) pdis →  Any (Recons* u) (List.map (compose-pdi-with d→r s-ev-d-r) pdis)
      find  [] any-recons-pdu-d-c = Nullary.contradiction any-recons-pdu-d-c ¬Any[]
      find  (pdi₁ ∷ pdis₁) = 
        λ { ( here recons-d-c-pdi₁)  →               
              here (compose-pdi-with-can-recons* {r} {d} {pref} {c} u (unflat ccs∈⟦d⟧) d→r d→r-unflat-ccs∈⟦d⟧≡u  s-ev-d-r pdi₁ recons-d-c-pdi₁ )
          ; ( there pxs) →  there (find pdis₁ pxs) }      

-- any-recons*-concatmap-advance-with-c :
--   search for the reconstructable pd instance from (concatMap advance-pdi*-with-c pdis) given that there exist some pd instance in pdis reconstructing u
any-recons*-concatmap-advance-with-c : ∀ { r : RE } { pref : List Char } { c : Char } { cs : List Char }
    → ( u : U r )
    → ( proj₁ (flat {r} u) ≡ pref ++ ( c ∷ cs ))
    → ( pdis : List (PDInstance* r pref) )
    → Any (Recons* {r} {pref} u) pdis
    → Any (Recons* {r} {pref ∷ʳ  c} u) (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
any-recons*-concatmap-advance-with-c {r} {pref} {c} {cs} u proj1-flatu≡pref++ccs ( pdi@(pdinstance* {d} {r} {_pref} d→r s-ev-d-r )  ∷ pdis) any-recons*u-pdis
  with any-recons*u-pdis
... | here px@(recons* u' ( w∈⟦d⟧ , d→r-unflat-w∈⟦d⟧≡u' )) = any-left-concat (any-advance-pdi*-with-c {r} {pref} {c} {cs} u proj1-flatu≡pref++ccs pdi px)
... | there pxs = any-right-concat (any-recons*-concatmap-advance-with-c {r} {pref} {c} {cs} u proj1-flatu≡pref++ccs pdis pxs )

-------------------------------------------------------------------------------------------------------------
-- Sub Lemma 23.1 - 23.3 END 
-------------------------------------------------------------------------------------------------------------

```


#### Sub Lemma 23.4 : Reconstructibility is preserved over pdUMany-aux. 

```agda


-- completeness for pdUMany-aux function 
pdUMany-aux-complete : ∀ { r : RE } { pref : List Char } { suff : List Char }
    → ( u : U r )
    → ( proj₁ (flat {r} u) ≡ pref ++ suff )
    → ( pdis : List (PDInstance* r pref) )
    → Any (Recons* {r} {pref} u) pdis
    → Any (Recons* {r} {pref ++ suff} u) (pdUMany-aux {r} {pref} suff pdis)
pdUMany-aux-complete {r} {pref} {[]}     u proj1-flat-u≡pref      (pdi ∷ pdis) (here (recons* u' ( w∈⟦p⟧ , inj∘unflatw∈⟦p⟧≡u ))) rewrite (++-identityʳ pref) = here (recons* u (w∈⟦p⟧ , inj∘unflatw∈⟦p⟧≡u))   -- base case
pdUMany-aux-complete {r} {pref} {[]}     u proj1-flat-u≡pref      (pdi ∷ pdis) (there pxs) rewrite (++-identityʳ pref) = there pxs   -- base case
pdUMany-aux-complete {r} {pref} {c ∷ cs} u proj1-flat-u≡pref++ccs (pdi ∷ pdis) any-recons*u-pdis  = ind-hyp -- fake-goal
  where

    any-recons*u-pdis' : Any (Recons* {r} {pref ∷ʳ c } u) ( concatMap (advance-pdi*-with-c {r} {pref} {c}) (pdi ∷ pdis) )
    any-recons*u-pdis' = 
      any-recons*-concatmap-advance-with-c {r} {pref} {c} {cs} u proj1-flat-u≡pref++ccs (pdi ∷ pdis) any-recons*u-pdis

    proj1-flat-u≡prefc++cs : proj₁ (flat u) ≡ pref ∷ʳ c ++ cs 
    proj1-flat-u≡prefc++cs = proj1-flat-u≡pref++ccs -- thanks to the REWRITE ∷ʳ-++ pragma
    {-
      begin
        proj₁ (flat u)
      ≡⟨ proj1-flat-u≡pref++ccs ⟩
        pref ++ c ∷ cs
      ≡⟨ sym (∷ʳ-++ pref c cs) ⟩
        pref ∷ʳ c ++ cs
      ∎
    -}
    

    ind-hyp : Any (Recons* {r} {pref ∷ʳ c ++  cs} u) (pdUMany-aux {r} {pref ∷ʳ c} cs ( concatMap (advance-pdi*-with-c {r} {pref} {c}) (pdi ∷ pdis) ))
    ind-hyp = pdUMany-aux-complete {r} {pref ∷ʳ c} {cs} u proj1-flat-u≡prefc++cs  (concatMap (advance-pdi*-with-c {r} {pref} {c}) (pdi ∷ pdis))  any-recons*u-pdis'

```

#### Main proof for Lemma 23 

```agda



-- main lemma   
pdUMany-complete : ∀ { r : RE }
  → ( u : U r )
  → Any (Recons* {r} {proj₁ (flat u)} u) pdUMany[ r , proj₁ (flat u) ]
pdUMany-complete {r} u =
  pdUMany-aux-complete {r} {[]} {proj₁ (flat u)} u refl 
    [  ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ]
    ( here (recons* {r} {r} {proj₁ (flat u)} {[]}  u (proj₂ (flat u),  unflat∘proj₂∘flat ) ) )



```



### Definition 24: ParseAll function

```agda

buildU : ∀ {r : RE } {w : List Char } → PDInstance* r w → List (U r)
buildU {r} {w} (pdinstance* {p} {r} p→r s-ev) with ε∈? p
...                            | yes ε∈p = List.map p→r (mkAllEmptyU ε∈p)
...                            | no _     = []


parseAll[_,_] : ( r : RE ) → ( w : List Char ) → List (U r)
parseAll[ r ,  cs ] =
  let pdinstances = pdUMany[ r , cs ]
  in List.concatMap buildU pdinstances 
```

### Example ParseAll
Let's consider an example

```agda
module ExampleParseAll where 
  a*●a* : RE
  a*●a* = ( ( $ 'a' ` 1 ) * ε∉$ ` 2 ) ● ( ( $ 'a' ` 3 ) * ε∉$ ` 4 ) ` 5

  ex_ts : List ( U a*●a* )
  ex_ts = parseAll[ a*●a* , [ 'a' ] ]



  ε+a●a+ε : RE 
  ε+a●a+ε = let a₁ = $ 'a' ` 1
                a₃ = $ 'a' ` 3 
            in (ε + a₁ ` 2) ● ( a₃ + ε ` 4) ` 5
  ex_vs :  List ( U ε+a●a+ε )
  ex_vs = parseAll[ ε+a●a+ε , [ 'a' ] ]


  a*+a*●a* : RE
  a*+a*●a* = ( ( ( $ 'a' ` 1 ) * ε∉$ ` 2 ) + ( ( $ 'a' ` 3 ) * ε∉$ ` 4) ` 5 ) ● ( ( $ 'a' ` 6 ) * ε∉$ ` 7 ) ` 8

  ex_us :  List ( U a*+a*●a* )
  ex_us = parseAll[ a*+a*●a* ,  'a' ∷ 'a' ∷ []  ]
  


  pdMany-aux : List RE → List Char → List RE
  pdMany-aux rs [] = rs
  pdMany-aux rs ( c ∷ cs ) =  pdMany-aux (concatMap (λ r → pd[ r , c ] ) rs) cs 

  pdMany[_,_] : RE → List Char → List RE
  pdMany[ r , w ] = pdMany-aux [ r ] w
  
  pds1  = pdMany[ a*+a*●a* ,  'a' ∷ 'a' ∷ []  ]
  pds1'  = pdMany[ a*+a*●a* ,  'a' ∷ []  ]

  a*+a*●a*+a* : RE
  a*+a*●a*+a* = ( ( ( $ 'a' ` 1 ) * ε∉$ ` 2 ) + ( ( $ 'a' ` 3 ) * ε∉$ ` 4) ` 5 ) ● ( ( ( $ 'a' ` 6 ) * ε∉$ ` 7 ) + ( ( $ 'a' ` 8 ) * ε∉$ ` 9 ) ` 10 ) ` 11 

  ex_ws :  List ( U a*+a*●a*+a* )
  ex_ws = parseAll[ a*+a*●a*+a* ,  'a' ∷ 'a' ∷ []  ]

  pds2  = pdMany[ a*+a*●a*+a* ,  'a' ∷ 'a' ∷ []  ]

  a*+a*●a*●a* : RE
  a*+a*●a*●a* = a*+a*●a* ● ( ( $ 'a' ` 10 ) * ε∉$ ` 11 ) ` 12
  
  ex_ys : List ( U a*+a*●a*●a* )
  ex_ys = parseAll[ a*+a*●a*●a* , 'a' ∷ 'a' ∷ [] ] 

  a*+a*●a*+a*●a* : RE
  a*+a*●a*+a*●a* = a*+a*●a*+a* ● ( ( $ 'a' ` 12 ) * ε∉$ ` 13 ) ` 14

  ex_zs : List ( U a*+a*●a*+a*●a* )
  ex_zs = parseAll[ a*+a*●a*+a*●a* , 'a' ∷ 'a' ∷ [] ]

  posix-test-r₁ : RE
  posix-test-r₁ =
      let a₁ = $ 'a' ` 1
          b₂ = $ 'b' ` 2
          a+b = a₁ + b₂ ` 3 
          a₄ = $ 'a' ` 4
          b₅ = $ 'b' ` 5
          a●b = a₄ ● b₅ ` 6
          r = ( a+b + a●b ` 7 ) * (ε∉ (ε∉ ε∉$ + ε∉$ ) + (ε∉fst ε∉$) ) ` 8
      in r

  ex_os : List ( U posix-test-r₁ )
  ex_os = parseAll[ posix-test-r₁ , 'a' ∷ 'b' ∷ [] ] 

  -- ((ab + a) ● ( a + baa )) ● (c + ac)
  posix-test-r₂ : RE   
  posix-test-r₂ =
      let a₁ = $ 'a' ` 1
          b₂ = $ 'b' ` 2
          a●b = a₁ ● b₂ ` 3 
          a₄ = $ 'a' ` 4
          a●b+a = a●b + a₄ ` 5
          a₆ =  $ 'a' ` 6
          b₇ =  $ 'b' ` 7
          a₈ =  $ 'a' ` 8
          a₉ =  $ 'a' ` 9
          baa = b₇ ● ( a₈ ● a₉ ` 10) ` 11
          a+baa = a₆ + baa ` 12
          c₁₃ = $ 'c' ` 13
          a₁₄ = $ 'a' ` 14
          c₁₅ = $ 'c' ` 15
          ac = a₁₄ ● c₁₅ ` 16
          c+ac = c₁₃ + ac ` 17

          r = ( a●b+a ● a+baa ` 18 ) ● c+ac ` 19
      in r

  ex_qs = parseAll[ posix-test-r₂ , 'a' ∷ 'b' ∷ 'a' ∷ 'a' ∷ 'c' ∷ [] ] 
```

Evaluating ExampleParseAll.ex_us

should yield 


~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))) (ListU [])
∷
PairU (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))) (ListU [])
∷
PairU (LeftU (ListU (LetterU 'a' ∷ []))) (ListU (LetterU 'a' ∷ []))
∷
PairU (RightU (ListU (LetterU 'a' ∷ []))) (ListU (LetterU 'a' ∷ []))
∷
PairU (LeftU (ListU [])) (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷
PairU (RightU (ListU [])) (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷
[]

~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~



Evaluating ExampleParseAll.ex_ys

should yield 

PairU (PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))       (ListU []))                                (ListU [])
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))      (ListU []))                                (ListU [])
∷
PairU (PairU (LeftU (ListU (LetterU 'a' ∷ [])))                     (ListU (LetterU 'a' ∷ [])))                (ListU [])
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ [])))                    (ListU (LetterU 'a' ∷ [])))                (ListU [])
∷
PairU (PairU (LeftU (ListU (LetterU 'a' ∷ [])))                     (ListU []))                                (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ [])))                    (ListU []))                                (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (LeftU (ListU []))                                     (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))  (ListU [])
∷
PairU (PairU (LeftU (ListU []))                                     (ListU (LetterU 'a' ∷ [])))                (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU []))                                    (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))  (ListU [])
∷
PairU (PairU (RightU (ListU []))                                    (ListU (LetterU 'a' ∷ [])))                (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (LeftU (ListU []))                                     (ListU []))                                (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU []))                                    (ListU []))                                (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷ []



~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
evaluating ExampleParseAll.ex_os yields


ListU (RightU (PairU (LetterU 'a') (LetterU 'b')) ∷ [])
∷ 
ListU (LeftU (LeftU (LetterU 'a')) ∷ LeftU (RightU (LetterU 'b')) ∷ [])
∷
[]


~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
evaluating ExampleParseAll.ex_qs yields

PairU (PairU (LeftU (PairU (LetterU 'a') (LetterU 'b')))   (LeftU (LetterU 'a')))                                                (RightU (PairU (LetterU 'a') (LetterU 'c')))
∷
PairU (PairU (RightU (LetterU 'a'))                        (RightU (PairU (LetterU 'b') (PairU (LetterU 'a') (LetterU 'a')))))   (LeftU (LetterU 'c'))
∷ []
