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
  pdinstance-assoc 
  ) 

import cgp.Recons as Recons
open Recons using ( Recons ; recons ; 
  any-recons-left ; any-recons-right ;
  any-recons-fst ; any-recons-star ;
  any-recons-pdinstance-snd ;
  any-recons-concatmap-pdinstance-snd ;
  any-recons-assoc 
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

[] ⊕ rs = rs
rs ⊕ [] = rs
[ s ] ⊕ [ t ] = [ s + t ] 


```agda


_⊕_`_ : Maybe RE → Maybe RE → ℕ →  Maybe RE
_⊕_`_ nothing mr loc = mr
_⊕_`_ mr nothing loc = mr
_⊕_`_ (just s) (just t) loc = just (s + t ` loc) 


pd[_,_] : RE →  Char → Maybe RE
pdConcat : ( l : RE ) → ( r : RE ) → ( ε∈l : ε∈ l ) → ( loc : ℕ ) → ( c : Char)  → Maybe RE

pd[ ε , c ]    = nothing
pd[ $ c ` loc  , c' ] with c Char.≟ c'
...                      | yes refl = just ε 
...                      | no  _    = nothing
pd[ l ● r ` loc , c ] with ε∈? l
...                      | yes ε∈l =  pdConcat  l r ε∈l loc c
...                      | no ¬ε∈l =  Maybe.map (λ l' → l' ● r ` loc ) pd[ l , c ]
pd[ l + r ` loc , c ]               = pd[ l , c ] ⊕  pd[ r , c ] ` loc 
pd[ r * nε ` loc , c ]              = Maybe.map (λ r' → r' ● ( r * nε ` loc ) ` loc ) pd[ r , c ]
{-# TERMINATING #-}
-- it seems to me that the ⊕ in pdConcat cases is unnecessary. 
pdConcat ε  r  ε∈ε loc c  = pd[ r  , c ]
pdConcat (l * ε∉l ` loc₂ ) r ε∈*             loc c = (Maybe.map (λ l' → l' ● r ` loc ) pd[ l * ε∉l ` loc₂ , c ]) ⊕ pd[ r , c ] ` loc  -- or loc₂? 
pdConcat (l ● s ` loc₂ )   r (ε∈ ε∈l ● ε∈s)  loc c = pd[ l ● ( s ● r  ` loc ) ` loc₂ , c ]
pdConcat (l + s ` loc₂ )   r (ε∈l+s)         loc c = (Maybe.map (λ p → p ● r ` loc ) pd[ l + s ` loc₂ , c ]) ⊕ pd[ r , c ] ` loc  -- or loc₂? 


```


### A question: is ⊕ necessary? how does ⊕ give us posix ordering? can we enforce posix order without using ⊕ ?

Observation: the difference between ⊕ and ++ is that ⊕ merges two partial derivatives into a single partial derivative,
hence subsequently the use of r' ∈ pd( r , ℓ ) in the ● case and * case, we are dealing with just one r' instead of a sequence of r'.

### An Example

r = (a + b + a ● b)*                                        
w = ab


#### Using lne

pd[ r , a ] = [ r' ● r | r' ∈ pd[ ( a + b) + a ● b, a ] ]
            = [ ε ● r , ε ● b ● r ]
            ∵ pd[ (a + b) + a ● b, a ] =
              pd[ a , a ] ++ pd[ b , a ] ++ pd[ a ● b , a ] =
              [ ε ] ++ [] ++ [ ε ● b ]
concatMap pd[ _ , b ] [ ε ● r , ε ● b ● r ] = pd[ ε ● r , b ] ++ pd[ ε ● b ● r , b ]
                                            = [ ε ● r ] ++ [ ε ● r ]  -- the first r has been unrolled again (in its 3rd iteration), while the 2nd r is stillin its 2nd iteration

#### Using posix

pd[ r , a ] = [ r' ● r | r' ∈ pd[ ( a + b) + a ● b, a ] ]
            = [ ( ε + ε ● b ) ● r ]
            ∵ pd[ (a + b) + a ● b, a ] =
              pd[ a , a ] ⊕ pd[ b , a ] ⊕ pd[ a ● b , a ] =
              [ ε ] ⊕ []  ⊕ [ ε ● b ] = 
              [ ε + ε ● b ] 
concatMap pd[ _ , b ] [ ( ε + ε ● b ) ● r ] = pd[ ( ε + ε ● b ) ● r , b ] 
                                            = pdConcat ( ε + ε ● b ) r b
                                            = ( map ( λ p → p ● r ) pd[ ε + ε ● b , b ] ) ⊕ pd[ r , b ] -- is this ⊕ necessary? 
                                            = ( map ( λ p → p ● r ) pd[ ε , b ] ⊕  pd[ ε ● b , b ]) ⊕ pd[ r , b ]
                                            = ( map ( λ p → p ● r ) [ ε ] ) ⊕  pd[ r , b ]
                                            = [ ε ● r ] ⊕ pd[ r , b ] -- the left r is not touched, i.e. still in the 2nd iteration.
                                            = [ ε ● r ] ⊕ [ ε ● r ]   -- the right r is in the 3nd iteration. thanks to the lne policy by default 
                                            
   
#### Using ⊕ only at + case

pd[ r , a ] = [ r' ● r | r' ∈ pd[ ( a + b) + a ● b, a ] ]
            = [ ( ε + ε ● b ) ● r ]
            ∵ pd[ (a + b) + a ● b, a ] =  -- this is + case, ⊕ is used to implement ∪ 
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
ps  = let a₁ = $ 'a' ` 1
          b₂ = $ 'b' ` 2
          a+b = a₁ + b₂ ` 3 
          a₄ = $ 'a' ` 4
          b₅ = $ 'b' ` 5
          a●b = a₄ ● b₅ ` 6
          r = ( a+b + a●b ` 7 ) * (ε∉ (ε∉ ε∉$ + ε∉$ ) + (ε∉fst ε∉$) ) ` 8 
      in pd[ r , 'a'] >>= (λ p → pd[ p , 'b'] )
```

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





hm... not a good example 

```agda
-- ^ applying parse tree constructors to coercion records (namely, the injection function and the soundness evidence) 
pdinstance-oplus : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → List (PDInstance (l + r ` loc) c)
  → List (PDInstance (l + r ` loc) c)
  → List (PDInstance (l + r ` loc) c)
pdinstance-oplus {l} {r} {loc} {c} [] pdis = pdis
pdinstance-oplus {l} {r} {loc} {c} pdis [] = pdis
pdinstance-oplus {l} {r} {loc} {c} pdisₗ  pdisᵣ =  concatMap (λ pdiₗ → List.map (fuse pdiₗ) pdisᵣ) pdisₗ 
    where
      fuse : PDInstance (l + r ` loc) c → PDInstance (l + r ` loc) c → PDInstance (l + r ` loc) c
      fuse (pdinstance {pₗ} {l+r} {c} inj-l s-ev-l) (pdinstance {pᵣ} {l+r} {_} inj-r s-ev-r) = 
        (pdinstance {pₗ + pᵣ ` loc} {l+r} {c} inj sound-ev )
        where
          inj : U (pₗ + pᵣ ` loc) → U ( l + r ` loc )
          inj (LeftU v₁) = inj-l v₁
          inj (RightU v₂) = inj-r v₂ 
          sound-ev : (u : U (pₗ + pᵣ ` loc)) 
                   → proj₁ (flat (inj u))  ≡ c ∷ proj₁ (flat u)
          sound-ev (LeftU v₁) = s-ev-l v₁
          sound-ev (RightU v₂) = s-ev-r v₂

      


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
  pdinstance-oplus
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
  ++ -- no need oplus? 
  concatmap-pdinstance-snd {l * ε∉l ` loc₁} {r} {ε∈*}   {loc₂} {c} pdU[ r , c ]
pdUConcat (l ● s ` loc₁)    r ε∈l●s loc₂ c = List.map pdinstance-assoc pdU[ ( l ● ( s ● r ` loc₂ ) ` loc₁ ) , c ]

pdUConcat (l + s ` loc₁)    r ε∈l+s loc₂ c =
  ( List.map pdinstance-fst pdU[ (l + s ` loc₁) , c ] )
  ++ -- no need oplus ? 
   concatmap-pdinstance-snd {l + s ` loc₁}   {r} {ε∈l+s} {loc₂} {c} pdU[ r , c ]

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

any-recons-oplus-left : ∀ { l s : RE } { loc : ℕ } { c : Char } { w : List Char } { u : U l }
    → ( pdis : List (PDInstance (l + s ` loc) c))
    → ( pdis' : List (PDInstance (l + s ` loc) c)) 
    → Any (Recons { l + s ` loc} {c} (LeftU u)) pdis
    → Any (Recons { l + s ` loc} {c} (LeftU u))
                (pdinstance-oplus pdis pdis')
any-recons-oplus-left {l} {s} {loc} {c} {w} {u} []           pdis' any-recons-left-pdis = Nullary.contradiction any-recons-left-pdis ¬Any[]
any-recons-oplus-left {l} {s} {loc} {c} {w} {u} (pdi ∷ pdis) pdis' (here (recons {p}
                                                                         {l + s ` loc}
                                                                         {c'} {w'} {inj} {sound-ev} left-u ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡left-u ) ))
                                                                         = {!!} 
  
```

#### Main proof for Lemma 19 


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
pdU-complete {l + s ` loc} {c}  {w} (LeftU u)  proj1-flat-leftu≡cw = any-recons-oplus-left {l} {s} {loc} {c} {w} {u} (List.map pdinstance-left pdU[ l , c ]) (List.map pdinstance-right pdU[ s , c ]) ys 
  where
    xs : Any (Recons {l} {c} u) pdU[ l , c ]
    xs =  pdU-complete {l} {c} u proj1-flat-leftu≡cw
    ys : Any (Recons { l + s ` loc} {c} (LeftU u)) (List.map pdinstance-left pdU[ l , c ])
    ys =  any-recons-left {l} {s} {loc} {c}  {w} {u} pdU[ l , c ]  xs      
