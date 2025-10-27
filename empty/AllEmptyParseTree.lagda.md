```agda
module cgp.empty.AllEmptyParseTree where

import cgp.RE as RE
open RE using (RE; ϕ ; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈ ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_)

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r)


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LeftU ; RightU ; PairU ; ListU ; flat ; unflat  )

import cgp.Utils as Utils
open Utils using (any-left-concat; any-right-concat ; inv-map-[] ; inv-concatMap-map-f-[] )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap )


import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalˡ ; ++-conicalʳ ;  ++-assoc )

import Data.Char as Char
open Char using (Char)

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

open import Function using (_∘_)
```

### Definition 13 : mkAllEmptyU 

Function `mkAllEmptyU` computes all empty parse tree of the given (non-problematic) regular expression r.

```agda
mkAllEmptyU : ∀ { s : RE } ( prf : ε∈ s ) → List (U s)  
mkAllEmptyU { ε }          ε∈ε          = [ EmptyU ]
mkAllEmptyU {l + r ` loc}  ε∈l+r   with ε∈l+r
...                                                     | ε∈ ε∈l + ε∈r = List.map (λ v → LeftU {l} {r} v ) (mkAllEmptyU {l} ε∈l) ++ 
                                                                         List.map (λ v → RightU {l} {r} v ) (mkAllEmptyU {r} ε∈r)
...                                                     | ε∈ ε∈l <+ _   = List.map (λ v → LeftU {l} {r} v ) (mkAllEmptyU {l}  ε∈l)
...                                                     | ε∈ _   +> ε∈r = List.map (λ v → RightU {l} {r} v ) (mkAllEmptyU {r}  ε∈r)
mkAllEmptyU {l ● r ` loc} ( ε∈ ε∈l ● ε∈r ) =
  let us = mkAllEmptyU {l} ε∈l
      vs = mkAllEmptyU {r} ε∈r
  in concatMap (λ u → List.map (λ v → PairU {l} {r} {loc} u v) vs) us 
mkAllEmptyU {r * nε ` loc } ε∈*  = [ ListU {r} {nε} {loc} [] ] 
```

Some testing examples of mkAllEmptyU

```agda


u = let a₁ = $ 'a' ` 1
        a₃ = $ 'a' ` 3 
    in mkAllEmptyU {((a₁ * ε∉$ ` 2) + (a₃ * ε∉$ ` 4) ` 5)} ( ε∈_+_ ( ε∈* ) ( ε∈* ) )
```

It should produce `ListU (ListU []) ∷ RightU (ListU []) ∷ []`


### Lemma 14 (Lemma 7 from [2]) : mkAllEmptyU soundness

Let r be a non-problematic regular expression. Let prf : ε ∈ r .  Then for all
 u ∈ mkAllEmptyU {r} {prf} we have flat u ≡ [].


First we define the property `flat u ≡ []` as the following data type

```agda
{-
flat-[] : ∀ { r : RE } → U r   → Set
flat-[]   { r } u  =  proj₁ (flat {r} u) ≡ []
-}


data Flat-[] :  (r : RE) → (U r) → Set where
  flat-[] : ∀ { r : RE } ( x :  U r ) →  ( (proj₁ (flat {r} x) ) ≡ [] ) → Flat-[] r x

```


To prove Lemma 14, we need a few auxilliary lemma

#### Sub Lemma 14.1 (concatenation for two `All` evidence)

```agda
all-concat : ∀ { r : Set } { P : r → Set } { xs ys  : List r }
  → All P xs
  → All P ys
  ----------------------
  → All P (xs ++ ys)
all-concat [] ys = ys
all-concat ( x ∷ xs ) ys = x ∷ (all-concat xs ys)
```


#### Sub Lemma 14.2

Let `xs` be a list of parse trees of a non problematic regular expression r such that all members in `xs`
are flattened to []. Then all members in `List.map RightU xs` are flattened to [].

```agda
{-
-- this sub lemma is too weak to be proven
-- it motivates us to use all-flat-[]-right
foo : ∀ { l r : RE } { loc : ℕ } { ε∈r : ε∈ r  } 
→ All (Flat-[] r) (mkAllEmptyU {r} ε∈r)
----------------------------------------------------------------------------------------------------
→ All (Flat-[] (l + r ` loc)) (List.map (λ u → RightU {l} {r} {loc} u) (mkAllEmptyU {r} ε∈r))
-- foo {l} {r} {loc} {ε∈r} ( ( flat-[] {r} x ) ∷ es )  = {! All.[]!}
-- foo (All._∷_ x xs ) = {!!}
foo x = {!!}
-}


all-flat-[]-right : ∀ { l r : RE } { loc : ℕ } { xs : List (U r) }
  → All (Flat-[] r) xs
  ----------------------------------------------------------------------------------------------------
  → All (Flat-[] (l + r ` loc)) (List.map (λ u → RightU {l} {r} {loc} u) xs)
all-flat-[]-right [] = []
all-flat-[]-right {l} {r} {loc} {x ∷ xs} ( (flat-[] u eq) ∷ pus) = (flat-[] (RightU u) eq) ∷ (all-flat-[]-right {l} {r} {loc} {xs} pus)
```


#### Sub Lemma 14.3

Let `xs` be a list of parse trees of a non problematic regular expression l such that all members in `xs`
are flattened to []. Then all members in `List.map LeftU xs` are flattened to [].

```agda

all-flat-[]-left : ∀ { l r : RE } { loc : ℕ } { xs : List (U l) }
  → All (Flat-[] l) xs
  ----------------------------------------------------------------------------------------------------
  → All (Flat-[] (l + r ` loc)) (List.map (λ u → LeftU {l} {r} {loc} u) xs)
all-flat-[]-left [] = []
all-flat-[]-left {l} {r} {loc} {x ∷ xs} ( (flat-[] u eq) ∷ pus) = (flat-[] (LeftU u) eq) ∷ (all-flat-[]-left {l} {r} {loc} {xs}  pus)

```


#### Sub Lemma 14.4

Let `xs` be a list of parse trees of a non problematic regular expression l such that all members in `xs`
are flattened to []. Let `ys` be a list of parse trees of a non problematic regular expression r such that all members in `ys`
are flattened to [].
Then all members in `List.map LeftU xs ++ List.map RightU ys` are flattened to [].

```agda

all-flat-[]-left-right : ∀ { l r : RE } { loc : ℕ } { xs : List (U l) } { ys : List (U r) }
  → All (Flat-[] l) xs
  → All (Flat-[] r) ys  
  ----------------------------------------------------------------------------------------------------
  → All (Flat-[] (l + r ` loc)) (List.map (λ u → LeftU {l} {r} {loc} u) xs ++ List.map (λ v → RightU {l} {r} {loc} v) ys)
-- all-flat-[]-left-right [] ys = all-flat-[]-right ys
-- all-flat-[]-left-right ( (flat-[] r x₁) ∷ pxs) ys = (flat-[] (LeftU r) x₁) ∷ (all-flat-[]-left-right pxs ys)
all-flat-[]-left-right {l} {r} {loc} {xs} {ys} us vs =
  all-concat (all-flat-[]-left {l} {r} {loc} {xs} us)  (all-flat-[]-right  {l} {r} {loc} {ys} vs)
```

#### Sub Lemma 14.5

Let `xs` be a list of parse trees of a non problematic regular expression l such that all members in `xs`
are flattened to []. Let `ys` be a list of parse trees of a non problematic regular expression r such that all members in `ys`
are flattened to [].
Then all members in the cartesian product of  `xs` and `ys` are  flattened to [].

```agda
flat-[]-pair : ∀ { l r : RE } { loc : ℕ } { u : (U l) } { v : (U r) }
  → Flat-[] l u
  → Flat-[] r v
  ---------------------------------------
  → Flat-[] (l ● r ` loc ) (PairU {l} {r} {loc} u v)
flat-[]-pair {l} {r} {loc} {u} {v} (flat-[] u prf₁) (flat-[] v prf₂) = flat-[] (PairU u v) prf 
  where 
     prf : proj₁ (flat { l ● r ` loc }  (PairU {l} {r} {loc} u v))  ≡ []
     prf with flat u    | flat v
     prf    | xs , xs∈l | ys , ys∈l = 
        begin
          xs ++ ys 
        ≡⟨ Eq.cong₂ ( λ z w → z ++ w ) prf₁ prf₂ ⟩
          [] 
        ∎

all-flat-[]-cartesian-prod : ∀ { l r : RE } { loc : ℕ } { us : List (U l) } { vs : List (U r) }
  → All (Flat-[] l) us
  → All (Flat-[] r) vs  
  ----------------------------------------------------------------------------------------------------
  → All (Flat-[] (l ● r ` loc)) (List.concatMap (λ u → List.map (λ v → PairU {l} {r} {loc} u v) vs) us)
all-flat-[]-cartesian-prod []                                                         pvs   = []
all-flat-[]-cartesian-prod {l} {r} {loc}  { u ∷ us } {  vs } ( (flat-[] u prf) ∷ pus) pvs  =
  all-concat (pu-pvs u vs (flat-[] u prf) pvs ) (all-flat-[]-cartesian-prod {l} {r} {loc}  {us} {vs} pus pvs)
  where
    pu-pvs : ( u : U l )
           → ( vs : List (U r) )
           → Flat-[] l u
           → All (Flat-[] r ) vs
           → All (Flat-[] ( l ● r ` loc )) (List.map (λ v → PairU {l} {r} {loc} u v) vs)
    pu-pvs u [] _ _ = []
    pu-pvs u ( v ∷ vs ) (flat-[] u prf) ( flat-[] v prf₁ ∷ pvs ) =
      flat-[]-pair {l} {r} {loc} {u} {v}  (flat-[] u prf) (flat-[] v prf₁) ∷ pu-pvs u vs (flat-[] u prf) pvs

```


Then Lemma 14 is verified by a structual induction over r by applying the Sub lemmas 14.1 to 14.5

```agda
mkAllEmptyU-sound : ∀ { s : RE } ( prf :  ε∈ s ) → All (Flat-[] s) (mkAllEmptyU {s} prf)
mkAllEmptyU-sound {ε}             ε∈ε = (flat-[] EmptyU refl) ∷ []
mkAllEmptyU-sound {l + r ` loc }  ε∈l+r with ε∈l+r
...                                       | ε∈ ε∈l + ε∈r = 
                                              let
                                                 ds : All (Flat-[] l) (mkAllEmptyU {l} ε∈l)
                                                 ds = mkAllEmptyU-sound {l} ε∈l
                                                 es : All (Flat-[] r) (mkAllEmptyU {r} ε∈r)
                                                 es = mkAllEmptyU-sound {r} ε∈r
                                               in all-flat-[]-left-right {l} {r} {loc} ds es
...                                      | ε∈ ε∈l <+ _   =
                                              let
                                                 es : All (Flat-[] l) (mkAllEmptyU {l} ε∈l)
                                                 es = mkAllEmptyU-sound {l} ε∈l
                                              in all-flat-[]-left {l} {r} {loc} es 
...                                      | ε∈ _ +> ε∈r   =
                                              let
                                                 es : All (Flat-[] r) (mkAllEmptyU {r} ε∈r)
                                                 es = mkAllEmptyU-sound {r} ε∈r
                                              in all-flat-[]-right {l} {r} {loc} es
mkAllEmptyU-sound {l ● r ` loc }  (ε∈ ε∈l ● ε∈r ) =
                                              let 
                                                 ds : All (Flat-[] l) (mkAllEmptyU {l} ε∈l)
                                                 ds = mkAllEmptyU-sound {l} ε∈l
                                                 es : All (Flat-[] r) (mkAllEmptyU {r} ε∈r)
                                                 es = mkAllEmptyU-sound {r} ε∈r
                                              in all-flat-[]-cartesian-prod {l} {r} {loc} ds es
                                                               
mkAllEmptyU-sound {r * nε ` loc } ε∈*              = (flat-[] (ListU []) refl) ∷ []
```


### Lemma 15 (Lemma 8 from [2]): mkAllEmptyU completeness

Let r be a non-problematic regular expression. Let prf : ε ∈ r .
Let u be a parse tree of r such that flat u ≡ [].
Then u ∈ mkAllEmptyU {r} {prf}.


#### Sub Lemma 15.1 ( Parse Tree membership congruence )

##### 15.1.1 
Let l and r be non problematic regular expressions.
Let loc be a source location.
Let v be a parse tree of r. Let us be a list of parse trees of r.
Let v ∈ us.
Then (RightU {l} {r} {loc} v) ∈ (map RightU us)


```agda
any-≡-v-right : ∀ { l r : RE } { loc : ℕ } { v : U r } { us : List (U r) }
  →  Any ( _≡_ v ) us
  ---------------------------------------------------------
  → Any ( _≡_ (RightU {l} {r} {loc} v) ) (List.map ( λ x →  (RightU x ) ) us )
any-≡-v-right (here px) = here (Eq.cong RightU px)
any-≡-v-right (there pxs) = there (any-≡-v-right pxs)
```

#### 15.1.2

Let l and r be non problematic regular expressions.
Let loc be a source location.
Let v be a parse tree of l. Let us be a list of parse trees of l.
Let v ∈ us.
Then (LeftU {l} {r} {loc} v) ∈ (map LeftU us)

```agda
any-≡-v-left : ∀ { l r : RE } { loc : ℕ } { v : U l } { us : List (U l) }
  →  Any ( _≡_ v ) us
  ---------------------------------------------------------
  → Any ( _≡_ (LeftU {l} {r} {loc} v) ) (List.map ( λ x →  (LeftU x ) ) us )
any-≡-v-left (here px) = here (Eq.cong LeftU px)
any-≡-v-left (there pxs) = there (any-≡-v-left pxs)
```



### Sub Lemma 15.2 (Flat left/right empty word)

#### 15.2.1 
Let l and r be regular expressions.
Let loc be a source location.
Let u be a parse tree of r
such that flat (RightU u) ≡ [].
Then flat u ≡ [].
```agda
flat-[]-right→flat-[] : ∀ { l r : RE } { loc : ℕ } { u : U r }
  → Flat-[] ( l + r ` loc ) (RightU u)
  -------------------------------------
  → Flat-[] r u
flat-[]-right→flat-[] (flat-[] (RightU u) prf) = flat-[] u prf -- we can use prf here because prf : Product.proj₁ (flat (RightU u) | flat u) ≡ []
```

#### 15.2.2
Let l and r be regular expressions.
Let loc be a source location.
Let u be a parse tree of r
such that flat (LeftU u) ≡ [].
Then flat u ≡ [].
```agda
flat-[]-left→flat-[] : ∀ { l r : RE } { loc : ℕ } { u : U l }
  → Flat-[] ( l + r ` loc ) (LeftU u)
  -------------------------------------
  → Flat-[] l u
flat-[]-left→flat-[] (flat-[] (LeftU u) prf) = flat-[] u prf -- we can use prf here because prf : Product.proj₁ (flat (RightU u) | flat u) ≡ []

```




#### Sub Lemma 15.3

Let l r be non problematic regular expression.
Let loc be a source location.
Let v be a parse tree of l, u be a parse tree of r.
Let xs be a list of parse trees of l, ys be a list of parse trees of r, such that v ∈ xs and u ∈ ys.
Then (PairU v u) ∈ (concatMap (λ x → map (λ y → PairU x y) ys) xs)

```agda
any-≡-v-any-≡-u-concatmap-map : ∀ { l r : RE } { loc : ℕ } { v : U l } { u : U r } { xs : List (U l) } { ys : List (U r) } 
  → Any ( _≡_ v ) xs
  → Any ( _≡_ u ) ys 
  → Any (_≡_ (PairU {l} {r} {loc} v u))
      (List.foldr _++_ [] (List.map (λ x → List.map (PairU x) ys) xs))
      -- conclusion same as
      -- Any (_≡_ (PairU {l} {r} {loc} v u)) (concatMap (λ x → List.map (λ y → PairU {l} {r} {loc} x y) ys) xs)

any-≡-v-any-≡-u-concatmap-map {l} {r} {loc} {v} {u} {xs} {ys} pxs pys = go xs ys pxs pys 
  where
    go : ( xs : List (U l) )  → ( ys : List (U r) ) 
       → Any ( _≡_ v ) xs    → Any ( _≡_ u ) ys 
       → Any (_≡_ (PairU v u)) (List.foldr _++_ [] (List.map (λ x → List.map (PairU x) ys) xs))
       -- → Any (_≡_ (PairU v u)) (concatMap (λ x → List.map (λ y → PairU x y) ys) xs)
    go (x ∷ xs) ( y ∷ ys) (here px) (here py)    = here (Eq.cong₂ (λ a b → (PairU {l} {r} {loc}  a b)) px py)
    go (x ∷ xs) ( y ∷ ys) (here px) (there pys)  = 
      there (any-left-concat (pair-v-u∈map-pair-x pys))
        where
          pair-v-u∈map-pair-x : {ys : List (U r) } → Any (_≡_ u) ys →  Any (_≡_ (PairU v u)) (List.map (PairU x) ys)
          pair-v-u∈map-pair-x { y ∷ ys } (here py)   = here (Eq.cong₂ (λ a b → (PairU {l} {r} {loc} a b)) px py) 
          pair-v-u∈map-pair-x { y ∷ ys } (there pys) = there (pair-v-u∈map-pair-x {ys} pys)
    go (x ∷ xs) ys (there pxs) pys = any-right-concat (go xs ys pxs pys)
        
```


Here is the proof of Lemma 15 (mkAllEmptyU completeness), by applying the sub lemmas.

```agda
mkAllEmptyU-complete : ∀ { s : RE } ( prf :  ε∈ s )
  → ( u : U s )
  → Flat-[] s u
  ---------------------------------
  → u ∈ (mkAllEmptyU {s}  prf)
mkAllEmptyU-complete {ε} ε∈ε EmptyU flat-[]-u = here refl
mkAllEmptyU-complete {l + r ` loc } ε∈l+r u flat-[]-u with ε∈l+r        | u         | flat-[]-u 
...                                                      | ε∈ ε∈l + ε∈r | LeftU v  | flat-[] (LeftU _ ) prf = any-left-concat (any-≡-v-left es) 
                                                          where
                                                            es : Any ( _≡_ v ) (mkAllEmptyU ε∈l ) -- alias of v ∈ (mkAllEmptyU ε∈l )
                                                            es = mkAllEmptyU-complete ε∈l v (flat-[]-left→flat-[] {l} {r} {loc} {v} (flat-[] (LeftU v) prf))
                                                                             
...                                                      | ε∈ ε∈l + ε∈r | RightU v | flat-[] (RightU _ ) prf = any-right-concat (any-≡-v-right es)
                                                           where
                                                             es : Any ( _≡_ v ) (mkAllEmptyU ε∈r ) -- alias of v ∈ (mkAllEmptyU ε∈r )
                                                             es = mkAllEmptyU-complete ε∈r v (flat-[]-right→flat-[] {l} {r} {loc} {v} (flat-[] (RightU v) prf))
...                                                      | ε∈ ε∈l <+ ε∉r  | LeftU v   | flat-[] (LeftU _ ) prf =  any-≡-v-left es
                                                           where
                                                             es : Any ( _≡_ v ) (mkAllEmptyU ε∈l ) -- alias of v ∈ (mkAllEmptyU ε∈l )
                                                             es = mkAllEmptyU-complete ε∈l v (flat-[]-left→flat-[] {l} {r} {loc} {v} (flat-[] (LeftU v) prf))                                                                         
...                                                      | ε∈ ε∉l  +> ε∈r | RightU v  | flat-[] (RightU _ ) prf = any-≡-v-right es
                                                           where
                                                             es : Any ( _≡_ v ) (mkAllEmptyU ε∈r ) -- alias of v ∈ (mkAllEmptyU ε∈r )
                                                             es = mkAllEmptyU-complete ε∈r v (flat-[]-right→flat-[] {l} {r} {loc} {v} (flat-[] (RightU v) prf))
-- the impossible cases for choice                                                             
mkAllEmptyU-complete {l + r ` loc } ε∈l+r u flat-[]-u   | ε∈ ε∈l <+ ε∉r  | RightU v   | flat-[] (RightU _ ) prf with flat v
mkAllEmptyU-complete {l + r ` loc } ε∈l+r u flat-[]-u   | ε∈ ε∈l <+ ε∉r  | RightU v   | flat-[] (RightU _ ) prf | [] , []∈⟦r⟧ = Nullary.contradiction ε∉r ([]∈⟦r⟧→¬ε∉r []∈⟦r⟧ ) 
mkAllEmptyU-complete {l + r ` loc } ε∈l+r u flat-[]-u   | ε∈ ε∉l +> ε∈r  | LeftU v   | flat-[] (LeftU _ ) prf with flat v
mkAllEmptyU-complete {l + r ` loc } ε∈l+r u flat-[]-u   | ε∈ ε∉l +> ε∈r  | LeftU v   | flat-[] (LeftU _ ) prf | [] , []∈⟦l⟧ = Nullary.contradiction ε∉l ([]∈⟦r⟧→¬ε∉r []∈⟦l⟧ ) 

mkAllEmptyU-complete {r * nε ` loc } ε∈* (ListU []) prf = here refl
-- the impossible cases for star
mkAllEmptyU-complete {r * nε ` loc} ε∈* (ListU {r} {nε'} (x ∷ xs)) (flat-[] .(ListU (x ∷ xs)) x₁) with flat x
...                                                 | [] , prf = Nullary.contradiction nε' ([]∈⟦r⟧→¬ε∉r prf)


mkAllEmptyU-complete {l ● r ` loc } (ε∈ ε∈l ● ε∈r ) (PairU v u) (flat-[] (PairU _ _ ) prf) = any-≡-v-any-≡-u-concatmap-map ds es  
                     where
                      ++≡[]-left : ∀ { t : Set } { xs ys : List t } → xs ++ ys ≡ [] → xs ≡ []
                      ++≡[]-left {t} {[]} {ys} xs++ys≡[] = refl

                      ++≡[]-right : ∀ { t : Set } { xs ys : List t } → xs ++ ys ≡ [] → ys ≡ []
                      ++≡[]-right {t} {xs} {[]} xs++ys≡[] = refl
                      ++≡[]-right {t} {[]} {y ∷ ys} = λ()


                      ds : Any ( _≡_ v ) (mkAllEmptyU ε∈l)
                      ds = mkAllEmptyU-complete {l} ε∈l v (flat-[] v (++≡[]-left prf)) 
                        
                      es : Any ( _≡_ u ) (mkAllEmptyU ε∈r)
                      es = mkAllEmptyU-complete {r} ε∈r u (flat-[] u (++≡[]-right prf))
```


### Aux Lemmas required by proofs in greedy/ExtendedOrder.lagda.md


### Aux Lemma :
  Let r be a non problematic regular expression such that r is nullable, i.e. ε∈r.
  Then mkAllEmptyU ε∈r is not an empty list. 
 


```agda

-- this should be moved AllEmptyParseTree.lagda.md 
mkAllEmptyU≢[] : ∀ { r : RE } ( ε∈r : ε∈ r )
    → ¬ (mkAllEmptyU {r} ε∈r ≡ [] )
mkAllEmptyU≢[] {ϕ} = λ()
mkAllEmptyU≢[] {ε} ε∈ε = λ ()
mkAllEmptyU≢[] {$ c ` _ } = λ()
mkAllEmptyU≢[] {l * ε∉l ` _ } ε∈* = λ () 
mkAllEmptyU≢[] {l + r ` _ } (ε∈ ε∈l + ε∈r) map-left-mkAllEmptyU-ε∈l++map-right-mkAllEmptyU-ε∈r≡[] = ind-hyp-l (inv-map-[]  map-left-mkAllEmptyU≡[])
  where
    ind-hyp-l :  ¬ (mkAllEmptyU {l} ε∈l ≡ [] )
    ind-hyp-l = mkAllEmptyU≢[] {l} ε∈l
    map-left-mkAllEmptyU≡[] : List.map LeftU (mkAllEmptyU ε∈l) ≡ []
    map-left-mkAllEmptyU≡[] = ++-conicalˡ (List.map LeftU (mkAllEmptyU ε∈l)) (List.map RightU (mkAllEmptyU ε∈r)) map-left-mkAllEmptyU-ε∈l++map-right-mkAllEmptyU-ε∈r≡[] 
mkAllEmptyU≢[] {l + r ` _ } (ε∈ ε∈l <+ ε∉r) map-left-mkAllEmptyU-ε∈l≡[] =  ind-hyp-l (inv-map-[]  map-left-mkAllEmptyU-ε∈l≡[]) 
  where
    ind-hyp-l :  ¬ (mkAllEmptyU {l} ε∈l ≡ [] )
    ind-hyp-l = mkAllEmptyU≢[] {l} ε∈l
mkAllEmptyU≢[] {l + r ` _ } (ε∈ ε∉l +> ε∈r) map-right-mkAllEmptyU-ε∈r≡[] =  ind-hyp-r (inv-map-[]  map-right-mkAllEmptyU-ε∈r≡[]) 
  where
    ind-hyp-r :  ¬ (mkAllEmptyU {r} ε∈r ≡ [] )
    ind-hyp-r = mkAllEmptyU≢[] {r} ε∈r
mkAllEmptyU≢[] {l ● r ` _ } (ε∈ ε∈l ● ε∈r ) map-left-mkAllEmptyU-ε∈l++map-right-mkAllEmptyU-ε∈r≡[]
  with inv-concatMap-map-f-[] {xs = (mkAllEmptyU ε∈l)} {ys = (mkAllEmptyU ε∈r)} {PairU} map-left-mkAllEmptyU-ε∈l++map-right-mkAllEmptyU-ε∈r≡[]
... | inj₁ mkAllEmptyU-ε∈l≡[] = ind-hyp-l mkAllEmptyU-ε∈l≡[]
  where 
    ind-hyp-l :  ¬ (mkAllEmptyU {l} ε∈l ≡ [] )
    ind-hyp-l = mkAllEmptyU≢[] {l} ε∈l
... | inj₂ mkAllEmptyU-ε∈r≡[] = ind-hyp-r mkAllEmptyU-ε∈r≡[]
  where 
    ind-hyp-r :  ¬ (mkAllEmptyU {r} ε∈r ≡ [] )
    ind-hyp-r = mkAllEmptyU≢[] {r} ε∈r

```
