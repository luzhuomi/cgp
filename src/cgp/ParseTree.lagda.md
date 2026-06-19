```agda
module cgp.ParseTree where

import cgp.RE as RE
open RE using (RE;  ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈ ; ε∈ε ; ε∈_●_ ; ε∈* ; ε∈? ; ε∉$ ; ε∉_+_ ; inv-¬ε∈l+r ; ε∉r→¬ε∈r )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→ε∈r ;  []∈⟦r⟧→¬ε∉r)

import cgp.Utils as Utils
open Utils using ( ∷-inj ) 

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ;
  length-++ 
  )


import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


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

open import Function using (_∘_)
```


### Definition 7:  Parse Tree

The following implements the parse tree as an indexed data type, (in [1], it is called `Tree`)

```agda
data U : RE → Set where
  EmptyU  : U ε
  LetterU : ∀ { loc : ℕ } ( c : Char ) → U ( $ c ` loc )
  LeftU   : ∀ { l r : RE } { loc : ℕ } ( u : U l ) → U ( l + r ` loc )
  RightU  : ∀ { l r : RE } { loc : ℕ }  ( u : U r ) → U ( l + r ` loc )
  PairU   : ∀ { l r : RE } { loc : ℕ }  ( u : U l ) ( v : U r ) → U ( l ● r ` loc )
  ListU   : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } ( us : List (U r) ) → U ( r * nε ` loc )  -- TODO : split ListU into NilU and ConsU
```


The above definition is a dependently typed version of `U` in [2].

In [1], `ListU` is broken into two sub constructors, namely `star[]` and `start-`.

> KL: Does it make a difference? It seems no difference

### Definition 8: Parstree flattening (Definition 4 from [2])

Following [2], we define the operation | u | that flattens a parse tree u into a word w, as follows 

   | EmptyU | = []        | ListU [] | = []       | ListU (u:us) | = |u| ++ |us|
   | LeftU u | = | u |    | RightU u | = | u |    | Pair (u,v)   | = |u| ++ |v|


### Definition 8a : 𝓣 ( r ) mapping regular expression to set of parse trees (Definition 3 form [2])

Similiar to 𝓛( r ) we could define 𝓣( r ) which maps a regular expression r to a set of of parse tree.

   𝓣( ϕ )       = {}
   𝓣( ε )       = { EmptyU }
   𝓣( ℓ )       = { LetterU ℓ }
   𝓣( r₁ + r₂ ) = { LeftU u ∣ u ∈ 𝓣( r₁ ) } ∪ { RightU u ∣ u ∈ 𝓣( r₂ ) }
   𝓣( r₁ ● r₂ ) = { PairU u v ∣ u ∈ 𝓣( r₁ ) ∧ v ∈ 𝓣( r₂ ) }
   𝓣( r * )     = ∪_{n ≥ 0} { ListU [u₁, ..., uₙ ] ∣ uᵢ ∈ 𝓣( r ) }
   

Then we can argue

### Lemma 8b (Lemma 5 of [2]) : Let r be a regular expression and t be a parse tree such that t ∈ 𝓣( r ). Then |t| ∈ 𝓛( r )

Similar issue like 𝓛 ( r ) and _∈_ arises here. The definition of 𝓣 ( t ) is mapping regular expression to some infinite set (lazy set). The _∈_ check must be done coninductively.

Instead of adopting definition 8a, we follow [1] to combine flattening of parse tree and Lemma 8b into a existentially quantified proposition.

### Lemma 9: Flattening and word membership (A variant of Lemma 8b)

Let r be a regular expression and t be a parse tree of r, then there exists a word w such that flat t  ≡ w and  w ∈ ⟦ r ⟧ 

```agda
flat : ∀ { s : RE } → U s → ∃[ xs ] xs ∈⟦ s ⟧ 
flat { ε }     EmptyU           = [] , ε
flat { $ c ` loc }   (LetterU c)      = [ c ] , ($ c )
flat { l + r ` loc } (LeftU {l} {r} {loc}  u)    with flat u
...                                    | xs , xs∈l = xs , ( r +L xs∈l )
flat { l + r ` loc } (RightU {l} {r} {loc} u)   with flat u
...                                    | xs , xs∈r = xs , ( l +R xs∈r ) 
flat { l ● r ` loc } (PairU {l} {r} {loc} u v)  with flat u     | flat v
...                                                | xs , xs∈l | ys , ys∈r = xs ++ ys , _●_⧺_ xs ys xs∈l ys∈r refl
flat { r * nε ` loc }   (ListU {r} {.nε} {loc} [])        = [] , (( (r ● (r * nε ` loc) ` loc ) +L ε ) *)       -- no  ⧺ because the ● is the RE constructor
flat { r * nε ` loc }   (ListU {r} {.nε} {loc} (u ∷ us)) with flat u  | flat (ListU {r} {nε} {loc} us)
...                                   | x , x∈r  | xs , xs∈r* = ( x ++ xs ) , ((ε +R (_●_⧺_ x xs x∈r xs∈r* refl)) *) 
```

The above is inspired by the `flat` definition from [1]. 



### Lemma 10 : Unflattening word yields parse tree.

We follow [1] to define the converse (or inverse?) of the flat operation

```agda
unListU : ∀ {r : RE} { nε : ε∉ r } { loc : ℕ }  → (U (r * nε `  loc)) → List (U r)
unListU (ListU us) = us

unflat : ∀ { s : RE } { xs : List Char } → xs ∈⟦ s ⟧ → U s
unflat {ε}          {[]}         ε          = EmptyU
unflat {$ c ` loc } { _ ∷ [] }  ( $ c )    = LetterU c
unflat {l + r ` loc } {xs} ( r +L xs∈l )   = LeftU {l} {r} {loc} (unflat {l} {xs} xs∈l )
unflat {l + r ` loc } {xs} ( l +R xs∈r )   = RightU {l} {r} {loc} (unflat {r} {xs} xs∈r ) 
unflat {l ● r ` loc } {xs++ys} (_●_⧺_ xs ys xs∈l ys∈r eq )                 = PairU (unflat xs∈l ) ( unflat ys∈r )
unflat {r * nε ` loc } (( (r ● (r * nε ` loc ) ` loc ) +L ε ) *)     = ListU []
unflat {r * nε ` loc } (( ε +R (_●_⧺_ x xs x∈r xs∈r* eq ) ) *)            =
   ListU ((unflat x∈r) ∷ (unListU (unflat xs∈r*)))

-- the following is an alt implenentation using `with` clause, we still prefer using the named function `unListU` to remove the ListU tag, which makes the proof unflat∘proj₂∘flat slightly easier.

-- unflat {r * nε ` loc } (( ε +R (x∈r ● xs∈r* ⧺ eq ) ) *) with unflat x∈r | unflat  xs∈r* 
-- ...                                                            | u        | ListU us = ListU (u ∷ us )
```

##### Observation: 

1. The `unflat` function builds a parse tree of r given the input word xs and the evidence xs ∈⟦ r ⟧.
2. The construction of the parse tree is driven by the evidence xs ∈⟦ r ⟧.

Some examples are given as follows, 
```agda
unflat_a : U ($ 'a' ` 1 )
-- unflat_a = unflat {$ 'a'} { 'a' ∷ []} ( $ 'a' )
unflat_a = unflat ( $ 'a' )


unflat_a* : U  (($ 'a' ` 1 ) * ε∉$ ` 2)
unflat_a* = unflat (( ε +R ( _●_⧺_ ('a' ∷ []) [] a∈$a ( ( ( a ● (a * ε∉$ ` 2) ` 2 ) +L ε ) * ) refl ))  * )
  where
    a∈$a : [ 'a' ] ∈⟦ $ 'a' ` 1  ⟧ 
    a∈$a = $ 'a'
    a : RE
    a = $ 'a' ` 1 
```


### Lemma 11 : unflat is inverse of the 2nd  projection of flat. (Lemma 1 of [1])

Let s be a RE and t : Tree e a parse tree. Then unflat (proj₂ (flat t)) ≡ t.

Note: proj₂ ( _ , y ) = y

```agda
unflat∘proj₂∘flat : ∀ { s : RE } { t : U s } → unflat (proj₂ (flat t)) ≡ t
unflat∘proj₂∘flat { ε }           { EmptyU }    = refl
unflat∘proj₂∘flat { $ c ` loc }   { LetterU c } = refl
unflat∘proj₂∘flat { l + r ` loc } { LeftU {l} {r} {loc} u } = cong ( λ w → (LeftU w) ) (unflat∘proj₂∘flat {l} {u})
{-
  -- detailed version
  let xsxs∈l :  ∃[ xs ] xs ∈⟦ l ⟧
      xsxs∈l = flat {l} u
      xs      = proj₁ xsxs∈l
      xs∈l   = proj₂ xsxs∈l
  in 
  begin
    unflat {l + r} {xs} (proj₂ (flat (LeftU {l} {r} u)))
  ≡⟨⟩
    unflat {l + r} {xs} ( r +L xs∈l )
  ≡⟨⟩
    -- LeftU {l} {r} ( unflat {l} {xs} xs∈l  )
    LeftU ( unflat xs∈l )
  ≡⟨⟩
    -- LeftU {l} {r} ( unflat {l} {xs} ( proj₂ (flat {l} u)) )
    LeftU ( unflat ( proj₂ (flat u)) )
  ≡⟨ cong ( λ w → (LeftU w) ) (unflat∘proj₂∘flat {l} {u}) ⟩    
    LeftU u 
  ∎
-}
unflat∘proj₂∘flat { l + r ` loc } { RightU {l} {r} {loc} u } = cong ( λ w → (RightU w) ) (unflat∘proj₂∘flat {r} {u})
{-
  -- detailed version
  let xsxs∈r :  ∃[ xs ] xs ∈⟦ r ⟧
      xsxs∈r = flat {r} u
      xs      = proj₁ xsxs∈r
      xs∈r   = proj₂ xsxs∈r
  in 
  begin
    unflat {l + r} {xs} (proj₂ (flat (RightU {l} {r} u)))
  ≡⟨⟩
    unflat {l + r} {xs} ( l +R xs∈r )
  ≡⟨⟩
    -- RightU {l} {r} ( unflat {r} {xs} xs∈r  )
    RightU ( unflat xs∈r )
  ≡⟨⟩
    -- RightU {l} {r} ( unflat {r} {xs} ( proj₂ (flat {r} u)) )
    RightU ( unflat ( proj₂ (flat u)) )
  ≡⟨ cong ( λ w → (RightU w) ) (unflat∘proj₂∘flat {r} {u}) ⟩    
    RightU u 
  ∎
-}
unflat∘proj₂∘flat { l ● r ` loc  } { PairU {l} {r} {loc} u v } = Eq.cong₂ ( λ w u → PairU w u ) (unflat∘proj₂∘flat {l} {u})  (unflat∘proj₂∘flat {r} {v}) -- short version
unflat∘proj₂∘flat { r * nε ` loc } { ListU {r} {nε} {loc} [] } = refl
unflat∘proj₂∘flat { r * nε ` loc } { ListU {r} {nε} {loc} (u ∷ us) } =
  Eq.cong₂ (λ w v → (ListU ( w ∷ (unListU v)))) (unflat∘proj₂∘flat {r} {u} ) (unflat∘proj₂∘flat { r * nε ` loc } { ListU us } ) -- short version
  -- detailed version
  {-
  let xx∈r : ∃[ x ] x ∈⟦ r ⟧
      xx∈r = flat {r} u
      x     = proj₁ xx∈r
      x∈r  = proj₂ xx∈r
      xsxs∈r* : ∃[ xs ] xs ∈⟦ r * nε ` loc  ⟧
      xsxs∈r* = flat {r * nε ` loc } (ListU us)
      xs      = proj₁ xsxs∈r*
      xs∈r*   = proj₂ xsxs∈r* 
  in 
  begin
    unflat (proj₂ (flat ( ListU {r} (u ∷ us) )))
  ≡⟨⟩
    unflat ((ε +R (x∈r ● xs∈r* ⧺ refl)) *) 
  ≡⟨⟩
    ListU ((unflat x∈r) ∷ (unListU (unflat xs∈r*)))
  ≡⟨ Eq.cong₂ (λ w v → (ListU ( w ∷ (unListU v)))) (unflat∘proj₂∘flat {r} {u} ) (unflat∘proj₂∘flat { r * nε ` loc } { ListU us } ) ⟩
    ListU {r} (u ∷ us)
  ∎
  -} 
```


### Lemma 12: flat is the inverse of unflat (Lemma 2 from [1])

Let xs be a string and s a RE s.t. xs ∈ s. Let prf be the proof of xs ∈ S. Then
flat (unflat prf ) ≡ (xs , prf ).

To prove the above lemma, we need a sub lemma, which says `ListU` and `unListU` are inverse functions.

#### Sub Lemma 12.1

```agda
listU∘unListU : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ }  { u : U (r * nε ` loc) } → ListU (unListU u) ≡ u
listU∘unListU {r} {nε} {loc} { ListU  [] } = refl
listU∘unListU {r} {nε} {loc} { ListU  (u ∷ us) } = refl
```

Here is the proof of Lemma 12.
```agda
flat∘unflat : ∀ { s : RE } { xs : List Char } → ( prf : xs ∈⟦ s ⟧ ) → flat (unflat prf ) ≡ ( xs , prf )
flat∘unflat {ε}     {[]}       ε             = refl
flat∘unflat {$ c ` loc }   { _ ∷ [] } ($ c)         = refl
flat∘unflat {l + r ` loc } {xs}       ( r +L xs∈l ) =
  cong (λ w → ( (proj₁ w) , ( r +L (proj₂ w) ))  ) (flat∘unflat {l} {xs} xs∈l ) -- short version
  -- detailed version
  {-
  begin
    flat (unflat ( r +L xs∈l ))
  ≡⟨⟩
    flat (LeftU (unflat xs∈l))
  ≡⟨⟩
    ( proj₁ (flat ( unflat xs∈l )) , r +L (proj₂ (flat ( unflat xs∈l ))))    
  ≡⟨ cong (λ w → ( (proj₁ w) , ( r +L (proj₂ w) ))  ) (flat∘unflat {l} {xs} xs∈l ) ⟩
    ( xs , ( r +L xs∈l))
  ∎
  -}
flat∘unflat {l + r ` loc } {xs}       ( l +R xs∈r ) = cong (λ w → ( (proj₁ w) , ( l +R (proj₂ w) ))  ) (flat∘unflat {r} {xs} xs∈r ) -- short version

flat∘unflat {l ● r ` loc } {xs++ys} (_●_⧺_ xs ys xs∈l ys∈r eq) rewrite flat∘unflat xs∈l | flat∘unflat ys∈r with eq
...                                                                                            | refl = refl -- short version
-- detailed version
{-
flat∘unflat {l ● r ` loc } {xs++ys} (xs∈l ● ys∈r ⧺ eq) with eq
... | refl = 
  begin
     ( proj₁ (flat (unflat xs∈l))  ++
       proj₁ (flat (unflat ys∈r))
     ,
     ( proj₂  (flat (unflat xs∈l)) ●
       proj₂  (flat (unflat ys∈r)) ⧺ refl))
  ≡⟨ Eq.cong₂ (λ x y → ( proj₁ x ++ proj₁ y , (proj₂ x ● proj₂ y ⧺ refl) ) ) (flat∘unflat xs∈l) (flat∘unflat ys∈r) ⟩
    (xs++ys , (xs∈l ● ys∈r ⧺ refl))
  ∎
-}

flat∘unflat {r * nε ` loc }   {[]}     (( (r ● (r * nε `  loc ) ` loc ) +L ε ) *) = refl

flat∘unflat {r * nε ` loc }   {x++xs}  ((ε +R (_●_⧺_ x xs x∈r xs∈r* eq)) *) rewrite flat∘unflat x∈r | listU∘unListU {r} {nε} {loc} {unflat xs∈r*} | flat∘unflat xs∈r* with eq
...                                                                                                                                                                  | refl = refl  -- short version
-- detailed version
{- 
flat∘unflat {r * nε ` loc }   {x++xs}    ((ε +R (x∈r ● xs∈r* ⧺ eq)) *) with eq
...                                                             | refl = 
  begin
    ( proj₁ (flat (unflat x∈r)) ++
      proj₁ (flat (ListU (unListU (unflat xs∈r*))))
    ,
      ((ε +R
        (proj₂ (flat (unflat x∈r)) ●
         proj₂ (flat (ListU (unListU (unflat xs∈r*)))) ⧺ refl))
      *)
    )
  ≡⟨ cong (λ x → ( proj₁ (flat (unflat x∈r)) ++ proj₁ (flat x) 
                 , ((ε +R (proj₂ (flat (unflat x∈r)) ● proj₂ (flat x) ⧺ refl))*)
                 ) ) (listU∘unListU {r} {nε} {loc} {unflat xs∈r*})
   ⟩
    ( proj₁ (flat (unflat x∈r)) ++
      proj₁ (flat (unflat xs∈r*))
    ,
      ((ε +R
        (proj₂ (flat (unflat x∈r)) ●
         proj₂ (flat (unflat xs∈r*)) ⧺ refl))
      *)
    )
  ≡⟨ Eq.cong₂ (λ x y → (proj₁ x ++ proj₁ y , ((ε +R (proj₂ x ● proj₂ y ⧺ refl)) *)) )
     (flat∘unflat x∈r) ( flat∘unflat xs∈r* ) ⟩ 
    ( x++xs , ((ε +R (x∈r ● xs∈r* ⧺ refl)) *))
  ∎ 
-}
```


### Aux lemma : parse tree of ε must be flatten to empty word

```agda
flat-Uε≡[] : ∀ ( u : U ε )
  → proj₁ (flat u) ≡ []
flat-Uε≡[] EmptyU = refl



```


### Aux Lemmas (inverse reasoning of the PairU parse trees and ListU parse trees)  needed by pdU completeness proof


```agda


inv-flat-pair-fst : ∀ { l r : RE }  { ¬ε∈l : ¬ (ε∈ l) } { loc : ℕ } { u : U l } { v : U r } { c : Char } { zs : List Char }
    → proj₁ (flat (PairU {l} {r} {loc} u v)) ≡ c ∷ zs
    → ∃[ xs ] ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ zs )



inv-flat-pair-fst {ε} {r}  {¬ε∈ε} {loc} {u} {v} {c} {zs}  _ = Nullary.contradiction ε∈ε ¬ε∈ε
inv-flat-pair-fst {l * ε∉l ` loc' } {r} {¬ε∈l*} {loc} {u} {v} {c} {zs} _ = Nullary.contradiction ε∈* ¬ε∈l*
inv-flat-pair-fst {$ c' ` loc'} {r} {¬ε∈l} {loc} {LetterU c''} {v} {c} {zs} with c' Char.≟ c
...                                                                         |  yes refl    = λ proj1-flat-$c-r≡czs →  [] , zs ,  refl , proj₂ (∷-inj proj1-flat-$c-r≡czs ) , refl 
...                                                                         |  no  ¬c'≡c   = λ proj1-flat-$c-r≡czs → Nullary.contradiction (proj₁ (∷-inj proj1-flat-$c-r≡czs )) ¬c'≡c
inv-flat-pair-fst {l + s ` loc'} {r} {¬ε∈l+s} {loc} {LeftU u} {v} {c} {zs} proj1-flat-leftu-v≡czs  with inv-flat-pair-fst {l} {r} {proj₁ (inv-¬ε∈l+r ¬ε∈l+s)} {loc} {u} {v} {c} {zs}  proj1-flat-leftu-v≡czs
...                                                                                                 | xs , ys ,  eq1 ,  eq2 , refl  =  xs , ys , eq1 , eq2 , refl
inv-flat-pair-fst {l + s ` loc'} {r} {¬ε∈l+s} {loc} {RightU u} {v} {c} {zs} proj1-flat-rightu-v≡czs with inv-flat-pair-fst {s} {r} {proj₂ (inv-¬ε∈l+r ¬ε∈l+s)} {loc} {u} {v} {c} {zs} proj1-flat-rightu-v≡czs
...                                                                                                 | xs , ys ,  eq1 ,  eq2 , refl  =  xs , ys , eq1 , eq2 , refl

inv-flat-pair-fst {l ● s ` loc'} {r} {¬ε∈l●s} {loc} {PairU u t} {v} {c} {zs} with flat (PairU u t)   
...                                                                         | [] , []∈⟦l●s⟧         = λ _ →  Nullary.contradiction  ([]∈⟦r⟧→ε∈r []∈⟦l●s⟧) ¬ε∈l●s
...                                                                         | c₁ ∷ cs₁ , ccs₁∈⟦l●s⟧ with ε∈? l
...                                                                                                  | no ¬ε∈l with flat u            | flat t         | flat v 
...                                                                                                             | [] , []∈⟦l⟧          | _              | _              = λ _ →  Nullary.contradiction  ([]∈⟦r⟧→ε∈r []∈⟦l⟧) ¬ε∈l
...                                                                                                             | c₂ ∷ cs₂ , ccs₂∈⟦l⟧ | cs₃ , cs₃∈⟦s⟧  | cs₄ , cs₄∈⟦r⟧   = λ proj1-flat-pairu-t-v≡czs → 
  let c≡c₂ ,  zs≡cs₂++cs₃++cs₄ = ∷-inj {c} {c₂} {zs} {(cs₂ ++ cs₃) ++ cs₄} (sym proj1-flat-pairu-t-v≡czs)
  in  cs₂ ++ cs₃ , cs₄ , Eq.cong₂ _∷_ (sym c≡c₂) refl  , (refl , sym zs≡cs₂++cs₃++cs₄)
  
inv-flat-pair-fst {l ● s ` loc'} {r}  {¬ε∈l●s} {loc} {PairU u t} {v} {c} {zs} | c₁ ∷ cs₁ , ccs₁∈⟦l●s⟧ | yes ε∈l with ε∈? s 
...                                                                                                             | yes ε∈s = λ _ → Nullary.contradiction (ε∈ ε∈l ● ε∈s) ¬ε∈l●s
...                                                                                                             | no ¬ε∈s with flat u              | flat t               | flat  v
...                                                                                                                         | _                     | [] , []∈⟦s⟧          | _             = λ _ →  Nullary.contradiction ([]∈⟦r⟧→ε∈r []∈⟦s⟧) ¬ε∈s
...                                                                                                                         | [] , []∈⟦l⟧           | c₃ ∷ cs₃ , ccs₃∈⟦s⟧ | cs₄ , cs₄∈⟦r⟧ = λ proj1-flat-pairu-t-v≡czs →
  let c≡c₃ , zs≡cs₃++cs₄ = ∷-inj {c} {c₃} {zs} {cs₃ ++ cs₄} (sym proj1-flat-pairu-t-v≡czs)
  in cs₃ , cs₄ , Eq.cong₂ _∷_ (sym c≡c₃) refl  , refl , sym zs≡cs₃++cs₄
...                                                                                                                         | c₂ ∷ cs₂ , ccs₂∈⟦l⟧  |  cs₃ , cs₃∈⟦s⟧       | cs₄ , cs₄∈⟦r⟧   = λ proj1-flat-pairu-t-v≡czs → 
  let c≡c₂ ,  zs≡cs₂++cs₃++cs₄ = ∷-inj {c} {c₂} {zs} {(cs₂ ++ cs₃) ++ cs₄} (sym proj1-flat-pairu-t-v≡czs)
  in  cs₂ ++ cs₃ , cs₄ , Eq.cong₂ _∷_ (sym c≡c₂) refl  , (refl , sym zs≡cs₂++cs₃++cs₄)



inv-flat-pair-snd : ∀ { l r : RE }  { ε∈l : (ε∈ l) } { loc : ℕ } { u : U l } { v : U r } { c : Char } { zs : List Char } 
                → proj₁ (flat (PairU {l} {r} {loc} u v)) ≡ c ∷ zs
                → ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ zs ) )
                  ⊎
                  ( ∃[ xs ] ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs ) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ zs ) )
inv-flat-pair-snd {$ _ ` _ } {r} {ε∈l} {loc} {u} {v} {c} {zs} proj1-flat-u-v≡czs  = Nullary.contradiction ε∈l (ε∉r→¬ε∈r ε∉$)
inv-flat-pair-snd {ε} {r} {loc} {ε∈l} {EmptyU} {v} {c} {zs} proj1-flat-u-v≡czs    =  inj₁ (zs , refl , proj1-flat-u-v≡czs , refl)
inv-flat-pair-snd {f ● s ` loc' } {r} {ε∈ ε∈f ● ε∈s} {loc} {u@(PairU u₁ u₂)} {v} {c} {zs} proj1-flat-u-v≡czs
  with flat {f} u₁           | flat {s} u₂            | flat {r} v 
... |  [] , []∈⟦f⟧           |  [] , []∈⟦s⟧           | _             = inj₁ (zs , refl ,  proj1-flat-u-v≡czs , refl)
... |  [] , []∈⟦f⟧           | (c₂ ∷ cs₂) , ccs₂∈⟦s⟧  | cs₃ , cs₃∈⟦r⟧ = let ( c₂≡c , cs₂++cs₃≡zs ) =  ∷-inj proj1-flat-u-v≡czs in inj₂ (cs₂ , cs₃ , cong ( _∷ cs₂) c₂≡c  , refl , cs₂++cs₃≡zs)
... |  (c₁ ∷ cs₁) , ccs₁∈⟦f⟧ | cs₂  , cs₂∈⟦s⟧         | cs₃ , cs₃∈⟦r⟧ = let ( c₁≡c , cs₁++cs₂++cs₃≡zs ) =  ∷-inj proj1-flat-u-v≡czs
                                                                       in inj₂ (cs₁ ++ cs₂ , cs₃ , cong ( _∷ cs₁ ++ cs₂ ) c₁≡c , refl ,  cs₁++cs₂++cs₃≡zs  )
inv-flat-pair-snd {f + s ` loc' } {r} {ε∈f+s} {loc} {u@(LeftU u₁)} {v} {c} {zs} proj1-flat-u-v≡czs
  with flat {f} u₁           | flat {r} v
... |  [] , []∈⟦f⟧           | (c₃ ∷ cs₃) , ccs₃∈⟦r⟧ = let ( c₃≡c , cs₃≡zs ) =  ∷-inj proj1-flat-u-v≡czs in inj₁ (cs₃ , refl , cong ( _∷ cs₃) c₃≡c , cs₃≡zs)
... |  (c₁ ∷ cs₁) , ccs₁∈⟦f⟧ | cs₃ , cs₃∈⟦r⟧         = let ( c₁≡c , cs₁++cs₃≡zs ) =  ∷-inj proj1-flat-u-v≡czs in inj₂ (cs₁ , cs₃ , cong ( _∷ cs₁ ) c₁≡c , refl , cs₁++cs₃≡zs )
inv-flat-pair-snd {f + s ` loc' } {r} {ε∈f+s} {loc} {u@(RightU u₂)} {v} {c} {zs} proj1-flat-u-v≡czs
  with flat {s} u₂           | flat {r} v
... |  [] , []∈⟦s⟧           | (c₃ ∷ cs₃) , ccs₃∈⟦r⟧ = let ( c₃≡c , cs₃≡zs ) =  ∷-inj proj1-flat-u-v≡czs in inj₁ (cs₃ , refl , cong ( _∷ cs₃) c₃≡c , cs₃≡zs)
... |  (c₂ ∷ cs₂) , ccs₂∈⟦s⟧ | cs₃ , cs₃∈⟦r⟧         = let ( c₂≡c , cs₂++cs₃≡zs ) =  ∷-inj proj1-flat-u-v≡czs in inj₂ (cs₂ , cs₃ , cong ( _∷ cs₂ ) c₂≡c , refl , cs₂++cs₃≡zs )
inv-flat-pair-snd {s * ε∉s ` loc' } {r} {ε∈*} {loc} {u@(ListU [])} {v} {c} {zs} proj1-flat-u-v≡czs = inj₁ (zs , refl , proj1-flat-u-v≡czs , refl)
inv-flat-pair-snd {s * ε∉s ` loc' } {r} {ε∈*} {loc} {u@(ListU (u₁ ∷ us₁))} {v} {c} {zs} proj1-flat-u-v≡czs
  with flat {s} u₁           | flat {s * ε∉s ` loc'} (ListU us₁) | flat {r} v
... |  [] , []∈⟦s⟧           |  _                                |  _            = Nullary.contradiction ε∉s ( []∈⟦r⟧→¬ε∉r []∈⟦s⟧ )
... |  (c₁ ∷ cs₁) , ccs₁∈⟦s⟧ | cs₂ , cs₂∈⟦s*⟧                     | cs₃ , cs₃∈⟦r⟧ = let ( c₁≡c , cs₁++cs₂++cs₃≡zs ) =  ∷-inj proj1-flat-u-v≡czs
                                                                                   in inj₂ (cs₁ ++ cs₂ , cs₃ , cong ( _∷ cs₁ ++ cs₂ ) c₁≡c , refl ,  cs₁++cs₂++cs₃≡zs  )





inv-flat-star : ∀ { r : RE } { ε∉r : (ε∉ r) } { loc : ℕ } { u : U r } { us : List (U r ) } { c : Char } { zs : List Char } 
                → proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us))) ≡ c ∷ zs
                → ∃[ xs ] ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs ) × (proj₁ (flat (ListU {r} {ε∉r} {loc} us)) ≡ ys) × ( xs ++ ys ≡ zs )  
-- inv-flat-star {ϕ} {loc} {u} {us} {c} {zs} {ε∉r}  = λ() -- not needed
inv-flat-star {ε}            {ε∉r} {loc} {EmptyU}         {us} {c} {zs} proj1-flat-u-us≡czs  = Nullary.contradiction ε∈ε (ε∉r→¬ε∈r ε∉r)
inv-flat-star {$ c' ` loc'}  {ε∉r} {loc} {u@(LetterU c₁)} {us} {c} {zs} proj1-flat-u-us≡czs  =
  let ( c₁≡c , proj1-flat-us≡zs ) =  ∷-inj proj1-flat-u-us≡czs in [] , zs ,  cong ( λ x → x ∷  []) c₁≡c , proj1-flat-us≡zs , refl
inv-flat-star {f + s ` loc'} {ε∉ ε∉f + ε∉s} {loc} {u@(LeftU u₁)}   {us} {c} {zs}  proj1-flat-u-us≡czs
  with flat u₁                | flat (ListU {f + s ` loc'} {ε∉ ε∉f + ε∉s} {loc} us)
... | [] , []∈⟦f⟧             | _                  =  Nullary.contradiction  ε∉f ([]∈⟦r⟧→¬ε∉r []∈⟦f⟧) 
... | ( c₁ ∷ cs₁ ) , ccs₁∈⟦f⟧ | cs₃ , cs₃∈⟦fsstar⟧ =  let ( c₁≡c , cs₁++cs₃≡zs ) =  ∷-inj proj1-flat-u-us≡czs in  cs₁ , cs₃ , cong ( _∷ cs₁ ) c₁≡c , refl , cs₁++cs₃≡zs 
inv-flat-star {f + s ` loc'} {ε∉ ε∉f + ε∉s} {loc} {u@(RightU u₂)}   {us} {c} {zs} proj1-flat-u-us≡czs
  with flat u₂                | flat (ListU {f + s ` loc'} {ε∉ ε∉f + ε∉s} {loc} us)
... | [] , []∈⟦s⟧             | _                  =  Nullary.contradiction  ε∉s ([]∈⟦r⟧→¬ε∉r []∈⟦s⟧) 
... | ( c₂ ∷ cs₂ ) , ccs₂∈⟦s⟧ | cs₃ , cs₃∈⟦fsstar⟧ =  let ( c₂≡c , cs₂++cs₃≡zs ) =  ∷-inj proj1-flat-u-us≡czs in  cs₂ , cs₃ , cong ( _∷ cs₂ ) c₂≡c , refl , cs₂++cs₃≡zs 
inv-flat-star {f ● s ` loc'} {ε∉f●s} {loc} {u@(PairU u₁ u₂)} {us} {c} {zs}  proj1-flat-u-us≡czs
  with flat u₁                | flat u₂                   | flat (ListU {f ● s ` loc'} {ε∉f●s} {loc}  us)
... | [] , []∈⟦f⟧             | [] , []∈⟦s⟧               |  _                   = Nullary.contradiction (ε∈ ([]∈⟦r⟧→ε∈r []∈⟦f⟧) ● ([]∈⟦r⟧→ε∈r []∈⟦s⟧) ) (ε∉r→¬ε∈r ε∉f●s)
... | [] , []∈⟦f⟧             | ( c₂ ∷ cs₂ ) , ccs₂∈⟦s⟧   |  cs₃ , cs₃∈⟦fsstar⟧  = let ( c₂≡c , cs₂++cs₃≡zs ) =  ∷-inj proj1-flat-u-us≡czs
                                                                                  in cs₂ , cs₃  ,  cong ( _∷ cs₂ ) c₂≡c , refl , cs₂++cs₃≡zs 
... | (c₁ ∷ cs₁) , ccs₁∈⟦f⟧   | cs₂ , cs₂∈⟦s⟧             |  cs₃ , cs₃∈⟦fsstar⟧  = let ( c₁≡c , cs₁++cs₂++cs₃≡zs ) =  ∷-inj proj1-flat-u-us≡czs
                                                                                  in cs₁ ++ cs₂ , cs₃ ,  cong ( _∷ cs₁ ++ cs₂ ) c₁≡c , refl , cs₁++cs₂++cs₃≡zs 
```



### Some aux lemmas required for ExtendedOrder


```agda
u-of-r*-islist : ∀ { r : RE } {ε∉r : ε∉ r } {loc : ℕ }
   → ( u : U (r * ε∉r ` loc) )
   ------------------------------------
   → (u ≡ ListU []) ⊎ ( ∃[ x ] ∃[ xs ] u ≡ (ListU (x ∷ xs )))
u-of-r*-islist (ListU []) = inj₁ refl
u-of-r*-islist (ListU (x ∷ xs)) = inj₂  (x , xs , refl)


pair-≡ : ∀ { l r : RE } { loc : ℕ }
  → { v₁ : U l }
  → { v₁' : U r }
  → { v₂ : U l }
  → { v₂' : U r }
  → v₁  ≡ v₂
  → v₁' ≡ v₂'
  ---------------------------
  → PairU {l} {r} {loc} v₁ v₁' ≡ PairU {l} {r} {loc} v₂ v₂'
pair-≡ refl refl = refl 

left-≡ : ∀ { l r : RE } { loc : ℕ }
  → { v₁ : U l }
  → { v₂ : U l }
  → v₁ ≡ v₂
  ----------------------------------
  → LeftU {l} {r} {loc}  v₁ ≡ LeftU {l} {r} {loc} v₂ 
left-≡ refl = refl 

right-≡ : ∀ { l r : RE } { loc : ℕ }
  → { v₁ : U r }
  → { v₂ : U r }
  → v₁ ≡ v₂
  ----------------------------------
  → RightU {l} {r} {loc}  v₁ ≡ RightU {l} {r} {loc} v₂ 
right-≡ refl = refl 

LeftU≢RightU : ∀ { l r : RE } {loc : ℕ }
  → (u : U l)
  → (v : U r)
  → ¬ ((LeftU {l} {r} {loc} u) ≡ (RightU {l} {r} {loc} v))
LeftU≢RightU {l} {r} {loc} u v = λ()


proj₁∘LeftU≢proj₁∘RightU : ∀ { l s r : RE } {loc₁ loc₂ : ℕ }
  → (u : U l)
  → (t : U s)
  → (v : U r)
  → (w : U r)
  → ¬ ( PairU { l + s ` loc₁ } {r} {loc₂} (LeftU {l} {s} {loc₁} u) v  ≡ PairU { l + s ` loc₁ } {r} {loc₂} (RightU {l} {s} {loc₁} t) w)
proj₁∘LeftU≢proj₁∘RightU {l} {s} {r} {loc₁} {loc₂} u t v w  = λ()



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
  → ¬ ((RightU {l} {r} {loc} u) ≡ (LeftU {l} {r} {loc} v))
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


inv-listU : ∀ { r : RE } {ε∉r : ε∉ r} { loc : ℕ }
  → ( u : U r )
  → ( us : List (U r) )
  → ( u' : U r )
  → ( us' : List (U r ) )
  → ( ListU {r} {ε∉r} {loc} (u ∷ us)) ≡ ListU {r} {ε∉r} {loc} (u' ∷ us' )
  ----------------------------------------------------------------
  → u ≡ u' × us ≡ us'
inv-listU _ _ _ _ refl = refl , refl   
  

inv-listU1 : ∀ { r : RE } {ε∉r : ε∉ r} { loc : ℕ }
  → ( us : List (U r) )
  → ( us' : List (U r ) )
  → ( ListU {r} {ε∉r} {loc} us) ≡ ListU {r} {ε∉r} {loc} us'
  ----------------------------------------------------------------
  → us ≡ us'
inv-listU1  _ _ refl = refl   



```

Auxillary property and lemma needed for greedy lne robustness

```agda

data ParseTreeOf : ( r : RE ) → ( u : U r ) → Set where 
  parseTreeOf : ∀ { r : RE } {u : U r } → ParseTreeOf r u 


r-∃u : ∀ ( r : RE )
  → ∃[ u ] ( ParseTreeOf r u ) 
r-∃u ε = ( EmptyU , parseTreeOf )
r-∃u ($ c ` loc) = (LetterU c , parseTreeOf ) 
r-∃u (l ● r ` loc) = (PairU v u , parseTreeOf )
  where
    v : U l 
    v = proj₁ (r-∃u l) 
    u : U r 
    u = proj₁ (r-∃u r)
r-∃u (l + r ` loc) = ( LeftU v , parseTreeOf )
  where
    v : U l 
    v = proj₁ (r-∃u l) 
r-∃u (r * ε∉r ` loc) = ( ListU [] , parseTreeOf ) 
```





-- decidability of structural equality of parse trees
```agda

_⊢_≟_ : ∀ ( r : RE ) ( u v : U r ) → Dec ( u ≡ v )
_⊢_≟_ ε             EmptyU        EmptyU       = yes refl -- Agda.Builtin.Bool.Bool.true Decidable.because Nullary.ofʸ refl
_⊢_≟_ ($ c ` loc)   (LetterU .c)  (LetterU .c) = yes refl
_⊢_≟_ (l ● r ` loc) (PairU v₁ v₂) (PairU u₁ u₂) with l ⊢ v₁ ≟ u₁ | r ⊢ v₂ ≟ u₂
... | no ¬v₁≡u₁ | _ = no  λ pair-v₁v₂≡pair-u₁u₂ → ¬v₁≡u₁ (proj₁ (inv-pairU v₁ v₂ u₁ u₂ pair-v₁v₂≡pair-u₁u₂))
... | _         | no ¬v₂≡u₂ = no  λ pair-v₁v₂≡pair-u₁u₂ → ¬v₂≡u₂ (proj₂ (inv-pairU v₁ v₂ u₁ u₂ pair-v₁v₂≡pair-u₁u₂))
... | yes v₁≡u₁ | yes v₂≡u₂ = yes (Eq.cong₂ (λ x y → PairU {l} {r} {loc} x y)  v₁≡u₁  v₂≡u₂)
_⊢_≟_ (l + r ` loc) (LeftU v)     (LeftU u)     with l ⊢ v ≟ u
... | no ¬v≡u = no λ left-v≡left-u → ¬v≡u (inv-leftU v u left-v≡left-u) 
... | yes v≡u = yes (cong LeftU v≡u )
_⊢_≟_ (l + r ` loc) (LeftU v)     (RightU u)   = no λ () 
_⊢_≟_ (l + r ` loc) (RightU v)    (RightU u)    with r ⊢ v ≟ u
... | no ¬v≡u = no λ right-v≡right-u → ¬v≡u (inv-rightU v u right-v≡right-u) 
... | yes v≡u = yes (cong RightU v≡u )
_⊢_≟_ (l + r ` loc) (RightU v)    (LeftU u)   = no λ ()
_⊢_≟_ (r * ε∉r ` loc) (ListU [])  (ListU [])  = yes refl
_⊢_≟_ (r * ε∉r ` loc) (ListU (x ∷ xs)) (ListU (y ∷ ys)) with r ⊢ x ≟ y | (r * ε∉r ` loc) ⊢ ListU xs ≟ ListU ys
... | no ¬x≡y   | _                   = no λ list-x∷xs≡list-y∷ys → ¬x≡y (proj₁ (inv-listU x xs y ys list-x∷xs≡list-y∷ys ))
... | _         | no ¬list-xs≡list-ys = no λ list-x∷xs≡list-y∷ys → ¬list-xs≡list-ys (cong ListU (proj₂ (inv-listU x xs y ys list-x∷xs≡list-y∷ys )))
... | yes x≡y   | yes list-xs≡list-ys = yes (Eq.cong₂ (λ z zs → ListU (z ∷ zs)) x≡y (inv-listU1 xs ys list-xs≡list-ys))
_⊢_≟_ (r * ε∉r ` loc) (ListU (x ∷ xs)) (ListU []) = no λ () 
_⊢_≟_ (r * ε∉r ` loc) (ListU []) (ListU (y ∷ ys))  = no λ () 

```

flattening non empty list should not be empty.

```agda
¬|list-u∷us|≡[] : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { u : U r } { us : List (U r) }
     → ¬ (proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us)))) ≡ []
¬|list-u∷us|≡[] {r} {ε∉r} {loc} {u} {us} |list-u∷us|≡[] =  ([]∈⟦r⟧→¬ε∉r []∈⟦r⟧ ) ε∉r
  where
    |u|≡[] :  proj₁ ( flat {r} u ) ≡ []
    |u|≡[] = ++-conicalˡ (proj₁ ( flat {r} u )) (proj₁ (flat {r * ε∉r ` loc} (ListU us))) |list-u∷us|≡[]  
    []∈⟦r⟧ : [] ∈⟦ r ⟧ 
    []∈⟦r⟧  rewrite (sym |u|≡[]) = proj₂ ( flat {r} u )
  


```
