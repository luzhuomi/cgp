```agda
module cgp.Word where

import cgp.RE as RE
open RE using (RE;  ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈ ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_)

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap )

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
-- open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)

import Relation.Nullary as Nullary 
import Relation.Nullary.Negation using (contradiction; contraposition)

open Nullary using (¬_)

open import Function using (_∘_)

```


### Defintion 5 : Word
A word is a sequence of literals.

 w :: = [] | ℓ ∷ w

We represent a word as a list of characters in Agda. 


### Definition 6 : word-regexp membership relation w ∈ ⟦ r ⟧ 

Let w be word, r be regular expression, we define the membership relationship as follows

  [] ∈ ⟦ ε ⟧ 

  ℓ  ∈ ⟦ ℓ ⟧


  xs ∈ ⟦ l ⟧
  ys ∈ ⟦ r ⟧
 ----------------------
  xs ++ ys ∈ ⟦ l ● r ⟧ 

  xs ∈ ⟦ l ⟧
  --------------
  xs ∈ ⟦ l + r ⟧


  ys ∈ ⟦ r ⟧
  --------------
  ys ∈ ⟦ l + r ⟧

  xs ∈ ⟦ ε + (r ● r*) ⟧ 
  ---------------------
  xs ∈ ⟦ r * ⟧ 


```agda
data _∈⟦_⟧ : List Char → RE → Set where
  ε      : [] ∈⟦ ε ⟧
  $_      : ∀ { loc : ℕ } ( c : Char ) → [ c ] ∈⟦ $ c ` loc ⟧ 
  _●_⧺_  : ∀ {xs ys zs : List Char} { l r : RE } { loc : ℕ }
        → xs ∈⟦ l ⟧
        → ys ∈⟦ r ⟧
        → xs ++ ys ≡ zs            -- this evidence is essential, without which the pair case in the unflat will not type-check, why?
        -------------------------
        → zs ∈⟦ l ● r ` loc ⟧
  _+L_   : ∀ { l : RE } {xs : List Char} { loc : ℕ } ( r : RE )
        → xs ∈⟦ l ⟧
        -------------------------
        → xs ∈⟦ l + r ` loc  ⟧
  _+R_ : ∀ { r : RE } {xs : List Char} { loc : ℕ } ( l : RE )
        → xs ∈⟦ r ⟧
        -------------------------
        → xs ∈⟦ l + r ` loc ⟧        
  _*   : ∀ { r : RE } { nε : ε∉ r } { xs : List Char } { loc : ℕ } 
        → xs ∈⟦ ε + (r ● (r * nε ` loc ) ` loc ) ` loc  ⟧
        --------------------------
        → xs ∈⟦ r * nε ` loc  ⟧

```  


> KL: The above definition is adopted from [1], except that the quantifers (for the constructors) were missing from [1].


An interesting observation is that the above definition is phrased in a deduction system, which is unlike the convention, in which we first
 define the mapping from regular expressions to sets of words, then the test can be expressed in terms of a set member test.


Definition 6':  𝓛( r ) mapping regular expression to set of strings

ℒ( r ), the language of r, defines the set of all string inhabiting in r.

   ℒ( ϕ ) = {}
   ℒ( ε ) = { [] }
   ℒ( ℓ ) = { ℓ ∷ [] }
   ℒ( l ● r ) = { w₁ ++ w₂ | w₁ ∈ ℒ( l ) ∧ w₂ ∈ ℒ( r ) }
   ℒ( l + r ) = ℒ( l ) ∪ ℒ( r )
   ℒ( r * )   = { w₁ ++ ... ++ wₙ | n ≥ 0 ∧ wᵢ ∈ ℒ( r ) ∧ i ∈ {1,...,n} }

   then
   w ∈⟦ r ⟧ can be defined as w ∈ ℒ( r ) where _∈_ is the set member relation.
   
### TODO: can we implement the above in agda?
If so, can we show that w ∈⟦ r ⟧ iff w ∈ ℒ( r )

> KL: Conjecture, to do so we need a lazy set, 𝓛( r ) maps r to a lazy set.
> The _∈_ test must be done coinductively, otherwise b ∈ 𝓛( a* ) won't terminate.


#### Sub Lemma 6.1 ( empty word inhabitance implies negation of non-nullability )

Let r be a non problematic regular expression.
Let [] ∈ ⟦ r ⟧.
Then ¬ ( ε∉ r ).

```agda
[]∈⟦r⟧→¬ε∉r : ∀ { r : RE } → [] ∈⟦ r ⟧  → ¬ ( ε∉ r )
[]∈⟦r⟧→¬ε∉r {ε} = λ x ε∉ε →  (ε∉r→¬ε∈r ε∉ε) ε∈ε
[]∈⟦r⟧→¬ε∉r {$ c ` loc } = λ()
[]∈⟦r⟧→¬ε∉r { s ● t ` loc } ( _●_⧺_ {[]} {[]} {[]} {s} {t} {loc} []∈s []∈t eq ) ε∉s●t with  ε∉s●t
...                         | ε∉fst  ε∉s = ([]∈⟦r⟧→¬ε∉r  []∈s) ε∉s
...                         | ε∉snd  ε∉t = ([]∈⟦r⟧→¬ε∉r  []∈t) ε∉t
[]∈⟦r⟧→¬ε∉r { s + t ` loc } (  _+L_ {s} {[]} {loc} t []∈s ) ε∉s+t with ε∉s+t
...                         | ε∉ ε∉s + ε∉t = ([]∈⟦r⟧→¬ε∉r  []∈s) ε∉s
[]∈⟦r⟧→¬ε∉r { s + t ` loc } (  _+R_ {t} {[]} {loc} s []∈t ) ε∉s+t with ε∉s+t
...                         | ε∉ ε∉s + ε∉t = ([]∈⟦r⟧→¬ε∉r  []∈t) ε∉t
[]∈⟦r⟧→¬ε∉r { s * ε∉s ` loc } ( _* {s} {ε∉s} {[]} {loc} []∈ε+s●s* )  ε∉s* =  (ε∉r→¬ε∈r ε∉s*) ε∈* 


[]∈⟦r⟧→ε∈r : ∀ { r : RE } → [] ∈⟦ r ⟧ → ε∈ r
[]∈⟦r⟧→ε∈r = RE.¬ε∉r→ε∈r ∘ []∈⟦r⟧→¬ε∉r 
```

```agda
-- aux lemma needed for proving sub lemma in partial-derivatives, such as ¬recons-[]-from-pdinstance-star
¬c∷w≡[] : ∀ { c : Char } { w : List Char } → ¬ c ∷ w ≡ []
¬c∷w≡[] {c} {w} = λ()

```

```agda
{-
import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

postulate
  enum : ( r : RE ) → ( w : List Char ) → List ( w ∈⟦ r ⟧ )
-}  
{-  
enum ϕ _ = []
enum ε [] = [  ε ]
enum ε (_ ∷ _) = [] 
enum ($ c ` loc ) [] = []
enum ($ c ` loc ) (c' ∷ []) with c Char.≟ c'
...                            | yes refl = [ $ c' ]
...                            | no  _    = []
enum ($ c ` loc ) (c' ∷ cs) = []
-}
{-
enum (l ● r ` loc ) xs  =
  let n = List.length xs
      ps = List.upTo n
      xxs = map (λ p → List.splitAt p xs ) ps
  in concatMap (λ { yzs →
                      let ys∈ls = enum l (proj₁ yzs)
                          zs∈rs = enum r (proj₂ yzs)
                      in concatMap (λ ys∈l → (List.map (λ zs∈r → ( ys∈l ● zs∈r ⧺ refl ) ) zs∈rs ) ) ys∈ls } ) xxs
-}    


```
