```agda
module cgp.ambig.Ambig where



import cgp.RE as RE
open RE using (RE)

import cgp.ParseTree as ParseTree
open ParseTree using (U; EmptyU; LetterU; LeftU; RightU; PairU; ListU; flat)



import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_ ; length ; head )

import Data.List.Properties
open Data.List.Properties using (∷-injective ; ++-identityʳ ; unfold-reverse ; ∷ʳ-++ ; ++-assoc )

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using (ℕ ; _>_ ; zero ; suc ; _+_ ) 

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst ; cong₂ )
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )



import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)


import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)


import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map ; tabulate )


open import Data.List.Relation.Unary.All.Properties using (map⁺)

open import Data.List.Relation.Unary.Any using (Any; here; there ; map)
import Data.List.Membership.Propositional
open Data.List.Membership.Propositional using (_∈_)

open import Function using (_∘_ ; flip )

import Relation.Nullary as Nullary 
open Nullary using (¬_ ; contraposition)



```


Definition:

A regular expression r is unambiguous iff for any parse trees flatten to the same word, they are identical.

```agda

data UnAmbig : RE → Set where
  unambig : ∀ ( r : RE )
    → ( u : U r )
    → ( v : U r )
    → ( proj₁ (flat u) ≡ proj₁ (flat v))
    → u ≡ v
    → UnAmbig r 
    


```


Definition:


```agda
data AmbigA1 : RE → Set where
  ambiga1 : ∀ ( r : RE )
    → List.length (mkAllEmpty r) Nat.> 1
    → AmbigA1 r 

```
