```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.GreedyLNE where

import cgp.RE as RE
open RE using (RE;  ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;   ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ; first ; ε∉r→¬first-r≡[] )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU;  unListU ; listU∘unListU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU )


import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; Flat-[] ; flat-[] ;  mkAllEmptyU≢[])


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ) 



import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming ( _⊢_>_  to  _⊢_>ᵍ_ )

import cgp.greedy.PartialDerivative as GreedyPD
open GreedyPD renaming ( parseAll[_,_] to parseAllᵍ[_,_] ) 

import cgp.lne.Order as LNEOrder
open LNEOrder renaming ( _⊢_>_  to  _⊢_>ˡ_ )

import cgp.lne.PartialDerivative as LNEPD
open LNEPD renaming ( parseAll[_,_] to parseAllˡ[_,_] ) 


import cgp.Utils as Utils
open Utils using (any-right-concat; any-left-concat ; all-concat ;  ∷-inj  ; ¬∷≡[]  ; inv-map-[]  )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_  )

import Data.List.Properties
open Data.List.Properties using (  ++-assoc ;  ++-identityʳ ; ++-identityˡ ; {-  unfold-reverse ; -} ∷ʳ-++ ; ++-cancelˡ ;  ++-conicalʳ ;  ++-conicalˡ  )


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

import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )

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

open import Level using (Level)

```

### Robustness definition 

```agda

data Robust : RE → Set where
  robust : ∀ { r : RE } { v₁ v₂ : U r }
    → ( to   : r ⊢ v₁ >ᵍ v₂ → r ⊢ v₁ >ˡ v₂ )
    → ( from : r ⊢ v₁ >ˡ v₂ → r ⊢ v₁ >ᵍ v₂ )
    -----------------------------------------
    → Robust r  
```


### ParseAll r w  means Robust?

step 1. We need to show that the sets of partial derivatives produced by Greedy.parseAll and LNE.parseAll are the equal

```agda


private
  variable
    a b c p ℓ : Level
    A : Set a
    B : Set b
    C : Set c


data SetEq { A : Set a } : ( xs ys : List A ) → Set a where
  setEq : { xs ys : List A }
    → All ( λ x → x ∈ ys ) xs 
    → All ( λ y → y ∈ xs ) ys 
    -------------------
    → SetEq xs ys


postulate
  greedy-lne-parseall : ∀ { r : RE } { w : List Char }
    → SetEq parseAllᵍ[ r , w ] parseAllˡ[ r , w ] 


```

step 2. if the multisets (lists) are in the same order, it implies robust?


```agda


```



### "Stable" Partial Derivative Descendant


step 3. if all pdi* of a r (regardless of greedy or lne ; since from step 1 we've proven they are the same set), are stable,
then r is having the same parseAll results for all w, i.e. it is lne-greedy robust.

```agda

data RightMostNull : RE → Set where
  rmn-+ε : ∀ { l : RE } { loc : ℕ } { ε∉l : ε∉ l }
    → RightMostNull ( l + ε ` loc )

  rmn-+* : ∀ { l r : RE } { ε∉r : ε∉ r } { loc₁ loc₂ : ℕ } { ε∉l : ε∉ l }
    → RightMostNull ( l + (r * ε∉r ` loc₁) ` loc₂)

  rmn-+● : ∀ { l s r : RE } { loc₁ loc₂ : ℕ } { ε∉l : ε∉ l } { ε∈s : ε∈ s } { ε∈r : ε∈ r }
    → RightMostNull ( l + ( s ● r ` loc₁ ) ` loc₂ )

  rmn-++ : ∀ { l s r : RE } { loc₁ loc₂ : ℕ } { ε∉l : ε∉ l } 
    → RightMostNull (s + r ` loc₁)
    ------------------------------------------------
    → RightMostNull ( l + ( s + r ` loc₁ ) ` loc₂ )


-- data StablePDI : RE → Set where
--   stable-pdd

```


### To show that the set of partial derivative descendants for 



```agda

data LNE : RE → Set where
  lne-ε  : LNE ε
  lne-$  : ∀ { c : Char } { loc : ℕ } → LNE ($ c ` loc)
  lne-●  : ∀ { l r : RE } { loc : ℕ }
    → LNE l
    → LNE r
    ----------------------------------
    → LNE ( l ● r ` loc )
  lne-+  : ∀ { l r : RE } { loc : ℕ }
    → ε∉ l
    → LNE r
    ---------------------------------
    → LNE ( l + r ` loc )
  lne-*  : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → LNE r
    --------------------------------
    → LNE ( r * ε∉r ` loc )
    


lne→robust : ∀ { r : RE }
  → LNE r
  → Robust r 
lne→robust {ε} lne-ε = robust {ε} {EmptyU} {EmptyU} (λ ()) λ ()


```
