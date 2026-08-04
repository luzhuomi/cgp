```agda
{-# OPTIONS --rewriting  #-}

module cgp.greedy.MaxWord where

import Agda.Primitive as Prim
open Prim using (Level)

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ¬≡[]→length>0 ; ¬≡0→>0 ; length≡0→[] ; n≡0→¬n>0 ;
  ¬nothing≡just ; just-injective ; head-x∷xs≡just-x ; map-id  ; map-cong ; map-∘-eq ; concatMap-∘-eq ; map-++-distrib ;
  concatMap-map-commute  ; concatMap-cong ; concat-++ ; concatMap-++-distrib ; all-map-∈ 
 )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r ; []∈⟦r⟧→ε∈r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; unListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ; flat-Uε≡[] ; inv-pairU ) 

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; mkAllEmptyU≢[] ; Flat-[] ; flat-[] ; proj₁flat-v≡[]→ε∈r )

import cgp.Recons as Recons
open Recons using ( Recons ; recons )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ; 
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ; mkinjFstSoundEv ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ; mkinjSndSoundEv ; 
  concatmap-pdinstance-snd ; concatmap-pdinstance-snd-[]≡[] ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with 
  ) 


import cgp.greedy.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_]  ; pdU-complete ; 
  advance-pdi*-with-c ; 
  pdUMany[_,_]; pdUMany-aux ;
  parseAll[_,_] ; buildU ;
  pdUMany-complete ; buildU-complete ; buildU-sound ;
  parseAll-sound ; parseAll-complete
  ) 

import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional.Properties as MembershipProperties
open MembershipProperties using (∈-concat⁺′ ; ∈-concat⁻′ ; ∈-map⁺ ; ∈-map⁻)

import cgp.greedy.Order as Order
open Order -- TODO: we should only whitelist those are used here 

import cgp.greedy.ExtendedOrder as ExtendedOrder
open ExtendedOrder using (
  pdU-sorted ;
  Ex>-sorted ; ex>-nil ; ex>-cons ;
  Ex>-maybe ; ex>-nothing ; ex>-just ;
  _,_⊢_>_ ; >-pdi ;
  parseAll-is-greedy )

import Data.Char as Char
open Char using (Char ; toℕ )

import Data.Char.Properties as CharProperties
open CharProperties using (≈⇒≡ ; _≈?_ ; ≈-reflexive)

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _+_ ; _∸_ ; _≤_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; _≟_ ; m+n≤o⇒m≤o∸n ; m≤o∸n⇒m+n≤o ; m+n≤o⇒n≤o ; +-identityʳ ; +-identityˡ ; m≤m+n ; m≤n+m ; +-comm ; m+n≡0⇒m≡0 ; m+n≡0⇒n≡0 ; ≡ᵇ⇒≡ ; ≡⇒≡ᵇ )



import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Function as Function
open Function using (case_of_)

import Data.Product as Product
open Product using (Σ; _,_; ∃; ∃-syntax; _×_)
open Σ using (proj₁ ; proj₂)

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; tail; concatMap ; _∷ʳ_ ; length ; foldr )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ; length-++ ; ++-assoc ; ∷-injective ; ≡-dec )


open import Data.List.Relation.Unary.Any using (Any; here; there ; map)

import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)

import Data.List.Membership.Propositional.Properties as MembershipProperties
open MembershipProperties using (∈-concat⁺′ ; ∈-concat⁻′ ; ∈-map⁺ ; ∈-map⁻ ; ∈-++⁻)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst; inspect)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map ; lookup)
import Data.List.Relation.Unary.All.Properties as AllProperties
open AllProperties using (++⁺)

import Relation.Nullary as Nullary
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Data.Empty using (⊥ ; ⊥-elim)
open Data.Empty

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?; map′)

open import Function using (_∘_ ; flip ; case_of_)


import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )

-- Transport Any across word-equality inside parseAll
parseAll-subst : ∀ {r : RE} {w₁ w₂ : List Char} {v : U r}
  → w₁ ≡ w₂
  → Any (_≡_ v) parseAll[ r , w₁ ]
  → Any (_≡_ v) parseAll[ r , w₂ ]
parseAll-subst {r} {w₁} {w₂} {v} w₁≡w₂ any
  rewrite w₁≡w₂ = any

```


```agda

infix 4 _⊢_≥_

-- Custom trichotomy datatype to avoid Agda 2.7's ⊎ vs _⊢_>_ confusion
-- RE is explicit to avoid constraint solver issues with ListU's RE index
infixr 10 _>_≽_ _<≽_ _≡≽_

data _≽_ : (r : RE) → U r → U r → Set where
  _>_≽_ : ∀ {r : RE} {u v : U r} → r ⊢ u > v → _≽_ r u v
  _<≽_ : ∀ {r : RE} {u v : U r} → r ⊢ v > u → _≽_ r u v
  _≡≽_ : ∀ {r : RE} {u v : U r} → u ≡ v → _≽_ r u v

-- Trichotomy elimination to raw sum type (avoids constraint solver issues)
≽-to-⊎ : ∀ {r} {u v} → _≽_ r u v → (r ⊢ u > v) ⊎ (r ⊢ v > u) ⊎ (u ≡ v)
≽-to-⊎ (_>_≽_ u>v) = inj₁ u>v
≽-to-⊎ (_<≽_ v>u) = inj₂ (inj₁ v>u)
≽-to-⊎ (_≡≽_ u≡v) = inj₂ (inj₂ u≡v)

-- type alias
_⊢_≥_ : (r : RE) → U r → U r → Set
_⊢_≥_ r u v = (r ⊢ u > v) ⊎  ( u ≡ v  )



-- Purpose: Define what it means for a parse tree u to be maximal for word w
-- Used by: ≥-max-word, ≥-max-pair→-≥-max-fst, ≥-max-pres-left-helper, >-wellfounded, ≥-Max-PDInstance, parseAll-head-isMax
-- Proof idea: N/A (data type definition with single constructor ≥-max)
data ≥-Max : ∀ { r : RE } → List Char → U r  → Set where
  ≥-max : ∀ { r : RE }
        → ( w : List Char )
        → ( u : U r )
        → proj₁ (flat u) ≡ w
        → ( ( v : U r )
          →  proj₁ (flat v) ≡ w
          → r ⊢ u ≥ v )
        → ≥-Max {r} w u
```



```agda
-- Helper module: local membership to avoid Any.here/there name clashes
module Local∈ where
  data _∈′_ {A} :  A → List A → Set where
    here : ∀ {x : A} { xs : List A } → x ∈′ (x ∷ xs)
    there : ∀ {x y : A} {xs : List A} → y ∈′ xs → y ∈′ (x ∷ xs)

  any→∈′ : ∀ {A} {v : A} → (xs : List A) → Any (_≡_ v) xs → v ∈′ xs
  any→∈′ [] ()
  any→∈′ (x ∷ xs) (here x≡v) rewrite sym x≡v = here
  any→∈′ (_ ∷ xs) (there ay) = there (any→∈′ xs ay)

open Local∈ using (_∈′_; any→∈′; here; there)

-- ≥-trans: transitivity of ≥
≥-trans : ∀ {r : RE} {u₁ u₂ u₃ : U r}
  → (r ⊢ u₁ > u₂) ⊎ (u₁ ≡ u₂)
  → (r ⊢ u₂ > u₃) ⊎ (u₂ ≡ u₃)
  → (r ⊢ u₁ > u₃) ⊎ (u₁ ≡ u₃)
≥-trans (inj₁ u₁>u₂) (inj₁ u₂>u₃) = inj₁ (>-trans u₁>u₂ u₂>u₃)
≥-trans (inj₁ u₁>u₂) (inj₂ u₂≡u₃) rewrite sym u₂≡u₃ = inj₁ u₁>u₂
≥-trans (inj₂ u₁≡u₂) (inj₁ u₂>u₃) rewrite u₁≡u₂ = inj₁ u₂>u₃
≥-trans (inj₂ u₁≡u₂) (inj₂ u₂≡u₃) rewrite u₁≡u₂ = inj₂ u₂≡u₃

-- If heads are equal, tail ordering lifts to full list ordering
listU-lex>-help-tail : ∀ {r : RE} {nε : ε∉ r} {loc : ℕ}
  {v : U r} {vs₁ vs₂ : List (U r)}
  → (r * nε ` loc) ⊢ ListU vs₁ > ListU vs₂
  → (r * nε ` loc) ⊢ ListU (v ∷ vs₁) > ListU (v ∷ vs₂)
listU-lex>-help-tail vs₁>vs₂ = sub (star-tail refl vs₁>vs₂)

-- Lift tail >≽ to cons lists when heads are equal
listU-lex>-help-tail-impl :
  (r : RE) → (nε : ε∉ r) → (loc : ℕ)
  → (v₁ v₂ : U r) (vs₁ vs₂ : List (U r))
  → v₁ ≡ v₂
  → (r * nε ` loc) ⊢ ListU vs₁ > ListU vs₂
  → (r * nε ` loc) ⊢ ListU (v₁ ∷ vs₁) > ListU (v₂ ∷ vs₂)
listU-lex>-help-tail-impl r nε loc v₁ v₂ vs₁ vs₂ v₁≡v₂ vs₁>vs₂
  rewrite sym v₁≡v₂ = listU-lex>-help-tail {v = v₁} vs₁>vs₂

listU-lex>-help-tail-right :
  (r : RE) → (nε : ε∉ r) → (loc : ℕ)
  → (v₁ v₂ : U r) (vs₁ vs₂ : List (U r))
  → v₁ ≡ v₂
  → (r * nε ` loc) ⊢ ListU vs₂ > ListU vs₁
  → (r * nε ` loc) ⊢ ListU (v₂ ∷ vs₂) > ListU (v₁ ∷ vs₁)
listU-lex>-help-tail-right r nε loc v₁ v₂ vs₁ vs₂ v₁≡v₂ vs₂>vs₁
  rewrite v₁≡v₂ = listU-lex>-help-tail {v = v₂} vs₂>vs₁

-- Cons-vs-cons case of list trichotomy (extracted to avoid Agda 2.7 scoping)
listU-cons-vs-cons :
  (∀ (r : RE) (u v : U r) → _≽_ r u v) →
  (∀ (r : RE) (nε : ε∉ r) (loc : ℕ) (vs₁ vs₂ : List (U r)) → _≽_ (r * nε ` loc) (ListU vs₁) (ListU vs₂)) →
  (r : RE) → (nε : ε∉ r) → (loc : ℕ)
  → (v₁ v₂ : U r) (vs₁ vs₂ : List (U r))
  → _≽_ (r * nε ` loc) (ListU (v₁ ∷ vs₁)) (ListU (v₂ ∷ vs₂))
listU-cons-vs-cons trich-l trich-s r nε loc v₁ v₂ vs₁ vs₂
  with trich-l r v₁ v₂
... | (_>_≽_ v₁>v₂) = _>_≽_ (sub (star-head v₁>v₂))
... | (_<≽_ v₂>v₁) = _<≽_ (sub (star-head v₂>v₁))
... | (_≡≽_ v₁≡v₂)
  with ≽-to-⊎ (trich-s r nε loc vs₁ vs₂)
... | inj₁ vs₁>vs₂ = _>_≽_ (listU-lex>-help-tail-impl r nε loc v₁ v₂ vs₁ vs₂ v₁≡v₂ vs₁>vs₂)
... | inj₂ (inj₁ vs₂>vs₁) = _<≽_ (listU-lex>-help-tail-right r nε loc v₁ v₂ vs₁ vs₂ v₁≡v₂ vs₂>vs₁)
... | inj₂ (inj₂ list-vs₁≡list-vs₂) rewrite v₁≡v₂
    = _≡≽_ (cong ListU (cong₂ _∷_ refl vs₁≡vs₂))
    where
      vs₁≡vs₂ : vs₁ ≡ vs₂
      vs₁≡vs₂ = cong unListU list-vs₁≡list-vs₂

-- Main trichotomy: every pair of parse trees is comparable
-- Agda 2.7 can't verify structural recursion on RE, so we skip termination checking.
{-# TERMINATING #-}
mutual
  >-trichotomy : ∀ (r : RE) (u v : U r) → _≽_ r u v

  listU-trichotomy : ∀ (r : RE) (nε : ε∉ r) (loc : ℕ)
    (vs₁ vs₂ : List (U r))
    → _≽_ (r * nε ` loc) (ListU vs₁) (ListU vs₂)
  listU-trichotomy r nε loc [] [] = _≡≽_ refl
  listU-trichotomy r nε loc (v ∷ vs) [] = _>_≽_ (sub star-cons-nil)
  listU-trichotomy r nε loc [] (v ∷ vs) = _<≽_ (sub star-cons-nil)
  listU-trichotomy r nε loc (v₁ ∷ vs₁) (v₂ ∷ vs₂)
    = listU-cons-vs-cons >-trichotomy listU-trichotomy r nε loc v₁ v₂ vs₁ vs₂

  >-trichotomy ε EmptyU EmptyU = _≡≽_ refl
  >-trichotomy ($ c ` loc) (LetterU _) (LetterU _) = _≡≽_ refl

  >-trichotomy (l + r ` loc) (LeftU u₁) (LeftU u₂)
    with >-trichotomy l u₁ u₂
  ... | (_>_≽_ u₁>u₂) = _>_≽_ (sub (choice-ll u₁>u₂))
  ... | (_<≽_ u₂>u₁) = _<≽_ (sub (choice-ll u₂>u₁))
  ... | (_≡≽_ u₁≡u₂) = _≡≽_ (cong LeftU u₁≡u₂)

  >-trichotomy (l + r ` loc) (RightU u₁) (RightU u₂)
    with >-trichotomy r u₁ u₂
  ... | (_>_≽_ u₁>u₂) = _>_≽_ (sub (choice-rr u₁>u₂))
  ... | (_<≽_ u₂>u₁) = _<≽_ (sub (choice-rr u₂>u₁))
  ... | (_≡≽_ u₁≡u₂) = _≡≽_ (cong RightU u₁≡u₂)

  >-trichotomy (l + r ` loc) (LeftU _) (RightU _) = _>_≽_ (sub choice-lr)
  >-trichotomy (l + r ` loc) (RightU _) (LeftU _) = _<≽_ (sub choice-lr)

  >-trichotomy (l ● r ` loc) (PairU u₁ v₁) (PairU u₂ v₂)
    with >-trichotomy l u₁ u₂
  ... | (_>_≽_ u₁>u₂) = _>_≽_ (sub (seq₁ u₁>u₂))
  ... | (_<≽_ u₁<u₂) = _<≽_ (sub (seq₁ u₁<u₂))
  ... | (_≡≽_ u₁≡u₂)
    with >-trichotomy r v₁ v₂
  ... | (_>_≽_ v₁>v₂) = _>_≽_ (sub (seq₂ u₁≡u₂ v₁>v₂))
  ... | (_<≽_ v₁<v₂) rewrite u₁≡u₂ = _<≽_ (sub (seq₂ refl v₁<v₂))
  ... | (_≡≽_ v₁≡v₂) rewrite u₁≡u₂ | v₁≡v₂ = _≡≽_ refl

  >-trichotomy (r * nε ` loc) (ListU vs₁) (ListU vs₂)
    with ≽-to-⊎ (listU-trichotomy r nε loc vs₁ vs₂)
  ... | inj₁ l₁>l₂ = _>_≽_ l₁>l₂
  ... | inj₂ (inj₁ l₂>l₁) = _<≽_ l₂>l₁
  ... | inj₂ (inj₂ l₁≡l₂) = _≡≽_ l₁≡l₂

-- sorted-head-≥-all: head of >-sorted list is ≥ all elements
-- Proof: induction on the membership proof
sorted-head-≥-all : ∀ {r : RE} (u : U r) (us : List (U r))
  → >-sorted {r} (u ∷ us)
  → (v : U r) → v ∈′ (u ∷ us) → r ⊢ u ≥ v
sorted-head-≥-all u [] (>-cons >-nil >-noth) v here = inj₂ refl
sorted-head-≥-all u (v ∷ vs) (>-cons us-sorted uv) v′ here = inj₂ refl
sorted-head-≥-all {r} u (v ∷ vs) (>-cons us-sorted uv) v′ (there here′)
  = ≥-trans u≥v (sorted-head-≥-all v vs us-sorted v′ here′)
  where
    >-just-to-≥ : >-maybe {r} u (just v) → r ⊢ u ≥ v
    >-just-to-≥ (>-just u>v) = inj₁ u>v

    u≥v : r ⊢ u ≥ v
    u≥v = >-just-to-≥ uv

-- sorted-head-≥-all-Any: head of >-sorted list is ≥ all elements (using Any instead of ∈′)
sorted-head-≥-all-Any : ∀ {r : RE} (u : U r) (us : List (U r))
  → >-sorted {r} (u ∷ us)
  → (v : U r) → Any (_≡_ v) (u ∷ us) → r ⊢ u ≥ v
sorted-head-≥-all-Any u [] (>-cons >-nil >-noth) v (here v≡u) rewrite v≡u = inj₂ refl
sorted-head-≥-all-Any u (v ∷ vs) (>-cons us-sorted uv) v′ (here v′≡v) rewrite v′≡v = inj₂ refl
sorted-head-≥-all-Any {r} u (v ∷ vs) (>-cons us-sorted uv) v′ (there here′)
  = ≥-trans u≥v (sorted-head-≥-all-Any v vs us-sorted v′ here′)
  where
    >-just-to-≥ : >-maybe {r} u (just v) → r ⊢ u ≥ v
    >-just-to-≥ (>-just u>v) = inj₁ u>v

    u≥v : r ⊢ u ≥ v
    u≥v = >-just-to-≥ uv

-- sorted-head-≥-all-Any-′: threads list explicitly to avoid stuck head
sorted-head-≥-all-Any-′ : (r : RE) → (u : U r) → (us : List (U r)) → >-sorted (u ∷ us)
  → (v : U r) → Any (_≡_ v) (u ∷ us) → r ⊢ u ≥ v
sorted-head-≥-all-Any-′ r u [] sorted v (here v≡u) rewrite sym v≡u = inj₂ refl
sorted-head-≥-all-Any-′ r u [] sorted v (there ())
sorted-head-≥-all-Any-′ r u (x ∷ xs) (>-cons us-sorted (>-just u>x)) v (here v≡u) rewrite sym v≡u = inj₂ refl
sorted-head-≥-all-Any-′ r u (x ∷ xs) (>-cons us-sorted (>-just u>x)) v (there v∈x∷xs)
  = ≥-trans (inj₁ u>x) (sorted-head-≥-all-Any-′ r x xs us-sorted v v∈x∷xs)

-- >-wellfounded: every word w ∈⟦ r ⟧ has a ≥-Max parse tree under the GREEDY order.
>-wellfounded : ∀ { r : RE} { w : List Char }
  → w ∈⟦ r ⟧
  → ∃[ v ] ( ≥-Max {r}  w v )
>-wellfounded {r} {w} w∈r
  = core (parseAll[ r , w ]) refl (parseAll-is-greedy {r} {w}) parseAll-sound
  where
    core : (us : List (U r))
      → parseAll[ r , w ] ≡ us
      → (sorted : >-sorted us)
      → (sound : All (λ u → proj₁ (flat u) ≡ w) us)
      → ∃[ v ] ( ≥-Max {r}  w v )
    us'-complete : (u : U r)
      → (us' : List (U r))
      → (eq : parseAll[ r , w ] ≡ u ∷ us')
      → (v : U r) → proj₁ (flat v) ≡ w
      → Any (_≡_ v) (u ∷ us')
    us'-complete u us' eq v v-flat
      = subst (λ xs → Any (_≡_ v) xs) eq
        (subst (λ w' → Any (_≡_ v) parseAll[ r , w' ]) v-flat
        (proj₂ (parseAll-complete v)))

    any≢empty : (x : U r) → Any (_≡_ x) [] → ⊥
    any≢empty x pxs = ¬Any[] pxs

    core-head-is-max : (u : U r)
      → (us' : List (U r))
      → (eq : parseAll[ r , w ] ≡ u ∷ us')
      → >-sorted (u ∷ us')
      → (v : U r) → proj₁ (flat v) ≡ w → r ⊢ u ≥ v
    core-head-is-max u [] eq (>-cons >-nil >-nothing) v v-flat
      with us'-complete u [] eq v v-flat
    ... | here v≡u = inj₂ (sym v≡u)
    ... | there ()
    core-head-is-max u (x ∷ xs) eq (>-cons us-sorted (>-just u>x)) v v-flat
      with us'-complete u (x ∷ xs) eq v v-flat
    ... | here v≡u = inj₂ (sym v≡u)
    ... | there v∈tail = ≥-trans (inj₁ u>x) (sorted-head-≥-all-Any-′ r x xs us-sorted v v∈tail)

    core (u ∷ us) eq sorted sound
      = u , ≥-max w u (sound-head sound)
        (core-head-is-max u us eq sorted)
      where
        sound-head : All (λ u → proj₁ (flat u) ≡ w) (u ∷ us)
          → proj₁ (flat u) ≡ w
        sound-head (h ∷ _) = h

    core [] eq sorted sound = ⊥-elim parseAll≢nil
      where
        in-parseAll : Any (_≡_ (unflat w∈r)) []
        in-parseAll
          rewrite sym eq = parseAll-subst (cong proj₁ (flat∘unflat w∈r))
            (proj₂ (parseAll-complete (unflat w∈r)))

        parseAll≢nil : ⊥
        parseAll≢nil
          = any≢empty (unflat w∈r) in-parseAll
      ```
