```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.greedylne.GreedyLNEUtils where

import cgp.RE as RE
open RE using (RE;  ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;   ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ; first ; ε∉r→¬first-r≡[] )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU;  unListU ; listU∘unListU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU ; r-∃u)


import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; Flat-[] ; flat-[] ;  mkAllEmptyU≢[] ; proj₁flat-v≡[]→ε∈r )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* )



import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming ( _⊢_>_  to  _⊢_>ᵍ_
  ; >→¬≡ to >ᵍ→¬≡
  ; u>v→¬v>u to u>ᵍv→¬v>ᵍu
  )

import cgp.greedy.PartialDerivative as GreedyPD
open GreedyPD renaming ( parseAll[_,_] to parseAllᵍ[_,_] ; parseAll-sound to parseAllᵍ-sound ; parseAll-complete to parseAllᵍ-complete )


import cgp.greedy.MaxWord as GreedyMax
open GreedyMax renaming ( ≥-Max to ≥-Maxᵍ ; ≥-max to ≥-maxᵍ )



import cgp.lne.Order as LNEOrder
open LNEOrder renaming ( _⊢_>_  to  _⊢_>ˡ_
  ; >→¬≡ to >ˡ→¬≡
  )

import cgp.lne.PartialDerivative as LNEPD
open LNEPD renaming ( parseAll[_,_] to parseAllˡ[_,_]
  ; parseAll-sound to parseAllˡ-sound
  ; parseAll-complete to parseAllˡ-complete
     )

import cgp.lne.MaxWord as LNEMax
open LNEMax renaming ( ≥-Max to ≥-Maxˡ ; ≥-max to ≥-maxˡ )


import cgp.Utils as Utils
open Utils using (any-right-concat; any-left-concat ; all-concat ;  ∷-inj  ; ¬∷≡[]  ; inv-map-[] ; length>0→¬≡[] ; ¬≡[]→¬length≡0 ; ¬≡[]→length>0 ; []→length≡0 ; length≡0→[] ; >0→¬≡0 ; n≡0→¬n>0 )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-assoc ;  ++-identityʳ ; ++-identityˡ ; {-  unfold-reverse ; -} ∷ʳ-++ ; ++-cancelˡ ;  ++-conicalʳ ;  ++-conicalˡ ; length-++  )


import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _>_ ; _+_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( m+n≡0⇒m≡0 ; +-monoʳ-≤ ; <⇒≤ ; ≤-trans ; ≤-refl ; +-identityˡ ; +-identityʳ ; m≤m+n ; +-suc )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst; _≢_)
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

import Data.Empty as Empty
open Empty using (⊥-elim; ⊥)

import Relation.Nullary as Nullary
import Relation.Nullary.Negation as Negation
open Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

open import Function using (_∘_ ; flip)

open import Level using (Level)

```

```agda

-- flat lemmas to avoid stuck terms from internal `with` clauses
¬proj₁flat-cons≡[] : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { u : U r } { us : List (U r) }
    → ¬ ( proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us))) ≡ [] )
¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us} proj₁flat-list-u∷us≡[] = (ε∉r→¬ε∈r ε∉r) (proj₁flat-v≡[]→ε∈r proj₁flat-u≡[])
  where
    proj₁flat-u++proj₁flat-list-us≡[] : proj₁ (flat u) ++ proj₁ (flat (ListU {r} {ε∉r} {loc} us)) ≡ []
    proj₁flat-u++proj₁flat-list-us≡[] rewrite  proj₁flat-list-u∷us≡[]  = refl
    proj₁flat-u≡[] :  proj₁ (flat u) ≡ []
    proj₁flat-u≡[] = ++-conicalˡ ( proj₁ (flat u) ) (proj₁ (flat (ListU {r} {ε∉r} {loc} us))) proj₁flat-u++proj₁flat-list-us≡[]

proj₁flat-nil≡[] : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → proj₁ (flat (ListU {r} {ε∉r} {loc} [] )) ≡ []
proj₁flat-nil≡[] {r} {ε∉r} {loc} = refl

+-monoʳ-<>0 : ∀ (a b : ℕ) → a > 0 → a + b > 0
+-monoʳ-<>0 (suc k) b _ = Nat.s≤s (Nat.z≤n {k + b})

+-monoˡ-<>0 : ∀ (a b : ℕ) → b > 0 → a + b > 0
+-monoˡ-<>0 a (suc k) _ = subst (λ x → 1 Nat.≤ x) (sym (+-suc a k)) (Nat.s≤s (Nat.z≤n {a + k}))

flat-list-cons : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { u : U r } { us : List (U r) }
    → proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us))) ≡ proj₁ (flat u) ++ proj₁ (flat (ListU {r} {ε∉r} {loc} us))
flat-list-cons {r} {ε∉r} {loc} {u} {us} with flat {r} u | flat {r * ε∉r ` loc} (ListU {r} {ε∉r} {loc} us)
... | _ , _ | _ , _ = refl

flat-pair : ∀ { l r : RE } { loc : ℕ } { u : U l } { v : U r }
    → proj₁ (flat (PairU {l} {r} {loc} u v)) ≡ proj₁ (flat u) ++ proj₁ (flat v)
flat-pair {l} {r} {loc} {u} {v} with flat {l} u | flat {r} v
... | _ , _ | _ , _ = refl

-- Length of flat PairU = sum of lengths
flat-pair-len : ∀ { l r : RE } { loc : ℕ } { u : U l } { v : U r }
  → length (proj₁ (flat (PairU {l} {r} {loc} u v))) ≡ length (proj₁ (flat u)) + length (proj₁ (flat v))
flat-pair-len {l} {r} {loc} {u} {v} with flat {l} u | flat {r} v
... | xs₁ , _ | xs₂ , _ = length-++ {A = Char} xs₁ {xs₂}

zero-plus-length : ∀ ( xs : List Char ) → 0 + length xs ≡ length xs
zero-plus-length [] = refl
zero-plus-length (x ∷ xs) rewrite zero-plus-length xs = refl

empty-concat-identity : ∀ ( xs : List Char ) → [] ++ xs ≡ xs
empty-concat-identity [] = refl
empty-concat-identity (x ∷ xs) rewrite empty-concat-identity xs = refl

flat-LeftU : ∀ { l r : RE } { loc : ℕ } { u : U l } → proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ proj₁ (flat u)
flat-LeftU {l} {r} {loc} {u} with flat {l} u
... | xs , _ = refl

flat-RightU : ∀ { l r : RE } { loc : ℕ } { u : U r } → proj₁ (flat (RightU {l} {r} {loc} u)) ≡ proj₁ (flat u)
flat-RightU {l} {r} {loc} {u} with flat {r} u
... | xs , _ = refl

flat-LeftU-len : ∀ { l r : RE } { loc : ℕ } { u : U l }
  → length (proj₁ (flat (LeftU {l} {r} {loc} u))) ≡ length (proj₁ (flat u))
flat-LeftU-len {l} {r} {loc} {u} with flat {l} u
... | xs , _ = refl

flat-RightU-len : ∀ { l r : RE } { loc : ℕ } { u : U r }
  → length (proj₁ (flat (RightU {l} {r} {loc} u))) ≡ length (proj₁ (flat u))
flat-RightU-len {l} {r} {loc} {u} with flat {r} u
... | xs , _ = refl

postulate
  flat-pair-u≡[]-v>0 : ∀ { l r : RE } { loc : ℕ } { u₁ : U l } { v₁ : U r }
    → length (proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} u₁ v₁))) > 0
    → proj₁ (flat {l} u₁) ≡ []
    → length (proj₁ (flat {r} v₁)) > 0

flat-list-cons-⊥ : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { u : U r } { us : List (U r) }
    → length (proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us)))) ≡ 0
    → ⊥
flat-list-cons-⊥ {r} {ε∉r} {loc} {u} {us} len≡0 = >0→¬≡0 len-u>0 len-u≡0
  where
    flat-u : List Char
    flat-u = proj₁ (flat u)

    flat-us : List Char
    flat-us = proj₁ (flat (ListU {r} {ε∉r} {loc} us))

    len-rewritten : length (flat-u ++ flat-us) ≡ 0
    len-rewritten rewrite flat-list-cons {r} {ε∉r} {loc} {u} {us} = len≡0

    len-add : (length flat-u + length flat-us) ≡ 0
    len-add = subst (λ l → l ≡ 0) (length-++ {A = Char} flat-u) len-rewritten

    len-u≡0 : length flat-u ≡ 0
    len-u≡0 = m+n≡0⇒m≡0 (length flat-u) len-add

    len-u>0 : length flat-u > 0
    len-u>0 = ¬≡[]→length>0 (ε∉r→¬ε∈r ε∉r ∘ proj₁flat-v≡[]→ε∈r)


```

```agda

-- type alias
not-empty : List Char → Set
not-empty xs = ¬ (xs ≡ [])

lne-be : ∀ { r : RE } { u v : U r }
  → proj₁ (flat u) ≡ []
  → proj₁ (flat v) ≡ []
  → LNEOrder._⊢_>ⁱ_ r u v
  → LNEOrder._⊢_>_ r u v
lne-be u≡[] v≡[] u>ⁱv = LNEOrder.be
  (trans ([]→length≡0  u≡[]) (sym ([]→length≡0  v≡[])))
  ([]→length≡0  v≡[]) u>ⁱv

lne-bne : ∀ { r : RE } { u v : U r }
  → ¬ (proj₁ (flat u) ≡ [])
  → ¬ (proj₁ (flat v) ≡ [])
  → LNEOrder._⊢_>ⁱ_ r u v
  → LNEOrder._⊢_>_ r u v
lne-bne ¬u≡[] ¬v≡[] u>ⁱv =
  LNEOrder.bne (¬≡[]→length>0 ¬u≡[]) (¬≡[]→length>0 ¬v≡[]) u>ⁱv

lne-lne : ∀ { r : RE } { u v : U r }
  → ¬ (proj₁ (flat u) ≡ [])
  → proj₁ (flat v) ≡ []
  → LNEOrder._⊢_>_ r u v
lne-lne ¬u≡[] v≡[] =
  LNEOrder.lne (¬≡[]→length>0 ¬u≡[]) ([]→length≡0 v≡[])

letter-flat : ∀ { c : Char } { loc : ℕ }
  → proj₁ (flat { $ c ` loc } (LetterU c)) ≡ c ∷ []
letter-flat = refl

flat-empty? : ∀ { r : RE } ( v : U r )
  → (proj₁ (flat v) ≡ []) ⊎ not-empty (proj₁ (flat v))
flat-empty? v with flat v
... | [] , _ = inj₁ refl
... | c ∷ cs , _ = inj₂ (λ ())

```

```agda

-- Purpose: Transport equal flattened words through a concatenating parse pair.
-- Used by: Repair branches that replace one component of a PairU tree.
-- Main idea: Rewrite both pair flattenings to concatenations and apply congruence of _++_.
flat-pair-cong : ∀ { l r : RE } { loc : ℕ }
  → { u₁ v₁ : U l } { u₂ v₂ : U r }
  → proj₁ (flat u₁) ≡ proj₁ (flat v₁)
  → proj₁ (flat u₂) ≡ proj₁ (flat v₂)
  → proj₁ (flat (PairU {l} {r} {loc} u₁ u₂))
      ≡ proj₁ (flat (PairU {l} {r} {loc} v₁ v₂))
flat-pair-cong {l} {r} {loc} {u₁} {v₁} {u₂} {v₂} u₁≡v₁ u₂≡v₂ =
  trans (flat-pair {l} {r} {loc} {u = u₁} {v = u₂})
    (trans (cong₂ _++_ u₁≡v₁ u₂≡v₂)
      (sym (flat-pair {l} {r} {loc} {u = v₁} {v = v₂})))

-- Purpose: Transport a flattened-word equality through LeftU.
-- Used by: Choice-left repair branches.
-- Main idea: Compose the defining LeftU flattening equalities around the inner equality.
flat-left-cong : ∀ { l r : RE } { loc : ℕ }
  → { u v : U l }
  → proj₁ (flat u) ≡ proj₁ (flat v)
  → proj₁ (flat (LeftU {l} {r} {loc} u))
      ≡ proj₁ (flat (LeftU {l} {r} {loc} v))
flat-left-cong {l} {r} {loc} {u} {v} u≡v =
  trans (flat-LeftU {l} {r} {loc} {u = u})
    (trans u≡v (sym (flat-LeftU {l} {r} {loc} {u = v})))

-- Purpose: Transport a flattened-word equality through RightU.
-- Used by: Choice-right repair branches.
-- Main idea: Compose the defining RightU flattening equalities around the inner equality.
flat-right-cong : ∀ { l r : RE } { loc : ℕ }
  → { u v : U r }
  → proj₁ (flat u) ≡ proj₁ (flat v)
  → proj₁ (flat (RightU {l} {r} {loc} u))
      ≡ proj₁ (flat (RightU {l} {r} {loc} v))
flat-right-cong {l} {r} {loc} {u} {v} u≡v =
  trans (flat-RightU {l} {r} {loc} {u = u})
    (trans u≡v (sym (flat-RightU {l} {r} {loc} {u = v})))

```

```agda

-- Purpose: Rule out an LNE order from an empty left word to a nonempty right word.
-- Used by: Sequence repair when a direct LNE branch would have impossible lengths.
-- Main idea: Each LNE constructor contradicts either the zero left length or the nonzero right length.
no-lne-empty-nonempty : ∀ { r : RE } { u v : U r }
  → proj₁ (flat u) ≡ []
  → not-empty (proj₁ (flat v))
  → LNEOrder._⊢_>_ r u v
  → ⊥
no-lne-empty-nonempty u≡[] not-v-empty
  (LNEOrder.be _ len-v≡0 _) =
  not-v-empty (length≡0→[] len-v≡0)
no-lne-empty-nonempty u≡[] not-v-empty
  (LNEOrder.bne len-u>0 _ _) =
  (>0→¬≡0 len-u>0) ([]→length≡0  u≡[])
no-lne-empty-nonempty u≡[] not-v-empty
  (LNEOrder.lne len-u>0 _) =
  (>0→¬≡0 len-u>0) ([]→length≡0  u≡[])

-- Purpose: Extract an empty first component from an empty PairU flattening.
-- Used by: Pair repair when selecting a nonempty replacement in the second component.
-- Main idea: Apply left conicality to the pair concatenation.
pair-first-empty : ∀ { l r : RE } { loc : ℕ }
  → { u₁ : U l } { u₂ : U r }
  → proj₁ (flat (PairU {l} {r} {loc} u₁ u₂)) ≡ []
  → proj₁ (flat u₁) ≡ []
pair-first-empty pair≡[] =
  ++-conicalˡ _ _ pair≡[]

-- Purpose: Extract an empty second component from an empty PairU flattening.
-- Used by: Pair repair when selecting a nonempty replacement in the first component.
-- Main idea: Apply right conicality to the pair concatenation.
pair-second-empty : ∀ { l r : RE } { loc : ℕ }
  → { u₁ : U l } { u₂ : U r }
  → proj₁ (flat (PairU {l} {r} {loc} u₁ u₂)) ≡ []
  → proj₁ (flat u₂) ≡ []
pair-second-empty pair≡[] =
  ++-conicalʳ _ _ pair≡[]

-- Purpose: Show that a nonempty pair with an empty first component has a nonempty second component.
-- Used by: The second-component PairU repair branch.
-- Main idea: Prove the contrapositive by concatenating two empty component words.
pair-second-not-empty : ∀ { l r : RE } { loc : ℕ }
  → { v₁ : U l } { v₂ : U r }
  → not-empty (proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
  → proj₁ (flat v₁) ≡ []
  → not-empty (proj₁ (flat v₂))
pair-second-not-empty {l} {r} {loc} {v₁} {v₂}
  not-pair-empty v₁-empty v₂-empty =
  not-pair-empty pair-empty
  where
    pair-empty :
      proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)) ≡ []
    pair-empty = trans
      (sym (flat-pair {l} {r} {loc} {u = v₁} {v = v₂}))
      (trans (cong₂ _++_ v₁-empty v₂-empty) refl)

-- Purpose: Transport a flattened-word equality through a nonempty list head.
-- Used by: Star-head repair when replacing the head parse tree.
-- Main idea: Rewrite both list flattenings with flat-list-cons and use congruence on concatenation.
flat-list-head-cong : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
  → { u v : U r } { us : List (U r) }
  → proj₁ (flat u) ≡ proj₁ (flat v)
  → proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us)))
      ≡ proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ us)))
flat-list-head-cong {r} {ε∉r} {loc} {u} {v} {us} u≡v =
  trans (flat-list-cons {r} {ε∉r} {loc} {u} {us})
    (trans (cong (λ xs → xs ++ proj₁ (flat (ListU {r} {ε∉r} {loc} us))) u≡v)
      (sym (flat-list-cons {r} {ε∉r} {loc} {u = v} {us})))

-- Purpose: Transport a flattened-word equality through a fixed list head and varying tail.
-- Used by: Star-tail repair when replacing the tail parse list.
-- Main idea: Rewrite both list flattenings and apply congruence to the tail concatenation.
flat-list-tail-cong : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
  → { u : U r } { us vs : List (U r) }
  → proj₁ (flat (ListU {r} {ε∉r} {loc} us))
      ≡ proj₁ (flat (ListU {r} {ε∉r} {loc} vs))
  → proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us)))
      ≡ proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ vs)))
flat-list-tail-cong {r} {ε∉r} {loc} {u} {us} {vs} us≡vs =
  trans (flat-list-cons {r} {ε∉r} {loc} {u} {us})
    (trans (cong (λ xs → proj₁ (flat u) ++ xs) us≡vs)
      (sym (flat-list-cons {r} {ε∉r} {loc} {u} {vs})))

-- Purpose: Contradict a greedy maximum when a strictly greedier same-word repair exists.
-- Used by: gmax→lmax after the repair branch.
-- Main idea: Split the greedy ≥ witness and use asymmetry or non-equality.
gmax-no-better : ∀ { r : RE } { u v : U r }
  → r ⊢ u >ᵍ v
  → GreedyMax._⊢_≥_ r v u
  → ⊥
gmax-no-better u>ᵍv (inj₁ v>ᵍu) =
  u>ᵍv→¬v>ᵍu u>ᵍv v>ᵍu
gmax-no-better u>ᵍv (inj₂ v≡u) =
  (>ᵍ→¬≡ u>ᵍv) (sym v≡u)

-- Purpose: Contradict an LNE maximum when a strictly greater same-word tree exists.
-- Used by: lmax-unique and the reverse maximality transfer.
-- Main idea: Split the LNE ≥ witness and use LNE asymmetry or non-equality.
lmax-no-better : ∀ { r : RE } { u v : U r }
  → LNEOrder._⊢_>_ r u v
  → LNEOrder._⊢_≥_ r v u
  → ⊥
lmax-no-better u>ˡv (inj₁ v>ˡu) =
  LNEOrder.>-asym u>ˡv v>ˡu
lmax-no-better u>ˡv (inj₂ v≡u) =
  LNEOrder.>→¬≡ u>ˡv (sym v≡u)

-- Purpose: Prove uniqueness of LNE maximal trees for a fixed word.
-- Used by: lmax→gmax to identify the LNE maximum with the supplied tree.
-- Main idea: Use LNE trichotomy; either strict direction contradicts one maximality witness, or equality remains.
lmax-unique : ∀ { r : RE } { w : List Char } { u v : U r }
  → ≥-Maxˡ {r} w u
  → ≥-Maxˡ {r} w v
  → u ≡ v
lmax-unique {r}
  (LNEMax.≥-max w u flat-u≡w max-u)
  (LNEMax.≥-max .w v flat-v≡w max-v)
  with LNEOrder.>-trichotomy u v
... | inj₁ u>ˡv =
  ⊥-elim (lmax-no-better u>ˡv (max-v u flat-u≡w))
... | inj₂ (inj₁ v>ˡu) =
  ⊥-elim (lmax-no-better v>ˡu (max-u v flat-v≡w))
... | inj₂ (inj₂ u≡v) = u≡v

```

Definition: is-epsilon

```agda

data ε≅ : RE → Set where
  ε≅ε : ε≅ ε
  ε≅● :  ∀ { l r : RE } { loc : ℕ }
    → ε≅ l
    → ε≅ r
    ---------------------
    → ε≅ ( l ● r ` loc )
  ε≅+ :  ∀ { l r : RE } { loc : ℕ }
    → ε≅ l
    → ε≅ r
    --------------------
    → ε≅ ( l + r ` loc )


postulate
  ε≅r→flat-[] : ∀ {r : RE} { ε≅r : ε≅ r }
    → ( u : U r )
    -------------------
    → Flat-[] r u 

```
