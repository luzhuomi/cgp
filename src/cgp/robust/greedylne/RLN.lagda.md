```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.greedylne.RLN where

import cgp.robust.greedylne.GreedyLNEUtils as Utils
open Utils public

import cgp.robust.greedylne.Iso as Iso
open Iso public

import cgp.robust.greedylne.LNN as LNN
open LNN public

import cgp.robust.greedylne.Robust as Robust
open Robust public

import cgp.RE as CGPRE
open CGPRE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉; ε∈; ε∈_+_; ε∈_<+_; ε∈_+>_; ε∈_●_; ε∈*; ε∈ε; ε∉r→¬ε∈r; ¬ε∈r→ε∉r; ε∉fst; ε∉snd; ε∉$; ε∉_+_; ε∉?; ε∈?; first; ε∉r→¬first-r≡[])

import cgp.ParseTree as ParseTree
open ParseTree using (U; EmptyU; LetterU; LeftU; RightU; PairU; ListU; flat; unflat; unflat∘proj₂∘flat; flat∘unflat; inv-flat-pair-fst; inv-flat-pair-snd; inv-flat-star; inv-leftU; inv-rightU; inv-pairU; inv-listU; unListU; listU∘unListU; LeftU≢RightU; RightU≢LeftU; proj₁∘LeftU≢proj₁∘RightU; r-∃u)

import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using (mkAllEmptyU; mkAllEmptyU-sound; mkAllEmptyU-complete; Flat-[]; flat-[]; mkAllEmptyU≢[]; proj₁flat-v≡[]→ε∈r)

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming (_⊢_>_ to _⊢_>ᵍ_; >→¬≡ to >ᵍ→¬≡; u>v→¬v>u to u>ᵍv→¬v>ᵍu)

import cgp.greedy.PartialDerivative as GreedyPD
open GreedyPD renaming (parseAll[_,_] to parseAllᵍ[_,_])

import cgp.greedy.MaxWord as GreedyMax
open GreedyMax renaming (≥-Max to ≥-Maxᵍ; ≥-max to ≥-maxᵍ)

import cgp.lne.Order as LNEOrder
open LNEOrder renaming (_⊢_>_ to _⊢_>ˡ_; >→¬≡ to >ˡ→¬≡)

import cgp.lne.PartialDerivative as LNEPD
open LNEPD renaming (parseAll[_,_] to parseAllˡ[_,_])

import cgp.lne.MaxWord as LNEMax
open LNEMax renaming (≥-Max to ≥-Maxˡ; ≥-max to ≥-maxˡ)

import Data.List as DataList
open DataList using (List; _∷_; []; _++_; map; concatMap; _∷ʳ_; length)

import Data.List.Properties
open Data.List.Properties using (++-assoc; ++-identityʳ; ++-identityˡ; ∷ʳ-++; ++-cancelˡ; ++-conicalʳ; ++-conicalˡ; length-++)

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using (ℕ; suc; zero; _>_; _+_)

import Data.Nat.Properties as NatProperties
open NatProperties using (m+n≡0⇒m≡0; +-monoʳ-≤; <⇒≤; ≤-trans; ≤-refl; +-identityˡ; +-identityʳ; m≤m+n; +-suc)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst; _≢_)
open Eq.≡-Reasoning using (begin_; step-≡; step-≡-∣; step-≡-⟩; _∎)

import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)
open Product.Σ using (proj₁; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

import Data.Empty as Empty
open Empty using (⊥-elim; ⊥)

import Relation.Nullary.Negation as Negation
open Negation using (contradiction; contraposition)

import Relation.Nullary as Nullary
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using (Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

import cgp.Utils as CGPUtils
open CGPUtils using (any-right-concat; any-left-concat; all-concat; ∷-inj; ¬∷≡[]; inv-map-[]; length>0→¬≡[]; ¬≡[]→¬length≡0; ¬≡[]→length>0; []→length≡0; length≡0→[]; >0→¬≡0; n≡0→¬n>0)

open import Function using (_∘_; flip)

open import Level using (Level)

```

Definition: A relaxed form of LNN, restricted left-nullability form

```agda

data RLN : RE → Set where
  rln-ε : RLN ε
  rln-$ : ∀ { c : Char } { loc : ℕ } → RLN ($ c ` loc)
  rln-●  : ∀ { l r : RE } { loc : ℕ }
    → RLN l
    → RLN r
    ----------------------------------
    → RLN ( l ● r ` loc )
  rln-+  : ∀ { l r : RE } { loc : ℕ }
    → ( ε∈ l → ε≅ r )
    → RLN l
    → RLN r
    ---------------------------------
    → RLN ( l + r ` loc )
  rln-* : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → RLN r
    --------------------------------
    → RLN ( r * ε∉r ` loc )

```

### RLN Robustness

```agda

{-# TERMINATING #-}
-- Purpose: Find a strictly greedier tree with the target word when the source is empty.
-- Used by: Repairing an order that cannot be represented directly in LNE.
-- Main idea: Recurse through RLN; choose star-cons-nil, a choice constructor, or repair one PairU component.
rln-empty→nonempty : ∀ { r : RE }
  → RLN r
  → ( u : U r )
  → ( v : U r )
  → proj₁ (flat u) ≡ []
  → not-empty (proj₁ (flat v))
  → ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat v))
              × (r ⊢ z >ᵍ u)
rln-empty→nonempty {ε} rln-ε EmptyU EmptyU u≡[] not-v-empty =
  ⊥-elim (not-v-empty refl)
rln-empty→nonempty {$ c ` loc} rln-$
  (LetterU {loc = .loc} .c) (LetterU {loc = .loc} .c) u≡[] not-v-empty =
  ⊥-elim (helper u≡[])
  where
    helper : proj₁ (flat { $ c ` loc } (LetterU c)) ≡ [] → ⊥
    helper eq = ¬∷≡[] (trans (sym (letter-flat {c} {loc})) eq)
rln-empty→nonempty {r * ε∉r ` loc} (rln-* rln-r)
  (ListU []) (ListU (v ∷ vs)) u≡[] not-v-empty =
  ListU (v ∷ vs) , refl , sub GreedyOrder.star-cons-nil
rln-empty→nonempty {r * ε∉r ` loc} (rln-* rln-r)
  (ListU []) (ListU []) u≡[] not-v-empty =
  ⊥-elim (not-v-empty refl)
rln-empty→nonempty {r * ε∉r ` loc} (rln-* rln-r)
  (ListU (u ∷ us)) v u≡[] not-v-empty =
  ⊥-elim ((¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us}) u≡[])
rln-empty→nonempty {l ● r ` loc} (rln-● rln-l rln-r)
  (PairU u₁ u₂) (PairU v₁ v₂) u≡[] not-pair-empty =
  pair-helper u₁ u₂ v₁ v₂
    (++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat u₂)) u≡[])
    (++-conicalʳ (proj₁ (flat u₁)) (proj₁ (flat u₂)) u≡[])
    u≡[] not-pair-empty
  where
    pair-first : ∀ (u₁ : U l) (u₂ : U r) (v₁ : U l) (v₂ : U r)
      → proj₁ (flat u₁) ≡ []
      → not-empty (proj₁ (flat v₁))
      → ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
                     × ((l ● r ` loc) ⊢ z >ᵍ PairU {l} {r} {loc} u₁ u₂)
    pair-first u₁ u₂ v₁ v₂ u₁-empty not-v₁-empty
      with rln-empty→nonempty {l} rln-l u₁ v₁ u₁-empty not-v₁-empty
    ... | z₁ , z₁≡v₁ , z₁>u₁ =
      PairU z₁ v₂ , flat-pair-cong {l} {r} {loc} z₁≡v₁ refl
        , sub (GreedyOrder.seq₁ z₁>u₁)

    pair-second : ∀ (u₁ : U l) (u₂ : U r) (v₁ : U l) (v₂ : U r)
      → proj₁ (flat u₂) ≡ []
      → proj₁ (flat u₁) ≡ []
      → proj₁ (flat v₁) ≡ []
      → not-empty (proj₁ (flat v₂))
      → ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
                     × ((l ● r ` loc) ⊢ z >ᵍ PairU {l} {r} {loc} u₁ u₂)
    pair-second u₁ u₂ v₁ v₂ u₂-empty u₁-empty v₁-empty not-v₂-empty
      with rln-empty→nonempty {r} rln-r u₂ v₂ u₂-empty not-v₂-empty
    ... | z₂ , z₂≡v₂ , z₂>u₂ =
      PairU u₁ z₂ , flat-pair-cong {l} {r} {loc}
        (trans u₁-empty (sym v₁-empty)) z₂≡v₂
        , sub (GreedyOrder.seq₂ refl z₂>u₂)

    pair-helper : ∀ (u₁ : U l) (u₂ : U r) (v₁ : U l) (v₂ : U r)
      → proj₁ (flat u₁) ≡ []
      → proj₁ (flat u₂) ≡ []
      → proj₁ (flat (PairU {l} {r} {loc} u₁ u₂)) ≡ []
      → not-empty (proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
      → ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
                     × ((l ● r ` loc) ⊢ z >ᵍ PairU {l} {r} {loc} u₁ u₂)
    pair-helper u₁ u₂ v₁ v₂ u₁-empty u₂-empty u≡[] not-pair-empty
      with flat-empty? v₁ | flat-empty? v₂
    ... | inj₂ not-v₁-empty | _ =
      pair-first u₁ u₂ v₁ v₂ u₁-empty not-v₁-empty
    ... | inj₁ v₁-empty | inj₁ v₂-empty =
      ⊥-elim (not-pair-empty pair-empty)
      where
        pair-empty : proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)) ≡ []
        pair-empty = trans
          (sym (flat-pair {l} {r} {loc} {u = v₁} {v = v₂}))
          (trans (cong₂ _++_ v₁-empty v₂-empty) refl)
    ... | inj₁ v₁-empty | inj₂ not-v₂-empty =
      pair-second u₁ u₂ v₁ v₂ u₂-empty u₁-empty v₁-empty not-v₂-empty
rln-empty→nonempty {l + r ` loc}
  (rln-+ ε∈l→ε≅r rln-l rln-r)
  (LeftU u) (LeftU v) u≡[] not-v-empty
  with rln-empty→nonempty {l} rln-l u v u≡[] not-v-empty
... | z , z≡v , z>u =
  LeftU z , flat-left-cong {l} {r} {loc} z≡v , sub (GreedyOrder.choice-ll z>u)
rln-empty→nonempty {l + r ` loc}
  (rln-+ ε∈l→ε≅r rln-l rln-r)
  (RightU u) (RightU v) u≡[] not-v-empty
  with rln-empty→nonempty {r} rln-r u v u≡[] not-v-empty
... | z , z≡v , z>u =
  RightU z , flat-right-cong {l} {r} {loc} z≡v , sub (GreedyOrder.choice-rr z>u)
rln-empty→nonempty {l + r ` loc}
  (rln-+ ε∈l→ε≅r rln-l rln-r)
  (RightU u) (LeftU v) u≡[] not-v-empty =
  LeftU v , refl , sub GreedyOrder.choice-lr
rln-empty→nonempty {l + r ` loc}
  (rln-+ ε∈l→ε≅r rln-l rln-r)
  (LeftU u) (RightU v) u≡[] not-v-empty =
  ⊥-elim (right-empty-impossible u≡[] not-v-empty)
  where
    right-empty-impossible : proj₁ (flat u) ≡ []
      → ¬ (proj₁ (flat (RightU {l} {r} {loc} v)) ≡ [])
      → ⊥
    right-empty-impossible u≡[] not-right-empty =
      not-right-empty (trans (sym (flat-RightU {l} {r} {loc} {u = v})) right-empty)
      where
        ε∈l' : ε∈ l
        ε∈l' = proj₁flat-v≡[]→ε∈r u≡[]

        ε≅r' : ε≅ r
        ε≅r' = ε∈l→ε≅r ε∈l'

        right-empty : proj₁ (flat v) ≡ []
        right-empty with ε≅r→flat-[] {r} {ε≅r'} v
        ... | flat-[] _ eq = eq

{-# TERMINATING #-}
mutual
  -- Purpose: Convert a greedy order into either an LNE order or a same-word greedy repair.
  -- Used by: Greedy-max to LNE-max transfer.
  -- Main idea: Recurse over RLN and order constructors; repair empty/nonempty mismatches by replacing the source tree.
  rln-repair : ∀ { r : RE }
    → RLN r
    → ( u : U r )
    → ( v : U r )
    → r ⊢ u >ᵍ v
    → (r ⊢ u >ˡ v)
      ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat v))
                  × (r ⊢ z >ᵍ u)

  -- Purpose: Lift the repair disjunction through a concatenation seq₁ order.
  -- Used by: rln-repair for PairU trees ordered through their first components.
  -- Main idea: Split source and target words into empty/nonempty cases and either build bne/be/lne or repair a component.
  rln-repair-seq₁ : ∀ { l r : RE } { loc : ℕ }
    → RLN r
    → (u₁ : U l) (u₂ : U r) (v₁ : U l) (v₂ : U r)
    → ((l ⊢ u₁ >ˡ v₁)
        ⊎ ∃[ z₁ ] (proj₁ (flat z₁) ≡ proj₁ (flat v₁))
                       × (l ⊢ z₁ >ᵍ u₁))
    → ((l ● r ` loc) ⊢ PairU {l} {r} {loc} u₁ u₂ >ˡ PairU {l} {r} {loc} v₁ v₂)
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
                    × ((l ● r ` loc) ⊢ z >ᵍ PairU {l} {r} {loc} u₁ u₂)

  -- Purpose: Handle seq₁ when the source pair is empty but the target pair is nonempty.
  -- Used by: The exceptional empty-first-component branch of rln-repair-seq₁.
  -- Main idea: Repair the second component and lift it with seq₂ when the first component cannot provide an LNE order.
  rln-repair-seq₁-special : ∀ { l r : RE } { loc : ℕ }
    → RLN r
    → (u₁ : U l) (u₂ : U r) (v₁ : U l) (v₂ : U r)
    → proj₁ (flat (PairU {l} {r} {loc} u₁ u₂)) ≡ []
    → not-empty (proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
    → proj₁ (flat v₁) ≡ []
    → l ⊢ u₁ >ˡ v₁
    → ((l ● r ` loc) ⊢ PairU {l} {r} {loc} u₁ u₂ >ˡ PairU {l} {r} {loc} v₁ v₂)
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
                    × ((l ● r ` loc) ⊢ z >ᵍ PairU {l} {r} {loc} u₁ u₂)

  -- Purpose: Lift the repair disjunction through a concatenation seq₂ order.
  -- Used by: rln-repair for PairU trees ordered through their second components.
  -- Main idea: Preserve the equal first component and either lift the LNE order or replace the second component.
  rln-repair-seq₂ : ∀ { l r : RE } { loc : ℕ }
    → (u₁ v₁ : U l) (u₂ v₂ : U r)
    → u₁ ≡ v₁
    → ((r ⊢ u₂ >ˡ v₂)
        ⊎ ∃[ z₂ ] (proj₁ (flat z₂) ≡ proj₁ (flat v₂))
                       × (r ⊢ z₂ >ᵍ u₂))
    → ((l ● r ` loc) ⊢ PairU {l} {r} {loc} u₁ u₂ >ˡ PairU {l} {r} {loc} v₁ v₂)
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
                    × ((l ● r ` loc) ⊢ z >ᵍ PairU {l} {r} {loc} u₁ u₂)

  -- Purpose: Lift repair through choice-ll.
  -- Used by: rln-repair for LeftU/LeftU trees.
  -- Main idea: Split empty/nonempty words, reuse the inner LNE order when possible, and inject a repaired tree with LeftU.
  rln-repair-choice-left : ∀ { l r : RE } { loc : ℕ }
    → (u v : U l)
    → ((l ⊢ u >ˡ v)
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat v))
                       × (l ⊢ z >ᵍ u))
    → ((l + r ` loc) ⊢ LeftU u >ˡ LeftU v)
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (LeftU {l} {r} {loc} v)))
                    × ((l + r ` loc) ⊢ z >ᵍ LeftU {l} {r} {loc} u)

  -- Purpose: Lift repair through choice-rr.
  -- Used by: rln-repair for RightU/RightU trees.
  -- Main idea: Split empty/nonempty words, reuse the inner LNE order when possible, and inject a repaired tree with RightU.
  rln-repair-choice-right : ∀ { l r : RE } { loc : ℕ }
    → (u v : U r)
    → ((r ⊢ u >ˡ v)
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat v))
                       × (r ⊢ z >ᵍ u))
    → ((l + r ` loc) ⊢ RightU u >ˡ RightU v)
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (RightU {l} {r} {loc} v)))
                    × ((l + r ` loc) ⊢ z >ᵍ RightU {l} {r} {loc} u)

  -- Purpose: Handle the cross-choice greedy order LeftU > RightU.
  -- Used by: rln-repair for LeftU/RightU trees.
  -- Main idea: Build be/bne/lne from the two word statuses; the empty-left/nonempty-right case contradicts ε∈l → ε≅r.
  rln-repair-choice-cross : ∀ { l r : RE } { loc : ℕ }
    → (ε∈ l → ε≅ r)
    → (u : U l) (v : U r)
    → ((l + r ` loc) ⊢ LeftU u >ˡ RightU v)
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (RightU {l} {r} {loc} v)))
                    × ((l + r ` loc) ⊢ z >ᵍ LeftU {l} {r} {loc} u)

  -- Purpose: Lift repair through star-head.
  -- Used by: rln-repair for nonempty star lists ordered by their heads.
  -- Main idea: Build bne for a direct LNE head order or replace the head and preserve the list word.
  rln-repair-star-head : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → (u v : U r) (us vs : List (U r))
    → ((r ⊢ u >ˡ v)
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat v))
                       × (r ⊢ z >ᵍ u))
    → ((r * ε∉r ` loc) ⊢ ListU (u ∷ us) >ˡ ListU (v ∷ vs))
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (ListU (v ∷ vs))))
                    × ((r * ε∉r ` loc) ⊢ z >ᵍ ListU (u ∷ us))

  -- Purpose: Lift repair through star-tail.
  -- Used by: rln-repair for equal star heads and recursively ordered tails.
  -- Main idea: Preserve the head equality and either lift the tail LNE order or replace the tail list.
  rln-repair-star-tail : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → (u v : U r) (us vs : List (U r))
    → u ≡ v
    → ((r * ε∉r ` loc) ⊢ ListU us >ˡ ListU vs)
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (ListU vs)))
                    × ((r * ε∉r ` loc) ⊢ z >ᵍ ListU us)
    → ((r * ε∉r ` loc) ⊢ ListU (u ∷ us) >ˡ ListU (v ∷ vs))
        ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (ListU (v ∷ vs))))
                    × ((r * ε∉r ` loc) ⊢ z >ᵍ ListU (u ∷ us))

  rln-repair {ε} rln-ε EmptyU EmptyU (sub ())
  rln-repair {$ c ` loc} rln-$ (LetterU .c) (LetterU .c) (sub ())
  rln-repair {l ● r ` loc} (rln-● rln-l rln-r)
    (PairU u₁ u₂) (PairU v₁ v₂) (sub (GreedyOrder.seq₁ u₁>ᵍv₁)) =
    rln-repair-seq₁ {l} {r} {loc} rln-r u₁ u₂ v₁ v₂
      (rln-repair {l} rln-l u₁ v₁ u₁>ᵍv₁)
  rln-repair {l ● r ` loc} (rln-● rln-l rln-r)
    (PairU u₁ u₂) (PairU v₁ v₂)
    (sub (GreedyOrder.seq₂ u₁≡v₁ u₂>ᵍv₂)) =
    rln-repair-seq₂ {l} {r} {loc} u₁ v₁ u₂ v₂ u₁≡v₁
      (rln-repair {r} rln-r u₂ v₂ u₂>ᵍv₂)
  rln-repair {l + r ` loc}
    (rln-+ ε∈l→ε≅r rln-l rln-r)
    (LeftU u) (LeftU v) (sub (GreedyOrder.choice-ll u>ᵍv)) =
    rln-repair-choice-left {l} {r} {loc} u v
      (rln-repair {l} rln-l u v u>ᵍv)
  rln-repair {l + r ` loc}
    (rln-+ ε∈l→ε≅r rln-l rln-r)
    (RightU u) (RightU v) (sub (GreedyOrder.choice-rr u>ᵍv)) =
    rln-repair-choice-right {l} {r} {loc} u v
      (rln-repair {r} rln-r u v u>ᵍv)
  rln-repair {l + r ` loc}
    (rln-+ ε∈l→ε≅r rln-l rln-r)
    (LeftU u) (RightU v) (sub GreedyOrder.choice-lr) =
    rln-repair-choice-cross {l} {r} {loc} ε∈l→ε≅r u v
  rln-repair {r * ε∉r ` loc} (rln-* rln-r)
    (ListU (u ∷ us)) (ListU []) (sub GreedyOrder.star-cons-nil) =
    inj₁ (lne-lne (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us}) refl)
  rln-repair {r * ε∉r ` loc} (rln-* rln-r)
    (ListU (u ∷ us)) (ListU (v ∷ vs)) (sub (GreedyOrder.star-head u>ᵍv)) =
    rln-repair-star-head {r} {ε∉r} {loc} u v us vs
      (rln-repair {r} rln-r u v u>ᵍv)
  rln-repair {r * ε∉r ` loc} (rln-* rln-r)
    (ListU (u ∷ us)) (ListU (v ∷ vs))
    (sub (GreedyOrder.star-tail u≡v us>ᵍvs)) =
    rln-repair-star-tail {r} {ε∉r} {loc} u v us vs u≡v
      (rln-repair {r * ε∉r ` loc} (rln-* rln-r)
        (ListU us) (ListU vs) us>ᵍvs)

  rln-repair-seq₁ {l} {r} {loc} rln-r u₁ u₂ v₁ v₂ result =
    helper (flat-empty? (PairU {l} {r} {loc} u₁ u₂))
      (flat-empty? (PairU {l} {r} {loc} v₁ v₂))
      (flat-empty? v₁) result
    where
      helper :
        (proj₁ (flat (PairU {l} {r} {loc} u₁ u₂)) ≡ []
          ⊎ not-empty (proj₁ (flat (PairU {l} {r} {loc} u₁ u₂))))
        → (proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)) ≡ []
          ⊎ not-empty (proj₁ (flat (PairU {l} {r} {loc} v₁ v₂))))
        → (proj₁ (flat v₁) ≡ []
          ⊎ not-empty (proj₁ (flat v₁)))
        → ((l ⊢ u₁ >ˡ v₁)
          ⊎ ∃[ z₁ ] (proj₁ (flat z₁) ≡ proj₁ (flat v₁))
                         × (l ⊢ z₁ >ᵍ u₁))
        → ((l ● r ` loc) ⊢ PairU {l} {r} {loc} u₁ u₂ >ˡ PairU {l} {r} {loc} v₁ v₂)
            ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
                        × ((l ● r ` loc) ⊢ z >ᵍ PairU {l} {r} {loc} u₁ u₂)
      helper (inj₂ u-not-empty) (inj₁ v-empty) _ _ =
        inj₁ (lne-lne u-not-empty v-empty)
      helper (inj₂ u-not-empty) (inj₂ v-not-empty) _ (inj₁ u₁>ˡv₁) =
        inj₁ (lne-bne u-not-empty v-not-empty
          (LNEOrder.seq₁ u₁>ˡv₁))
      helper (inj₂ u-not-empty) (inj₂ v-not-empty) _
        (inj₂ (z₁ , z₁≡v₁ , z₁>ᵍu₁)) =
        inj₂ (PairU z₁ v₂
          , flat-pair-cong {l} {r} {loc} z₁≡v₁ refl
          , sub (GreedyOrder.seq₁ z₁>ᵍu₁))
      helper (inj₁ u-empty) (inj₁ v-empty) _ (inj₁ u₁>ˡv₁) =
        inj₁ (lne-be u-empty v-empty
          (LNEOrder.seq₁ u₁>ˡv₁))
      helper (inj₁ u-empty) (inj₁ v-empty) _
        (inj₂ (z₁ , z₁≡v₁ , z₁>ᵍu₁)) =
        inj₂ (PairU z₁ v₂
          , flat-pair-cong {l} {r} {loc} z₁≡v₁ refl
          , sub (GreedyOrder.seq₁ z₁>ᵍu₁))
      helper (inj₁ u-empty) (inj₂ v-not-empty) (inj₂ v₁-not-empty)
        (inj₁ u₁>ˡv₁) =
        ⊥-elim (no-lne-empty-nonempty
          (pair-first-empty {l} {r} {loc} u-empty)
          v₁-not-empty u₁>ˡv₁)
      helper (inj₁ u-empty) (inj₂ v-not-empty) (inj₂ v₁-not-empty)
        (inj₂ (z₁ , z₁≡v₁ , z₁>ᵍu₁)) =
        inj₂ (PairU z₁ v₂
          , flat-pair-cong {l} {r} {loc} z₁≡v₁ refl
          , sub (GreedyOrder.seq₁ z₁>ᵍu₁))
      helper (inj₁ u-empty) (inj₂ v-not-empty) (inj₁ v₁-empty)
        (inj₁ u₁>ˡv₁) =
        rln-repair-seq₁-special {l} {r} {loc} rln-r
          u₁ u₂ v₁ v₂ u-empty v-not-empty v₁-empty u₁>ˡv₁
      helper (inj₁ u-empty) (inj₂ v-not-empty) (inj₁ v₁-empty)
        (inj₂ (z₁ , z₁≡v₁ , z₁>ᵍu₁)) =
        inj₂ (PairU z₁ v₂
          , flat-pair-cong {l} {r} {loc} z₁≡v₁ refl
          , sub (GreedyOrder.seq₁ z₁>ᵍu₁))

  rln-repair-seq₁-special {l} {r} {loc} rln-r
    u₁ u₂ v₁ v₂ u-empty v-not-empty v₁-empty u₁>ˡv₁
    with rln-empty→nonempty {r} rln-r u₂ v₂
      (pair-second-empty {l} {r} {loc} u-empty)
      (pair-second-not-empty {l} {r} {loc} v-not-empty v₁-empty)
  ... | z₂ , z₂≡v₂ , z₂>u₂ =
    inj₂ (PairU u₁ z₂
      , flat-pair-cong {l} {r} {loc}
          (trans (pair-first-empty {l} {r} {loc} u-empty)
            (sym v₁-empty))
          z₂≡v₂
      , sub (GreedyOrder.seq₂ refl z₂>u₂))

  rln-repair-seq₂ {l} {r} {loc} u₁ v₁ u₂ v₂ u₁≡v₁ result =
    helper (flat-empty? (PairU {l} {r} {loc} u₁ u₂))
      (flat-empty? (PairU {l} {r} {loc} v₁ v₂)) result
    where
      helper :
        (proj₁ (flat (PairU {l} {r} {loc} u₁ u₂)) ≡ []
          ⊎ not-empty
              (proj₁ (flat (PairU {l} {r} {loc} u₁ u₂))))
        → (proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)) ≡ []
          ⊎ not-empty
              (proj₁ (flat (PairU {l} {r} {loc} v₁ v₂))))
        → ((r ⊢ u₂ >ˡ v₂)
          ⊎ ∃[ z₂ ] (proj₁ (flat z₂) ≡ proj₁ (flat v₂))
                         × (r ⊢ z₂ >ᵍ u₂))
        → ((l ● r ` loc) ⊢ PairU {l} {r} {loc} u₁ u₂ >ˡ PairU {l} {r} {loc} v₁ v₂)
            ⊎ ∃[ z ] (proj₁ (flat z) ≡
                proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
                        × ((l ● r ` loc) ⊢ z >ᵍ
                            PairU {l} {r} {loc} u₁ u₂)
      helper (inj₂ u-not-empty) (inj₁ v-empty) _ =
        inj₁ (lne-lne u-not-empty v-empty)
      helper (inj₂ u-not-empty) (inj₂ v-not-empty) (inj₁ u₂>ˡv₂) =
        inj₁ (lne-bne u-not-empty v-not-empty
          (LNEOrder.seq₂ u₁≡v₁ u₂>ˡv₂))
      helper (inj₂ u-not-empty) (inj₂ v-not-empty)
        (inj₂ (z₂ , z₂≡v₂ , z₂>ᵍu₂)) =
        inj₂ (PairU v₁ z₂
          , flat-pair-cong {l} {r} {loc} refl z₂≡v₂
          , sub (GreedyOrder.seq₂ (sym u₁≡v₁) z₂>ᵍu₂))
      helper (inj₁ u-empty) (inj₁ v-empty) (inj₁ u₂>ˡv₂) =
        inj₁ (lne-be u-empty v-empty
          (LNEOrder.seq₂ u₁≡v₁ u₂>ˡv₂))
      helper (inj₁ u-empty) (inj₁ v-empty)
        (inj₂ (z₂ , z₂≡v₂ , z₂>ᵍu₂)) =
        inj₂ (PairU v₁ z₂
          , flat-pair-cong {l} {r} {loc} refl z₂≡v₂
          , sub (GreedyOrder.seq₂ (sym u₁≡v₁) z₂>ᵍu₂))
      helper (inj₁ u-empty) (inj₂ v-not-empty) (inj₁ u₂>ˡv₂) =
        ⊥-elim (no-lne-empty-nonempty
          (pair-second-empty {l} {r} {loc} u-empty)
          (pair-second-not-empty {l} {r} {loc} v-not-empty
            (trans (sym (cong (λ x → proj₁ (flat x)) u₁≡v₁))
              (pair-first-empty {l} {r} {loc} u-empty)))
          u₂>ˡv₂)
      helper (inj₁ u-empty) (inj₂ v-not-empty)
        (inj₂ (z₂ , z₂≡v₂ , z₂>ᵍu₂)) =
        inj₂ (PairU v₁ z₂
          , flat-pair-cong {l} {r} {loc} refl z₂≡v₂
          , sub (GreedyOrder.seq₂ (sym u₁≡v₁) z₂>ᵍu₂))

  rln-repair-choice-left {l} {r} {loc} u v result =
    helper (flat-empty? (LeftU {l} {r} {loc} u))
      (flat-empty? (LeftU {l} {r} {loc} v)) result
    where
      helper :
        (proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ []
          ⊎ not-empty (proj₁ (flat (LeftU {l} {r} {loc} u))))
        → (proj₁ (flat (LeftU {l} {r} {loc} v)) ≡ []
          ⊎ not-empty (proj₁ (flat (LeftU {l} {r} {loc} v))))
        → ((l ⊢ u >ˡ v)
          ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat v))
                         × (l ⊢ z >ᵍ u))
        → ((l + r ` loc) ⊢ LeftU {l} {r} {loc} u >ˡ LeftU v)
            ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (LeftU {l} {r} {loc} v)))
                        × ((l + r ` loc) ⊢ z >ᵍ LeftU {l} {r} {loc} u)
      helper (inj₂ not-u) (inj₁ v-empty) _ =
        inj₁ (lne-lne not-u v-empty)
      helper (inj₂ not-u) (inj₂ not-v) (inj₁ u>ˡv) =
        inj₁ (lne-bne not-u not-v (LNEOrder.choice-ll u>ˡv))
      helper (inj₂ not-u) (inj₂ not-v)
        (inj₂ (z , z≡v , z>ᵍu)) =
        inj₂ (LeftU z , flat-left-cong {l} {r} {loc} z≡v
          , sub (GreedyOrder.choice-ll z>ᵍu))
      helper (inj₁ u-empty) (inj₁ v-empty) (inj₁ u>ˡv) =
        inj₁ (lne-be u-empty v-empty (LNEOrder.choice-ll u>ˡv))
      helper (inj₁ u-empty) (inj₁ v-empty)
        (inj₂ (z , z≡v , z>ᵍu)) =
        inj₂ (LeftU z , flat-left-cong {l} {r} {loc} z≡v
          , sub (GreedyOrder.choice-ll z>ᵍu))
      helper (inj₁ u-empty) (inj₂ not-v) (inj₁ u>ˡv) =
        ⊥-elim (no-lne-empty-nonempty u-empty not-v u>ˡv)
      helper (inj₁ u-empty) (inj₂ not-v)
        (inj₂ (z , z≡v , z>ᵍu)) =
        inj₂ (LeftU z , flat-left-cong {l} {r} {loc} z≡v
          , sub (GreedyOrder.choice-ll z>ᵍu))

  rln-repair-choice-right {l} {r} {loc} u v result =
    helper (flat-empty? (RightU {l} {r} {loc} u))
      (flat-empty? (RightU {l} {r} {loc} v)) result
    where
      helper :
        (proj₁ (flat (RightU {l} {r} {loc} u)) ≡ []
          ⊎ not-empty (proj₁ (flat (RightU {l} {r} {loc} u))))
        → (proj₁ (flat (RightU {l} {r} {loc} v)) ≡ []
          ⊎ not-empty (proj₁ (flat (RightU {l} {r} {loc} v))))
        → ((r ⊢ u >ˡ v)
          ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat v))
                         × (r ⊢ z >ᵍ u))
        → ((l + r ` loc) ⊢ RightU {l} {r} {loc} u >ˡ RightU v)
            ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (RightU {l} {r} {loc} v)))
                        × ((l + r ` loc) ⊢ z >ᵍ RightU {l} {r} {loc} u)
      helper (inj₂ not-u) (inj₁ v-empty) _ =
        inj₁ (lne-lne not-u v-empty)
      helper (inj₂ not-u) (inj₂ not-v) (inj₁ u>ˡv) =
        inj₁ (lne-bne not-u not-v (LNEOrder.choice-rr u>ˡv))
      helper (inj₂ not-u) (inj₂ not-v)
        (inj₂ (z , z≡v , z>ᵍu)) =
        inj₂ (RightU z , flat-right-cong {l} {r} {loc} z≡v
          , sub (GreedyOrder.choice-rr z>ᵍu))
      helper (inj₁ u-empty) (inj₁ v-empty) (inj₁ u>ˡv) =
        inj₁ (lne-be u-empty v-empty (LNEOrder.choice-rr u>ˡv))
      helper (inj₁ u-empty) (inj₁ v-empty)
        (inj₂ (z , z≡v , z>ᵍu)) =
        inj₂ (RightU z , flat-right-cong {l} {r} {loc} z≡v
          , sub (GreedyOrder.choice-rr z>ᵍu))
      helper (inj₁ u-empty) (inj₂ not-v) (inj₁ u>ˡv) =
        ⊥-elim (no-lne-empty-nonempty u-empty not-v u>ˡv)
      helper (inj₁ u-empty) (inj₂ not-v)
        (inj₂ (z , z≡v , z>ᵍu)) =
        inj₂ (RightU z , flat-right-cong {l} {r} {loc} z≡v
          , sub (GreedyOrder.choice-rr z>ᵍu))

  rln-repair-choice-cross {l} {r} {loc} ε∈l→ε≅r u v =
    helper (flat-empty? (LeftU {l} {r} {loc} u))
      (flat-empty? (RightU {l} {r} {loc} v))
    where
      helper :
        (proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ []
          ⊎ not-empty (proj₁ (flat (LeftU {l} {r} {loc} u))))
        → (proj₁ (flat (RightU {l} {r} {loc} v)) ≡ []
          ⊎ not-empty (proj₁ (flat (RightU {l} {r} {loc} v))))
        → ((l + r ` loc) ⊢ LeftU {l} {r} {loc} u >ˡ RightU v)
            ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat (RightU {l} {r} {loc} v)))
                        × ((l + r ` loc) ⊢ z >ᵍ LeftU {l} {r} {loc} u)
      helper (inj₂ not-u) (inj₁ v-empty) =
        inj₁ (lne-lne not-u v-empty)
      helper (inj₂ not-u) (inj₂ not-v) =
        inj₁ (lne-bne not-u not-v LNEOrder.choice-lr)
      helper (inj₁ u-empty) (inj₁ v-empty) =
        inj₁ (lne-be u-empty v-empty LNEOrder.choice-lr)
      helper (inj₁ u-empty) (inj₂ not-v) =
        ⊥-elim (bad-cross u-empty not-v)
        where
          bad-cross : proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ []
            → not-empty (proj₁ (flat (RightU {l} {r} {loc} v)))
            → ⊥
          bad-cross left-empty not-right-empty =
            not-right-empty (trans (sym (flat-RightU {l} {r} {loc} {u = v})) right-empty)
            where
              ε∈l' : ε∈ l
              ε∈l' = proj₁flat-v≡[]→ε∈r
                (trans (sym (flat-LeftU {l} {r} {loc} {u = u})) left-empty)
              ε≅r' : ε≅ r
              ε≅r' = ε∈l→ε≅r ε∈l'
              right-empty : proj₁ (flat v) ≡ []
              right-empty with ε≅r→flat-[] {r} {ε≅r'} v
              ... | flat-[] _ eq = eq
  rln-repair-star-head {r} {ε∉r} {loc} u v us vs result =
    helper result
    where
      not-u : not-empty
        (proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us))))
      not-u = ¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us}

      not-v : not-empty
        (proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ vs))))
      not-v = ¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs}

      helper : ((r ⊢ u >ˡ v)
          ⊎ ∃[ z ] (proj₁ (flat z) ≡ proj₁ (flat v))
                         × (r ⊢ z >ᵍ u))
        → ((r * ε∉r ` loc) ⊢ ListU (u ∷ us) >ˡ ListU (v ∷ vs))
            ⊎ ∃[ z ] (proj₁ (flat z) ≡
                proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ vs))))
                        × ((r * ε∉r ` loc) ⊢ z >ᵍ
                            ListU {r} {ε∉r} {loc} (u ∷ us))
      helper (inj₁ u>ˡv) =
        inj₁ (lne-bne not-u not-v (LNEOrder.star-head u>ˡv))
      helper (inj₂ (z , z≡v , z>ᵍu)) =
        inj₂ (ListU {r} {ε∉r} {loc} (z ∷ vs)
          , flat-list-head-cong {r} {ε∉r} {loc}
              {u = z} {v = v} {us = vs} z≡v
          , sub (GreedyOrder.star-head z>ᵍu))

  rln-repair-star-tail {r} {ε∉r} {loc} u v us vs u≡v result =
    helper result
    where
      not-u : not-empty
        (proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us))))
      not-u = ¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us}

      not-v : not-empty
        (proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ vs))))
      not-v = ¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs}

      helper : ((r * ε∉r ` loc) ⊢ ListU us >ˡ ListU vs)
          ⊎ ∃[ z ] (proj₁ (flat z) ≡
                proj₁ (flat (ListU {r} {ε∉r} {loc} vs)))
                         × ((r * ε∉r ` loc) ⊢ z >ᵍ ListU us)
        → ((r * ε∉r ` loc) ⊢ ListU (u ∷ us) >ˡ ListU (v ∷ vs))
            ⊎ ∃[ z ] (proj₁ (flat z) ≡
                proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ vs))))
                        × ((r * ε∉r ` loc) ⊢ z >ᵍ
                            ListU {r} {ε∉r} {loc} (u ∷ us))
      helper (inj₁ us>ˡvs) =
        inj₁ (lne-bne not-u not-v
          (LNEOrder.star-tail u≡v us>ˡvs))
      helper (inj₂ (ListU zs , zs≡vs , zs>ᵍus)) =
        inj₂ (ListU {r} {ε∉r} {loc} (v ∷ zs)
          , flat-list-tail-cong {r} {ε∉r} {loc}
              {u = v} {us = zs} {vs = vs} zs≡vs
          , sub (GreedyOrder.star-tail (sym u≡v) zs>ᵍus))

-- Purpose: Convert a greedy maximal witness into an LNE maximal witness for RLN expressions.
-- Used by: rln→robust for the greedy-to-LNE direction.
-- Main idea: Apply rln-repair to every greedy strict comparison; a repair would contradict greedy maximality.
rln-gmax→lmax : ∀ { r : RE }
  → RLN r
  → ∀ { w : List Char } { v : U r }
  → ≥-Maxᵍ {r} w v
  → ≥-Maxˡ {r} w v
rln-gmax→lmax {r} rln-r
  (≥-maxᵍ w v flat-v≡w max-v) =
  ≥-maxˡ w v flat-v≡w max-vˡ
  where
    max-vˡ : (u : U r) → proj₁ (flat u) ≡ w → LNEOrder._⊢_≥_ r v u
    max-vˡ u flat-u≡w with max-v u flat-u≡w
    ... | inj₂ v≡u = inj₂ v≡u
    ... | inj₁ v>ᵍu with rln-repair rln-r v u v>ᵍu
    ... | inj₁ v>ˡu = inj₁ v>ˡu
    ... | inj₂ (z , z≡u , z>ᵍv) =
      ⊥-elim (gmax-no-better z>ᵍv
        (max-v z (trans z≡u flat-u≡w)))

-- Purpose: Convert an LNE maximal witness into a greedy maximal witness for RLN expressions.
-- Used by: rln→robust for the LNE-to-greedy direction.
-- Main idea: Obtain a greedy maximum via well-foundedness, convert to LNE maximum via gmax→lmax, then use LNE uniqueness.
rln-lmax→gmax : ∀ { r : RE }
  → RLN r
  → ∀ { w : List Char } { v : U r }
  → ≥-Maxˡ {r} w v
  → ≥-Maxᵍ {r} w v
rln-lmax→gmax {r} rln-r
  (≥-maxˡ w v flat-v≡w max-v) with
    GreedyMax.>-wellfounded {r} {proj₁ (flat v)} (proj₂ (flat v))
... | g , max-g =
  max-g-v
  where
    max-g-w : ≥-Maxᵍ {r} w g
    max-g-w = subst (λ w′ → ≥-Maxᵍ {r} w′ g) flat-v≡w max-g

    max-gˡ : ≥-Maxˡ {r} (proj₁ (flat v)) g
    max-gˡ = rln-gmax→lmax rln-r max-g

    v≡g : v ≡ g
    v≡g = lmax-unique
      (≥-maxˡ (proj₁ (flat v)) v refl max-v-flat)
      max-gˡ
      where
        max-v-flat : (u : U r) → proj₁ (flat u) ≡ proj₁ (flat v) → LNEOrder._⊢_≥_ r v u
        max-v-flat u flat-u≡flat-v = max-v u (trans flat-u≡flat-v flat-v≡w)

    max-g-v : ≥-Maxᵍ {r} w v
    max-g-v rewrite v≡g = max-g-w

-- Purpose: Establish maximality robustness for every RLN regular expression.
-- Used by: Clients needing Greedy/LNE maximality equivalence without full pointwise Iso.
-- Main idea: Transfer greedy maxima directly using repair, and transfer LNE maxima through well-founded greedy maxima plus LNE uniqueness.
rln→robust : ∀ ( r : RE )
  → RLN r
  → Robust r
rln→robust r rln-r = robust {r} ev
  where
    ev : (w : List Char) (v : U r)
      → (≥-Maxᵍ {r} w v → ≥-Maxˡ {r} w v)
        × (≥-Maxˡ {r} w v → ≥-Maxᵍ {r} w v)
    ev w v = rln-gmax→lmax rln-r , rln-lmax→gmax rln-r

```


RLN is more "relaxed" than RLNN.

Is RLN necessary for Robustness ? No.

Counterexample: `ε + $ 'a'` is Robust (each word has at most one tree,
so greedy max and LNE max coincide trivially) but not RLN
(`ε∈ ε` holds yet `ε≅ $ 'a'` does not).

```agda

counter-robust-not-rln-re : RE
counter-robust-not-rln-re = ε + ($ 'a' ` 1) ` 1

-- ε≅ has no constructor for $_`_, so it cannot hold for any literal.
¬-ε≅-$ : ∀ { c : Char } { loc : ℕ } → ¬ ε≅ ($ c ` loc)
¬-ε≅-$ ()

-- RLN (ε + $ 'a' ` 1) requires ε∈ ε → ε≅ $ 'a', which fails because
-- ε∈ ε is inhabited (ε∈ε) but ε≅ $ 'a' is not.
counter-¬-rln : ¬ RLN counter-robust-not-rln-re
counter-¬-rln (rln-+ ε∈l→ε≅r rln-ε rln-$) =
  ¬-ε≅-$ (ε∈l→ε≅r ε∈ε)

-- In U (ε + $ 'a' ` 1) there are exactly two trees:
--   LeftU  EmptyU        → word []
--   RightU (LetterU 'a') → word ['a']
-- Each word is produced by exactly one tree, so any maximality predicate
-- is trivially satisfied (the maximum is the unique tree for that word).
counter-flat-uniq : ∀ (u u' : U counter-robust-not-rln-re)
  → proj₁ (flat u) ≡ proj₁ (flat u')
  → u ≡ u'
counter-flat-uniq (LeftU EmptyU) (LeftU EmptyU) _ = refl
counter-flat-uniq (LeftU EmptyU) (RightU (LetterU c)) flat≡ =
  ⊥-elim (¬∷≡[] (trans (trans (sym (flat-RightU {l = ε} {r = $ 'a' ` 1} {loc = 1} {u = LetterU c})) (sym flat≡)) (flat-LeftU {l = ε} {r = $ 'a' ` 1} {loc = 1} {u = EmptyU})))
counter-flat-uniq (RightU (LetterU c)) (LeftU EmptyU) flat≡ =
  ⊥-elim (¬∷≡[] (trans (trans (sym (flat-RightU {l = ε} {r = $ 'a' ` 1} {loc = 1} {u = LetterU c})) flat≡) (flat-LeftU {l = ε} {r = $ 'a' ` 1} {loc = 1} {u = EmptyU})))
counter-flat-uniq (RightU (LetterU c)) (RightU (LetterU c')) _ = refl

counter-robust : Robust counter-robust-not-rln-re
counter-robust = robust {counter-robust-not-rln-re} ev
  where
    r = counter-robust-not-rln-re

    counter-maxᵍ→ˡ : (v : U r) (w : List Char) → proj₁ (flat v) ≡ w
      → (u : U r) → proj₁ (flat u) ≡ w
      → LNEOrder._⊢_≥_ r v u
    counter-maxᵍ→ˡ v w pv≡w u pu≡w =
      inj₂ (counter-flat-uniq v u (trans pv≡w (sym pu≡w)))

    counter-maxˡ→ᵍ : (v : U r) (w : List Char) → proj₁ (flat v) ≡ w
      → (u : U r) → proj₁ (flat u) ≡ w
      → GreedyMax._⊢_≥_ r v u
    counter-maxˡ→ᵍ v w pv≡w u pu≡w =
      inj₂ (counter-flat-uniq v u (trans pv≡w (sym pu≡w)))

    gmax→lmax : ∀ { w : List Char } { v : U r }
      → ≥-Maxᵍ {r} w v → ≥-Maxˡ {r} w v
    gmax→lmax (≥-maxᵍ w v flat-v≡w max-v) =
      ≥-maxˡ w v flat-v≡w (counter-maxᵍ→ˡ v w flat-v≡w)

    lmax→gmax : ∀ { w : List Char } { v : U r }
      → ≥-Maxˡ {r} w v → ≥-Maxᵍ {r} w v
    lmax→gmax (≥-maxˡ w v flat-v≡w max-v) =
      ≥-maxᵍ w v flat-v≡w (counter-maxˡ→ᵍ v w flat-v≡w)

    ev : (w : List Char) (v : U r)
      → (≥-Maxᵍ w v → ≥-Maxˡ w v) × (≥-Maxˡ w v → ≥-Maxᵍ w v)
    ev w v = gmax→lmax , lmax→gmax

```


Is RLN sufficient for Iso ? No.

The RLNN counterexample expression `(ε + ε) ● a*` is actually RLN:
the `rln-+` side condition on `ε + ε` is `ε∈ ε → ε≅ ε`, which holds.
The same witness trees separate the two orders, so RLN does not
imply Iso (though it does imply Robust).

```agda

counter-iso-left : RE
counter-iso-left = ε + ε ` 1

counter-iso-letter : RE
counter-iso-letter = $ 'a' ` 2

counter-iso-star : RE
counter-iso-star = counter-iso-letter * ε∉$ ` 3

counter-iso-re : RE
counter-iso-re = counter-iso-left ● counter-iso-star ` 4

-- (ε + ε) is RLN: the side condition is ε∈ ε → ε≅ ε.
counter-iso-rln-left : RLN counter-iso-left
counter-iso-rln-left = rln-+ (λ _ → ε≅ε) rln-ε rln-ε

counter-iso-rln-star : RLN counter-iso-star
counter-iso-rln-star = rln-* rln-$

counter-iso-rln : RLN counter-iso-re
counter-iso-rln = rln-● counter-iso-rln-left counter-iso-rln-star

-- u picks the left ε and an empty a*; v picks the right ε and one a.
counter-iso-u : U counter-iso-re
counter-iso-u = PairU
  (LeftU EmptyU)
  (ListU {r = counter-iso-letter} {nε = ε∉$} {loc = 3} [])

counter-iso-v : U counter-iso-re
counter-iso-v = PairU
  (RightU EmptyU)
  (ListU {r = counter-iso-letter} {nε = ε∉$} {loc = 3} (LetterU 'a' ∷ []))

-- Greedy: the left choice beats the right choice in the first component.
counter-iso-u>ᵍv : counter-iso-re ⊢ counter-iso-u >ᵍ counter-iso-v
counter-iso-u>ᵍv = sub (GreedyOrder.seq₁ (sub GreedyOrder.choice-lr))

-- LNE: no constructor relates u and v
-- (u flattens to [], v flattens to 'a' ∷ [];
--  be/bne need equal/positive lengths, lne needs a positive left length).
counter-iso-no-u>ˡv : ¬ counter-iso-re ⊢ counter-iso-u >ˡ counter-iso-v
counter-iso-no-u>ˡv (be () _ _)
counter-iso-no-u>ˡv (bne () _ _)
counter-iso-no-u>ˡv (lne () _)

-- Iso would require counter-iso-u >ᵍ counter-iso-v to imply
-- counter-iso-u >ˡ counter-iso-v; the two lines above refute that.
counter-iso-¬-iso : ¬ Iso counter-iso-re
counter-iso-¬-iso (iso ev) =
  counter-iso-no-u>ˡv (proj₁ (ev counter-iso-u counter-iso-v) counter-iso-u>ᵍv)

```
