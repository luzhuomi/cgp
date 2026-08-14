```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.greedylne.RobustRepair where

import cgp.RE as RE
open RE using (RE)

import cgp.ParseTree as ParseTree
open ParseTree using (U; EmptyU; LetterU; LeftU; RightU; PairU; ListU; flat)

-- Shared utilities and order renamings.
import cgp.robust.greedylne.GreedyLNEUtils as Utils
open Utils public

-- Existing Robust definition and RLN repair machinery.
import cgp.robust.greedylne.Robust as Robust
open Robust using (Robust; robust)

import cgp.robust.greedylne.RLN as RLN
open RLN using (RLN; rln-repair)

-- Greedy / LNE maximality and language membership.
import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming (_⊢_>_ to _⊢_>ᵍ_; >→¬≡ to >ᵍ→¬≡; u>v→¬v>u to u>ᵍv→¬v>ᵍu)

import cgp.greedy.MaxWord as GreedyMax
open GreedyMax renaming (≥-Max to ≥-Maxᵍ; ≥-max to ≥-maxᵍ) using (_⊢_≥_)

import cgp.lne.Order as LNEOrder
open LNEOrder renaming (_⊢_>_ to _⊢_>ˡ_; >→¬≡ to >ˡ→¬≡)
open LNEOrder using (_⊢_≥_; >-trichotomy)

import cgp.lne.MaxWord as LNEMax
open LNEMax renaming (≥-Max to ≥-Maxˡ; ≥-max to ≥-maxˡ)

import cgp.Word as Word
open Word using (_∈⟦_⟧)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; subst; _≢_)

import Data.Empty as Empty
open Empty using (⊥; ⊥-elim)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Data.Product as Product
open Product using (Σ; _,_; ∃; ∃-syntax; _×_)
open Product.Σ using (proj₁; proj₂)

import Data.List as DataList
open DataList using (List; _∷_; [])

import Data.Char as Char
open Char using (Char)

```

### Same-Word Repair (SWR)

`SWR r` says: every greedy strict comparison between two trees of the same word is either already valid in the LNE order, or the loser can be "repaired" into another tree of the same word that is strictly greedier than the winner.

This is the exact semantic content used by the existing `rln→robust` proof; RLN is just one syntactic certificate for it.

```agda

data SWR : RE → Set where
  swr : ∀ { r : RE }
    → ( ∀ { w : List Char } ( u v : U r )
      → proj₁ (flat u) ≡ w
      → proj₁ (flat v) ≡ w
      → r ⊢ u >ᵍ v
      ---------------------------------------------------------
      → ( r ⊢ u >ˡ v ) ⊎ ( ∃[ z ] ( proj₁ (flat z) ≡ w ) × ( r ⊢ z >ᵍ u ) )
      )
    -----------------------------------------
    → SWR r

```

### SWR is sufficient for Robust

```agda

SWR→robust : ∀ { r : RE }
  → SWR r
  → Robust r
SWR→robust {r} (swr swr-r) = robust ev
  where
    -- Greedy-maximum implies LNE-maximum (generic over word and tree).
    gmax→lmax : ∀ (w : List Char) (v : U r)
      → ≥-Maxᵍ {r} w v → ≥-Maxˡ {r} w v
    gmax→lmax w v (≥-maxᵍ .w .v flat-v≡w max-v) =
      ≥-maxˡ w v flat-v≡w max-vˡ
      where
        max-vˡ : ( u : U r ) → proj₁ (flat u) ≡ w → LNEOrder._⊢_≥_ r v u
        max-vˡ u flat-u≡w with max-v u flat-u≡w
        ... | inj₂ v≡u = inj₂ v≡u
        ... | inj₁ v>ᵍu with swr-r v u flat-v≡w flat-u≡w v>ᵍu
        ... | inj₁ v>ˡu = inj₁ v>ˡu
        ... | inj₂ ( z , flat-z≡w , z>ᵍv ) =
          ⊥-elim (gmax-no-better z>ᵍv (max-v z flat-z≡w))

    ev : ( w : List Char ) ( v : U r )
      → ( ≥-Maxᵍ {r} w v → ≥-Maxˡ {r} w v )
        × ( ≥-Maxˡ {r} w v → ≥-Maxᵍ {r} w v )
    ev w v = gmax→lmax w v , lmax→gmax
      where
        lmax→gmax : ≥-Maxˡ {r} w v → ≥-Maxᵍ {r} w v
        lmax→gmax mv with
          GreedyMax.>-wellfounded {r} {proj₁ (flat v)} (proj₂ (flat v))
        ... | g , gmax-g with mv
        ... | ≥-maxˡ .w .v flat-v≡w max-v =
          subst (λ x → ≥-Maxᵍ {r} w x) (sym v≡g) max-g
          where
            max-g : ≥-Maxᵍ {r} w g
            max-g = subst (λ x → ≥-Maxᵍ {r} x g) flat-v≡w gmax-g

            gmax-g→lmax-g : ≥-Maxˡ {r} w g
            gmax-g→lmax-g = gmax→lmax w g max-g

            v≡g : v ≡ g
            v≡g = lmax-unique mv gmax-g→lmax-g

```

### SWR is necessary for Robust

If `r` is Robust, then any greedy edge inside a single word must already be an LNE edge or be repairable: otherwise the source of the edge would itself be greedy-maximal, hence LNE-maximal, contradicting the existence of a strictly larger LNE tree.

```agda

robust→SWR : ∀ { r : RE }
   → Robust r
   → SWR r
robust→SWR {r} (robust ev-r) = swr robust→SWR-f
  where
    robust→SWR-f : ∀ { w : List Char } ( u v : U r )
      → proj₁ (flat u) ≡ w
      → proj₁ (flat v) ≡ w
      → r ⊢ u >ᵍ v
      → ( r ⊢ u >ˡ v ) ⊎ ( ∃[ z ] ( proj₁ (flat z) ≡ w ) × ( r ⊢ z >ᵍ u ) )
    robust→SWR-f {w} u v flat-u≡w flat-v≡w u>ᵍv with LNEOrder.>-trichotomy u v
    ... | inj₁ u>ˡv = inj₁ u>ˡv
    ... | inj₂ (inj₂ u≡v) = ⊥-elim ((>ᵍ→¬≡ u>ᵍv) u≡v)
    ... | inj₂ (inj₁ v>ˡu) =
      inj₂ (g , flat-g≡w , g>u)
      where
        w∈r : w ∈⟦ r ⟧
        w∈r = subst (_∈⟦ r ⟧) flat-u≡w (proj₂ (flat u))

        g-exists : ∃[ g ] ≥-Maxᵍ {r} w g
        g-exists = GreedyMax.>-wellfounded {r} {w} w∈r

        g : U r
        g = proj₁ g-exists

        gmax-g : ≥-Maxᵍ {r} w g
        gmax-g = proj₂ g-exists

        flat-g≡w : proj₁ (flat g) ≡ w
        flat-g≡w with gmax-g
        ... | ≥-maxᵍ .w .g fg≡w _ = fg≡w

        g≥u : GreedyMax._⊢_≥_ r g u
        g≥u with gmax-g
        ... | ≥-maxᵍ .w .g _ max-g = max-g u flat-u≡w

        u≥v-helper : ≥-Maxˡ {r} w u → LNEOrder._⊢_≥_ r u v
        u≥v-helper (≥-maxˡ .w .u _ max-u) = max-u v flat-v≡w

        u-not-g : g ≡ u → ⊥
        u-not-g g≡u =
          let u-gmax : ≥-Maxᵍ {r} w u
              u-gmax = subst (λ x → ≥-Maxᵍ {r} w x) g≡u gmax-g
              u-lmax : ≥-Maxˡ {r} w u
              u-lmax = ev-r w u .proj₁ u-gmax
          in lmax-no-better v>ˡu (u≥v-helper u-lmax)

        g>u : r ⊢ g >ᵍ u
        g>u with g≥u
        ... | inj₁ g>ᵍu = g>ᵍu
        ... | inj₂ g≡u = ⊥-elim (u-not-g g≡u)

```

### RLN implies SWR

`rln-repair` already proves the stronger, cross-word repair property for RLN expressions; restricting it to a single word gives SWR immediately.

```agda

RLN→SWR : ∀ { r : RE }
  → RLN r
  → SWR r
RLN→SWR {r} rln-r = swr rln-swr-f
   where
    rln-swr-f : ∀ { w : List Char } ( u v : U r )
      → proj₁ (flat u) ≡ w
      → proj₁ (flat v) ≡ w
      → r ⊢ u >ᵍ v
      → ( r ⊢ u >ˡ v ) ⊎ ( ∃[ z ] ( proj₁ (flat z) ≡ w ) × ( r ⊢ z >ᵍ u ) )
    rln-swr-f u v flat-u≡w flat-v≡w u>ᵍv
      with rln-repair rln-r u v u>ᵍv
    ... | inj₁ u>ˡv = inj₁ u>ˡv
    ... | inj₂ ( z , flat-z≡flat-v , z>ᵍu ) =
      inj₂ ( z , trans flat-z≡flat-v flat-v≡w , z>ᵍu )

```
