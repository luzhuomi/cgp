```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.greedyposix.Robust where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_)

import cgp.ParseTree as ParseTree
open ParseTree using (U; EmptyU; LetterU; LeftU; RightU; PairU; ListU; flat)

import cgp.PDInstance as PDI
open PDI using (PDInstance; pdinstance)

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming (_⊢_>_ to _⊢_>ᵍ_; >→¬≡ to >ᵍ→¬≡; u>v→¬v>u to u>ᵍv→¬v>ᵍu)

import cgp.greedy.PartialDerivative as GreedyPD
open GreedyPD renaming (parseAll[_,_] to parseAllᵍ[_,_])

import cgp.greedy.MaxWord as GreedyMax
open GreedyMax renaming (≥-Max to ≥-Maxᵍ; ≥-max to ≥-maxᵍ)

import cgp.posix.Order as PosixOrder
open PosixOrder renaming (_⊢_>_ to _⊢_>ᵖ_; >→¬≡ to >ᵖ→¬≡)

import cgp.posix.PartialDerivative as PosixPD
open PosixPD renaming (parseAll[_,_] to parseAllᵖ[_,_])

import cgp.posix.MaxWord as PosixMax
open PosixMax renaming (≥-Max to ≥-Maxᵖ; ≥-max to ≥-maxᵖ)

import cgp.Utils as Utils
open Utils using (∷-inj; ¬∷≡[])

import Data.List as List
open List using (List; _∷_; []; _++_; length)

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using (ℕ; suc; zero)

import Data.Product as Product
open Product using (_×_; _,_)
open Product.Σ using (proj₁; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Data.Empty as Empty
open Empty using (⊥-elim; ⊥)

import Relation.Nullary.Negation as Negation
open Negation using (contradiction; ¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; subst)
open Eq.≡-Reasoning using (begin_; step-≡; _∎)

import cgp.robust.greedyposix.Iso as Iso
open Iso using (Iso; iso)

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using (Ambig;  UnAmbig) 

```

### Robustness Definition

```agda

data Robust : RE → Set where
  robust : ∀ { r : RE }
              → ( ∀ ( w : List Char )
                → ( v : U r )
                → ( ( ≥-Maxᵍ {r} w v ) → (≥-Maxᵖ {r} w v ) ) × ( ( ≥-Maxᵖ {r} w v ) → (≥-Maxᵍ {r} w v ) )
                )
            -----------------------------------------
            → Robust r


iso→robust : ∀ ( r : RE )
  → Iso r
  → Robust r
iso→robust r (iso iso-ev) = robust {r} ev
  where
    ev : ( w : List Char ) → ( v : U r )
      → ( ≥-Maxᵍ {r} w v → ≥-Maxᵖ {r} w v )
      × ( ≥-Maxᵖ {r} w v → ≥-Maxᵍ {r} w v )
    ev w v = to-ev , from-ev
      where
        to-ev : ≥-Maxᵍ {r} w v → ≥-Maxᵖ {r} w v
        to-ev (GreedyMax.≥-max w' v' flat-v'≡w' max-v') =
          PosixMax.≥-max w' v' flat-v'≡w' max-vᵖ
          where
            max-vᵖ : ( u : U r ) → proj₁ (flat u) ≡ w' → PosixMax._⊢_≥_ r v' u
            max-vᵖ u flat-u≡w' with max-v' u flat-u≡w'
            ... | inj₁ v'>ᵍu = inj₁ (proj₁ (iso-ev v' u) v'>ᵍu)
            ... | inj₂ v'≡u = inj₂ v'≡u

        from-ev : ≥-Maxᵖ {r} w v → ≥-Maxᵍ {r} w v
        from-ev (PosixMax.≥-max w' v' flat-v'≡w' max-v') =
          GreedyMax.≥-max w' v' flat-v'≡w' max-vᵍ
          where
            max-vᵍ : ( u : U r ) → proj₁ (flat u) ≡ w' → GreedyMax._⊢_≥_ r v' u
            max-vᵍ u flat-u≡w' with max-v' u flat-u≡w'
            ... | inj₁ v'>ᵖu = inj₁ (proj₂ (iso-ev v' u) v'>ᵖu)
            ... | inj₂ v'≡u = inj₂ v'≡u



unambig→robust : ∀ { r : RE }
  → UnAmbig r
  → Robust r
unambig→robust {r} unambig = robust {r} ev
  where
    ev : ( w : List Char ) → ( v : U r )
      → ( ≥-Maxᵍ {r} w v → ≥-Maxᵖ {r} w v )
      × ( ≥-Maxᵖ {r} w v → ≥-Maxᵍ {r} w v )
    ev w v = to-ev , from-ev
      where
        -- an unambiguous r has at most one tree per word: any two trees
        -- reading the same word are identical, so the comparison field of
        -- a maximality proof always holds on its equality side
        eq-side : ( v' u : U r ) ( w' : List Char )
          → proj₁ (flat {r} v') ≡ w' → proj₁ (flat {r} u) ≡ w'
          → v' ≡ u
        eq-side v' u w' v'≡w' u≡w' = unambig v' u (trans v'≡w' (sym u≡w'))

        to-ev : ≥-Maxᵍ {r} w v → ≥-Maxᵖ {r} w v
        to-ev (GreedyMax.≥-max w' v' flat-v'≡w' _) =
          PosixMax.≥-max w' v' flat-v'≡w'
            (λ u flat-u≡w' → inj₂ (eq-side v' u w' flat-v'≡w' flat-u≡w'))

        from-ev : ≥-Maxᵖ {r} w v → ≥-Maxᵍ {r} w v
        from-ev (PosixMax.≥-max w' v' flat-v'≡w' _) =
          GreedyMax.≥-max w' v' flat-v'≡w'
            (λ u flat-u≡w' → inj₂ (eq-side v' u w' flat-v'≡w' flat-u≡w'))
```

### The converse (robust→unambig) does not hold

`Robust r` compares the two maximality notions *within* one word's trees.
For `r = a + a` the two orders coincide on all of `U r`: the only trees are
`L = LeftU (LetterU a)` and `R = RightU (LetterU a)`; greedy's `choice-lr`
proves `L >ᵍ R` and posix matches with `len-≡`/`choice-lr` (its length side
condition `1 ≥ 1` holds); `L > L` and `R > R` fail in both orders (the
comparison recurses to a letter, where no rule applies); and `R > L` fails
in both orders (greedy has no right-branch-first rule, and posix's `len->`
and `choice-rl` side conditions demand the absurd `1 > 1`). Hence
`Iso aa-r` holds and `Robust aa-r` follows through `iso→robust` — while
`a + a` is ambiguous. So `Robust r` does not imply `UnAmbig r`.

```agda
aa-r : RE
aa-r = ( $ 'a' ` 1 ) + ( $ 'a' ` 2 ) ` 3

-- 1 > 1 is absurd (both trees of aa-r read the word [ a ])
¬1>1 : ¬ ( 1 Nat.> 1 )
¬1>1 (Nat.s≤s ())

-- no strict order (either flavour) is derivable between the trees of a
-- letter expression: both orders are two-level (outer layer sub, or
-- len-≡ + len->, over the inner >ⁱ), and the inner order has no rule
-- for letter trees, while len-> at letters asks for the absurd 1 > 1
¬a>aᵍ : ∀ { loc : ℕ } → ¬ ( ($ 'a' ` loc) ⊢ LetterU 'a' >ᵍ LetterU 'a' )
¬a>aᵍ (GreedyOrder.sub ())

¬a>aᵖ : ∀ { loc : ℕ } → ¬ ( ($ 'a' ` loc) ⊢ LetterU 'a' >ᵖ LetterU 'a' )
¬a>aᵖ (PosixOrder.len-≡ _ ())
¬a>aᵖ (PosixOrder.len-> d) = ¬1>1 d

-- on aa-r the two orders agree pair by pair, so aa-r satisfies the
-- stronger hypothesis Iso of iso→robust
iso-aa : Iso aa-r
iso-aa = iso ev
  where
    L = LeftU {l = $ 'a' ` 1} {r = $ 'a' ` 2} {loc = 3} (LetterU 'a')
    R = RightU {l = $ 'a' ` 1} {r = $ 'a' ` 2} {loc = 3} (LetterU 'a')

    ¬LL>ᵍ : ¬ ( aa-r ⊢ L >ᵍ L )
    ¬LL>ᵍ (GreedyOrder.sub (GreedyOrder.choice-ll p)) = ¬a>aᵍ p

    ¬RR>ᵍ : ¬ ( aa-r ⊢ R >ᵍ R )
    ¬RR>ᵍ (GreedyOrder.sub (GreedyOrder.choice-rr p)) = ¬a>aᵍ p

    ¬RL>ᵍ : ¬ ( aa-r ⊢ R >ᵍ L )
    ¬RL>ᵍ (GreedyOrder.sub ())

    ¬LL>ᵖ : ¬ ( aa-r ⊢ L >ᵖ L )
    ¬LL>ᵖ (PosixOrder.len-≡ _ (PosixOrder.choice-ll p)) = ¬a>aᵖ p
    ¬LL>ᵖ (PosixOrder.len-> d) = ¬1>1 d

    ¬RR>ᵖ : ¬ ( aa-r ⊢ R >ᵖ R )
    ¬RR>ᵖ (PosixOrder.len-≡ _ (PosixOrder.choice-rr p)) = ¬a>aᵖ p
    ¬RR>ᵖ (PosixOrder.len-> d) = ¬1>1 d

    ¬RL>ᵖ : ¬ ( aa-r ⊢ R >ᵖ L )
    ¬RL>ᵖ (PosixOrder.len-≡ _ (PosixOrder.choice-rl d)) = ¬1>1 d
    ¬RL>ᵖ (PosixOrder.len-> d) = ¬1>1 d

    -- the three pairs without L > R have no order proof either way,
    -- both directions hold by absurdity
    fLLᵍ : aa-r ⊢ L >ᵍ L → aa-r ⊢ L >ᵖ L
    fLLᵍ x = ⊥-elim (¬LL>ᵍ x)
    fLLᵖ : aa-r ⊢ L >ᵖ L → aa-r ⊢ L >ᵍ L
    fLLᵖ x = ⊥-elim (¬LL>ᵖ x)

    fRRᵍ : aa-r ⊢ R >ᵍ R → aa-r ⊢ R >ᵖ R
    fRRᵍ x = ⊥-elim (¬RR>ᵍ x)
    fRRᵖ : aa-r ⊢ R >ᵖ R → aa-r ⊢ R >ᵍ R
    fRRᵖ x = ⊥-elim (¬RR>ᵖ x)

    fRLᵍ : aa-r ⊢ R >ᵍ L → aa-r ⊢ R >ᵖ L
    fRLᵍ x = ⊥-elim (¬RL>ᵍ x)
    fRLᵖ : aa-r ⊢ R >ᵖ L → aa-r ⊢ R >ᵍ L
    fRLᵖ x = ⊥-elim (¬RL>ᵖ x)

    -- the only pair with order proofs both ways: greedy choice-lr and
    -- posix len-≡/choice-lr (side condition 1 ≥ 1)
    fLRᵍ : aa-r ⊢ L >ᵍ R → aa-r ⊢ L >ᵖ R
    fLRᵍ (GreedyOrder.sub (GreedyOrder.choice-lr)) =
      PosixOrder.len-≡ refl (PosixOrder.choice-lr (Nat.s≤s Nat.z≤n))

    fLRᵖ : aa-r ⊢ L >ᵖ R → aa-r ⊢ L >ᵍ R
    fLRᵖ (PosixOrder.len-≡ _ (PosixOrder.choice-lr _)) =
      GreedyOrder.sub GreedyOrder.choice-lr
    fLRᵖ (PosixOrder.len-> d) = ⊥-elim (¬1>1 d)

    ev : ( v₁ v₂ : U aa-r )
      → ( aa-r ⊢ v₁ >ᵍ v₂ → aa-r ⊢ v₁ >ᵖ v₂ ) × ( aa-r ⊢ v₁ >ᵖ v₂ → aa-r ⊢ v₁ >ᵍ v₂ )
    ev (LeftU (LetterU c)) (LeftU (LetterU c₁)) = ( fLLᵍ , fLLᵖ )
    ev (LeftU (LetterU c)) (RightU (LetterU c₁)) = ( fLRᵍ , fLRᵖ )
    ev (RightU (LetterU c)) (LeftU (LetterU c₁)) = ( fRLᵍ , fRLᵖ )
    ev (RightU (LetterU c)) (RightU (LetterU c₁)) = ( fRRᵍ , fRRᵖ )

-- robust but ambiguous: the counterexample to robust→unambig
robust-aa : Robust aa-r
robust-aa = iso→robust aa-r iso-aa

¬unambig-aa : ¬ UnAmbig aa-r
¬unambig-aa unambig =
  ParseTree.LeftU≢RightU (LetterU 'a') (LetterU 'a')
    (unambig (LeftU (LetterU 'a')) (RightU (LetterU 'a')) refl)

converse-fails : ¬ ( Robust aa-r → UnAmbig aa-r )
converse-fails f = ¬unambig-aa (f robust-aa)
```
