# StarFreeDecide: the static checker for star-free regexes

The decidable half of `cgp.robust.greedyposix.IsoCheck` §5.2, built.
For a regex without `*` the tree set `U r` is finite, every order rule
peels matching tree constructors, and all premises sit on STRICT
sub-regexes — so both order relations become structural recursion on the
regex, and `Iso r` becomes a `Dec`.

Contents:

1. `StarFree r` — star-free syntax as an indexed predicate (no star
   constructor, so `StarFree ( m * nε ` loc )` is absurd and the
   list/`ListU` cases disappear);
2. `U≟` — decidable equality of parse trees (the `seq₂` side condition);
3. `dec-ᵍ` / `dec-ᵖ` — decide the two orders on tree pairs of a
   star-free regex (`inner-ᵖ` carries the equal-length branch);
4. `dec∀` + `dec-Iso` — aggregate the pointwise decisions (the tree set
   is finite exactly when the regex is star-free) into `Dec (Iso r)`,
   and the `Bool` wrapper `check-Iso?`;
5. Calibration: the IsoCheck §2/§3 examples compute to their known
   answers — `aa`, `maskC` → `false`; `b₁`, `b+b` → `true`.

What is NOT covered: the star case. There `star-head`/`star-tail`
recur into the SAME regex with smaller lists, and cutting that loop is
exactly the bounded-witness lemma left open in IsoCheck §5; until it is
proved this checker does not extend past star-free syntax.

```agda
{-# OPTIONS --rewriting #-}
module cgp.robust.greedyposix.StarFreeDecide where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉; ε∉$)

import cgp.ParseTree as ParseTree
open ParseTree using (U; EmptyU; LetterU; LeftU; RightU; PairU; flat; inv-leftU; inv-rightU; inv-pairU)

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming (_⊢_>_ to _⊢_>ᵍ_)

import cgp.posix.Order as PosixOrder
open PosixOrder renaming (_⊢_>_ to _⊢_>ᵖ_)

import cgp.robust.greedyposix.Iso as IsoMod
open IsoMod using (Iso; iso)

import cgp.robust.greedyposix.IsoCheck as IsoCheck
open IsoCheck using (aa; maskC; b₁; b+b; no-ᵍ-rl; no-ᵖ-if-shorter; tri)

import Data.Bool as Bool
open Bool using (Bool; true; false)

import Data.Char as Char
open Char using (Char)

import Data.List as List
open List using (length)

import Data.Nat as Nat
open Nat using (ℕ; _<_; _>_)

import Data.Nat.Properties as NatProperties
open NatProperties using (<-asym; <⇒≢)

import Data.Sum as Sum
open Sum using (inj₁; inj₂)

import Data.Product as Product
open Product using (_×_; _,_; proj₁; proj₂)

import Relation.Nullary as Nullary
open Nullary using (Dec; yes; no; ¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; subst)

import Data.Empty as Empty
open Empty using (⊥-elim)
```

## 1. Star-free syntax

```agda
-- Purpose: regexes without _*_ anywhere (the domain where U r is finite).
-- Used by: every decision function below.
-- Proof idea: N/A (indexed predicate; no star constructor).
data StarFree : RE → Set where
  sf-ε : StarFree ε
  sf-$ : ∀ { c loc } → StarFree ( $ c ` loc )
  sf-+ : ∀ { l s loc } → StarFree l → StarFree s → StarFree ( l + s ` loc )
  sf-● : ∀ { l s loc } → StarFree l → StarFree s → StarFree ( l ● s ` loc )
```

## 2. No-rule cases and length contradiction

```agda
-- No rule of either order concludes a pair of EmptyU or of LetterU.
no-ᵍ-Empty : ¬ ( ε ⊢ EmptyU >ᵍ EmptyU )
no-ᵍ-Empty (GreedyOrder.sub ())

no-ᵍ-Letter : ∀ { loc : ℕ } { c : Char }
  → ¬ ( ( $ c ` loc ) ⊢ LetterU c >ᵍ LetterU c )
no-ᵍ-Letter (GreedyOrder.sub ())

no-ᵖ-Empty : ¬ ( ε ⊢ EmptyU >ᵖ EmptyU )
no-ᵖ-Empty (PosixOrder.len-≡ eq ())
no-ᵖ-Empty (PosixOrder.len-> ())

no-ᵖ-Letter : ∀ { loc : ℕ } { c : Char }
  → ¬ ( ( $ c ` loc ) ⊢ LetterU c >ᵖ LetterU c )
no-ᵖ-Letter (PosixOrder.len-≡ eq ())
no-ᵖ-Letter (PosixOrder.len-> n) = ⊥-elim (<⇒≢ n refl)

-- Purpose: the len-> premise contradicts a supplied length equality
--   (the no-case of every equal-length branch of the posix decision).
-- Used by: inner-ᵖ.
-- Proof idea: transport |v| < |u| across |u| ≡ |v| to |v| < |v|.
¬ᵖ->-at-eq : ∀ { r : RE } { u v : U r }
  → length (proj₁ (flat u)) ≡ length (proj₁ (flat v))
  → ¬ ( length (proj₁ (flat u)) > length (proj₁ (flat v)) )
¬ᵖ->-at-eq {r} {u} {v} eq n = <⇒≢ (subst (λ x → length (proj₁ (flat v)) < x) eq n) refl
```

## 3. Decidable tree equality

```agda
-- Purpose: decidable equality of parse trees of a star-free regex
--   (the seq₂ left-sibling test inside the order decisions).
-- Used by: dec-ᵍ, inner-ᵖ.
-- Proof idea: recursion on the tree pair; constructor clashes are
--   absurd; the star node is StarFree-absurd, so ListU never appears.

U≟ : (r : RE) → (sf : StarFree r) → (u v : U r) → Dec (u ≡ v)
U≟ ε sf EmptyU EmptyU = yes refl
U≟ ( $ c ` loc ) sf (LetterU c) (LetterU .c) = yes refl
U≟ ( l + s ` loc ) (sf-+ sfl sfs) (LeftU x) (LeftU y) with U≟ l sfl x y
... | yes p = yes (cong (LeftU {l} {s} {loc}) p)
... | no ¬p = no (λ e → ¬p (inv-leftU {l} {s} {loc} x y e))
U≟ ( l + s ` loc ) (sf-+ sfl sfs) (LeftU x) (RightU y) = no (λ ())
U≟ ( l + s ` loc ) (sf-+ sfl sfs) (RightU x) (LeftU y) = no (λ ())
U≟ ( l + s ` loc ) (sf-+ sfl sfs) (RightU x) (RightU y) with U≟ s sfs x y
... | yes p = yes (cong (RightU {l} {s} {loc}) p)
... | no ¬p = no (λ e → ¬p (inv-rightU {l} {s} {loc} x y e))
U≟ ( l ● s ` loc ) (sf-● sfl sfs) (PairU u₁ u₂) (PairU v₁ v₂)
  with U≟ l sfl u₁ v₁
... | no ¬e = no (λ eq → ¬e (proj₁ (inv-pairU {l} {s} {loc} u₁ u₂ v₁ v₂ eq)))
... | yes e₁ with U≟ s sfs u₂ v₂
...   | no ¬e₂ = no (λ eq → ¬e₂ (proj₂ (inv-pairU {l} {s} {loc} u₁ u₂ v₁ v₂ eq)))
...   | yes e₂ = yes (cong₂ (PairU {l} {s} {loc}) e₁ e₂)
U≟ ( m * nε ` loc ) () u v
```

## 4. Deciding the two orders

```agda
-- Purpose: inversion helpers for the no-cases of the decisions: which
--   inner rule could derive the pair, and which premise refutes it.
--   (Named top-level clauses, as in the IsoCheck §5 engines: multi-
--   clause lambda cases on two constructors of an indexed family share
--   metavariables between branches and mis-solve the rule implicits.)
-- Used by: dec-ᵍ, inner-ᵖ.
-- Proof idea: the matching rule yields the premise that refutes; other
--   head constructors clash rigidly (auto-absurd); a len-> premise
--   contradicts the carried length equality (¬ᵖ->-at-eq).
no-ᵍ-LL : ∀ { l s : RE } { loc : ℕ } { x y : U l }
  → ¬ ( l ⊢ x >ᵍ y )
  → ¬ ( ( l + s ` loc ) ⊢ LeftU x >ᵍ LeftU y )
no-ᵍ-LL ¬d (GreedyOrder.sub (GreedyOrder.choice-ll d₁)) = ¬d d₁

no-ᵍ-RR : ∀ { l s : RE } { loc : ℕ } { x y : U s }
  → ¬ ( s ⊢ x >ᵍ y )
  → ¬ ( ( l + s ` loc ) ⊢ RightU x >ᵍ RightU y )
no-ᵍ-RR ¬d (GreedyOrder.sub (GreedyOrder.choice-rr d₁)) = ¬d d₁

no-ᵍ-Pair₂ : ∀ { l s : RE } { loc : ℕ } { u₁ v₁ : U l } { u₂ v₂ : U s }
  → ¬ ( l ⊢ u₁ >ᵍ v₁ ) → ¬ ( s ⊢ u₂ >ᵍ v₂ )
  → ¬ ( ( l ● s ` loc ) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂ )
no-ᵍ-Pair₂ ¬d ¬d₂ (GreedyOrder.sub (GreedyOrder.seq₁ d₁)) = ¬d d₁
no-ᵍ-Pair₂ ¬d ¬d₂ (GreedyOrder.sub (GreedyOrder.seq₂ eq₁ d₁)) = ¬d₂ d₁

no-ᵍ-Pair≠ : ∀ { l s : RE } { loc : ℕ } { u₁ v₁ : U l } { u₂ v₂ : U s }
  → ¬ ( l ⊢ u₁ >ᵍ v₁ ) → ¬ ( u₁ ≡ v₁ )
  → ¬ ( ( l ● s ` loc ) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂ )
no-ᵍ-Pair≠ ¬d ¬eq (GreedyOrder.sub (GreedyOrder.seq₁ d₁)) = ¬d d₁
no-ᵍ-Pair≠ ¬d ¬eq (GreedyOrder.sub (GreedyOrder.seq₂ eq₁ _)) = ¬eq eq₁

no-ᵖ-LL : ∀ { l s : RE } { loc : ℕ } { x y : U l }
  → length (proj₁ (flat (LeftU {l} {s} {loc} x)))
    ≡ length (proj₁ (flat (LeftU {l} {s} {loc} y)))
  → ¬ ( l ⊢ x >ᵖ y )
  → ¬ ( ( l + s ` loc ) ⊢ LeftU x >ᵖ LeftU y )
no-ᵖ-LL eq ¬d (PosixOrder.len-≡ eq₁ (PosixOrder.choice-ll d)) = ¬d d
no-ᵖ-LL {l} {s} {loc} {x} {y} eq ¬d (PosixOrder.len-> n)
  = ⊥-elim (¬ᵖ->-at-eq {l + s ` loc} {LeftU {l} {s} {loc} x}
                        {LeftU {l} {s} {loc} y} eq n)

no-ᵖ-RR : ∀ { l s : RE } { loc : ℕ } { x y : U s }
  → length (proj₁ (flat (RightU {l} {s} {loc} x)))
    ≡ length (proj₁ (flat (RightU {l} {s} {loc} y)))
  → ¬ ( s ⊢ x >ᵖ y )
  → ¬ ( ( l + s ` loc ) ⊢ RightU x >ᵖ RightU y )
no-ᵖ-RR eq ¬d (PosixOrder.len-≡ eq₁ (PosixOrder.choice-rr d)) = ¬d d
no-ᵖ-RR {l} {s} {loc} {x} {y} eq ¬d (PosixOrder.len-> n)
  = ⊥-elim (¬ᵖ->-at-eq {l + s ` loc} {RightU {l} {s} {loc} x}
                        {RightU {l} {s} {loc} y} eq n)

no-ᵖ-RL : ∀ { l s : RE } { loc : ℕ } { x : U s } { y : U l }
  → length (proj₁ (flat (RightU {l} {s} {loc} x)))
    ≡ length (proj₁ (flat (LeftU {l} {s} {loc} y)))
  → ¬ ( ( l + s ` loc ) ⊢ RightU x >ᵖ LeftU y )
no-ᵖ-RL eq (PosixOrder.len-≡ eq₁ ())
no-ᵖ-RL {l} {s} {loc} {x} {y} eq (PosixOrder.len-> n)
  = ⊥-elim (¬ᵖ->-at-eq {l + s ` loc} {RightU {l} {s} {loc} x}
                        {LeftU {l} {s} {loc} y} eq n)

no-ᵖ-Pair₂ : ∀ { l s : RE } { loc : ℕ } { u₁ v₁ : U l } { u₂ v₂ : U s }
  → length (proj₁ (flat (PairU {l} {s} {loc} u₁ u₂)))
    ≡ length (proj₁ (flat (PairU {l} {s} {loc} v₁ v₂)))
  → ¬ ( l ⊢ u₁ >ᵖ v₁ ) → ¬ ( s ⊢ u₂ >ᵖ v₂ )
  → ¬ ( ( l ● s ` loc ) ⊢ PairU u₁ u₂ >ᵖ PairU v₁ v₂ )
no-ᵖ-Pair₂ eq ¬d ¬d₂ (PosixOrder.len-≡ eq₁ (PosixOrder.seq₁ d₁)) = ¬d d₁
no-ᵖ-Pair₂ eq ¬d ¬d₂ (PosixOrder.len-≡ eq₁ (PosixOrder.seq₂ _ d₁)) = ¬d₂ d₁
no-ᵖ-Pair₂ {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq ¬d ¬d₂ (PosixOrder.len-> n)
  = ⊥-elim (¬ᵖ->-at-eq {l ● s ` loc} {PairU {l} {s} {loc} u₁ u₂}
                        {PairU {l} {s} {loc} v₁ v₂} eq n)

no-ᵖ-Pair≠ : ∀ { l s : RE } { loc : ℕ } { u₁ v₁ : U l } { u₂ v₂ : U s }
  → length (proj₁ (flat (PairU {l} {s} {loc} u₁ u₂)))
    ≡ length (proj₁ (flat (PairU {l} {s} {loc} v₁ v₂)))
  → ¬ ( l ⊢ u₁ >ᵖ v₁ ) → ¬ ( u₁ ≡ v₁ )
  → ¬ ( ( l ● s ` loc ) ⊢ PairU u₁ u₂ >ᵖ PairU v₁ v₂ )
no-ᵖ-Pair≠ eq ¬d ¬eq (PosixOrder.len-≡ eq₁ (PosixOrder.seq₁ d₁)) = ¬d d₁
no-ᵖ-Pair≠ eq ¬d ¬eq (PosixOrder.len-≡ eq₁ (PosixOrder.seq₂ eq₂ _)) = ¬eq eq₂
no-ᵖ-Pair≠ {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq ¬d ¬eq (PosixOrder.len-> n)
  = ⊥-elim (¬ᵖ->-at-eq {l ● s ` loc} {PairU {l} {s} {loc} u₁ u₂}
                        {PairU {l} {s} {loc} v₁ v₂} eq n)

case-ᵍ-LL : ∀ { l s : RE } { loc : ℕ } { x y : U l }
  → Dec ( l ⊢ x >ᵍ y ) → Dec ( ( l + s ` loc ) ⊢ LeftU x >ᵍ LeftU y )
case-ᵍ-LL {l} {s} {loc} {x} {y} (yes d)
  = yes (GreedyOrder.sub (GreedyOrder.choice-ll {l} {s} {loc} {x} {y} d))
case-ᵍ-LL {l} {s} {loc} {x} {y} (no ¬d) = no (no-ᵍ-LL {l} {s} {loc} {x} {y} ¬d)

case-ᵍ-RR : ∀ { l s : RE } { loc : ℕ } { x y : U s }
  → Dec ( s ⊢ x >ᵍ y ) → Dec ( ( l + s ` loc ) ⊢ RightU x >ᵍ RightU y )
case-ᵍ-RR {l} {s} {loc} {x} {y} (yes d)
  = yes (GreedyOrder.sub (GreedyOrder.choice-rr {l} {s} {loc} {x} {y} d))
case-ᵍ-RR {l} {s} {loc} {x} {y} (no ¬d) = no (no-ᵍ-RR {l} {s} {loc} {x} {y} ¬d)

case-ᵍ-Pair : ∀ { l s : RE } { loc : ℕ } { u₁ v₁ : U l } { u₂ v₂ : U s }
  → Dec ( l ⊢ u₁ >ᵍ v₁ ) → Dec ( u₁ ≡ v₁ ) → Dec ( s ⊢ u₂ >ᵍ v₂ )
  → Dec ( ( l ● s ` loc ) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂ )
case-ᵍ-Pair {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} (yes d) _ _
  = yes (GreedyOrder.sub (GreedyOrder.seq₁ {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} d))
case-ᵍ-Pair {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} (no ¬d) (yes eq) (yes d₂)
  = yes (GreedyOrder.sub (GreedyOrder.seq₂ {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq d₂))
case-ᵍ-Pair {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} (no ¬d) (yes eq) (no ¬d₂)
  = no (no-ᵍ-Pair₂ {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} ¬d ¬d₂)
case-ᵍ-Pair {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} (no ¬d) (no ¬eq) _
  = no (no-ᵍ-Pair≠ {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} ¬d ¬eq)

-- Purpose: decide the greedy order on tree pairs of a star-free regex.
-- Used by: dec-Iso.
-- Proof idea: the top level is sub alone, so the decision IS the inner
--   one: at ε / $ no rule concludes the pair (absurd inversion); at
--   l + s the four constructor pairs match choice-ll / choice-lr /
--   (none, meta-fact 3 of IsoCheck) / choice-rr; at l ● s: seq₁, or
--   seq₂ with equal left siblings (U≟), and nothing else; every
--   premise sits on a strict sub-regex, so the recursion is on r;
--   the star case is StarFree-absurd. The branching goes through the
--   case-* combinators below (a nested with would abstract the tree
--   variables that also occur in the scrutinees).
dec-ᵍ : (r : RE) → (sf : StarFree r) → (u v : U r) → Dec (r ⊢ u >ᵍ v)
dec-ᵍ ε sf EmptyU EmptyU = no no-ᵍ-Empty
dec-ᵍ ( $ c ` loc ) sf (LetterU c) (LetterU .c) = no no-ᵍ-Letter
dec-ᵍ ( l + s ` loc ) (sf-+ sfl sfs) (LeftU x) (LeftU y)
  = case-ᵍ-LL {l} {s} {loc} {x} {y} (dec-ᵍ l sfl x y)
dec-ᵍ ( l + s ` loc ) (sf-+ sfl sfs) (LeftU x) (RightU y)
  = yes (GreedyOrder.sub GreedyOrder.choice-lr)
dec-ᵍ ( l + s ` loc ) (sf-+ sfl sfs) (RightU x) (LeftU y) = no no-ᵍ-rl
dec-ᵍ ( l + s ` loc ) (sf-+ sfl sfs) (RightU x) (RightU y)
  = case-ᵍ-RR {l} {s} {loc} {x} {y} (dec-ᵍ s sfs x y)
dec-ᵍ ( l ● s ` loc ) (sf-● sfl sfs) (PairU u₁ u₂) (PairU v₁ v₂)
  = case-ᵍ-Pair {l} {s} {loc} {u₁} {v₁} {u₂} {v₂}
      (dec-ᵍ l sfl u₁ v₁) (U≟ l sfl u₁ v₁) (dec-ᵍ s sfs u₂ v₂)
dec-ᵍ ( m * nε ` loc ) () u v

-- (dec-ᵖ and inner-ᵖ are mutually recursive: the equal-length branch
--  descends through the shared inner rules whose premises are dec-ᵖ on
--  strict sub-regexes, so the mutual block is still structural on r)
case-ᵖ-LL : ∀ { l s : RE } { loc : ℕ } { x y : U l }
  → length (proj₁ (flat (LeftU {l} {s} {loc} x)))
    ≡ length (proj₁ (flat (LeftU {l} {s} {loc} y)))
  → Dec ( l ⊢ x >ᵖ y ) → Dec ( ( l + s ` loc ) ⊢ LeftU x >ᵖ LeftU y )
case-ᵖ-LL {l} {s} {loc} {x} {y} eq (yes d)
  = yes (PosixOrder.len-≡ eq (PosixOrder.choice-ll {l} {s} {loc} {x} {y} d))
case-ᵖ-LL {l} {s} {loc} {x} {y} eq (no ¬d)
  = no (no-ᵖ-LL {l} {s} {loc} {x} {y} eq ¬d)

case-ᵖ-RR : ∀ { l s : RE } { loc : ℕ } { x y : U s }
  → length (proj₁ (flat (RightU {l} {s} {loc} x)))
    ≡ length (proj₁ (flat (RightU {l} {s} {loc} y)))
  → Dec ( s ⊢ x >ᵖ y ) → Dec ( ( l + s ` loc ) ⊢ RightU x >ᵖ RightU y )
case-ᵖ-RR {l} {s} {loc} {x} {y} eq (yes d)
  = yes (PosixOrder.len-≡ eq (PosixOrder.choice-rr {l} {s} {loc} {x} {y} d))
case-ᵖ-RR {l} {s} {loc} {x} {y} eq (no ¬d)
  = no (no-ᵖ-RR {l} {s} {loc} {x} {y} eq ¬d)

case-ᵖ-Pair : ∀ { l s : RE } { loc : ℕ } { u₁ v₁ : U l } { u₂ v₂ : U s }
  → length (proj₁ (flat (PairU {l} {s} {loc} u₁ u₂)))
    ≡ length (proj₁ (flat (PairU {l} {s} {loc} v₁ v₂)))
  → Dec ( l ⊢ u₁ >ᵖ v₁ ) → Dec ( u₁ ≡ v₁ ) → Dec ( s ⊢ u₂ >ᵖ v₂ )
  → Dec ( ( l ● s ` loc ) ⊢ PairU u₁ u₂ >ᵖ PairU v₁ v₂ )
case-ᵖ-Pair {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq (yes d) _ _
  = yes (PosixOrder.len-≡ eq (PosixOrder.seq₁ {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} d))
case-ᵖ-Pair {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq (no ¬d) (yes eq₁) (yes d₂)
  = yes (PosixOrder.len-≡ eq (PosixOrder.seq₂ {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq₁ d₂))
case-ᵖ-Pair {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq (no ¬d) (yes eq₁) (no ¬d₂)
  = no (no-ᵖ-Pair₂ {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq ¬d ¬d₂)
case-ᵖ-Pair {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq (no ¬d) (no ¬eq₁) _
  = no (no-ᵖ-Pair≠ {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq ¬d ¬eq₁)

mutual
  -- Purpose: decide the posix order: the top level is a pure length
  --   filter, so compare lengths first (meta-facts 1–2 of IsoCheck).
  -- Used by: dec-Iso.
  -- Proof idea: |u| < |v| → never (no-ᵖ-if-shorter); |u| > |v| → len->;
  --   equal → the decision moves to inner-ᵖ under the equality.
  dec-ᵖ : (r : RE) → (sf : StarFree r) → (u v : U r) → Dec (r ⊢ u >ᵖ v)
  dec-ᵖ r sf u v with tri (length (proj₁ (flat u))) (length (proj₁ (flat v)))
  ... | inj₁ h         = no (no-ᵖ-if-shorter h)
  ... | inj₂ (inj₁ eq) = inner-ᵖ r sf u v eq
  ... | inj₂ (inj₂ n)  = yes (PosixOrder.len-> n)

  -- Purpose: the equal-length branch of the posix decision: shape case
  --   analysis over the SHARED inner rules (the rule sets are identical
  --   to the greedy ones after the posix simplification), wrapped
  --   through len-≡.
  -- Used by: dec-ᵖ.
  -- Proof idea: as in dec-ᵍ, but premises are dec-ᵖ on strict
  --   sub-regexes; a len-> branch contradicts the carried equality
  --   (¬ᵖ->-at-eq).
  inner-ᵖ : (r : RE) → (sf : StarFree r) → (u v : U r)
    → length (proj₁ (flat u)) ≡ length (proj₁ (flat v))
    → Dec (r ⊢ u >ᵖ v)
  inner-ᵖ ε sf EmptyU EmptyU eq = no no-ᵖ-Empty
  inner-ᵖ ( $ c ` loc ) sf (LetterU c) (LetterU .c) eq = no no-ᵖ-Letter
  inner-ᵖ ( l + s ` loc ) (sf-+ sfl sfs) (LeftU x) (LeftU y) eq
    = case-ᵖ-LL {l} {s} {loc} {x} {y} eq (dec-ᵖ l sfl x y)
  inner-ᵖ ( l + s ` loc ) (sf-+ sfl sfs) (LeftU x) (RightU y) eq
    = yes (PosixOrder.len-≡ eq PosixOrder.choice-lr)
  inner-ᵖ ( l + s ` loc ) (sf-+ sfl sfs) (RightU x) (LeftU y) eq
    = no (no-ᵖ-RL {l} {s} {loc} {x} {y} eq)
  inner-ᵖ ( l + s ` loc ) (sf-+ sfl sfs) (RightU x) (RightU y) eq
    = case-ᵖ-RR {l} {s} {loc} {x} {y} eq (dec-ᵖ s sfs x y)
  inner-ᵖ ( l ● s ` loc ) (sf-● sfl sfs) (PairU u₁ u₂) (PairU v₁ v₂) eq
    = case-ᵖ-Pair {l} {s} {loc} {u₁} {v₁} {u₂} {v₂} eq
        (dec-ᵖ l sfl u₁ v₁) (U≟ l sfl u₁ v₁) (dec-ᵖ s sfs u₂ v₂)
  inner-ᵖ ( m * nε ` loc ) () u v eq
```

## 5. Aggregating to `Iso`

```agda
-- Purpose: aggregate a pointwise decision into a decision of ∀ over all
--   trees of a star-free regex (U r is finite exactly when r has no *).
-- Used by: dec-Iso.
-- Proof idea: recursion on the regex; sums/pairs split the quantifier
--   through the tree constructors; the star node is StarFree-absurd.
case-∀-ε : ∀ { P : U ε → Set }
  → Dec (P EmptyU) → Dec (∀ u → P u)
case-∀-ε (yes p) = yes (λ { EmptyU → p })
case-∀-ε (no ¬p) = no (λ g → ¬p (g EmptyU))

case-∀-$ : ∀ { c : Char } { loc : ℕ } { P : U ( $ c ` loc ) → Set }
  → Dec (P (LetterU {loc} c)) → Dec (∀ u → P u)
case-∀-$ {c} {loc} (yes p) = yes (λ { (LetterU .c) → p })
case-∀-$ {c} {loc} (no ¬p) = no (λ g → ¬p (g (LetterU {loc} c)))

case-∀-+ : ∀ { l s : RE } { loc : ℕ } { P : U ( l + s ` loc ) → Set }
  → Dec (∀ x → P (LeftU {l} {s} {loc} x))
  → Dec (∀ y → P (RightU {l} {s} {loc} y))
  → Dec (∀ u → P u)
case-∀-+ {l} {s} {loc} (yes pL) (yes pR)
  = yes (λ { (LeftU x) → pL x ; (RightU y) → pR y })
case-∀-+ {l} {s} {loc} (yes pL) (no ¬R)
  = no (λ g → ¬R (λ y → g (RightU {l} {s} {loc} y)))
case-∀-+ {l} {s} {loc} (no ¬L) _
  = no (λ g → ¬L (λ x → g (LeftU {l} {s} {loc} x)))

case-∀-● : ∀ { l s : RE } { loc : ℕ } { P : U ( l ● s ` loc ) → Set }
  → Dec (∀ u₁ u₂ → P (PairU {l} {s} {loc} u₁ u₂))
  → Dec (∀ u → P u)
case-∀-● {l} {s} {loc} (yes p) = yes (λ { (PairU u₁ u₂) → p u₁ u₂ })
case-∀-● {l} {s} {loc} (no ¬p)
  = no (λ g → ¬p (λ u₁ u₂ → g (PairU {l} {s} {loc} u₁ u₂)))

dec∀ : (r : RE) → (sf : StarFree r) → (P : U r → Set)
  → (∀ u → Dec (P u)) → Dec (∀ u → P u)
dec∀ ε sf P f = case-∀-ε (f EmptyU)
dec∀ ( $ c ` loc ) sf P f = case-∀-$ (f (LetterU c))
dec∀ ( l + s ` loc ) (sf-+ sfl sfs) P f
  = case-∀-+ {l} {s} {loc}
      (dec∀ l sfl (λ x → P (LeftU {l} {s} {loc} x)) (λ x → f (LeftU {l} {s} {loc} x)))
      (dec∀ s sfs (λ y → P (RightU {l} {s} {loc} y)) (λ y → f (RightU {l} {s} {loc} y)))
dec∀ ( l ● s ` loc ) (sf-● sfl sfs) P f
  = case-∀-● {l} {s} {loc}
      (dec∀ l sfl (λ u₁ → ∀ u₂ → P (PairU {l} {s} {loc} u₁ u₂))
        (λ u₁ → dec∀ s sfs (λ u₂ → P (PairU {l} {s} {loc} u₁ u₂))
                       (λ u₂ → f (PairU {l} {s} {loc} u₁ u₂))))
dec∀ ( m * nε ` loc ) () P f

-- the per-pair agreement proposition, as a single type (Iso's field
-- unfolds to exactly this).
IffPair : (r : RE) → (u v : U r) → Set
IffPair r u v = ((r ⊢ u >ᵍ v) → (r ⊢ u >ᵖ v)) × ((r ⊢ u >ᵖ v) → (r ⊢ u >ᵍ v))

-- Purpose: combine two decided relations into a decision of agreement.
-- Used by: dec-Iso.
-- Proof idea: four cases; a one-sided yes is the refuting pair.
dec⇔ : {A B : Set} → Dec A → Dec B → Dec ((A → B) × (B → A))
dec⇔ (yes a) (yes b) = yes ((λ _ → b) , (λ _ → a))
dec⇔ (yes a) (no ¬b) = no (λ (f₁ , f₂) → ¬b (f₁ a))
dec⇔ (no ¬a) (yes b) = no (λ (f₁ , f₂) → ¬a (f₂ b))
dec⇔ (no ¬a) (no ¬b) = yes ((λ x → ⊥-elim (¬a x)) , (λ y → ⊥-elim (¬b y)))

-- Purpose: decide the pointwise agreement of the two orders at one
--   tree u, uniformly over all partner trees v.
-- Used by: dec-Iso (a with-abstraction over an eta-expandable
--   scrutinee mis-parses the higher-order predicate arguments).
-- Proof idea: aggregate dec⇔ over the (finite) tree set.
dec-Iso-u : (r : RE) → (sf : StarFree r) → (u : U r)
  → Dec (∀ v → IffPair r u v)
dec-Iso-u r sf u =
  dec∀ r sf (λ v → IffPair r u v) (λ v → dec⇔ (dec-ᵍ r sf u v) (dec-ᵖ r sf u v))

case-Iso : ∀ { r : RE } { sf : StarFree r }
  → Dec (∀ u v → IffPair r u v) → Dec (Iso r)
case-Iso (yes f) = yes (iso f)
case-Iso {r = r} (no ¬f) = no ¬¬iso
  where
    ¬¬iso : ¬ (Iso r)
    ¬¬iso (iso f) = ¬f f

-- Purpose: the static criterion for star-free regexes: Dec (Iso r).
-- Used by: check-Iso?, §6 calibration.
-- Proof idea: pointwise agreement via dec-ᵍ/dec-ᵖ, aggregated by dec∀.
-- the aggregated agreement predicate over all pairs (the type dec∀
--   can't always infer from a bare predicate lambda in an argument).
AggIff : (r : RE) → Set
AggIff r = ∀ u v → IffPair r u v

-- the agreement predicate aggregated over the partner tree v (the
--   unary predicate dec∀ needs: P u must be a proposition, NOT the
--   partial application IffPair r u whose type is U r → Set).
pred-agg : (r : RE) → (u : U r) → Set
pred-agg r u = ∀ v → IffPair r u v

-- Purpose: aggregate the per-tree decisions over every tree of r.
-- Used by: dec-Iso-all.
-- Proof idea: dec∀ with the pred-agg predicate (one branch per tree
--   constructor of the star-free regex).
dec∀-iff : (r : RE) → (sf : StarFree r)
  → (∀ u → Dec (∀ v → IffPair r u v))
  → Dec (AggIff r)
dec∀-iff r sf f = dec∀ r sf (pred-agg r) f

dec-Iso-all : (r : RE) → (sf : StarFree r) → Dec (AggIff r)
dec-Iso-all r sf = dec∀-iff r sf (λ u → dec-Iso-u r sf u)

dec-Iso : (r : RE) → (sf : StarFree r) → Dec (Iso r)
dec-Iso r sf = case-Iso {r} {sf} (dec-Iso-all r sf)



check-Iso? : (r : RE) → (sf : StarFree r) → Bool
check-Iso? r sf with dec-Iso r sf
... | yes _ = true
... | no  _ = false
```

## 6. Calibration against the IsoCheck examples

The four decision results below compute (`refl`); they agree with the
hand proofs in `cgp.robust.greedyposix.IsoCheck`: `no ¬iso-aa` and
`no ¬iso-maskC` on one side, `iso-b₁` and `iso-b+b` on the other —
the checker and the certificates never disagree on these regexes.

```agda
sf-b₁ : StarFree b₁
sf-b₁ = sf-$

sf-b+b : StarFree b+b
sf-b+b = sf-+ sf-$ sf-$

sf-aa : StarFree aa
sf-aa = sf-+ sf-$ (sf-● sf-$ sf-$)

sf-maskC : StarFree maskC
sf-maskC = sf-● (sf-+ sf-$ sf-$) (sf-+ (sf-● sf-$ sf-$) sf-$)

-- §2 family B: the checker finds the shorter-winner pair (refl).
chk-aa : check-Iso? aa sf-aa ≡ false
chk-aa = refl

-- §2 family C: the checker finds the context-skewed pair (refl).
chk-maskC : check-Iso? maskC sf-maskC ≡ false
chk-maskC = refl

-- §3 positives: no unbalanced skeleton exists (refl).
chk-b₁ : check-Iso? b₁ sf-b₁ ≡ true
chk-b₁ = refl

chk-b+b : check-Iso? b+b sf-b+b ≡ true
chk-b+b = refl
```
