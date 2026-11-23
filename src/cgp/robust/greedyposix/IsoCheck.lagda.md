# IsoCheck: can `Iso` be checked statically?

```agda
{-# OPTIONS --rewriting #-}
module cgp.robust.greedyposix.IsoCheck where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉; ε∉$)

import cgp.ParseTree as ParseTree
open ParseTree using (U; LetterU; LeftU; RightU; PairU; ListU; flat; unListU)

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming (_⊢_>_ to _⊢_>ᵍ_; >→¬≡ to >ᵍ→¬≡)

import cgp.posix.Order as PosixOrder
open PosixOrder renaming (_⊢_>_ to _⊢_>ᵖ_; >→¬≡ to >ᵖ→¬≡)

import cgp.robust.greedyposix.Iso as IsoMod
open IsoMod using (Iso; iso)

import Data.Char as Char
open Char using (Char)

import Data.List as List
open List using (List; _∷_; []; _++_; length)

import Data.List.Properties as ListProperties
open ListProperties using (length-++)

import Data.Nat as Nat
open Nat using (ℕ; suc; zero; _≤_; _<_; _>_; s≤s; z≤n)

import Data.Nat.Properties as NatProperties
open NatProperties using (<-asym; <-irrefl; <⇒≢; +-suc; +-identityʳ)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Data.Product as Product
open Product using (Σ; _,_; _×_; proj₁; proj₂)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; subst₂)

import Relation.Nullary as Nullary
open Nullary using (¬_)

import Data.Empty as Empty
open Empty using (⊥-elim)
```

## 0. What is assessed here

`Iso r` (`cgp.robust.greedyposix.Iso`) demands the greedy and posix orders
relate **every pair of trees of r** identically — no word quantifier, no
maximality. This module assesses whether that property has a *static*
checking criterion: a bounded search over regex subterms with arithmetic
side conditions, in the style of `cgp.ambig.AmbigCheck`'s `crit`.

Contents:

1. `NonIso₁` / `NonIso₂` — the pair forms of failure, `NonIsoᵢ → ¬Iso`;
   and the four *meta-facts* that pin the gap down to two sources only:
   posix's top-level length filter and length totality (meta-facts 1–2).
   The choice and star rules of the two orders now match — both carry an
   unguarded `choice-lr`, neither has a `choice-rl`, and `star-cons-nil` is
   one-directional in both (meta-facts 3–4) — so no pair ever diverges at a
   rule shape; every divergence comes from the length handling on top.
2. Three counterexample families, each fully formalized at its minimal
   regex: **B** (a choice pair whose winner is the shorter branch —
   greedy's `choice-lr` fires but the posix length filter rejects it), **C**
   (a *balanced* sum whose length-neutral greedy pair is length-skewed by a
   concatenation sibling — no single occurrence looks unbalanced, so the
   naive one-occurrence test is incomplete), **A** (the reversed star pair,
   decided by posix `len->` but never derivable greedily).
3. Two positive proofs: `Iso ($ 'b')` and `Iso ($ 'b' + $ 'b')` — the
   shape of a positive certificate (all pairs settled by shape gaps or
   matching rules).
4. Assessment prose: the criterion shape (occurrence scan + minLen/maxLen
   arithmetic), what is proved here, what remains open.
5. Reassessment after the posix rule simplification (commits dropping
   `choice-rl` and the `choice-lr` guard): the simplification is
   relation-preserving (the top-level posix order is unchanged), and the
   now-identical inner rule sets let `NonIso₁`/`NonIso₂` be reduced to
   pure length arithmetic (`ShortPair`/`LongPair` normal forms).

What is NOT connected: the decision procedure itself, and the
completeness direction (every `¬Iso` regex fires one of the families).
Neither is claimed; §4 states precisely what each side would need.
(§5 updates the status of these open halves.)

## 1. Pair-form failure and the four meta-facts

```agda
-- Purpose: witness that the greedy→posix half of Iso fails (a greedy pair
--   the posix order does not relate).
-- Used by: noniso₁→¬iso, §2 examples.
-- Proof idea: N/A (record type).
NonIso₁ : RE → Set
NonIso₁ r = Σ ( U r ) λ u → Σ ( U r ) λ v → ( r ⊢ u >ᵍ v ) × ¬ ( r ⊢ u >ᵖ v )

-- Purpose: witness that the posix→greedy half fails.
-- Used by: noniso₂→¬iso, §2 examples.
-- Proof idea: N/A (record type).
NonIso₂ : RE → Set
NonIso₂ r = Σ ( U r ) λ u → Σ ( U r ) λ v → ( r ⊢ u >ᵖ v ) × ¬ ( r ⊢ u >ᵍ v )

-- Purpose: a pair witness refutes Iso.
-- Used by: §2 examples.
-- Proof idea: apply the Iso half to the pair.
noniso₁→¬iso : ∀ { r : RE } → NonIso₁ r → ¬ Iso r
noniso₁→¬iso (u , v , dᵍ , ¬dᵖ) (iso f) = ¬dᵖ (proj₁ (f u v) dᵍ)

noniso₂→¬iso : ∀ { r : RE } → NonIso₂ r → ¬ Iso r
noniso₂→¬iso (u , v , dᵖ , ¬dᵍ) (iso f) = ¬dᵍ (proj₂ (f u v) dᵖ)
```

The whole gap between the two orders comes from four facts (proved by
inversion on the two top levels, `cgp.greedy.Order` / `cgp.posix.Order`):

```agda
-- Meta-fact 1: the posix top level is a length filter. Its only rules are
--   len-> (strictly longer) and len-≡ (equal length), so a strictly
--   shorter winner is never posix-related to its rival.
-- Used by: noniso₁-aa, noniso₁-maskC.
-- Proof idea: invert; the len-≡ equality contradicts <⇒≢; the len->
--   premise contradicts <-asym.
no-ᵖ-if-shorter : ∀ { r : RE } { u v : U r }
  → length (proj₁ (flat u)) < length (proj₁ (flat v))
  → ¬ ( r ⊢ u >ᵖ v )
no-ᵖ-if-shorter h (PosixOrder.len-≡ eq _) = ⊥-elim (<⇒≢ h eq)
no-ᵖ-if-shorter h (PosixOrder.len-> n)    = ⊥-elim (<-asym h n)

-- Meta-fact 2: posix is total on length-descending pairs.
-- Used by: noniso₂-aa, noniso₂-star.
-- Proof idea: len-> is a rule.
pos-long-wins : ∀ { r : RE } { u v : U r }
  → length (proj₁ (flat u)) > length (proj₁ (flat v))
  → r ⊢ u >ᵖ v
pos-long-wins n = PosixOrder.len-> n

-- Meta-fact 3: the greedy order NEVER relates a right-branch tree above a
--   left-branch tree at a choice node (greedy has no choice-rl rule).
-- Used by: noniso₂-aa, iso-bb.
-- Proof idea: the single top constructor sub; every inner rule whose
--   conclusion is RightU > LeftU requires a choice node, and the only
--   such conclusion is choice-rl, absent from the greedy order — all
--   constructor patterns clash, so sub () closes the case.
no-ᵍ-rl : ∀ { l s : RE } { loc : ℕ } { a : U l } { c : U s }
  → ¬ ( (l + s ` loc) ⊢ RightU c >ᵍ LeftU a )
no-ᵍ-rl (GreedyOrder.sub ())

-- Meta-fact 4: the greedy order NEVER relates an empty star list above a
--   non-empty one (star-cons-nil is one-directional in both orders).
-- Used by: no-ᵍ-₁₂ (the star counterexample).
-- Proof idea: every star rule of the inner order has ListU (v ∷ vs) on the
--   left; seq/choice rules need a different top constructor — clash.
no-ᵍ-empty-nonempty : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ }
  { w : U m } { ws : List (U m) }
  → ¬ ( (m * nε ` loc) ⊢ ListU [] >ᵍ ListU (w ∷ ws) )
no-ᵍ-empty-nonempty (GreedyOrder.sub ())
```

Read together: the two orders **share their shape rules** — `choice-lr` is
unguarded in both, `choice-rl` (a right reading above a left reading) is
absent from both, and `star-cons-nil` is one-directional in both (meta-facts
3–4), so no pair diverges at a rule shape. The **only** asymmetry is the
top-level length layer: greedy promotes any inner `u >ⁱ v` to `u > v` via
`sub` regardless of length, whereas posix is length-filtered and
length-total (meta-facts 1–2). Every `Iso` failure is a pair one order's
length layer reaches and the other's does not — a shorter winner
(families B/C) or a reversed star (family A).

## 2. The counterexample families

### Family B — a shorter-branch winner

```agda
-- Purpose: minimal family-B regex: the choice branch a against the branch
--   a●a. Used by: noniso₁-aa, noniso₂-aa, ¬iso-aa.
-- Proof idea: N/A (definition).
aa : RE
aa = ( $ 'a' ` 11 ) + ( ( $ 'a' ` 12 ) ● ( $ 'a' ` 13 ) ` 14 ) ` 15

aa-l : U aa
aa-l = LeftU (LetterU 'a')

aa-r : U aa
aa-r = RightU (PairU (LetterU 'a') (LetterU 'a'))

-- 1 < 2, the length gap of the pair (computes by refl-normalization).
1<2 : length (proj₁ (flat aa-l)) < length (proj₁ (flat aa-r))
1<2 = s≤s (s≤s z≤n)

-- Purpose: family B, greedy side: choice-lr always fires, but the pair is
--   too short to pass the posix length filter (meta-facts 1+3 with the
--   roles swapped give both halves).
-- Used by: ¬iso-aa.
-- Proof idea: greedy sub choice-lr; ¬posix by no-ᵖ-if-shorter.
noniso₁-aa : NonIso₁ aa
noniso₁-aa = aa-l , aa-r , ( GreedyOrder.sub GreedyOrder.choice-lr
  , no-ᵖ-if-shorter 1<2 )

-- Purpose: family B, posix side: the reversed pair is length-descending,
--   so pos-long-wins decides it, while greedy cannot (meta-fact 3).
-- Used by: ¬iso-aa.
-- Proof idea: pos-long-wins 1<2; no-ᵍ-rl.
noniso₂-aa : NonIso₂ aa
noniso₂-aa = aa-r , aa-l , ( pos-long-wins 1<2 , no-ᵍ-rl )

¬iso-aa : ¬ Iso aa
¬iso-aa = noniso₁→¬iso noniso₁-aa
```

The left branch `a` (length 1) is shorter than the right branch `a●a`
(length 2); the same pair then witnesses BOTH halves: `(a, aa)` is greedy
(`choice-lr`) but the posix length filter rejects it (`no-ᵖ-if-shorter`),
`(aa, a)` is posix (`len->`) but has no greedy rule.

### Family C — balanced sums, skewed by context

The per-occurrence length test that catches family B (a sum whose chosen
branch is shorter than its sibling branch) is NOT sufficient. The regex
below has two sum occurrences, neither of them locally length-skewed
(single letters on both sides; the right sum even puts the longer branch on
the LEFT) — yet the lexicographic `seq₁` rule leaves the right siblings
unconstrained, so a length-neutral greedy pair at the left sum pairs with
*any* pair of right siblings, and choosing shorter-then-longer siblings
makes the whole pair fail the posix length filter.

```agda
-- Purpose: minimal family-C regex: (d + d) ● (e●e + e). Neither sum
--   occurrence is locally length-skewed.
-- Used by: noniso₁-maskC, ¬iso-maskC.
-- Proof idea: N/A (definition).
maskC : RE
maskC = ( ( $ 'd' ` 61 ) + ( $ 'd' ` 62 ) ` 63 )
      ● ( ( ( $ 'e' ` 64 ) ● ( $ 'e' ` 65 ) ` 66 ) + ( $ 'e' ` 67 ) ` 68 )
      ` 69

maskC-u : U maskC
maskC-u = PairU (LeftU (LetterU 'd')) (RightU (LetterU 'e'))

maskC-v : U maskC
maskC-v = PairU (RightU (LetterU 'd'))
            (LeftU (PairU (LetterU 'e') (LetterU 'e')))

-- 2 < 3, the total length gap (1+1 vs 1+2).
2<3 : length (proj₁ (flat maskC-u)) < length (proj₁ (flat maskC-v))
2<3 = s≤s (s≤s (s≤s z≤n))

-- Purpose: family C: seq₁ orders the (d,d) pair unconditionally, the (e,
--   e●e) siblings are free, and the total pair is filtered by length.
-- Used by: ¬iso-maskC.
-- Proof idea: sub (seq₁ (sub choice-lr)); ¬posix by no-ᵖ-if-shorter.
noniso₁-maskC : NonIso₁ maskC
noniso₁-maskC = maskC-u , maskC-v
  , ( GreedyOrder.sub (GreedyOrder.seq₁
        (GreedyOrder.sub GreedyOrder.choice-lr))
    , no-ᵖ-if-shorter 2<3 )

¬iso-maskC : ¬ Iso maskC
¬iso-maskC = noniso₁→¬iso noniso₁-maskC
```

Note the right siblings `(RightU e, LeftU(e●e))` are related by NEITHER
order — both lack a `choice-rl` rule, so `RightU >ⁱ LeftU` is unprovable
(meta-fact 3 now holds for the posix order too) — they are legal precisely
because `seq₁` never looks at them.

### Family A — the reversed star pair, no sums at all

```agda
-- Purpose: minimal sum-free counterexample: b* ● c*. The right star
--   supplies the length; there is no sum occurrence for a per-occurrence
--   length test to flag — the failure is purely the top-level length layer
--   (positional `len->` versus greedy's shape rules).
-- Used by: noniso₂-star, ¬iso-star.
-- Proof idea: N/A (definition).
starC : RE
starC = ( ( $ 'b' ` 21 ) * ε∉$ ` 22 ) ● ( ( $ 'c' ` 23 ) * ε∉$ ` 24 ) ` 25

starC-u : U starC
starC-u = PairU (ListU []) (ListU (LetterU 'c' ∷ LetterU 'c' ∷ []))

starC-v : U starC
starC-v = PairU (ListU (LetterU 'b' ∷ [])) (ListU [])

-- Purpose: the empty-list-wins pair is never greedy: seq₁ would need the
--   star pair ordered (meta-fact 4); seq₂ would need the lists equal
--   (decided after cong unListU).
-- Used by: noniso₂-star.
-- Proof idea: inversion on the two concatenation rules.
no-ᵍ-uv : ¬ ( starC ⊢ starC-u >ᵍ starC-v )
no-ᵍ-uv (GreedyOrder.sub (GreedyOrder.seq₁ d)) =
  ⊥-elim (no-ᵍ-empty-nonempty d)
no-ᵍ-uv (GreedyOrder.sub (GreedyOrder.seq₂ eq _)) with cong unListU eq
... | ()

-- Purpose: family A: |starC-u| = 2 > 1 = |starC-v| so posix decides the
--   pair by len-> alone, but greedy has no derivation (the shape needs
--   the empty star list to win).
-- Used by: ¬iso-star.
-- Proof idea: pos-long-wins (1 < 2 computes); no-ᵍ-uv.
noniso₂-star : NonIso₂ starC
noniso₂-star = starC-u , starC-v
  , ( pos-long-wins (s≤s (s≤s z≤n)) , no-ᵍ-uv )

¬iso-star : ¬ Iso starC
¬iso-star = noniso₂→¬iso noniso₂-star
```

## 3. Positive certificates

`Iso` for small regexes is proved pair by pair: each pair is settled
either by a shape gap (neither order derives it) or by matching rules.
These are the shapes a static criterion must ACCEPT, so they calibrate
the side conditions (a *balanced* choice, `minLen = maxLen` on both
sides, survives; a bare letter is vacuously Iso).

```agda
-- Purpose: a bare letter has one tree; both strict orders are irreflexive,
--   so the empty relation agrees.
-- Used by: §3, criterion calibration.
-- Proof idea: >ᵍ→¬≡ / >ᵖ→¬≡ applied to the pair identity.
b₁ : RE
b₁ = $ 'b' ` 71

iso-b₁ : Iso b₁
iso-b₁ = iso λ { (LetterU 'b') (LetterU 'b')
  → ( (λ d → ⊥-elim (>ᵍ→¬≡ d refl)) , (λ d → ⊥-elim (>ᵖ→¬≡ d refl)) ) }

-- Purpose: the balanced choice b + b IS Iso: the only cross pair agrees
--   in both orders (each relates `L > R` by its unguarded `choice-lr` at
--   equal length; the reverse pair is a shape gap in both orders), same-side
--   pairs are never related.
-- Used by: criterion calibration (a choice with no length-skew between its
--   branches — equal-length here — is Iso: no pair can trip the length filter).
-- Proof idea: four shape lemmas + reconstruction for the (LeftU, RightU)
--   pair: len-≡ refl choice-lr and sub choice-lr.  Unlisted
--   clause heads close by constructor clash (absurd automatically).
b+b : RE
b+b = ( $ 'b' ` 81 ) + ( $ 'b' ` 82 ) ` 83

no-ᵍ-ll : ¬ ( b+b ⊢ LeftU (LetterU 'b') >ᵍ LeftU (LetterU 'b') )
no-ᵍ-ll (GreedyOrder.sub (GreedyOrder.choice-ll d)) = ⊥-elim (>ᵍ→¬≡ d refl)

no-ᵍ-rr : ¬ ( b+b ⊢ RightU (LetterU 'b') >ᵍ RightU (LetterU 'b') )
no-ᵍ-rr (GreedyOrder.sub (GreedyOrder.choice-rr d)) = ⊥-elim (>ᵍ→¬≡ d refl)

no-ᵖ-ll : ¬ ( b+b ⊢ LeftU (LetterU 'b') >ᵖ LeftU (LetterU 'b') )
no-ᵖ-ll (PosixOrder.len-> n) = ⊥-elim (<-irrefl refl n)
no-ᵖ-ll (PosixOrder.len-≡ _ (PosixOrder.choice-ll d)) = ⊥-elim (>ᵖ→¬≡ d refl)

no-ᵖ-rr : ¬ ( b+b ⊢ RightU (LetterU 'b') >ᵖ RightU (LetterU 'b') )
no-ᵖ-rr (PosixOrder.len-> n) = ⊥-elim (<-irrefl refl n)
no-ᵖ-rr (PosixOrder.len-≡ _ (PosixOrder.choice-rr d)) = ⊥-elim (>ᵖ→¬≡ d refl)

no-ᵖ-rl : ¬ ( b+b ⊢ RightU (LetterU 'b') >ᵖ LeftU (LetterU 'b') )
no-ᵖ-rl (PosixOrder.len-> n) = ⊥-elim (<-irrefl refl n)

iso-b+b : Iso b+b
iso-b+b = iso λ
  { (LeftU (LetterU 'b')) (LeftU (LetterU 'b'))
      → ( (λ d → ⊥-elim (no-ᵍ-ll d)) , (λ d → ⊥-elim (no-ᵖ-ll d)) )
  ; (RightU (LetterU 'b')) (RightU (LetterU 'b'))
      → ( (λ d → ⊥-elim (no-ᵍ-rr d)) , (λ d → ⊥-elim (no-ᵖ-rr d)) )
  ; (LeftU (LetterU 'b')) (RightU (LetterU 'b')) →
      ( (λ _ → PosixOrder.len-≡ refl PosixOrder.choice-lr)
      , (λ _ → GreedyOrder.sub GreedyOrder.choice-lr) )
  ; (RightU (LetterU 'b')) (LeftU (LetterU 'b'))
      → ( (λ d → ⊥-elim (no-ᵍ-rl d)) , (λ d → ⊥-elim (no-ᵖ-rl d)) ) }
```

## 4. Assessment: is there a static criterion?

**Short answer: yes in shape, and it needs no word equations** — unlike
the `RobustCheck` analysis, every obstruction here is visible from the
regex structure plus integer length bounds; no language-overlap test
(pd machinery) is needed. A decidable criterion of `crit` style is
plausible; its exact side conditions are worked out below, and the
completeness proof is the open half.

**The four meta-facts of §1 are the entire rule-set gap.** For any pair
of trees, both orders follow the pair shape identically: the seq, star and
choice rules now match exactly (both carry an unguarded `choice-lr`, neither
has a `choice-rl`). They differ only in the top-level layer that promotes an
inner `>ⁱ` to a `>`:

- posix `len->`: *every* pair with |u| > |v| is posix-related (top-level
  totality — this is what family A exploits);
- posix `len-≡`: nothing with |u| < |v| ever is (length filter);
- greedy's `sub`, by contrast, promotes *any* inner `u >ⁱ v` to `u > v`
  with no length test at all;
- the one-directional `star-cons-nil` is shared, but only becomes an
  obstruction combined with the length filter (family A).

**The criterion shape.** Enumerate occurrences of `r` (finite, structural,
like `AmbigCheck`'s `Ctx`), with per-subterm arithmetic computed by
structural recursion — for this RE grammar (no intersection/complement,
star guarded by `ε∉`):

- `minLen(ε) = 0`, `minLen($ c) = 1`, `minLen(l●m) = minLen l + minLen m`,
  `minLen(l+s) = min`, `minLen(m* ) = 0` (the `ListU []` tree);
- `maxLen` likewise, and `maxLen(m* nε) = ∞` always in this grammar
  (`ε∉ m` forces every reading of `m` to be non-empty, and every `U r`
  is inhabited);
- `hasOrderedPair(r)`: whether some pair of `r` is greedy-derivable —
  true iff `r` contains a `+` or `*` occurrence, or a `●` whose left
  subterm has one (recursively);
- the family conditions:
  - **B**: a sum occurrence `(l + s)` with `minLen l < maxLen s` fires a
    pair witness at the occurrence itself (§2 `aa`; context fillings of
    equal length keep firing, which is why family C reduces to
    occurrence-plus-spread arithmetic);
  - **C**: a concatenation occurrence `(l ● m)` with `hasOrderedPair l`
    and `spread m = maxLen m − minLen m` exceeding the smallest length
    difference of an ordered pair of `l` (§2 `maskC` — a length-neutral
    ordered pair at the left sum, siblings of lengths 1 and 2);
  - **A**: a star occurrence `m*` whose position in a concatenation
    continuation lets the empty-list-wins pair be length-descending
    (§2 `starC`: the `c*` continuation of the `b*` occurrence supplies
    lengths 2 vs 1 — this family is invisible to every sum-based length
    test, the regex has no sums).

Soundness ("pattern fires ⇒ `¬Iso`") is exactly what §2 proves at three
instances: the pattern is the pair, and its two halves follow from
meta-facts, with context fillings chosen equal (family B) or free
(families A/C) — the same embedding argument as the `CtxT`/`A2→Ambig`
machinery in `RobustCheck` §5. Every condition is integer arithmetic over
a finite occurrence scan (with ∞ handled by comparisons), so **the
procedure this describes is decidable**.

**What remains open.**

1. The exact arithmetic for family C: "the smallest length difference of
   an ordered pair of `l`" is a per-subterm *set* of differences, not a
   single minimum — a subterm can have both length-neutral and
   length-skewing ordered pairs. The sets are effectively semilinear for
   regexes (and the grammar here is plain regex), so the data is
   computable; formalizing min/max-sets per subterm was not done here.
   The simpler `minLen`/`maxLen`/`hasOrderedPair` version above is NOT
   sufficient (family C is exactly the counterexample to the naive
   version with a single `minDiff`).
2. Completeness: every `¬Iso r` pair is generated by one of the families.
   The descent argument would be an inversion on the two derivations —
   both follow the pair shape (rules are shape-deterministic except at
   sum/letter nodes), so any counterexample pair's derivation bottoms out
   at exactly one of the four meta-fact points. This is the same shape
   as `cgp.ambig.Completeness`'s descent but has not been formalized
   here. (Status update after the rule-set simplification: this descent
   IS now formalized, as the normal-form theorems `noniso₁→short` and
   `noniso₂→long` of §5 — no divergence mode other than the length
   layer exists. What remains open is only the bounded-witness question
   restated at the end of §5.)
3. A dual positive characterization: §3 shows what survives (letters,
   balanced choices with `minLen(left) ≥ maxLen(right)`, and — not
   formalized but checkable by the same pair analysis — stars only when
   every concatenation continuation of the star occurrence has spread 0).
   Practically the surviving class is small: almost any real regex has an
   unbalanced choice or a star beside a variable-length sibling, so for
   grading-style use the useful question is the (decidable, above)
   *rejection* criterion, not enumeration of the Iso class.

**Contrast with `RobustCheck`.** There, a fired pattern was not enough:
`OrderDiverge ↛ NonRobust` (the `sepx` counterexample) and the missing
half was a *word-level* dominance condition needing pd-list machinery.
Here the situation is the opposite: the word-free static search sees
everything (`Iso` is word-blind by definition — it quantifies over tree
pairs, not words), and the only open half is arithmetic bookkeeping over
occurrences. If one wants a middle notion, `Iso` is strictly stronger
than `Robust` (`iso→robust` in `Robust.lagda.md`), and the family
witnesses above (`aa`, `maskC`, `starC`) are rejected by the criterion —
`a + a` is the calibration case that is `Iso` and `Robust` at once.

## 5. Reassessment after the posix rule simplification

The posix order rules were simplified (removal of `choice-rl` and of the
`length v₁ ≥ length v₂` premise of `choice-lr`, `cgp.posix.Order`). This
section re-runs the assessment. Three findings: the simplification does
not change the top-level posix relation (it is a true redundancy
elimination); with the inner rule sets now IDENTICAL, the failure of
`Iso` reduces to pure length arithmetic (normal-form theorems,
formalized); and the static-criterion question sharpens into a precise
Presburger-shaped arithmetic problem per regex.

### 5.1 The refactor is relation-preserving

The inner order is reachable from the top level ONLY through `len-≡`
(`len->` has no inner premise). So at every inner choice node of a
top-level derivation, the enclosing `len-≡` already supplies
|left reading| ≡ |right reading|: the removed `choice-lr` guard was
always satisfiable there, and the removed `choice-rl` (strictly longer
right reading) contradicted its own enclosing equality — it could never
fire inside a top-level derivation. Pairs where the right reading IS
strictly longer (the only instances `choice-rl` could have matched) are
exactly what top-level `len->` already relates:

```agda
-- Purpose: the instances the old choice-rl could match (right reading
--   strictly longer) are all derivable by len-> at the top level.
-- Used by: §5.1 safety argument.
-- Proof idea: with-abstract the two branch flattings; the hypothesis and
--   the len-> premise then present the same lengths, so len-> applies.
rl-len : ∀ { l s : RE } { loc : ℕ } { a : U l } { c : U s }
  → length (proj₁ (flat c)) > length (proj₁ (flat a))
  → length (proj₁ (flat (RightU {l} {s} {loc} c)))
    > length (proj₁ (flat (LeftU {l} {s} {loc} a)))
rl-len {l} {s} {loc} {a} {c} n with flat a | flat c
... | w₁ , _ | w₂ , _ = n

right-longer→ᵖ : ∀ { l s : RE } { loc : ℕ } { a : U l } { c : U s }
  → length (proj₁ (flat c)) > length (proj₁ (flat a))
  → ( (l + s ` loc) ⊢ RightU c >ᵖ LeftU a )
right-longer→ᵖ {l} {s} {loc} {a} {c} n =
  PosixOrder.len-> (rl-len {l} {s} {loc} {a} {c} n)

-- Purpose: at equal branch lengths, RightU >ᵖ LeftU is unprovable — the
--   len-≡ route has no inner rule for that orientation (no choice-rl),
--   and the len-> route contradicts the supplied equality.
-- Used by: §5.1 safety argument (the self-contradictory old instances).
-- Proof idea: inversion on the two top rules; the len-> premise
--   contradicts the equality (with-abstraction makes them coincide).
rl-not : ∀ { l s : RE } { loc : ℕ } { a : U l } { c : U s }
  → length (proj₁ (flat c)) ≡ length (proj₁ (flat a))
  → ¬ ( length (proj₁ (flat (RightU {l} {s} {loc} c)))
      > length (proj₁ (flat (LeftU {l} {s} {loc} a))) )
rl-not {l} {s} {loc} {a} {c} h n with flat a | flat c
... | w₁ , _ | w₂ , _ = <⇒≢ n (sym h)

no-ᵖ-rl-at-equal : ∀ { l s : RE } { loc : ℕ } { a : U l } { c : U s }
  → length (proj₁ (flat c)) ≡ length (proj₁ (flat a))
  → ¬ ( (l + s ` loc) ⊢ RightU c >ᵖ LeftU a )
no-ᵖ-rl-at-equal {l} {s} {loc} {a} {c} h (PosixOrder.len-> n) =
  rl-not {l} {s} {loc} {a} {c} h n
no-ᵖ-rl-at-equal {l} {s} {loc} {a} {c} h (PosixOrder.len-≡ eq ())
```

### 5.2 Normal forms: the length layer is all there is

With the two inner rule sets now IDENTICAL (same `seq₁`/`seq₂` with free
lexicographic siblings, same unguarded `choice-lr`, same choice-ll/rr,
same one-directional star rules, and no `choice-rl` on either side —
meta-facts 3–4 hold for BOTH orders), every `Iso` failure reduces to a
statement about lengths of greedy pairs / non-greedy pairs:

- `NonIso₁ r` ⟺ `r` has a pair with a GREEDY derivation whose winner is
  strictly shorter (`ShortPair`);
- `NonIso₂ r` ⟺ `r` has a strictly longer pair with NO greedy derivation
  (`LongPair`).

The hard directions run the derivation through the shared inner rules:
at equal lengths every premise either replays across (the rules match)
or already contains the smaller counterexample, so induction on the
derivation produces a witness at the length layer.

```agda
-- Purpose: a greedy-related pair whose winner is strictly shorter.
-- Used by: noniso₁→short, short→noniso₁ (normal form for NonIso₁).
-- Proof idea: N/A (record type).
ShortPair : RE → Set
ShortPair r = Σ ( U r ) λ u → Σ ( U r ) λ v
  → ( r ⊢ u >ᵍ v ) × length (proj₁ (flat u)) Nat.< length (proj₁ (flat v))

-- Purpose: a strictly longer pair with no greedy derivation.
-- Used by: noniso₂→long, long→noniso₂ (normal form for LongPair).
-- Proof idea: N/A (record type).
LongPair : RE → Set
LongPair r = Σ ( U r ) λ u → Σ ( U r ) λ v
  → ¬ ( r ⊢ u >ᵍ v ) × length (proj₁ (flat v)) Nat.< length (proj₁ (flat u))

-- Length transports through the tree constructors (used by sp-*, lp-*).
-- Each is proved by with-abstracting on the sub-flattening: `flat`
--   evaluates the sub-flattening first (its own with-blocks), so inside
--   the with-clause the goal and the hypothesis present the very same
--   length expressions and the transport is the identity. (Proving them
--   by rewriting/subst over the neutral `proj₁ ∘ flat` equalities hits
--   Agda's inversion-depth wall instead.)
L-< : ∀ { l s : RE } { loc : ℕ } { x y : U l }
  → length (proj₁ (flat x)) Nat.< length (proj₁ (flat y))
  → length (proj₁ (flat (LeftU {l} {s} {loc} x)))
    Nat.< length (proj₁ (flat (LeftU {l} {s} {loc} y)))
L-< {l} {s} {loc} {x} {y} h with flat x | flat y
... | w₁ , _ | w₂ , _ = h

R-< : ∀ { l s : RE } { loc : ℕ } { x y : U s }
  → length (proj₁ (flat x)) Nat.< length (proj₁ (flat y))
  → length (proj₁ (flat (RightU {l} {s} {loc} x)))
    Nat.< length (proj₁ (flat (RightU {l} {s} {loc} y)))
R-< {l} {s} {loc} {x} {y} h with flat x | flat y
... | w₁ , _ | w₂ , _ = h

-- (_++_ on the right is the only place needing real arithmetic: length
--  of a concatenation, and _+_ computes on its LEFT operand only)
+-mono-<-r : ∀ { a b : ℕ } → a Nat.< b → (c : ℕ) → (a Nat.+ c) Nat.< (b Nat.+ c)
+-mono-<-r {a} {b} h zero    = subst₂ _<_ (sym (+-identityʳ a)) (sym (+-identityʳ b)) h
+-mono-<-r {a} {b} h (suc c) =
  subst₂ _<_ (sym (+-suc a c)) (sym (+-suc b c)) (s≤s (+-mono-<-r {a} {b} h c))

++-< : ∀ { p q w : List Char }
  → length p Nat.< length q → length (p ++ w) Nat.< length (q ++ w)
++-< {p} {q} {w} h =
  subst₂ _<_ (sym (length-++ p)) (sym (length-++ q)) (+-mono-<-r h (length w))

PairR-< : ∀ { l s : RE } { loc : ℕ } { x y : U l } { w : U s }
  → length (proj₁ (flat x)) Nat.< length (proj₁ (flat y))
  → length (proj₁ (flat (PairU {l} {s} {loc} x w)))
    Nat.< length (proj₁ (flat (PairU {l} {s} {loc} y w)))
PairR-< {l} {s} {loc} {x} {y} {w} h with flat x | flat y | flat w
... | w₁ , _ | w₂ , _ | w₃ , _ = ++-< {w₁} {w₂} {w₃} h

-- (left concatenation: by induction on the concatenated prefix, where
--  _++_ and _<_ both compute, so no arithmetic transport is needed)
++l-< : ∀ (w : List Char) { p q : List Char }
  → length p Nat.< length q → length (w ++ p) Nat.< length (w ++ q)
++l-< []      h = h
++l-< (c ∷ w) h = s≤s (++l-< w h)

PairL-< : ∀ { l s : RE } { loc : ℕ } { x y : U s } { w : U l }
  → length (proj₁ (flat x)) Nat.< length (proj₁ (flat y))
  → length (proj₁ (flat (PairU {l} {s} {loc} w x)))
    Nat.< length (proj₁ (flat (PairU {l} {s} {loc} w y)))
PairL-< {l} {s} {loc} {x} {y} {w} h with flat w | flat x | flat y
... | w₃ , _ | w₁ , _ | w₂ , _ = ++l-< w₃ h

Cons-< : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { x y : U m } { xs : List (U m) }
  → length (proj₁ (flat x)) Nat.< length (proj₁ (flat y))
  → length (proj₁ (flat (ListU {m} {nε} {loc} (x ∷ xs))))
    Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} (y ∷ xs))))
Cons-< {m} {nε} {loc} {x} {y} {xs} h
  with flat x | flat y | flat (ListU {m} {nε} {loc} xs)
... | w₁ , _ | w₂ , _ | w₃ , _ = ++-< {w₁} {w₂} {w₃} h

-- trichotomy, kept local (plain < / ≡ / > as a sum, so with-clauses
-- carry the length evidence directly; `compare`'s Ordering is indexed
-- and does not survive with-patterns on two neutral lengths).
tri : ∀ ( a b : ℕ) → (a Nat.< b) ⊎ (a ≡ b) ⊎ (b Nat.< a)
tri zero    zero       = inj₂ (inj₁ refl)
tri zero    (suc b)    = inj₁ (s≤s z≤n)
tri (suc a) zero       = inj₂ (inj₂ (s≤s z≤n))
tri (suc a) (suc b) with tri a b
... | inj₁ h           = inj₁ (s≤s h)
... | inj₂ (inj₁ refl) = inj₂ (inj₁ refl)
... | inj₂ (inj₂ h)    = inj₂ (inj₂ (s≤s h))

-- Re-embedding helpers: a length-layer witness inside a subterm yields
--   one for the enclosing regex (the shared rules replay both ways).
-- Used by: replay-ᵍ, replay-ᵖ.
sp-ll : ∀ { l s : RE } { loc : ℕ } → ShortPair l → ShortPair (l + s ` loc)
sp-ll {l} {s} {loc} (x , y , dᵍₓ , h)
  = LeftU x , LeftU y
    , ( GreedyOrder.sub (GreedyOrder.choice-ll {l} {s} {loc} {x} {y} dᵍₓ) , L-< {l} {s} {loc} {x} {y} h )

sp-rr : ∀ { l s : RE } { loc : ℕ } → ShortPair s → ShortPair (l + s ` loc)
sp-rr {l} {s} {loc} (x , y , dᵍₓ , h)
  = RightU x , RightU y
    , ( GreedyOrder.sub (GreedyOrder.choice-rr {l} {s} {loc} {x} {y} dᵍₓ) , R-< {l} {s} {loc} {x} {y} h )

sp-pairr : ∀ { l s : RE } { loc : ℕ } (w : U s) → ShortPair l → ShortPair (l ● s ` loc)
sp-pairr {l} {s} {loc} w (x , y , dᵍₓ , h)
  = PairU x w , PairU y w
    , ( GreedyOrder.sub (GreedyOrder.seq₁ {l} {s} {loc} {x} {y} {w} {w} dᵍₓ) , PairR-< {l} {s} {loc} {x} {y} {w} h )

sp-pairl : ∀ { l s : RE } { loc : ℕ } (w : U l) → ShortPair s → ShortPair (l ● s ` loc)
sp-pairl {l} {s} {loc} w (x , y , dᵍₓ , h)
  = PairU w x , PairU w y
    , ( GreedyOrder.sub (GreedyOrder.seq₂ {l} {s} {loc} {w} {w} {x} {y} refl dᵍₓ) , PairL-< {l} {s} {loc} {x} {y} {w} h )

sp-cons : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ }
  → (xs : List (U m)) → ShortPair m → ShortPair (m * nε ` loc)
sp-cons {m} {nε} {loc} xs (x , y , dᵍₓ , h)
  = ListU (x ∷ xs) , ListU (y ∷ xs)
    , ( GreedyOrder.sub (GreedyOrder.star-head {m} {loc} {nε} {x} {y} {xs} {xs} dᵍₓ) , Cons-< {m} {nε} {loc} {x} {y} {xs} h )

mutual
  short-from-ᵍ : ∀ { r : RE } { u v : U r }
    → (dᵍ : r ⊢ u >ᵍ v) → ¬ ( r ⊢ u >ᵖ v ) → ShortPair r
  short-from-ᵍ {r} {u} {v} dᵍ ¬dᵖ
    with tri (length (proj₁ (flat u))) (length (proj₁ (flat v)))
  ... | inj₁ h         = u , v , dᵍ , h
  ... | inj₂ (inj₁ eq) = replay-ᵍ dᵍ eq ¬dᵖ
  ... | inj₂ (inj₂ h)  = ⊥-elim (¬dᵖ (pos-long-wins h))

  replay-ᵍ : ∀ { r : RE } { u v : U r }
    → (dᵍ : r ⊢ u >ᵍ v)
    → length (proj₁ (flat u)) ≡ length (proj₁ (flat v))
    → ¬ ( r ⊢ u >ᵖ v ) → ShortPair r
  replay-ᵍ (GreedyOrder.sub GreedyOrder.choice-lr) eq ¬dᵖ
    = ⊥-elim (¬dᵖ (PosixOrder.len-≡ eq PosixOrder.choice-lr))
  replay-ᵍ {r = l + s ` loc} (GreedyOrder.sub (GreedyOrder.choice-ll {l} {s} {loc} {v₁} {v₁'} d₁)) eq ¬dᵖ
    = sp-ll {l} {s} {loc}
        (short-from-ᵍ d₁ (λ d₁ᵖ → ⊥-elim (¬dᵖ (PosixOrder.len-≡ eq
          (PosixOrder.choice-ll {l} {s} {loc} {v₁} {v₁'} d₁ᵖ)))))
  replay-ᵍ {r = l + s ` loc} (GreedyOrder.sub (GreedyOrder.choice-rr {l} {s} {loc} {v₂} {v₂'} d₁)) eq ¬dᵖ
    = sp-rr {l} {s} {loc}
        (short-from-ᵍ d₁ (λ d₁ᵖ → ⊥-elim (¬dᵖ (PosixOrder.len-≡ eq
          (PosixOrder.choice-rr {l} {s} {loc} {v₂} {v₂'} d₁ᵖ)))))
  replay-ᵍ {r = l ● s ` loc} (GreedyOrder.sub (GreedyOrder.seq₁ {l} {s} {loc} {v₁} {v₁'} {v₂} {v₂'} d₁)) eq ¬dᵖ
    = sp-pairr {l} {s} {loc} v₂
        (short-from-ᵍ d₁ (λ d₁ᵖ → ⊥-elim (¬dᵖ (PosixOrder.len-≡ eq
          (PosixOrder.seq₁ {l} {s} {loc} {v₁} {v₁'} {v₂} {v₂'} d₁ᵖ)))))
  replay-ᵍ {r = l ● s ` loc} (GreedyOrder.sub (GreedyOrder.seq₂ {l} {s} {loc} {v₁} {v₁'} {v₂} {v₂'} e d₂)) eq ¬dᵖ
    = sp-pairl {l} {s} {loc} v₁
        (short-from-ᵍ d₂ (λ d₂ᵖ → ⊥-elim (¬dᵖ (PosixOrder.len-≡ eq
          (PosixOrder.seq₂ {l} {s} {loc} {v₁} {v₁'} {v₂} {v₂'} e d₂ᵖ)))))
  replay-ᵍ (GreedyOrder.sub GreedyOrder.star-cons-nil) eq ¬dᵖ
    = ⊥-elim (¬dᵖ (PosixOrder.len-≡ eq PosixOrder.star-cons-nil))
  replay-ᵍ {r = m * nε ` loc} (GreedyOrder.sub (GreedyOrder.star-head {m} {loc} {nε} {v₁} {v₂} {vs₁} {vs₂} d₁)) eq ¬dᵖ
    = sp-cons {m} {nε} {loc} vs₁
        (short-from-ᵍ d₁ (λ d₁ᵖ → ⊥-elim (¬dᵖ (PosixOrder.len-≡ eq
          (PosixOrder.star-head {m} {loc} {nε} {v₁} {v₂} {vs₁} {vs₂} d₁ᵖ)))))
  replay-ᵍ {r = m * nε ` loc} (GreedyOrder.sub (GreedyOrder.star-tail {m} {loc} {nε} {v₁} {v₂} {vs₁} {vs₂} e d₂)) eq ¬dᵖ
    = short-from-ᵍ d₂ (λ d₂ᵖ → ⊥-elim (¬dᵖ (PosixOrder.len-≡ eq
        (PosixOrder.star-tail {m} {loc} {nε} {v₁} {v₂} {vs₁} {vs₂} e d₂ᵖ))))
        -- the premise pair is a star-regex pair itself: no re-embedding

-- Purpose: NonIso₁ r ↔ ShortPair r (the normal-form equivalence, half 1).
-- Used by: §5 prose.
-- Proof idea: →: short-from-ᵍ; ←: no-ᵖ-if-shorter (meta-fact 1).
noniso₁→short : ∀ { r : RE } → NonIso₁ r → ShortPair r
noniso₁→short (u , v , dᵍ , ¬dᵖ) = short-from-ᵍ dᵍ ¬dᵖ

short→noniso₁ : ∀ { r : RE } → ShortPair r → NonIso₁ r
short→noniso₁ (u , v , dᵍ , h) = u , v , dᵍ , no-ᵖ-if-shorter h
```

```agda
-- Purpose: inversion helpers: an embedded pair (same context on one
--   side) is greedy-related only if the inner pair is (the seq₂ /
--   star-tail congruence branches die on the length gap).
-- Used by: lp-*, replay-ᵖ.
-- Proof idea: invert through sub; the matching rule gives the premise;
--   congruence premises give a tree equality contradicting the strict
--   length gap (<⇒≢); remaining heads clash by constructors.
¬ᵍ-LeftU : ∀ { l s : RE } { loc : ℕ } { x y : U l }
  → ¬ ( l ⊢ x >ᵍ y ) → ¬ ( (l + s ` loc) ⊢ LeftU x >ᵍ LeftU y )
¬ᵍ-LeftU ¬xy (GreedyOrder.sub (GreedyOrder.choice-ll d)) = ¬xy d

¬ᵍ-RightU : ∀ { l s : RE } { loc : ℕ } { x y : U s }
  → ¬ ( s ⊢ x >ᵍ y ) → ¬ ( (l + s ` loc) ⊢ RightU x >ᵍ RightU y )
¬ᵍ-RightU ¬xy (GreedyOrder.sub (GreedyOrder.choice-rr d)) = ¬xy d

¬ᵍ-PairR : ∀ { l s : RE } { loc : ℕ } { x y : U l } { w : U s }
  → ¬ ( l ⊢ x >ᵍ y )
  → length (proj₁ (flat y)) Nat.< length (proj₁ (flat x))
  → ¬ ( (l ● s ` loc) ⊢ PairU x w >ᵍ PairU y w )
¬ᵍ-PairR ¬xy h (GreedyOrder.sub (GreedyOrder.seq₁ d)) = ¬xy d
¬ᵍ-PairR ¬xy h (GreedyOrder.sub (GreedyOrder.seq₂ e _)) =
  <⇒≢ h (sym (cong (λ z → length (proj₁ (flat z))) e))

¬ᵍ-PairL : ∀ { l s : RE } { loc : ℕ } { x y : U s } { w : U l }
  → ¬ ( s ⊢ x >ᵍ y ) → ¬ ( (l ● s ` loc) ⊢ PairU w x >ᵍ PairU w y )
¬ᵍ-PairL ¬xy (GreedyOrder.sub (GreedyOrder.seq₁ d)) = ⊥-elim (>ᵍ→¬≡ d refl)
¬ᵍ-PairL ¬xy (GreedyOrder.sub (GreedyOrder.seq₂ _ d₂)) = ¬xy d₂

¬ᵍ-ListCons : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { x y : U m } { xs : List (U m) }
  → ¬ ( m ⊢ x >ᵍ y )
  → length (proj₁ (flat y)) Nat.< length (proj₁ (flat x))
  → ¬ ( (m * nε ` loc) ⊢ ListU (x ∷ xs) >ᵍ ListU (y ∷ xs) )
¬ᵍ-ListCons ¬xy h (GreedyOrder.sub (GreedyOrder.star-head d)) = ¬xy d
¬ᵍ-ListCons ¬xy h (GreedyOrder.sub (GreedyOrder.star-tail e _)) =
  <⇒≢ h (sym (cong (λ z → length (proj₁ (flat z))) e))

-- Re-embedding for the LongPair normal form.
lp-ll : ∀ { l s : RE } { loc : ℕ } → LongPair l → LongPair (l + s ` loc)
lp-ll {l} {s} {loc} (x , y , ¬xy , h)
  = LeftU x , LeftU y , ( ¬ᵍ-LeftU {l} {s} {loc} {x} {y} ¬xy , L-< {l} {s} {loc} {y} {x} h )

lp-rr : ∀ { l s : RE } { loc : ℕ } → LongPair s → LongPair (l + s ` loc)
lp-rr {l} {s} {loc} (x , y , ¬xy , h)
  = RightU x , RightU y , ( ¬ᵍ-RightU {l} {s} {loc} {x} {y} ¬xy , R-< {l} {s} {loc} {y} {x} h )

lp-pairr : ∀ { l s : RE } { loc : ℕ } (w : U s) → LongPair l → LongPair (l ● s ` loc)
lp-pairr {l} {s} {loc} w (x , y , ¬xy , h)
  = PairU x w , PairU y w
    , ( ¬ᵍ-PairR {l} {s} {loc} {x} {y} {w} ¬xy h , PairR-< {l} {s} {loc} {y} {x} {w} h )

lp-pairl : ∀ { l s : RE } { loc : ℕ } (w : U l) → LongPair s → LongPair (l ● s ` loc)
lp-pairl {l} {s} {loc} w (x , y , ¬xy , h)
  = PairU w x , PairU w y
    , ( ¬ᵍ-PairL {l} {s} {loc} {x} {y} {w} ¬xy , PairL-< {l} {s} {loc} {y} {x} {w} h )

lp-cons : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ }
  → (xs : List (U m)) → LongPair m → LongPair (m * nε ` loc)
lp-cons {m} {nε} {loc} xs (x , y , ¬xy , h)
  = ListU (x ∷ xs) , ListU (y ∷ xs)
    , ( ¬ᵍ-ListCons {m} {nε} {loc} {x} {y} {xs} ¬xy h , Cons-< {m} {nε} {loc} {y} {x} {xs} h )

-- Purpose: NORMAL FORM, half 2: a posix derivation whose pair is not
--   greedy-related always contains (after re-embedding) a strictly
--   longer pair with no greedy derivation.
-- Used by: noniso₂→long.
-- Proof idea: len-> makes the pair itself the witness; len-≡ runs the
--   SHARED inner rules — a premise with no greedy derivation gives the
--   smaller witness (recursion), a derivable premise reconstructs the
--   whole pair (the rule sets are identical on both sides).
mutual
  long-from-ᵖ : ∀ { r : RE } { u v : U r }
    → (dᵖ : r ⊢ u >ᵖ v) → ¬ ( r ⊢ u >ᵍ v ) → LongPair r
  long-from-ᵖ {r} {u} {v} (PosixOrder.len-> n) ¬dᵍ = u , v , ¬dᵍ , n
  long-from-ᵖ {r} {u} {v} (PosixOrder.len-≡ eq d) ¬dᵍ = replay-ᵖ d eq ¬dᵍ

  replay-ᵖ : ∀ { r : RE } { u v : U r }
    → (d : PosixOrder._⊢_>ⁱ_ r u v)
    → length (proj₁ (flat u)) ≡ length (proj₁ (flat v))
    → ¬ ( r ⊢ u >ᵍ v ) → LongPair r
  replay-ᵖ PosixOrder.choice-lr eq ¬dᵍ
    = ⊥-elim (¬dᵍ (GreedyOrder.sub GreedyOrder.choice-lr))
  replay-ᵖ {r = l + s ` loc} (PosixOrder.choice-ll {l} {s} {loc} {v₁} {v₁'} d₁) eq ¬dᵍ
    = lp-ll {l} {s} {loc}
        (long-from-ᵖ d₁ (λ d₁ᵍ → ⊥-elim (¬dᵍ (GreedyOrder.sub
          (GreedyOrder.choice-ll {l} {s} {loc} {v₁} {v₁'} d₁ᵍ)))))
  replay-ᵖ {r = l + s ` loc} (PosixOrder.choice-rr {l} {s} {loc} {v₂} {v₂'} d₁) eq ¬dᵍ
    = lp-rr {l} {s} {loc}
        (long-from-ᵖ d₁ (λ d₁ᵍ → ⊥-elim (¬dᵍ (GreedyOrder.sub
          (GreedyOrder.choice-rr {l} {s} {loc} {v₂} {v₂'} d₁ᵍ)))))
  replay-ᵖ {r = l ● s ` loc} (PosixOrder.seq₁ {l} {s} {loc} {v₁} {v₁'} {v₂} {v₂'} d₁) eq ¬dᵍ
    = lp-pairr {l} {s} {loc} v₂
        (long-from-ᵖ d₁ (λ d₁ᵍ → ⊥-elim (¬dᵍ (GreedyOrder.sub
          (GreedyOrder.seq₁ {l} {s} {loc} {v₁} {v₁'} {v₂} {v₂'} d₁ᵍ)))))
  replay-ᵖ {r = l ● s ` loc} (PosixOrder.seq₂ {l} {s} {loc} {v₁} {v₁'} {v₂} {v₂'} e d₂) eq ¬dᵍ
    = lp-pairl {l} {s} {loc} v₁
        (long-from-ᵖ d₂ (λ d₂ᵍ → ⊥-elim (¬dᵍ (GreedyOrder.sub
          (GreedyOrder.seq₂ {l} {s} {loc} {v₁} {v₁'} {v₂} {v₂'} e d₂ᵍ)))))
  replay-ᵖ PosixOrder.star-cons-nil eq ¬dᵍ
    = ⊥-elim (¬dᵍ (GreedyOrder.sub GreedyOrder.star-cons-nil))
  replay-ᵖ {r = m * nε ` loc} (PosixOrder.star-head {m} {loc} {nε} {v₁} {v₂} {vs₁} {vs₂} d₁) eq ¬dᵍ
    = lp-cons {m} {nε} {loc} vs₁
        (long-from-ᵖ d₁ (λ d₁ᵍ → ⊥-elim (¬dᵍ (GreedyOrder.sub
          (GreedyOrder.star-head {m} {loc} {nε} {v₁} {v₂} {vs₁} {vs₂} d₁ᵍ)))))
  replay-ᵖ {r = m * nε ` loc} (PosixOrder.star-tail {m} {loc} {nε} {v₁} {v₂} {vs₁} {vs₂} e d₂) eq ¬dᵍ
    = long-from-ᵖ d₂ (λ d₂ᵍ → ⊥-elim (¬dᵍ (GreedyOrder.sub
        (GreedyOrder.star-tail {m} {loc} {nε} {v₁} {v₂} {vs₁} {vs₂} e d₂ᵍ))))
        -- the premise pair is a star-regex pair itself: no re-embedding

-- Purpose: NonIso₂ r ↔ LongPair r (the normal-form equivalence, half 2).
-- Used by: §5 prose.
-- Proof idea: →: long-from-ᵖ; ←: pos-long-wins (meta-fact 2).
noniso₂→long : ∀ { r : RE } → NonIso₂ r → LongPair r
noniso₂→long (u , v , dᵖ , ¬dᵍ) = long-from-ᵖ dᵖ ¬dᵍ

long→noniso₂ : ∀ { r : RE } → LongPair r → NonIso₂ r
long→noniso₂ (u , v , ¬dᵍ , h) = u , v , pos-long-wins h , ¬dᵍ

-- Purpose: the §2 families ARE instances of the normal forms: feeding
--   each family witness to the engines yields ShortPair/LongPair on the
--   very same pair.
-- Used by: §5 prose (families B/C → ShortPair, family A → LongPair).
-- Proof idea: every family pair carries a strict length gap that
--   computes (1<2, 2<3, 1<2), so tri selects the < branch and len->
--   matches directly: both engines return the witness unchanged.
short-aa : ShortPair aa
short-aa = noniso₁→short noniso₁-aa

short-maskC : ShortPair maskC
short-maskC = noniso₁→short noniso₁-maskC

long-aa : LongPair aa
long-aa = noniso₂→long noniso₂-aa

long-starC : LongPair starC
long-starC = noniso₂→long noniso₂-star
```

Consequences for the static criterion (updating §4):

- §4 open item 2 (the descent/completeness half) is CLOSED as a
  structural statement: the normal forms show no `Iso` failure exists
  outside the length layer — the §2 families are all instances of
  `ShortPair`/`LongPair` (family B fires BOTH: `short-aa`/`long-aa`;
  family C produces `short-maskC`, family A produces `long-starC`),
  and the engines `short-from-ᵍ`/`long-from-ᵖ` are that descent, with
  re-embedding into the enclosing regex.
- The criterion question is now exactly: **decide whether
  `ShortPair r` / `LongPair r` is inhabited**, i.e. whether the set of
  length-differences of greedy-related pairs of `r` contains a negative
  value (`ShortPair`), or the length-differences of NOT-greedy-related
  pairs contain a positive one (`LongPair`). This is arithmetic over
  the tree pairs of a regex — no words, no pd machinery.
- For a STAR-FREE regex both questions are decidable directly: greedy
  derivations and pair shapes are finite skeletons (list arguments
  force no recursion), each skeleton fixes its length pair (every letter
  leaf contributes 1, character choice is irrelevant), so brute-force
  skeleton enumeration decides `Iso`.
- With stars the per-skeleton length pairs range over unbounded sums
  (`ListU` lists of arbitrary length), so the questions become
  Presburger-style emptiness problems over semilinear length sets —
  decidable in principle, but the bounded-witness lemma ("if inhabited,
  witnessed with list lengths bounded by the regex structure", the
  analogue of the `crit` bound) is still open, as is the exact
  per-subterm difference-set computation (former §4 item 1).
- The `a + a` calibration is unchanged and lands on the right side:
  its only cross pair has difference 0 — neither a `ShortPair` nor a
  `LongPair` exists, matching `iso-b+b` of §3.
