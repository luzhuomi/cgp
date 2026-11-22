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

import Data.List as List
open List using (List; _∷_; []; length)

import Data.Nat as Nat
open Nat using (ℕ; suc; zero; _≤_; _<_; _>_; s≤s; z≤n)

import Data.Nat.Properties as NatProperties
open NatProperties using (<-asym; <-irrefl; <⇒≢)

import Data.Product as Product
open Product using (Σ; _,_; _×_; proj₁; proj₂)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)

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
   and the four *meta-facts* that explain the whole gap between the two
   rule sets (two per side: posix's length filter and length totality;
   greedy's two unconditional shape rules with no posix counterpart guard).
2. Three counterexample families, each fully formalized at its minimal
   regex: **B** (unguarded `choice-lr` vs the length guard), **C** (a
   *balanced* sum whose length-neutral greedy pair is length-skewed by a
   concatenation sibling — no occurrence locally violates the guard, so
   the naive one-occurrence criterion is incomplete), **A** (the reversed
   star pair, decided by posix `len->` but never derivable greedily).
3. Two positive proofs: `Iso ($ 'b')` and `Iso ($ 'b' + $ 'b')` — the
   shape of a positive certificate (all pairs settled by shape gaps or
   matching rules).
4. Assessment prose: the criterion shape (occurrence scan + minLen/maxLen
   arithmetic), what is proved here, what remains open.

What is NOT connected: the decision procedure itself, and the
completeness direction (every `¬Iso` regex fires one of the families).
Neither is claimed; §4 states precisely what each side would need.

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

Read together: **greedy is shape-total at two points** (`choice-lr`
unconditional — meta-fact 3 shows its converse is absent; `star-cons-nil`)
**while posix is length-total** (meta-facts 1–2) **and shape-guarded**
(`choice-lr` needs the left reading at least as long, `choice-rl` strictly
longer). Every `Iso` failure is one of these asymmetries seen through a
tree-pair shape.

## 2. The counterexample families

### Family B — the unguarded choice rule

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

At the choice occurrence itself the guard fails (`minLen(a) = 1 <
maxLen(a●a) = 2`); the same pair then witnesses BOTH halves: `(a, aa)` is
greedy but filtered by length, `(aa, a)` is posix (`len->`) but has no
greedy rule.

### Family C — balanced sums, skewed by context

Family B's occurrence test (`minLen(left) ≥ maxLen(right)` at every sum)
is NOT sufficient. The regex below has two sum occurrences, both
*balanced* (single letters on both sides; and the right sum puts the
longer branch on the LEFT, which satisfies the guard direction) — yet the
lexicographic `seq₁` rule leaves the right siblings unconstrained, so a
length-neutral greedy pair at the left sum pairs with *any* pair of right
siblings, and choosing shorter-then-longer siblings makes the whole pair
fail the posix length filter.

```agda
-- Purpose: minimal family-C regex: (d + d) ● (e●e + e). Every sum
--   occurrence has minLen(left) ≥ maxLen(right).
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
order (meta-fact 3 kills the greedy one; the posix guard would need
`1 > 2`) — they are legal precisely because `seq₁` never looks at them.

### Family A — the reversed star pair, no sums at all

```agda
-- Purpose: minimal sum-free counterexample: b* ● c*. The right star
--   supplies the length; no sum occurrence exists, so no guard test of
--   any kind can fire here — the failure is pure rule-set shape.
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
--   in both orders (the guard 1 ≥ 1 holds; the reverse pair is a shape
--   gap on both sides), same-side pairs are never related.
-- Used by: criterion calibration (minLen(left) ≥ maxLen(right) at a sum is
--   exactly the surviving condition).
-- Proof idea: four shape lemmas + reconstruction for the (LeftU, RightU)
--   pair: len-≡ refl (choice-lr (1 ≤ 1)) and sub choice-lr.  Unlisted
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
no-ᵖ-rl (PosixOrder.len-≡ _ (PosixOrder.choice-rl q)) = ⊥-elim (<-irrefl refl q)

iso-b+b : Iso b+b
iso-b+b = iso λ
  { (LeftU (LetterU 'b')) (LeftU (LetterU 'b'))
      → ( (λ d → ⊥-elim (no-ᵍ-ll d)) , (λ d → ⊥-elim (no-ᵖ-ll d)) )
  ; (RightU (LetterU 'b')) (RightU (LetterU 'b'))
      → ( (λ d → ⊥-elim (no-ᵍ-rr d)) , (λ d → ⊥-elim (no-ᵖ-rr d)) )
  ; (LeftU (LetterU 'b')) (RightU (LetterU 'b')) →
      ( (λ _ → PosixOrder.len-≡ refl (PosixOrder.choice-lr (s≤s z≤n)))
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
of trees, both orders follow the pair shape identically (seq/star/choice-
same-side rules match). They differ only at:

- posix `len->`: *every* pair with |u| > |v| is posix-related (top-level
  totality — this is what family A exploits);
- posix `len-≡`: nothing with |u| < |v| ever is (length filter);
- posix guards at choice nodes (`choice-lr` needs |left| ≥ |right|;
  `choice-rl` needs strict >) versus greedy's unconditional `choice-lr`
  and absent `choice-rl`;
- the one-directional `star-cons-nil` in both, which only becomes an
  obstruction when combined with the length filter (family A).

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
    lengths 2 vs 1 — this family is invisible to every sum-guard test,
    the regex has no sums).

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
   here.
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
