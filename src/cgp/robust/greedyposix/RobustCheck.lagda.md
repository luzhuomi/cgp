# RobustCheck: the criteria side of robustness

This module develops the *decision criteria* for the robustness property
`Robust` of `cgp.robust.greedyposix.Robust` (greedy vs posix maximal
parse trees agreeing word by word), in the shape of the ambiguity
criteria of `cgp.ambig.AmbigCheck` §13 (`crit`). Four layers:

1. `NonRobust` — the Σ-over-trees negation of robustness (a word-free,
   `Ambig`-mirror-shaped statement) and the exact characterization
   `Robust r ↔ ¬ NonRobust r`. Sound and complete; all ingredients are
   existing theorems: maximality existence (`>-wellfounded`ᵍ,
   `parseAll-head-isMax`ᵖ + `parseAll-complete`ᵖ) and uniqueness
   (`>-asym`, `>→¬≡` on both sides). Totality of the orders is NOT needed.
2. `OrderDiverge` — the *pair form*: two trees of one word that the two
   orders direct oppositely. `NonRobust → OrderDiverge → Ambig`:
   not-robustness is exactly the *order-visible* part of ambiguity;
   `a + a` shows `OrderDiverge` need not hold for an ambiguous-but-robust
   regex, and a dominating third alternative shows a fired `OrderDiverge`
   pair need not defeat robustness (the pair must decide the fiber).
3. `headEq? r w` — the semidecision procedure: compare the heads of the
   two computed `parseAll` lists with the parse-tree equality decision
   procedure `cgp.ParseTree._⊢_≟_`. `headEq? r w ≡ false → NonRobust r`
   (soundness) and `NonRobust r → ∃ w. headEq? r w ≡ false`
   (completeness, for words as finite witnesses).
4. `RobustCrit` — a static *certificate*: a divergence pair whose fiber
   is exactly the pair (a tight word fiber, decidable at a witness via
   membership in the computed list). `RobustCrit → NonRobust` with a
   concrete non-robust regex firing it. What is NOT connected: a bounded
   static search (subterm `Ctx`/`plug` patterns à la `crit` §13, with the
   shifted-split emptiness test at a concatenation boundary) that fires
   for *every* non-robust regex — see the note after §4.
5. The investigation of that bounded search: the two order rule sets
   differ ONLY at choice-node guards, so every divergent pair has the
   shifted-split shape (a bounded position search generates all of
   them); but `OrderDiverge` does NOT imply `NonRobust` — the formal
   `sepx` regex is `Robust` while firing a divergent pair — so a
   dominance side condition is provably required.

Why a `crit`-style test can never be A1/A3-shaped: at equal word length
the two orders coincide at every choice node (`choice-lr` fires on both
sides; `choice-rl`/`len->` need strict length difference — this is
precisely why `a + a` is robust). Divergence requires the comparison to
reach *unequal-length* prefix trees across a concatenation boundary.

```agda
{-# OPTIONS --rewriting  #-}
module cgp.robust.greedyposix.RobustCheck where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_)

import cgp.Word as Word
open Word using (_∈⟦_⟧)

import cgp.ParseTree as ParseTree
open ParseTree using (U; EmptyU; LetterU; LeftU; RightU; PairU; ListU; flat; unflat; _⊢_≟_)

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming (_⊢_>_ to _⊢_>ᵍ_; >→¬≡ to >ᵍ→¬≡; u>v→¬v>u to u>ᵍv→¬v>ᵍu)

import cgp.greedy.PartialDerivative as GreedyPD
open GreedyPD renaming (parseAll[_,_] to parseAllᵍ[_,_])

import cgp.greedy.ExtendedOrder as GreedyExt
open GreedyExt using (parseAll-is-greedy)

import cgp.greedy.MaxWord as GreedyMax
open GreedyMax renaming (≥-Max to ≥-Maxᵍ; ≥-max to ≥-maxᵍ)

import cgp.posix.Order as PosixOrder
open PosixOrder renaming (_⊢_>_ to _⊢_>ᵖ_; >→¬≡ to >ᵖ→¬≡)

import cgp.posix.PartialDerivative as PosixPD
open PosixPD renaming (parseAll[_,_] to parseAllᵖ[_,_])

import cgp.posix.MaxWord as PosixMax
open PosixMax renaming (≥-Max to ≥-Maxᵖ; ≥-max to ≥-maxᵖ)

import cgp.Utils as Utils
open Utils using (lookup-All)

import cgp.robust.greedyposix.Robust as RobustMod
open RobustMod using (Robust; robust)

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using (Ambig)

import Data.Bool as Bool
open Bool using (Bool; true; false)

import Data.List as List
open List using (List; _∷_; []; head)

import Data.Char as Char
open Char using (Char)

import Data.List.Relation.Unary.All as AllMod
open AllMod using (All)

import Data.List.Relation.Unary.Any as AnyMod
open AnyMod using (Any; here; there)

import Data.Nat as Nat
open Nat using (ℕ; suc; zero)

import Data.Product as Product
open Product using (_×_; _,_; Σ-syntax; ∃; ∃-syntax)
open Product.Σ using (proj₁; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Data.Empty as Empty
open Empty using (⊥-elim; ⊥)

import Relation.Nullary as Nullary
open Nullary using (Dec; yes; no)

import Relation.Nullary.Negation as Negation
open Negation using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; subst)

```

## 1. `NonRobust` and the characterization `Robust ↔ ¬ NonRobust`

`NonRobust` has no quantification over words: the word is a *component
of the witness*, exactly as in `Ambig` (`AmbigCheck` §1). The
characterization needs only: maxima exist (each parser produces one), a
max is unique per order (`>-asym`/`>→¬≡`), and case analysis on parse
tree equality (`_⊢_≟_`).

```agda
-- Purpose: the negation of robustness in Σ-over-trees form: two parse
--   trees that are the maximal trees of a common word under the two
--   different orders, and they are distinct.
-- Used by: the three characterization theorems below; §2, §3, §4.
-- Proof idea: N/A (definition).
NonRobust : RE → Set
NonRobust r = Σ[ u ∈ U r ] Σ[ v ∈ U r ] Σ[ w ∈ List Char ]
    ( ≥-Maxᵍ {r} w u ) × ( ≥-Maxᵖ {r} w v ) × ( ¬ ( u ≡ v ) )

-- Purpose: a ≥-Max witness is unique per order (greedy flavour).
-- Used by: characterization (robust→¬nonrobust), §3.
-- Proof idea: each maximal beats the other; asymmetry / >→¬≡ kill the
--   strict cases, the equality side is the conclusion.
≥-Maxᵍ-unique : ∀ { r : RE } { w : List Char } { u v : U r }
  → ≥-Maxᵍ {r} w u → ≥-Maxᵍ {r} w v → u ≡ v
≥-Maxᵍ-unique {r} {w} {u} {v} (≥-maxᵍ .w u flat-u≡w cmp-u) (≥-maxᵍ .w v flat-v≡w cmp-v)
  with cmp-u v flat-v≡w | cmp-v u flat-u≡w
...   | inj₁ u>v | inj₁ v>u = ⊥-elim (u>ᵍv→¬v>ᵍu u>v v>u)
...   | inj₁ u>v | inj₂ v≡u = ⊥-elim (>ᵍ→¬≡ u>v (sym v≡u))
...   | inj₂ u≡v | _        = u≡v

-- Purpose: a ≥-Max witness is unique per order (posix flavour).
-- Used by: characterization (robust→¬nonrobust, ¬nonrobust→robust), §3.
-- Proof idea: as ≥-Maxᵍ-unique, via PosixOrder.>-asym and >ᵖ→¬≡.
≥-Maxᵖ-unique : ∀ { r : RE } { w : List Char } { u v : U r }
  → ≥-Maxᵖ {r} w u → ≥-Maxᵖ {r} w v → u ≡ v
≥-Maxᵖ-unique {r} {w} {u} {v} (≥-maxᵖ .w u flat-u≡w cmp-u) (≥-maxᵖ .w v flat-v≡w cmp-v)
  with cmp-u v flat-v≡w | cmp-v u flat-u≡w
...   | inj₁ u>v | inj₁ v>u = ⊥-elim (PosixOrder.>-asym u>v v>u)
...   | inj₁ u>v | inj₂ v≡u = ⊥-elim (>ᵖ→¬≡ u>v (sym v≡u))
...   | inj₂ u≡v | _        = u≡v

-- Purpose: any tree of w is a member of the computed list, at the word
--   w itself (transport of parseAll-complete along the word equation).
-- Used by: ≥-Maxᵖ-∃, head-isMax lemmas, §3 cases.
-- Proof idea: parseAll-complete gives membership at proj₁ (flat u);
--   subst along proj₁ (flat u) ≡ w.
∈-parseAllᵍ : ∀ { r : RE } ( u : U r ) ( w : List Char )
  → proj₁ (flat {r} u) ≡ w
  → Any ( _≡_ u ) (parseAllᵍ[ r , w ])
∈-parseAllᵍ {r} u w u≡w = subst ( λ k → Any ( _≡_ u ) parseAllᵍ[ r , k ] ) u≡w
                           (proj₂ (GreedyPD.parseAll-complete {r} u))

∈-parseAllᵖ : ∀ { r : RE } ( u : U r ) ( w : List Char )
  → proj₁ (flat {r} u) ≡ w
  → Any ( _≡_ u ) (parseAllᵖ[ r , w ])
∈-parseAllᵖ {r} u w u≡w = subst ( λ k → Any ( _≡_ u ) parseAllᵖ[ r , k ] ) u≡w
                           (proj₂ (PosixPD.parseAll-complete {r} u))

-- Purpose: every word has a posix maximal tree (existence, ∃-form).
-- Used by: ¬nonrobust→robust.
-- Proof idea: the list parseAll[ r , w ] is non-empty (the tree u is in
--   it, ∈-parseAllᵖ); its head is ≥-Max (parseAll-head-isMax). Explicit
--   list + equation core, per the greedy >-wellfounded idiom (opaque
--   parseAll does not decompose in the constraint solver).
≥-Maxᵖ-∃ : ∀ { r : RE } { w : List Char }
  → ( u : U r ) → proj₁ (flat {r} u) ≡ w
  → ∃[ v ] ( ≥-Maxᵖ {r} w v )
≥-Maxᵖ-∃ {r} {w} u u≡w = core (parseAllᵖ[ r , w ]) refl
  where
    core : ( xs : List (U r) )
      → parseAllᵖ[ r , w ] ≡ xs
      → ∃[ v ] ( ≥-Maxᵖ {r} w v )
    core [] xs≡[] = ⊥-elim
      ( ∈-[] (subst ( λ L → Any ( _≡_ u ) L ) xs≡[] (∈-parseAllᵖ u w u≡w)) )
      where
        ∈-[] : Any ( _≡_ u ) [] → ⊥
        ∈-[] ()
    core (h ∷ t) xs≡h∷t = h , PosixMax.parseAll-head-isMax r w h
                            (trans (cong head xs≡h∷t) refl)

-- Purpose: soundness half — robustness rules out the NonRobust witness.
-- Used by: the characterization; the standing fact unambig→robust sits
--   on the same proof path (via UnAmbig → no distinct pair at all).
-- Proof idea: the robust biconditional transports the greedy maximum of
--   u into a posix ≥-Max of u; uniqueness then collapses u and v.
robust→¬nonrobust : ∀ ( r : RE ) → Robust r → ¬ NonRobust r
robust→¬nonrobust r (robust ev) (u , v , w , ( maxᵍ-u , maxᵖ-v , u≢v )) =
  u≢v (≥-Maxᵖ-unique (proj₁ (ev w u) maxᵍ-u) maxᵖ-v)

-- Purpose: the nonrobust witness refutes robustness.
-- Used by: the characterization.
-- Proof idea: same as robust→¬nonrobust (a direct refutation).
nonrobust→¬robust : ∀ ( r : RE ) → NonRobust r → ¬ Robust r
nonrobust→¬robust r (u , v , w , ( maxᵍ-u , maxᵖ-v , u≢v )) (robust ev) =
  u≢v (≥-Maxᵖ-unique (proj₁ (ev w u) maxᵍ-u) maxᵖ-v)

-- Purpose: completeness half — with no NonRobust witness available, the
--   two maximality notions agree for every word and tree.
-- Used by: the characterization (this is the Robust-construction).
-- Proof idea: transport a ≥-Maxᵍ of v into some posix maximum p
--   (≥-Maxᵖ-∃); either v ≡ p (decidable, _⊢_≟_) and we transport, or
--   (v, p) is a NonRobust witness, absurd. The other direction is the
--   mirror image using the greedy existence theorem >-wellfounded.
¬nonrobust→robust : ∀ ( r : RE ) → ¬ NonRobust r → Robust r
¬nonrobust→robust r ¬nr = robust {r} ev
  where
    ev : ( w : List Char ) → ( v : U r )
      → ( ≥-Maxᵍ {r} w v → ≥-Maxᵖ {r} w v )
      × ( ≥-Maxᵖ {r} w v → ≥-Maxᵍ {r} w v )
    ev w v = to-ev , from-ev
      where
        to-ev : ≥-Maxᵍ {r} w v → ≥-Maxᵖ {r} w v
        to-ev maxᵍ@ (≥-maxᵍ .w v v≡w _) with ≥-Maxᵖ-∃ {r} {w} v v≡w
        ...   | ( p , maxᵖ-p ) with r ⊢ v ≟ p
        ...   | yes v≡p = subst ( λ x → ≥-Maxᵖ {r} w x ) (sym v≡p) maxᵖ-p
        ...   | no v≢p  = ⊥-elim (¬nr (v , p , w , ( maxᵍ , ( maxᵖ-p , v≢p ))))

        from-ev : ≥-Maxᵖ {r} w v → ≥-Maxᵍ {r} w v
        from-ev maxᵖ@ (≥-maxᵖ .w v v≡w _) with GreedyMax.>-wellfounded {r} {w}
            (subst ( λ k → k ∈⟦ r ⟧ ) v≡w (proj₂ (flat {r} v)))
        ...   | ( g , maxᵍ-g ) with r ⊢ v ≟ g
        ...   | yes v≡g = subst ( λ x → ≥-Maxᵍ {r} w x ) (sym v≡g) maxᵍ-g
        ...   | no v≢g  = ⊥-elim
            ( ¬nr (g , v , w , ( maxᵍ-g , ( maxᵖ , λ g≡v → v≢g (sym g≡v) ) )))
```

## 2. `OrderDiverge`: the pair form, sitting inside ambiguity

Two trees of one word that the two orders direct *oppositely*. This is
the obstruction half of the decomposition: ambiguous regexes split into
those whose ambiguity the orders can see (`OrderDiverge` fires) and
order-blind ambiguity like `a + a` (it does not).

```agda
-- Purpose: a word-fiber pair that the two orders direct oppositely.
-- Used by: NonRobust→OrderDiverge, OrderDiverge→Ambig below.
-- Proof idea: N/A (definition).
OrderDiverge : RE → Set
OrderDiverge r = Σ[ u ∈ U r ] Σ[ v ∈ U r ]
    ( proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) )
  × ( r ⊢ u >ᵍ v ) × ( r ⊢ v >ᵖ u )

-- Purpose: a non-robustness witness IS an order-divergent pair: the two
--   maxima themselves (their comparison fields decide the directions).
-- Used by: the decomposition prose; §4 (RobustCrit strengthens this).
-- Proof idea: ≥-Max of u beats v and vice versa; the equality sides are
--   killed by the u ≢ v field.
NonRobust→OrderDiverge : ∀ ( r : RE ) → NonRobust r → OrderDiverge r
NonRobust→OrderDiverge r (u , v , w , ( ≥-maxᵍ .w u u≡w cmp-u ,
                                        ( ≥-maxᵖ .w v v≡w cmp-v , u≢v ) ))
  with cmp-u v v≡w | cmp-v u u≡w
...   | inj₁ u>ᵍv | inj₁ v>ᵖu = u , v , ( trans u≡w (sym v≡w) , u>ᵍv , v>ᵖu )
...   | inj₁ u>ᵍv | inj₂ v≡u  = ⊥-elim (u≢v (sym v≡u))
...   | inj₂ u≡v  | _         = ⊥-elim (u≢v u≡v)

-- Purpose: order divergence is a special case of ambiguity.
-- Used by: the decomposition prose.
-- Proof idea: >ᵍ→¬≡ turns the strict greedy comparison into tree
--   disequality.
OrderDiverge→Ambig : ∀ ( r : RE ) → OrderDiverge r → Ambig r
OrderDiverge→Ambig r (u , v , ( word≡ , ( u>ᵍv , _ ) )) =
  u , v , ( word≡ , >ᵍ→¬≡ u>ᵍv )
```

The two inclusions are strict in the interesting direction:
`NonRobust → OrderDiverge → Ambig` holds, but not converses.
`a + a` (`Robust.lagda.md` §"the converse does not hold") is ambiguous
with *no* divergent pair. Conversely an `OrderDiverge` pair can sit
*below* a shared maximum and robustness survives — the `sepx` regex of
§5 is a fully formalized instance: the two `robex` trees of `aab` are
divergent there, but the third tree (the literal branch `a ● a ● b`)
beats both in both orders at the higher choice node (`choice-lr` on
both sides, equal lengths), and `sepx` is `Robust`. (A pattern that
merely puts a longer alternative first does NOT work: with a fixed
continuation like `● b` all branches read the same prefix, so no
divergent pair exists at all — the dominating branch must *duplicate*
the pattern's word.) So a criterion targeting `NonRobust` must be about
*deciding the fiber*, not merely about firing.

## 3. The semidecision procedure `headEq?`

`NonRobust` is semidecidable: for a concrete word both parser outputs
are computed lists, heads are comparable by the parse-tree equality
decision procedure (`cgp.ParseTree._⊢_≟_`), and by the head-is-maximal
theorems plus uniqueness, a detected head difference is a `NonRobust`
witness.

```agda
-- local: the two Bool truth values are not propositionally equal
true≢false : ¬ ( true ≡ false )
true≢false ()

-- Purpose: compare the two heads of two computed tree lists (true = the
--   heads agree; both lists empty counts as agreeing).
-- Used by: headEq?, §3 theorems (which match lists explicitly).
-- Proof idea: N/A (definition; _⊢_≟_ decides head equality).
cmp-heads : ∀ { r : RE } → List (U r) → List (U r) → Bool
cmp-heads []       []        = true
cmp-heads []       (p ∷ ps)  = false
cmp-heads (g ∷ gs) []        = false
cmp-heads {r} (g ∷ gs) (p ∷ ps) with r ⊢ g ≟ p
...   | yes _ = true
...   | no  _ = false

-- Purpose: word-indexed Bool test: do the two parsers pick the same
--   head tree for w?
-- Used by: the two §3 theorems.
-- Proof idea: N/A (definition).
headEq? : ( r : RE ) → ( w : List Char ) → Bool
headEq? r w = cmp-heads (parseAllᵍ[ r , w ]) (parseAllᵖ[ r , w ])

-- Purpose: the head of the greedy computed list is ≥-Maxᵍ (the greedy
--   counterpart of cgp.posix.MaxWord.parseAll-head-isMax).
-- Used by: §3 theorems.
-- Proof idea: as the posix one: transport Theorem (parseAll-is-greedy
--   sortedness) along the head equation; any competitor reading w is a
--   list member (∈-parseAllᵍ), dominated by the sorted head
--   (sorted-head-≥-all-Any-′); reading-w is inherited from list soundness.
parseAllᵍ-head-isMax : ∀ ( r : RE ) ( w : List Char ) ( t : List (U r) ) ( g : U r )
  → parseAllᵍ[ r , w ] ≡ g ∷ t
  → ≥-Maxᵍ {r} w g
parseAllᵍ-head-isMax r w t g pa≡g∷t = ≥-maxᵍ w g flat-g≡w max-of-v
  where
    sorted : GreedyOrder.>-sorted {r} (g ∷ t)
    sorted = subst ( λ L → GreedyOrder.>-sorted {r} L ) pa≡g∷t
             (GreedyExt.parseAll-is-greedy {r} {w})

    g∈ : Any ( _≡_ g ) (parseAllᵍ[ r , w ])
    g∈ = subst ( λ L → Any ( _≡_ g ) L ) (sym pa≡g∷t) (here refl)

    flat-g≡w : proj₁ (flat {r} g) ≡ w
    flat-g≡w = lookup-All (GreedyPD.parseAll-sound {r} {w}) g∈

    max-of-v : ( v : U r ) → proj₁ (flat {r} v) ≡ w → GreedyMax._⊢_≥_ r g v
    max-of-v v v≡w = GreedyMax.sorted-head-≥-all-Any-′ r g t sorted v
        (subst ( λ L → Any ( _≡_ v ) L ) pa≡g∷t (∈-parseAllᵍ v w v≡w))

-- Purpose: soundness of the test — a detected head difference is a
--   NonRobust witness (the two heads, maximal by the head-isMax results).
-- Used by: the semidecision reading.
-- Proof idea: case analysis on the two computed lists (explicit-list
--   core, the parseAll terms are opaque to the solver); the two-empty-
--   list shapes are absurd by parser completeness + soundness; the
--   head-equal shape is absurd for a `false` verdict.
headEq?-false→NonRobust : ∀ ( r : RE ) ( w : List Char )
  → headEq? r w ≡ false
  → NonRobust r
headEq?-false→NonRobust r w h¬ =  core (parseAllᵍ[ r , w ]) (parseAllᵖ[ r , w ]) refl refl h¬
  where
    core : ( xs ys : List (U r) )
      → parseAllᵍ[ r , w ] ≡ xs → parseAllᵖ[ r , w ] ≡ ys
      → cmp-heads xs ys ≡ false → NonRobust r
    core []      []       eq₁ eq₂ h = ⊥-elim (true≢false h)
    core []      (p ∷ ps) eq₁ eq₂ h = ⊥-elim
      ( ∈-[]ᵍ (subst ( λ L → Any ( _≡_ p ) L ) eq₁ (∈-parseAllᵍ p w p≡w)) )
      where
        p≡w : proj₁ (flat {r} p) ≡ w
        p≡w = lookup-All
          (subst ( λ L → All ( λ u → proj₁ (flat {r} u) ≡ w ) L ) eq₂
            (PosixPD.parseAll-sound {r} {w}))
          (here refl)
        ∈-[]ᵍ : Any ( _≡_ p ) [] → ⊥
        ∈-[]ᵍ ()
    core (g ∷ gs) []      eq₁ eq₂ h = ⊥-elim
      ( ∈-[]ᵖ (subst ( λ L → Any ( _≡_ g ) L ) eq₂ (∈-parseAllᵖ g w g≡w)) )
      where
        g≡w : proj₁ (flat {r} g) ≡ w
        g≡w = lookup-All
          (subst ( λ L → All ( λ u → proj₁ (flat {r} u) ≡ w ) L ) eq₁
            (GreedyPD.parseAll-sound {r} {w}))
          (here refl)
        ∈-[]ᵖ : Any ( _≡_ g ) [] → ⊥
        ∈-[]ᵖ ()
    core (g ∷ gs) (p ∷ ps) eq₁ eq₂ h with r ⊢ g ≟ p
    ...   | yes _   = ⊥-elim (true≢false h)
    ...   | no ¬g≡p = g , p , w , ( parseAllᵍ-head-isMax r w gs g eq₁ ,
        ( PosixMax.parseAll-head-isMax r w p (trans (cong head eq₂) refl)
        , ¬g≡p ) )

-- Purpose: completeness of the test — a NonRobust witness word is
--   detected (enumerate the witness word).
-- Used by: the semidecision reading.
-- Proof idea: at the witness word the heads are maximal (head-isMax
--   lemmas), hence equal to the witness maxima (uniqueness); if the
--   heads agreed the witnesses would agree.
NonRobust→∃-word-detected : ∀ ( r : RE )
  → NonRobust r
  → Σ[ w ∈ List Char ] ( headEq? r w ≡ false )
NonRobust→∃-word-detected r (u , v , w , ( maxᵍ-u@ (≥-maxᵍ .w u u≡w _) ,
    ( maxᵖ-v@ (≥-maxᵖ .w v v≡w _) , u≢v ) )) = w , core (parseAllᵍ[ r , w ])
    (parseAllᵖ[ r , w ]) refl refl
  where
    core : ( xs ys : List (U r) )
      → parseAllᵍ[ r , w ] ≡ xs → parseAllᵖ[ r , w ] ≡ ys
      → cmp-heads xs ys ≡ false
    core []      []       eq₁ eq₂ = ⊥-elim (∈-[]ᵐ (subst ( λ L → Any ( _≡_ u ) L )
        eq₁ (∈-parseAllᵍ u w u≡w)))
      where
        ∈-[]ᵐ : Any ( _≡_ u ) [] → ⊥
        ∈-[]ᵐ ()
    core []      (p ∷ ps) eq₁ eq₂ = ⊥-elim (∈-[]ᵐ (subst ( λ L → Any ( _≡_ u ) L )
        eq₁ (∈-parseAllᵍ u w u≡w)))
      where
        ∈-[]ᵐ : Any ( _≡_ u ) [] → ⊥
        ∈-[]ᵐ ()
    core (g ∷ gs) []      eq₁ eq₂ = ⊥-elim (∈-[]ᵛ (subst ( λ L → Any ( _≡_ v ) L )
        eq₂ (∈-parseAllᵖ v w v≡w)))
      where
        ∈-[]ᵛ : Any ( _≡_ v ) [] → ⊥
        ∈-[]ᵛ ()
    core (g ∷ gs) (p ∷ ps) eq₁ eq₂ with r ⊢ g ≟ p
    ...   | no ¬g≡p = refl
    ...   | yes g≡p = ⊥-elim (u≢v
        (trans (sym (≥-Maxᵍ-unique (parseAllᵍ-head-isMax r w gs g eq₁) maxᵍ-u))
          (trans g≡p (≥-Maxᵖ-unique
            (PosixMax.parseAll-head-isMax r w p (trans (cong head eq₂) refl))
            maxᵖ-v))))
```

## 4. `RobustCrit`: a static certificate for non-robustness

A `RobustCrit` witness is an `OrderDiverge` pair plus a *tightness*
condition: the two trees exhaust the fiber of their word. Tightness
turns "the orders differ somewhere" into "the orders differ *decisively*
— the two maxima are exactly the pair", so the certificate carries no
`≥-Max` records at all (its maximality is checked pairwise) — and at a
concrete witness tightness is decidable: membership of any `z` in the
computed list (`∈-parseAllᵖ`) reduces to a structural case analysis on
`here`/`there`, and the list is a concrete finite value for a concrete
regex and word.

```agda
-- Purpose: static certificate of non-robustness: a divergent order pair
--   that exhausts its word fiber.
-- Used by: RobustCrit→NonRobust, the robex example.
-- Proof idea: N/A (definition).
RobustCrit : RE → Set
RobustCrit r = Σ[ u ∈ U r ] Σ[ v ∈ U r ] Σ[ w ∈ List Char ]
    ( proj₁ (flat {r} u) ≡ w ) × ( proj₁ (flat {r} v) ≡ w )
  × ( r ⊢ u >ᵍ v ) × ( r ⊢ v >ᵖ u )
  × ( ( z : U r ) → proj₁ (flat {r} z) ≡ w → ( z ≡ u ) ⊎ ( z ≡ v ) )

-- Purpose: a tight divergent pair are each other's only competitors, so
--   they are the maxima of their fiber in the respective orders.
-- Used by: the decomposition reading; the robex example.
-- Proof idea: the comparison fields of the two ≥-max records are decided
--   by the tightness case analysis; u ≢ v by >ᵍ→¬≡.
RobustCrit→NonRobust : ∀ ( r : RE ) → RobustCrit r → NonRobust r
RobustCrit→NonRobust r (u , v , w , ( u≡w , ( v≡w , ( u>ᵍv , ( v>ᵖu , tight ) ) ) )) =
  u , v , w , ( ≥-maxᵍ w u u≡w (maxᵍ-cmp u>ᵍv)
              , ( ≥-maxᵖ w v v≡w (maxᵖ-cmp v>ᵖu) , >ᵍ→¬≡ u>ᵍv ) )
  where
    maxᵍ-cmp : r ⊢ u >ᵍ v
      → ( z : U r ) → proj₁ (flat {r} z) ≡ w → GreedyMax._⊢_≥_ r u z
    maxᵍ-cmp u>ᵍv z z≡w with tight z z≡w
    ...   | inj₁ z≡u = inj₂ (sym z≡u)
    ...   | inj₂ z≡v = inj₁ (subst ( λ x → r ⊢ u >ᵍ x ) (sym z≡v) u>ᵍv)

    maxᵖ-cmp : r ⊢ v >ᵖ u
      → ( z : U r ) → proj₁ (flat {r} z) ≡ w → ( r ⊢ v >ᵖ z ) ⊎ ( v ≡ z )
    maxᵖ-cmp v>ᵖu z z≡w with tight z z≡w
    ...   | inj₁ z≡u = inj₁ (subst ( λ x → r ⊢ v >ᵖ x ) (sym z≡u) v>ᵖu)
    ...   | inj₂ z≡v = inj₂ (sym z≡v)

-- Purpose: a concrete non-robust regex: a choice with unequal-length
--   alternatives under a concatenation whose right part splits both
--   prefix lengths consistently (the shifted-split shape).
-- Used by: robex-crit.
-- Proof idea: N/A (definition).
robex : RE
robex = ( (($ 'a' ` 1) + (($ 'a' ` 2) ● ($ 'a' ` 3) ` 10) ` 4)
        ● ((($ 'a' ` 5) ● ($ 'b' ` 6) ` 11) + ($ 'b' ` 7) ` 8) ` 9 )

robex-word : List Char
robex-word = 'a' ∷ 'a' ∷ 'b' ∷ []

-- reading "a" ++ "ab" = "aab"
robex-u : U robex
robex-u = PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b')))

-- reading "aa" ++ "b" = "aab"
robex-v : U robex
robex-v = PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b'))

-- Purpose: robex fires the certificate: the pair is divergent (greedy
--   choice-lr vs posix len-> on the shifted split) and the fiber of
--   "aab" is exactly the pair (the computed posix list has two members).
-- Used by: the decomposition prose.
-- Proof idea: word equations by computation; the order pair by the
--   respective constructors; tightness by case analysis on Any membership
--   in the computed list (evaluation produces exactly the two trees).
robex-crit : RobustCrit robex
robex-crit = robex-u , robex-v , robex-word ,
  ( refl , ( refl , ( GreedyOrder.sub
      (GreedyOrder.seq₁ (GreedyOrder.sub GreedyOrder.choice-lr))
    , ( PosixOrder.len-≡ refl (PosixOrder.seq₁
        (PosixOrder.len-> (Nat.s≤s (Nat.s≤s Nat.z≤n))))
      , tight-robex ) ) ) )
  where
    tight-robex : ( z : U robex )
      → proj₁ (flat {robex} z) ≡ robex-word
      → ( z ≡ robex-u ) ⊎ ( z ≡ robex-v )
    tight-robex z z≡w with ∈-parseAllᵖ z robex-word z≡w
    ...   | here refl         = inj₂ refl
    ...   | there (here refl) = inj₁ refl
    ...   | there (there ())
```

**What is not connected.** `RobustCrit` is decidable at a witness, but
it (and `headEq?` with its word search) is not yet the bounded static
`crit` analogue for robustness. The paper-style static shape would be a
subterm search (`cgp.ambig.AmbigCheck`'s `Ctx`/`plug`) for the
shifted-split pattern `((l + s ` loc₁) ● m)` — with an emptiness test
for the shifted overlap (∃ w₁ ∈ ⟦l⟧, w₂ ∈ ⟦r⟧, x, y ∈ ⟦m⟧ : w₁·x ≡ w₂·y
with |w₁| ≠ |w₂|) played over the pd-derivative lists, the same
machinery class as `pd-Idemp?` — plus a dominance side condition
(nothing outside the pattern outranks the pair). Soundness of such a
pattern reduces to the fact that context filling embeds both orders
(`CtxT` with `seq₁`/`seq₂`/`choice-ll`/`choice-rr` propagation, the
`A2→Ambig` machinery) and reflects maximality under unambiguous
siblings. The completeness direction — every `NonRobust` regex fires a
*bounded* pattern — would need the descent argument of
`cgp.ambig.Completeness`; it is open here, and the `sepx` regex of §5
shows the dominance condition is real proof content, not a technicality.

## 5. Investigation: can the static search be dominance-free?

The remaining open half is the bounded static search (position search +
shifted-overlap test + dominance). This section investigates how much
of it is forced by the shape of the two orders. Two findings:

**Finding 1 (the pattern shape is forced — pair generation is bounded).**
Comparing the two rule sets (`cgp.greedy.Order` / `cgp.posix.Order`):
for two trees of a *common word* the top levels are equivalent wrappers
(greedy `sub` versus posix `len-≡` at equal lengths — `len->` can never
fire inside one fiber), and the descent rules are *identical*:
`seq₁`/`seq₂` (lexicographic — the `seq₁` sibling is unconstrained),
`choice-ll`/`choice-rr`, and the three star rules. The only
difference is the guard at choice occurrences: greedy `choice-lr` is
unconditional (left always beats right), while posix `choice-lr`
requires |left reading| ≥ |right reading| and has `choice-rl` only for
a *strictly longer* right reading. Any derivation for a fixed tree pair
follows the structure of the pair (each shape admits one rule family),
and both orders follow it identically until the first choice occurrence
where the trees pick different branches. Hence: an `OrderDiverge` pair
can only exist with the shape — a shared spine down to a choice
occurrence `(l + s)` in `r`, one tree taking `LeftU` reading `a ∈ ⟦l⟧`,
the other `RightU` reading `c ∈ ⟦s⟧`, with `|c| > |a|`, and continuations
below making both trees read one word (`a·x ≡ c·y` — the shifted split;
`robex` above is the minimal instance). So a bounded subterm position
search is structurally complete for *generating divergent pairs*: no
unbounded pattern family is needed for that half. (This paragraph is a
reading of the two inductive definitions, not a formalized inversion
lemma.)

**Finding 2 (dominance is NOT eliminable — formal counterexample).**
The natural hope was that a fired pattern might already imply
`NonRobust` — i.e. `OrderDiverge r → NonRobust r`: if a pair `u >ᵍ v`,
`v >ᵖ u` exists, perhaps the two maxima could never coincide, because
transitivity would force the maxima to differ wherever the pair differs.
This is false. `sepx` below is the literal word `a ● a ● b` as a choice
*branch* next to the `robex` shape: at the word `aab` the two divergent
`robex` trees still exist, but the third tree (the literal branch)
beats *both* of them in *both* orders at the higher choice node
(`choice-lr` both sides, equal lengths), so both parsers agree there.
Formally: `OrderDiverge sepx` holds while `Robust sepx` holds (via
`¬ NonRobust sepx` and §1's `¬nonrobust→robust`). A static criterion
must therefore decide the *fiber* — the dominance/maximality side
condition cannot be dropped. (Nor can it be replaced by `RobustCrit`
tightness: adding a duplicate continuation branch inside `m`, e.g.
`(a + aa) ● ((ab + b) + (a ● b))`, makes the two maxima share a
3-tree fiber — the maxima are not tight — informally observed, not
formalized.)

```agda
-- Purpose: OrderDiverge but Robust: the literal word aab as a choice
--   branch beside the robex shape.
-- Used by: sepx-diverge, ¬NonRobust-sepx, robust-sepx.
-- Proof idea: N/A (definition).
sepx : RE
sepx = ( ( ($ 'a' ` 21) ● ( ($ 'a' ` 22) ● ($ 'b' ` 23) ` 24 ) ` 25 )
       + ( ( ($ 'a' ` 26) + ( ($ 'a' ` 27) ● ($ 'a' ` 28) ` 29 ) ` 30 )
         ● ( ( ($ 'a' ` 31) ● ($ 'b' ` 32) ` 33 ) + ( $ 'b' ` 34 ) ` 35 )
         ` 36 )
       ` 37 )

-- the unique tree of the literal branch, reading "aab"
sepx-m : U sepx
sepx-m = LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))

-- robex trees of "aab": (a · ab) and (aa · b)
sepx-t1 : U sepx
sepx-t1 = RightU (PairU (LeftU (LetterU 'a'))
                         (LeftU (PairU (LetterU 'a') (LetterU 'b'))))

sepx-t4 : U sepx
sepx-t4 = RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a')))
                        (RightU (LetterU 'b')))

-- the other two robex trees (singleton fibers: "ab" and "aaab")
sepx-t2 : U sepx
sepx-t2 = RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))

sepx-t3 : U sepx
sepx-t3 = RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a')))
                        (LeftU (PairU (LetterU 'a') (LetterU 'b'))))

-- Purpose: sepx fires the divergence pair (the robex pair, unchanged).
-- Used by: Finding 2.
-- Proof idea: choice-rr descends to the robex prefix sum; greedy
--   choice-lr there, posix len-> (2 > 1) — the robex argument.
sepx-diverge : OrderDiverge sepx
sepx-diverge = sepx-t1 , sepx-t4 , ( refl
  , ( GreedyOrder.sub (GreedyOrder.choice-rr
        (GreedyOrder.sub (GreedyOrder.seq₁
          (GreedyOrder.sub GreedyOrder.choice-lr))))
    , ( PosixOrder.len-≡ refl (PosixOrder.choice-rr
        (PosixOrder.len-≡ refl (PosixOrder.seq₁
          (PosixOrder.len-> (Nat.s≤s (Nat.s≤s Nat.z≤n))))))) ) )

-- Purpose: the literal branch beats the divergent trees in both orders
--   (their comparison ends at the top choice; the guards fail).
-- Used by: ¬NonRobust-sepx.
-- Proof idea: no rule derives RightU > LeftU in the greedy inner order;
--   posix choice-rl needs 3 > 3; len-> needs 3 > 3; equality is absurd.
-- 4 ≤ 3: the guard that both length guards above reduce to (all three
--   trees read "aab", so every strict-length guard here is 3 > 3).
-- Used by: not-t1≥ᵖm, not-t4≥ᵖm.
¬4≤3 : ¬ ( suc (suc (suc (suc zero))) Nat.≤ (suc (suc (suc zero))) )
¬4≤3 (Nat.s≤s (Nat.s≤s (Nat.s≤s ())))

not-t1≥ᵖm : ¬ ( PosixMax._⊢_≥_ sepx sepx-t1 sepx-m )
not-t1≥ᵖm (inj₁ (PosixOrder.len-> n)) = ¬4≤3 n
not-t1≥ᵖm (inj₁ (PosixOrder.len-≡ refl (PosixOrder.choice-rl q))) = ¬4≤3 q
not-t1≥ᵖm (inj₂ ())

not-t4≥ᵖm : ¬ ( PosixMax._⊢_≥_ sepx sepx-t4 sepx-m )
not-t4≥ᵖm (inj₁ (PosixOrder.len-> n)) = ¬4≤3 n
not-t4≥ᵖm (inj₁ (PosixOrder.len-≡ refl (PosixOrder.choice-rl q))) = ¬4≤3 q
not-t4≥ᵖm (inj₂ ())

not-t1≥ᵍm : ¬ ( GreedyMax._⊢_≥_ sepx sepx-t1 sepx-m )
not-t1≥ᵍm (inj₁ (GreedyOrder.sub ()))
not-t1≥ᵍm (inj₂ ())

not-t4≥ᵍm : ¬ ( GreedyMax._⊢_≥_ sepx sepx-t4 sepx-m )
not-t4≥ᵍm (inj₁ (GreedyOrder.sub ()))
not-t4≥ᵍm (inj₂ ())

-- Purpose: two trees with different words cannot both read the word w.
-- Used by: ¬NonRobust-sepx (the word-mismatch clauses).
-- Proof idea: transitivity gives word ≡ word, refuted term-level by
--   the concrete list disequality (absurd λ () — kernel evaluation).
wmismatch : { u v : U sepx } { w : List Char }
  → proj₁ (flat u) ≡ w → proj₁ (flat v) ≡ w
  → ¬ ( proj₁ (flat u) ≡ proj₁ (flat v) )
  → ⊥
wmismatch p q ¬eq = ¬eq (trans p (sym q))

-- Purpose: sepx is not NonRobust: every candidate pair of its nine
--   trees is killed — different fibers by word mismatch; the shared
--   fiber at "aab" has literal maximum sepx-m in both orders, and a
--   right-branch tree is never ≥ the literal tree (the guards fail).
-- Used by: robust-sepx.
-- Proof idea: case analysis on the two tree shapes (five forms each);
--   equal trees contradict u≢v; the (m, t1), (m, t4), (t1, ·), (t4, ·)
--   same-fiber cases apply a maximality field to sepx-m, contradicting
--   the guard lemmas; all other pairs read different words (wmismatch,
--   discharged by kernel evaluation of the two words).
¬NonRobust-sepx : ¬ NonRobust sepx
¬NonRobust-sepx (u , v , w , ( ≥-maxᵍ .w u u≡w cmpᵍ ,
  ( ≥-maxᵖ .w v v≡w cmᵖ , u≢v ) )) with u | v
... | LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))
    | LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))
    = u≢v refl
... | LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))
    | RightU (PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    = ⊥-elim (not-t1≥ᵖm (cmᵖ sepx-m u≡w))
... | LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))
    | RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))
    = ⊥-elim (wmismatch {u = sepx-m} {v = sepx-t2} u≡w v≡w λ ())
... | LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))
    | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    = ⊥-elim (wmismatch {u = sepx-m} {v = sepx-t3} u≡w v≡w λ ())
... | LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))
    | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b')))
    = ⊥-elim (not-t4≥ᵖm (cmᵖ sepx-m u≡w))
... | RightU (PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    | LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))
    = ⊥-elim (not-t1≥ᵍm (cmpᵍ sepx-m v≡w))
... | RightU (PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    | RightU (PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    = u≢v refl
... | RightU (PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    | RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))
    = ⊥-elim (wmismatch {u = sepx-t1} {v = sepx-t2} u≡w v≡w λ ())
... | RightU (PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    = ⊥-elim (wmismatch {u = sepx-t1} {v = sepx-t3} u≡w v≡w λ ())
... | RightU (PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b')))
    = ⊥-elim (not-t1≥ᵍm (cmpᵍ sepx-m v≡w))
... | RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))
    | LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))
    = ⊥-elim (wmismatch {u = sepx-t2} {v = sepx-m} u≡w v≡w λ ())
... | RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))
    | RightU (PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    = ⊥-elim (wmismatch {u = sepx-t2} {v = sepx-t1} u≡w v≡w λ ())
... | RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))
    | RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))
    = u≢v refl
... | RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))
    | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    = ⊥-elim (wmismatch {u = sepx-t2} {v = sepx-t3} u≡w v≡w λ ())
... | RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))
    | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b')))
    = ⊥-elim (wmismatch {u = sepx-t2} {v = sepx-t4} u≡w v≡w λ ())
... | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    | LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))
    = ⊥-elim (wmismatch {u = sepx-t3} {v = sepx-m} u≡w v≡w λ ())
... | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    | RightU (PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    = ⊥-elim (wmismatch {u = sepx-t3} {v = sepx-t1} u≡w v≡w λ ())
... | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    | RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))
    = ⊥-elim (wmismatch {u = sepx-t3} {v = sepx-t2} u≡w v≡w λ ())
... | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    = u≢v refl
... | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b')))
    = ⊥-elim (wmismatch {u = sepx-t3} {v = sepx-t4} u≡w v≡w λ ())
... | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b')))
    | LeftU (PairU (LetterU 'a') (PairU (LetterU 'a') (LetterU 'b')))
    = ⊥-elim (not-t4≥ᵍm (cmpᵍ sepx-m v≡w))
... | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b')))
    | RightU (PairU (LeftU (LetterU 'a')) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    = ⊥-elim (not-t4≥ᵍm (cmpᵍ sepx-m v≡w))
... | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b')))
    | RightU (PairU (LeftU (LetterU 'a')) (RightU (LetterU 'b')))
    = ⊥-elim (wmismatch {u = sepx-t4} {v = sepx-t2} u≡w v≡w λ ())
... | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b')))
    | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (LeftU (PairU (LetterU 'a') (LetterU 'b'))))
    = ⊥-elim (wmismatch {u = sepx-t4} {v = sepx-t3} u≡w v≡w λ ())
... | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b')))
    | RightU (PairU (RightU (PairU (LetterU 'a') (LetterU 'a'))) (RightU (LetterU 'b')))
    = u≢v refl

-- Purpose: sepx IS robust — the fired divergence pair decides nothing.
-- Used by: Finding 2 (OrderDiverge ↛ NonRobust).
-- Proof idea: ¬ NonRobust-sepx through §1's completeness half.
robust-sepx : Robust sepx
robust-sepx = ¬nonrobust→robust sepx ¬NonRobust-sepx

-- Purpose: concrete witness of the agreement at the shared fiber.
-- Used by: Finding 2.
-- Proof idea: kernel computation of both parseAll lists (heads equal).
sepx-heads-agree : headEq? sepx ( 'a' ∷ 'a' ∷ 'b' ∷ [] ) ≡ true
sepx-heads-agree = refl
```

Consequences for the criteria design:

- `NonRobust ↔ OrderDiverge ↔ ∃ position (shifted overlap witnessed)`
  are *not* equivalent: `NonRobust → OrderDiverge` holds (§2) but the
  converse fails at `sepx`; and every divergent pair has the
  shifted-split shape, so `OrderDiverge` is exactly what a bounded
  position search can certify.
- The open half is now precisely: find a *decidable dominance*
  condition — static (no word quantifier) per fired position — such
  that fired + dominant ⇒ the pair are the two fiber maxima. At a
  fixed word, maximality is checkable by `headEq?`/list membership
  (§3, §4 tightness); making it word-free is the remaining gap, and
  the `sepx` shape shows any such condition must rule out a
  higher choice node whose reading outranks both pattern trees — a
  question about the *complement* of the pattern (all other readings
  of the context), which is exactly where the pd-list machinery of
  `AmbigCheck` §13 would have to be extended.
