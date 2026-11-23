# StarBound: the star layer of the bounded-witness problem

Half of the open item left by `cgp.robust.greedyposix.IsoCheck` §5:
the bounded-witness lemma for `ShortPair` AT A TOP-LEVEL STAR is proved
here. For `r = m * nε ` loc` every `ShortPair r` either

* descends to a `ShortPair m` in the body (the `|w₁| < |w₂|` case of a
  `star-head` derivation), or
* has a NORMALIZED witness `(ListU [ w₁ ] , ListU (w₂ ∷ t))` whose
  derivation is one `star-head` step, with the right tail bounded:
  `length t ≤ |w₁| ∸ |w₂| + 1` (the prefix `t` exists because `ε∉ m`
  makes every body tree contribute length ≥ 1).

`star-tail` steps (equal heads) are collapsed by structural recursion
on the left forest. The example regex `mb2 = (b●b) + b` shows the star
layer genuinely firing (its body has NO `ShortPair`) and that a per-list
bound of 1 is impossible — the `∸`-bound here is attained by the
construction.

What is NOT proved here: the `LongPair` dual at stars (the negated side
needs case analysis over ABSENT derivations); and the recursion over
regex structure that turns the tree-length bound into a bound computable
from the regex alone (the Presburger half of §5). The star-free decision
procedure is `cgp.robust.greedyposix.StarFreeDecide`. The `flat`
transport lemmas mirror `cgp.robust.greedylne.GreedyLNEUtils` and are
re-proved here so this module stays postulate-free.

```agda
{-# OPTIONS --rewriting #-}
module cgp.robust.greedyposix.StarBound where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉; ε∉$; ε∉fst; ε∉snd; ε∉_+_)

import cgp.ParseTree as ParseTree
open ParseTree using (U; EmptyU; LetterU; LeftU; RightU; PairU; ListU; flat)

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming (_⊢_>_ to _⊢_>ᵍ_)

import cgp.robust.greedyposix.IsoCheck as IsoCheck
open IsoCheck using (ShortPair; tri; no-ᵍ-rl)

import Data.Bool as Bool
open Bool using (Bool; true; false)

import Data.Char as Char
open Char using (Char)

import Data.List as List
open List using (List; _∷_; []; length)

import Data.List.Properties as ListProperties
open ListProperties using (length-++)

import Data.Nat as Nat
open Nat using (ℕ; _≤_; _<_; _+_; _∸_; suc; zero; z≤n; s≤s)

import Data.Nat.Properties as NatProperties
open NatProperties
  using ( ≤-refl; ≤-trans; ∸-monoˡ-≤
        ; +-cancelˡ-< ; +-monoʳ-≤ ; +-suc ; +-comm ; +-identityʳ
        ; m≤m+n ; m≤n+m ; m≤n⇒m≤o+n ; m≤n⇒m≤n+o ; m≤n+m∸n ; m∸n≤m
        ; m≤n⇒m∸n≡0 ; m∸n+n≡m ; m+n∸m≡n ; <⇒≤ )

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Data.Product as Product
open Product using (Σ; _×_; _,_; proj₁; proj₂; Σ-syntax)

import Relation.Nullary as Nullary
open Nullary using (¬_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; cong₂; subst; subst₂)

import Data.Empty as Empty
open Empty using (⊥; ⊥-elim)
```

## 1. Forest lengths in ℕ and `flat` transport

```agda
-- Purpose: total word length of a forest of body trees (a star list).
-- Used by: len-ListU, diff-≥, short-★-normalize.
-- Proof idea: N/A (definition).
wlen : ∀ { m : RE } → List (U m) → ℕ
wlen []       = 0
wlen (x ∷ xs) = length (proj₁ (flat x)) + wlen xs

-- Purpose: flattening a star tree is exactly wlen of its forest.
-- Used by: short-★-normalize (all length arithmetic then happens in ℕ).
-- Proof idea: induction on the forest; with-flat over the head makes the
--   head occurrences in the goal literal (the repo's standard workaround
--   for the inversion wall over neutral proj₁ ∘ flat).
len-ListU : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } (ws : List (U m))
  → length (proj₁ (flat (ListU {m} {nε} {loc} ws))) ≡ wlen ws
len-ListU {m} {nε} {loc} [] = refl
len-ListU {m} {nε} {loc} (x ∷ xs) with flat x
... | w₁ , _ = trans (length-++ w₁) (cong₂ _+_ refl (len-ListU xs))

-- Purpose: flattening commutes with the choice/concat injections
--   (length-preserving forms). Mirrors GreedyLNEUtils (re-proved here
--   to keep this module postulate-free).
-- Used by: len≥1.
-- Proof idea: with-flat makes both sides literal.
flat-LeftU-len : ∀ { l s : RE } { loc : ℕ } { u : U l }
  → length (proj₁ (flat (LeftU {l} {s} {loc} u))) ≡ length (proj₁ (flat u))
flat-LeftU-len {l} {s} {loc} {u} with flat {l} u
... | xs , _ = refl

flat-RightU-len : ∀ { l s : RE } { loc : ℕ } { u : U s }
  → length (proj₁ (flat (RightU {l} {s} {loc} u))) ≡ length (proj₁ (flat u))
flat-RightU-len {l} {s} {loc} {u} with flat {s} u
... | xs , _ = refl

flat-PairU-len : ∀ { l s : RE } { loc : ℕ } { u : U l } { v : U s }
  → length (proj₁ (flat (PairU {l} {s} {loc} u v)))
    ≡ length (proj₁ (flat u)) + length (proj₁ (flat v))
flat-PairU-len {l} {s} {loc} {u} {v} with flat {l} u | flat {s} v
... | xs₁ , _ | xs₂ , _ = length-++ {A = Char} xs₁ {xs₂}

-- Purpose: ε∉ bounds every body tree to be NONEMPTY: length ≥ 1.
-- Used by: pref-req (the element bound of the prefix needs ≥ 1 per tree).
-- Proof idea: induction on the tree; the ε and star positions are
--   ε∉-absurd (ε∉ has no constructor there); + re-embeds through the
--   transport lemmas; ● uses one ε∉ side plus monotone sums.
len≥1 : ∀ { r : RE } → (nε : ε∉ r) → (u : U r)
  → suc zero Nat.≤ length (proj₁ (flat u))
len≥1 () EmptyU
len≥1 nε (LetterU c) = s≤s z≤n
len≥1 (ε∉_+_ {l} {s} {loc} nεl nεs) (LeftU {l} {s} {loc} u)
  = subst (suc zero Nat.≤_) (sym (flat-LeftU-len {l} {s} {loc} {u}))
      (len≥1 nεl u)
len≥1 (ε∉_+_ {l} {s} {loc} nεl nεs) (RightU {l} {s} {loc} u)
  = subst (suc zero Nat.≤_) (sym (flat-RightU-len {l} {s} {loc} {u}))
      (len≥1 nεs u)
len≥1 (ε∉fst {l} {s} {loc} nεl) (PairU {l} {s} {loc} u v)
  = subst (suc zero Nat.≤_) (sym (flat-PairU-len {l} {s} {loc} {u} {v}))
      (≤-trans (len≥1 nεl u) (m≤n⇒m≤n+o (length (proj₁ (flat v))) ≤-refl))
len≥1 (ε∉snd {l} {s} {loc} nεs) (PairU {l} {s} {loc} u v)
  = subst (suc zero Nat.≤_) (sym (flat-PairU-len {l} {s} {loc} {u} {v}))
      (≤-trans (len≥1 nεs v) (m≤n⇒m≤o+n (length (proj₁ (flat u))) ≤-refl))
len≥1 () (ListU us)

-- ¬ (a < 0).
¬<-0 : ∀ {a : ℕ} → ¬ (a Nat.< zero)
¬<-0 ()
```

## 2. Prefix selection

```agda
-- helper of pref-req: a nonempty subtrahend drops the deficit:
-- (suc n ∸ l) ≤ n whenever l ≥ 1.
∸bound : (n : ℕ) {l : ℕ} → suc zero Nat.≤ l → suc n Nat.∸ l Nat.≤ n
∸bound n {zero} ()
∸bound n {suc l} _ = m∸n≤m n l

-- Purpose: if a forest's total length reaches `need`, then at most
--   `need` trees of it (a prefix) already reach `need`.
-- Used by: short-★-normalize (the star-head shortening).
-- Proof idea: recursion on the forest; when the tail alone suffices
--   (trichotomy) recurse into the tail, else consume the head and
--   recurse on the deficit (need ∸ |x|) — legal since every |x| ≥ 1
--   (len≥1), which keeps the element count ≤ need (∸bound).
pref-req : ∀ { m : RE } { nε : ε∉ m }
  → (need : ℕ) → (ws : List (U m))
  → need Nat.≤ wlen ws
  → Σ[ t ∈ List (U m) ] (need Nat.≤ wlen t × length t Nat.≤ need)
pref-req zero ws p = [] , (z≤n , z≤n)
pref-req (suc need) [] ()
pref-req {m} {nε} (suc need) (x ∷ xs) p with tri (wlen xs) (suc need)
... | inj₁ _
  = let lx = length (proj₁ (flat {m} x))
        t , (wt , lt)
          = pref-req {m} {nε} (suc need Nat.∸ lx) xs
              (subst ((suc need Nat.∸ lx) Nat.≤_)
                      (m+n∸m≡n lx (wlen xs))
                      (∸-monoˡ-≤ lx p))
    in (x ∷ t)
     , ( ≤-trans (m≤n+m∸n (suc need) (length (proj₁ (flat {m} x))))
                 (+-monoʳ-≤ (length (proj₁ (flat {m} x))) wt)
       , ≤-trans (s≤s lt) (s≤s (∸bound need (len≥1 {m} nε x))) )
... | inj₂ (inj₁ eq)
  = pref-req {m} {nε} (suc need) xs (subst (suc need Nat.≤_) (sym eq) ≤-refl)
... | inj₂ (inj₂ h)
  = pref-req {m} {nε} (suc need) xs (<⇒≤ h)
```

## 3. Star-level inversion and length transport

```agda
-- Purpose: the two ways a cons/cons star pair can be greedy-related:
--   star-head, or star-tail with equal heads. star-cons-nil concludes
--   an empty RIGHT forest, never a cons one (rigid index clash).
-- Used by: short-★-normalize, §5 example.
-- Proof idea: invert sub + the inner star rules; every other inner rule
--   has a non-star regex index and cannot match.
inv-★-der : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { w₁ w₂ : U m } { ws₁ ws₂ : List (U m) }
  → ( ( m * nε ` loc ) ⊢ ListU {m} {nε} {loc} (w₁ ∷ ws₁)
      >ᵍ ListU {m} {nε} {loc} (w₂ ∷ ws₂) )
  → ( ( m ⊢ w₁ >ᵍ w₂ )
    ⊎ ( ( w₁ ≡ w₂ )
      × ( ( m * nε ` loc ) ⊢ ListU {m} {nε} {loc} ws₁
          >ᵍ ListU {m} {nε} {loc} ws₂ ) ) )
inv-★-der (GreedyOrder.sub (GreedyOrder.star-head {m} {loc} {nε} {w₁} {w₂} {ws₁} {ws₂} d₀))
  = inj₁ d₀
inv-★-der (GreedyOrder.sub (GreedyOrder.star-tail {m} {loc} {nε} {w₁} {w₂} {ws₁} {ws₂} e d₂))
  = inj₂ (e , d₂)

-- Purpose: no greedy derivation has an EMPTY left forest at a star.
-- Used by: short-★-normalize, §5 example.
-- Proof idea: every star rule concludes a cons left forest; after
--   forced case splits no constructor is left.
no-ᵍ-nilL : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { vs : List (U m) }
  → ¬ ( ( m * nε ` loc ) ⊢ ListU {m} {nε} {loc} []
        >ᵍ ListU {m} {nε} {loc} vs )
no-ᵍ-nilL (GreedyOrder.sub ())

-- Purpose: cancel equal heads from a raw length inequality.
-- Used by: short-★-normalize (the star-tail recursion).
-- Proof idea: len-ListU turns raw lengths into wlen, the (equal) head
--   lengths cancel, turn back.
tail-< : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { w₁ w₂ : U m } { ws₁ ws₂ : List (U m) }
  → w₁ ≡ w₂
  → length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ ws₁))))
    Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ ws₂))))
  → length (proj₁ (flat (ListU {m} {nε} {loc} ws₁)))
    Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} ws₂)))
tail-< {m} {nε} {loc} {w₁} {w₂} {ws₁} {ws₂} e h
  = subst₂ _<_ (sym (len-ListU ws₁)) (sym (len-ListU ws₂))
    (+-cancelˡ-< (length (proj₁ (flat {m} w₁))) (wlen ws₁) (wlen ws₂)
      (subst (λ z → length (proj₁ (flat {m} w₁)) + wlen ws₁ Nat.< z + wlen ws₂)
              (cong (λ t → length (proj₁ (flat {m} t))) (sym e))
              (subst₂ _<_ (len-ListU (w₁ ∷ ws₁)) (len-ListU (w₂ ∷ ws₂)) h)))

-- Purpose: raw ℕ fact behind the shortening: b < a together with
--   a + s1 < b + s2 forces s2 ≥ (a ∸ b) + 1.
-- Used by: short-★-normalize (the star-head shortening premise).
-- Proof idea: induction on the numerals a, b (every ∸ / + step then
--   computes); the base b = 0 uses monotonicity of +.
diff-≥ : (a b : ℕ) → b Nat.< a → (s1 s2 : ℕ)
  → suc (a Nat.+ s1) Nat.≤ b Nat.+ s2 → suc (a Nat.∸ b) Nat.≤ s2
diff-≥ zero b () s1 s2 hc
diff-≥ (suc a) zero lt s1 s2 hc
  = ≤-trans (s≤s (s≤s (m≤m+n a s1))) hc
diff-≥ (suc a) (suc b) (s≤s lt) s1 s2 (s≤s hc) = diff-≥ a b lt s1 s2 hc
```

## 4. The normal form and the reduction theorem

```agda
-- Purpose: the normal form: a star ShortPair witness made of ONE tree
--   on the left and a BOUNDED forest on the right, derived by a single
--   star-head step (which never inspects the tails).
-- Used by: short-★-normalize.
-- Proof idea: N/A (record type).
NormShort : (m : RE) → (nε : ε∉ m) → (loc : ℕ) → Set
NormShort m nε loc = Σ ( U m ) λ w₁ → Σ ( U m ) λ w₂ →
  Σ[ t ∈ List (U m) ]
    ( ( m ⊢ w₁ >ᵍ w₂ )
    × ( ( m * nε ` loc ) ⊢ ListU {m} {nε} {loc} (w₁ ∷ [])
        >ᵍ ListU {m} {nε} {loc} (w₂ ∷ t) )
    × ( length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ []))))
        Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ t)))) )
    × ( length t Nat.≤ suc (length (proj₁ (flat {m} w₁))
                                Nat.∸ length (proj₁ (flat {m} w₂))) ) )

-- Purpose: assemble a NormShort from body data: given a tail forest t
--   carrying enough total length (≥ |w₁| ∸ |w₂| + 1), the length
--   inequality follows by the ∸-calculus; the derivation is star-head.
-- Used by: short-★-normalize.
-- Proof idea: |w₂| + wlen t ≥ |w₂| + (|w₁| ∸ |w₂|) + 1 = |w₁| + 1.
mk-norm : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { w₁ w₂ : U m }
  → ( d₀ : m ⊢ w₁ >ᵍ w₂ )
  → ( lte : length (proj₁ (flat {m} w₂)) Nat.≤ length (proj₁ (flat {m} w₁)) )
  → ( t : List (U m) )
  → ( wt : suc (length (proj₁ (flat {m} w₁)) Nat.∸ length (proj₁ (flat {m} w₂)))
             Nat.≤ wlen t )
  → ( lt : length t
           Nat.≤ suc (length (proj₁ (flat {m} w₁)) Nat.∸ length (proj₁ (flat {m} w₂))) )
  → NormShort m nε loc
mk-norm {m} {nε} {loc} {w₁} {w₂} d₀ lte t wt lt =
  w₁ , w₂ , t , ( d₀
  , ( GreedyOrder.sub (GreedyOrder.star-head {m} {loc} {nε} {w₁} {w₂} {[]} {t} d₀)
  , ( hlen , lt ) ) )
  where
  lx₁ = length (proj₁ (flat {m} w₁))
  lx₂ = length (proj₁ (flat {m} w₂))

  eq₁ : length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ [])))) ≡ lx₁
  eq₁ = trans (len-ListU {m} {nε} {loc} (w₁ ∷ [])) (+-identityʳ lx₁)

  eq₂ : length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ t)))) ≡ (lx₂ + wlen t)
  eq₂ = len-ListU {m} {nε} {loc} (w₂ ∷ t)

  -- lx₂ + suc (lx₁ ∸ lx₂) ≡ suc lx₁  (lte makes ∸ exact)
  suc-lex : lx₂ Nat.+ suc (lx₁ Nat.∸ lx₂) ≡ suc lx₁
  suc-lex = trans (+-suc lx₂ (lx₁ Nat.∸ lx₂))
              (cong suc (trans (+-comm lx₂ (lx₁ Nat.∸ lx₂)) (m∸n+n≡m lte)))

  suc-lx₁≤ : suc lx₁ Nat.≤ lx₂ + suc (lx₁ Nat.∸ lx₂)
  suc-lx₁≤ = subst (suc lx₁ Nat.≤_) (sym suc-lex) ≤-refl

  hlen : length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ []))))
         Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ t))))
  hlen = subst₂ _<_ (sym eq₁) (sym eq₂)
    (≤-trans suc-lx₁≤ (+-monoʳ-≤ lx₂ wt))

-- Purpose: the star-head half of norm: decide whether the head pair
--   (w₁, w₂) itself is short (body branch) or the pair shortens to the
--   bounded normal form (star-head never inspects the tails).
-- Used by: norm.
-- Proof idea: trichotomy on the head lengths; see the clause comments.
head-case : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { w₁ w₂ : U m } { ws₁ ws₂ : List (U m) }
  → ( d₀ : m ⊢ w₁ >ᵍ w₂ )
  → ( h : length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ ws₁))))
          Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ ws₂)))) )
  → ShortPair m ⊎ NormShort m nε loc
head-case {m} {nε} {loc} {w₁} {w₂} {ws₁} {ws₂} d₀ h
  with tri (length (proj₁ (flat {m} w₁))) (length (proj₁ (flat {m} w₂)))
... | inj₁ lt
    -- star-head with a SHORTER head: the body already witnesses it.
    = inj₁ (w₁ , w₂ , d₀ , lt)
... | inj₂ (inj₁ eq)
    -- equal head lengths: the deficit lx₁ ∸ lx₂ is 0; any nonempty
    -- right forest works, and the raw inequality supplies one.
    = let lx₁ = length (proj₁ (flat {m} w₁))
          lx₂ = length (proj₁ (flat {m} w₂))
          p′ = subst (λ z → suc z Nat.≤ wlen ws₂)
                 (sym (m≤n⇒m∸n≡0 (subst (lx₁ Nat.≤_) eq ≤-refl)))
                 (≤-trans (s≤s z≤n)
                   (+-cancelˡ-< lx₁ (wlen ws₁) (wlen ws₂)
                     (subst (λ z → lx₁ Nat.+ wlen ws₁ Nat.< z Nat.+ wlen ws₂)
                       (sym eq)
                       (subst₂ _<_ (len-ListU (w₁ ∷ ws₁))
                                   (len-ListU (w₂ ∷ ws₂)) h))))
          t , (wt , lt) = pref-req {m} {nε} (suc (lx₁ Nat.∸ lx₂)) ws₂ p′
      in inj₂ (mk-norm {m} {nε} {loc} {w₁} {w₂} d₀
           (subst (λ z → lx₂ Nat.≤ z) (sym eq) ≤-refl) t wt lt)
... | inj₂ (inj₂ lt₂)
    -- star-head with |w₁| > |w₂|: diff-≥ says the right forest ws₂
    -- has length ≥ (|w₁| ∸ |w₂|) + 1; pref-req extracts the bounded
    -- prefix t.
    = let lx₁ = length (proj₁ (flat {m} w₁))
          lx₂ = length (proj₁ (flat {m} w₂))
          p′ = diff-≥ lx₁ lx₂ lt₂ (wlen ws₁) (wlen ws₂)
                 (subst₂ _<_ (len-ListU (w₁ ∷ ws₁)) (len-ListU (w₂ ∷ ws₂)) h)
          t , (wt , lt) = pref-req {m} {nε} (suc (lx₁ Nat.∸ lx₂)) ws₂ p′
      in inj₂ (mk-norm {m} {nε} {loc} {w₁} {w₂} d₀ (<⇒≤ lt₂) t wt lt)

-- Purpose: the case analysis for a cons/cons star pair (the recursive
--   core of short-★-normalize; separate top-level clauses because
--   multi-clause lambda cases mis-solve indexed rule implicits).
-- Used by: short-★-normalize.
-- Proof idea: see the clause comments.
norm : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ }
  → (us vs : List (U m))
  → ( ( m * nε ` loc ) ⊢ ListU {m} {nε} {loc} us
      >ᵍ ListU {m} {nε} {loc} vs )
  → length (proj₁ (flat (ListU {m} {nε} {loc} us)))
    Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} vs)))
  → ShortPair m ⊎ NormShort m nε loc
norm [] vs dᵍ h = ⊥-elim (no-ᵍ-nilL dᵍ)                    -- rule-absurd
norm (w₁ ∷ ws₁) [] dᵍ h = ⊥-elim (¬<-0 h)                  -- length-absurd
norm {m} {nε} {loc} (w₁ ∷ ws₁) (w₂ ∷ ws₂) dᵍ h
  with inv-★-der {m} {nε} {loc} {w₁} {w₂} {ws₁} {ws₂} dᵍ
... | inj₁ d₀ = head-case {m} {nε} {loc} {w₁} {w₂} {ws₁} {ws₂} d₀ h
... | inj₂ (e , d₂)
    -- star-tail: equal heads cancel; recurse into the tails.
    = norm ws₁ ws₂ d₂ (tail-< {m} {nε} {loc} {w₁} {w₂} {ws₁} {ws₂} e h)

norm-heads : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ }
  → (u : U ( m * nε ` loc )) → (v : U ( m * nε ` loc ))
  → ( ( m * nε ` loc ) ⊢ u >ᵍ v )
  → length (proj₁ (flat u)) Nat.< length (proj₁ (flat v))
  → ShortPair m ⊎ NormShort m nε loc
norm-heads {m} {nε} {loc} (ListU us) (ListU vs) dᵍ h = norm {m} {nε} {loc} us vs dᵍ h

-- Purpose: the star layer of the bounded-witness problem for ShortPair:
--   every ShortPair at a top-level star either descends to the body,
--   or is realized in the bounded normal form NormShort.
-- Used by: the bounded-witness open item of IsoCheck §5; §5 example.
-- Proof idea: structural recursion on the left forest (norm).
short-★-normalize : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ }
  → ShortPair ( m * nε ` loc )
  → ShortPair m ⊎ NormShort m nε loc
short-★-normalize (u , v , dᵍ , h) = norm-heads u v dᵍ h
```

## 5. The example: `mb2 = (b●b) + b`

```agda
b2b : RE
b2b = ( $ 'b' ` 91 ) ● ( $ 'b' ` 92 ) ` 93

mb2 : RE
mb2 = b2b + ( $ 'b' ` 94 ) ` 95

nε-mb2 : ε∉ mb2
nε-mb2 = ε∉_+_ (ε∉fst ε∉$) ε∉$

star-★-mb2 : RE
star-★-mb2 = mb2 * nε-mb2 ` 96

-- the two body trees (U mb2 has exactly these two shapes).
L-★ : U mb2
L-★ = LeftU {b2b} { $ 'b' ` 94 } { 95 }
        (PairU { $ 'b' ` 91 } { $ 'b' ` 92 } { 93 } (LetterU 'b') (LetterU 'b'))

R-★ : U mb2
R-★ = RightU {b2b} { $ 'b' ` 94 } { 95 } (LetterU 'b')

-- (L, R) IS greedy-related (choice-lr), but never short.
d₀-★ : mb2 ⊢ L-★ >ᵍ R-★
d₀-★ = GreedyOrder.sub
         (GreedyOrder.choice-lr {b2b} { $ 'b' ` 94 } { 95 }
            {PairU { $ 'b' ` 91 } { $ 'b' ` 92 } { 93 } (LetterU 'b') (LetterU 'b')}
            {LetterU 'b'})

-- rigid-length facts (numerals compute; absurd by construction)
¬2<2 : ¬ (suc (suc zero) Nat.< suc (suc zero))
¬2<2 (s≤s (s≤s ()))
¬2<1 : ¬ (suc (suc zero) Nat.< suc zero)
¬2<1 (s≤s ())
¬1<1 : ¬ (suc zero Nat.< suc zero)
¬1<1 (s≤s ())

-- ¬ ShortPair mb2: the BODY is clean (4 rigid cases; all lengths and
-- rule sets are forced by the indices).
no-sp-mb2 : ¬ ShortPair mb2
no-sp-mb2 (u , v , dᵍ , h) = go u v dᵍ h
  where
  go : (u v : U mb2) → ( mb2 ⊢ u >ᵍ v )
    → length (proj₁ (flat u)) Nat.< length (proj₁ (flat v)) → ⊥
  go (LeftU (PairU (LetterU 'b') (LetterU 'b')))
     (LeftU (PairU (LetterU 'b') (LetterU 'b'))) dᵍ h = ⊥-elim (¬2<2 h)
  go (LeftU (PairU (LetterU 'b') (LetterU 'b')))
     (RightU (LetterU 'b')) dᵍ h = ⊥-elim (¬2<1 h)
  go (RightU (LetterU 'b'))
     (LeftU (PairU (LetterU 'b') (LetterU 'b'))) dᵍ h = ⊥-elim (no-ᵍ-rl dᵍ)
  go (RightU (LetterU 'b'))
     (RightU (LetterU 'b')) dᵍ h = ⊥-elim (¬1<1 h)

-- A real star-layer ShortPair: forests of lengths (1, 3), via star-head
-- on the (non-short!) body pair (|L-★| = 2 < 1+1+1 = the forest of three R-★).
sp-★-raw : ShortPair star-★-mb2
sp-★-raw = ListU {mb2} {nε-mb2} {96} (L-★ ∷ [])
         , ListU {mb2} {nε-mb2} {96} (R-★ ∷ R-★ ∷ R-★ ∷ [])
         , ( GreedyOrder.sub
               (GreedyOrder.star-head {mb2} {96} {nε-mb2} {L-★} {R-★}
                  {[]} {R-★ ∷ R-★ ∷ []} d₀-★)
           , s≤s (s≤s (s≤s z≤n)) )   -- 2 < 3, by computation

-- The reduction theorem on this input computes to the bounded right
-- branch (the body branch is impossible by no-sp-mb2): the refl below
-- forces the whole construction to evaluate.
which-⊎ : {A B : Set} → A ⊎ B → Bool
which-⊎ (inj₁ _) = false
which-⊎ (inj₂ _) = true

norm-★-mb2-right : which-⊎ (short-★-normalize sp-★-raw) ≡ true
norm-★-mb2-right = refl

-- The bound 1 is IMPOSSIBLE at this star: no witness with both forests
-- of length ≤ 1 (all cases rigid).
no-sp-★-1 : (us vs : List (U mb2))
  → length us Nat.≤ 1 → length vs Nat.≤ 1
  → ( star-★-mb2 ⊢ ListU {mb2} {nε-mb2} {96} us
      >ᵍ ListU {mb2} {nε-mb2} {96} vs )
  → length (proj₁ (flat (ListU {mb2} {nε-mb2} {96} us)))
    Nat.< length (proj₁ (flat (ListU {mb2} {nε-mb2} {96} vs)))
  → ⊥
no-sp-★-1 [] vs _ _ dᵍ h = ⊥-elim (no-ᵍ-nilL dᵍ)
no-sp-★-1 (x ∷ y ∷ ys) vs (s≤s ()) _ dᵍ h
no-sp-★-1 (x ∷ []) (y ∷ y₂ ∷ ys) _ (s≤s ()) dᵍ h
no-sp-★-1 (LeftU (PairU (LetterU 'b') (LetterU 'b')) ∷ [])
         (LeftU (PairU (LetterU 'b') (LetterU 'b')) ∷ []) _ _ dᵍ h
  = ⊥-elim (¬2<2 h)
no-sp-★-1 (RightU (LetterU 'b') ∷ []) (RightU (LetterU 'b') ∷ []) _ _ dᵍ h
  = ⊥-elim (¬1<1 h)
no-sp-★-1 (LeftU (PairU (LetterU 'b') (LetterU 'b')) ∷ [])
         (RightU (LetterU 'b') ∷ []) _ _ dᵍ h
  = ⊥-elim (¬2<1 h)
no-sp-★-1 (RightU (LetterU 'b') ∷ [])
         (LeftU (PairU (LetterU 'b') (LetterU 'b')) ∷ []) _ _ dᵍ h
  with inv-★-der dᵍ
... | inj₁ d₀ = ⊥-elim (no-ᵍ-rl d₀)
... | inj₂ (() , _)   -- RightU ≡ LeftU is constructor-absurd

```

## 6. Status of the bounded-witness problem

Proved here (star layer, ShortPair half): every `ShortPair (m * nε ` loc)`
yields a witness with FOREST LENGTHS BOUNDED — either a `ShortPair m` in
the body, or a `star-head` pair whose forests have lengths `1` and
`≤ |w₁| ∸ |w₂| + 2`. `mb2` shows the body branch can be empty and that
no per-list bound of 1 suffices (its normalized shape is forced up to the
∸-bound).

Still open:
1. the `LongPair` dual at a star (case analysis over absent derivations);
2. feeding this reduction into a recursion over the regex: the bound here
   is in terms of the FOUND trees `w₁, w₂`; a bound computable from the
   regex alone needs their lengths bounded by the same theorem applied to
   the body — the induction over regex structure formalized by §5's
   "Presburger-style emptiness" step.
