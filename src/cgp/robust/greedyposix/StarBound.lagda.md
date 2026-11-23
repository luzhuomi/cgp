# StarBound: the star layer of the bounded-witness problem

The star layer of the open item left by `cgp.robust.greedyposix.IsoCheck`
§5: the bounded-witness lemmas for `ShortPair` AND `LongPair` AT A
TOP-LEVEL STAR, plus bounds computable from the regex. For
`r = m * nε ` loc` every `ShortPair r` either

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

The `LongPair` dual is proved here too (§7): at a star its witness is
ALWAYS realized at the star itself — `star-tail` needs equal heads AS
TREES, so a tree-equality decision (§6) replaces the length trichotomy
as the head split, and absent derivations are handled by inverting what
`star-head`/`star-tail`/`star-cons-nil` could conclude. §8 adds
`MaxLen` EVIDENCE (a regex-computable bound, `∞` at stars as in
IsoCheck §5) and upgrades both normal forms to bounds computable from
the regex alone.

Still open: the composition of these layers through `●`/`+` (the
"descend" lemmas: a pair of compound trees whose difference lives in a
sub-derivation), and the per-subterm semilinear difference sets
(IsoCheck §5 item 3). The star-free decision procedure is
`cgp.robust.greedyposix.StarFreeDecide`. The `flat` transport lemmas
mirror `cgp.robust.greedylne.GreedyLNEUtils` and are re-proved here so
this module stays postulate-free.

```agda
{-# OPTIONS --rewriting #-}
module cgp.robust.greedyposix.StarBound where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉; ε∉$; ε∉fst; ε∉snd; ε∉_+_)

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU; LetterU; LeftU; RightU; PairU; ListU; flat
                     ; inv-leftU; inv-rightU; inv-pairU; inv-listU1
                     ; RightU≢LeftU)

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming (_⊢_>_ to _⊢_>ᵍ_)

import cgp.robust.greedyposix.IsoCheck as IsoCheck
open IsoCheck using (ShortPair; LongPair; tri; no-ᵍ-rl)

import Data.Bool as Bool
open Bool using (Bool; true; false)

import Data.Char as Char
open Char using (Char)

import Data.List as List
open List using (List; _∷_; []; length)

import Data.List.Properties as ListProperties
open ListProperties using (length-++)

import Data.Nat as Nat
open Nat using (ℕ; _≤_; _<_; _+_; _∸_; _⊔_; suc; zero; z≤n; s≤s)

import Data.Nat.Properties as NatProperties
open NatProperties
  using ( ≤-refl; ≤-trans; ∸-monoˡ-≤ ; ∸-mono ; m+[n∸m]≡n
        ; +-cancelˡ-< ; +-monoʳ-≤ ; +-mono-≤ ; +-suc ; +-comm ; +-identityʳ
        ; m≤m+n ; m≤n+m ; m≤n⇒m≤o+n ; m≤n⇒m≤n+o ; m≤n+m∸n ; m∸n≤m
        ; m≤n⇒m∸n≡0 ; m∸n+n≡m ; m+n∸m≡n ; <⇒≤ ; m≤m⊔n ; m≤n⊔m )

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Data.Product as Product
open Product using (Σ; _×_; _,_; proj₁; proj₂; Σ-syntax)

import Relation.Nullary as Nullary
open Nullary using (¬_; Dec; yes; no)

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

## 6. Deciding parse-tree equality

```agda
-- Purpose: decide propositional equality of parse trees. The LongPair
--   side needs this: `star-tail` fires exactly when the heads are EQUAL
--   AS TREES (a length equality is not enough — the tails must then be
--   inverted through the same star).
-- Used by: normL.
-- Proof idea: mutual structural recursion; the ParseTree injectivity
--   inversions give the negative branches, leaf constructor indices are
--   forced by the shared index m.
mutual
  tree-≟ : ∀ { m : RE } → (u v : U m) → Dec (u ≡ v)
  tree-≟ EmptyU EmptyU = yes refl
  tree-≟ (LetterU c) (LetterU .c) = yes refl
  tree-≟ (LeftU u) (LeftU v) with tree-≟ u v
  ... | yes e = yes (cong LeftU e)
  ... | no ¬e = no (λ h → ¬e (inv-leftU u v h))
  tree-≟ (LeftU u) (RightU v) = no (λ ())
  tree-≟ (RightU u) (LeftU v) = no (λ ())
  tree-≟ (RightU u) (RightU v) with tree-≟ u v
  ... | yes e = yes (cong RightU e)
  ... | no ¬e = no (λ h → ¬e (inv-rightU u v h))
  tree-≟ (PairU u v) (PairU u₂ v₂) with tree-≟ u u₂ | tree-≟ v v₂
  ... | yes e₁ | yes e₂ = yes (cong₂ PairU e₁ e₂)
  ... | no ¬e₁ | _ = no (λ h → ¬e₁ (proj₁ (inv-pairU u v u₂ v₂ h)))
  ... | yes e₁ | no ¬e₂ = no (λ h → ¬e₂ (proj₂ (inv-pairU u v u₂ v₂ h)))
  tree-≟ (ListU us) (ListU vs) with list-≟ us vs
  ... | yes e = yes (cong ListU e)
  ... | no ¬e = no (λ h → ¬e (inv-listU1 us vs h))

  cons-inj₁ : ∀ {A : Set} {x y : A} {xs ys : List A}
    → x ∷ xs ≡ y ∷ ys → x ≡ y
  cons-inj₁ refl = refl
  cons-inj₂ : ∀ {A : Set} {x y : A} {xs ys : List A}
    → x ∷ xs ≡ y ∷ ys → xs ≡ ys
  cons-inj₂ refl = refl

  list-≟ : ∀ { m : RE } → (us vs : List (U m)) → Dec (us ≡ vs)
  list-≟ [] [] = yes refl
  list-≟ [] (v ∷ vs) = no (λ ())
  list-≟ (u ∷ us) [] = no (λ ())
  list-≟ (u ∷ us) (v ∷ vs) with tree-≟ u v | list-≟ us vs
  ... | yes e₁ | yes e₂ = yes (cong₂ (λ x xs → x ∷ xs) e₁ e₂)
  ... | no ¬e₁ | _ = no (λ h → ¬e₁ (cons-inj₁ h))
  ... | yes e₁ | no ¬e₂ = no (λ h → ¬e₂ (cons-inj₂ h))
```

## 7. The `LongPair` normal form and its reduction at a star

A `LongPair (m * nε ` loc)` pair `(u, v)` has `¬ (u >ᵍ v)` and
`|v| < |u|`. Inverting the star rules from the NEGATED side: if the
heads are distinct trees, `star-tail` cannot fire and `star-head` is
the only possible derivation, so the absence hypothesis yields
`¬ (w₁ >ᵍ w₂)` — and then `(w₁ ∷ t, w₂ ∷ [])` is NOT related for ANY
forest `t`: every star rule is blocked. Its length condition
`|w₂ ∷ []| < |w₁ ∷ t|` needs `wlen t ≥ (|w₂| ∸ |w₁|) + 1` exactly when
`|w₂| ≥ |w₁|`; the raw hypothesis `h` supplies that weight in `ws₁`,
and `pref-req` extracts the bounded prefix. Equal heads recurse into
the tails (`star-tail` lifts any tail derivation, so the tails keep
their non-derivation). The body branch NEVER fires on this side — a
body `LongPair` would need `¬ (w₂ >ᵍ w₁)`, which the star negation
does not supply; the star witness is always constructible instead.

```agda
-- Purpose: the LongPair normal form: a single tree on the right, a
--   BOUNDED forest on the left, and NO greedy derivation (star-head
--   blocked by an unrelatable head pair, star-tail by distinct heads,
--   star-cons-nil cannot conclude a cons right forest).
-- Used by: long-★-normalize.
-- Proof idea: N/A (record type).
NormLong : (m : RE) → (nε : ε∉ m) → (loc : ℕ) → Set
NormLong m nε loc = Σ ( U m ) λ w₁ → Σ ( U m ) λ w₂ →
  Σ[ t ∈ List (U m) ]
    ( ¬ ( ( m * nε ` loc ) ⊢ ListU {m} {nε} {loc} (w₁ ∷ t)
          >ᵍ ListU {m} {nε} {loc} (w₂ ∷ []) )
    × ( length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ []))))
        Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ t)))) )
    × ( length t Nat.≤ suc (length (proj₁ (flat {m} w₂))
                                Nat.∸ length (proj₁ (flat {m} w₁))) ) )

-- Purpose: the non-derivation witness of NormLong (see §7 prose).
-- Used by: mk-normL, mk-normL0.
-- Proof idea: inv-★-der lists exactly the star-head and star-tail
--   possibilities for a cons/cons pair; both are contradicted.
¬der-★ : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { w₁ w₂ : U m } { t : List (U m) }
  → ¬ ( m ⊢ w₁ >ᵍ w₂ ) → ¬ ( w₁ ≡ w₂ )
  → ¬ ( ( m * nε ` loc ) ⊢ ListU {m} {nε} {loc} (w₁ ∷ t)
        >ᵍ ListU {m} {nε} {loc} (w₂ ∷ []) )
¬der-★ {m} {nε} {loc} {w₁} {w₂} {t} ¬d₀ ¬e dᵍ
  with inv-★-der {m} {nε} {loc} {w₁} {w₂} {t} {[]} dᵍ
... | inj₁ d₀ = ¬d₀ d₀
... | inj₂ (e , _) = ¬e e

-- Purpose: assemble a NormLong from a prefix t of ws₁ carrying the
--   needed weight (the |w₂| ≥ |w₁| cases).
-- Used by: normL.
-- Proof idea: |w₂| = |w₁| + (|w₂| ∸ |w₁|) when |w₁| ≤ |w₂|, so
--   |w₂| < |w₁| + suc (|w₂| ∸ |w₁|) ≤ |w₁| + wlen t. Mirrors mk-norm.
mk-normL : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { w₁ w₂ : U m }
  → ( ¬e : ¬ ( w₁ ≡ w₂ ) )
  → ( ¬d₀ : ¬ ( m ⊢ w₁ >ᵍ w₂ ) )
  → ( lx≤ : length (proj₁ (flat {m} w₁)) Nat.≤ length (proj₁ (flat {m} w₂)) )
  → ( t : List (U m) )
  → ( wt : suc (length (proj₁ (flat {m} w₂)) Nat.∸ length (proj₁ (flat {m} w₁)))
             Nat.≤ wlen t )
  → ( lt : length t
           Nat.≤ suc (length (proj₁ (flat {m} w₂)) Nat.∸ length (proj₁ (flat {m} w₁))) )
  → NormLong m nε loc
mk-normL {m} {nε} {loc} {w₁} {w₂} ¬e ¬d₀ lx≤ t wt lt =
  w₁ , w₂ , t , ( ¬der-★ {m} {nε} {loc} {w₁} {w₂} {t} ¬d₀ ¬e , ( hlen , lt ) )
  where
  lx₁ = length (proj₁ (flat {m} w₁))
  lx₂ = length (proj₁ (flat {m} w₂))

  eq₁ : length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ [])))) ≡ lx₂
  eq₁ = trans (len-ListU {m} {nε} {loc} (w₂ ∷ [])) (+-identityʳ lx₂)

  eq₂ : length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ t)))) ≡ (lx₁ + wlen t)
  eq₂ = len-ListU {m} {nε} {loc} (w₁ ∷ t)

  -- lx₁ + suc (lx₂ ∸ lx₁) ≡ suc lx₂  (lx≤ makes ∸ exact)
  suc-lex : lx₁ Nat.+ suc (lx₂ Nat.∸ lx₁) ≡ suc lx₂
  suc-lex = trans (+-suc lx₁ (lx₂ Nat.∸ lx₁))
              (cong suc (m+[n∸m]≡n lx≤))

  suc-lx₂≤ : suc lx₂ Nat.≤ lx₁ + suc (lx₂ Nat.∸ lx₁)
  suc-lx₂≤ = subst (suc lx₂ Nat.≤_) (sym suc-lex) ≤-refl

  hlen : length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ []))))
         Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ t))))
  hlen = subst₂ _<_ (sym eq₁) (sym eq₂)
    (≤-trans suc-lx₂≤ (+-monoʳ-≤ lx₁ wt))

-- Purpose: the |w₂| < |w₁| case needs NO prefix: t = [] already
--   satisfies the length inequality from the heads alone.
-- Used by: normL.
-- Proof idea: |w₂| < |w₁| = |w₁ ∷ []| by hypothesis; the tail bound is
--   0 ≤ suc (|w₂| ∸ |w₁|) = trivial.
mk-normL0 : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { w₁ w₂ : U m }
  → ( ¬e : ¬ ( w₁ ≡ w₂ ) )
  → ( ¬d₀ : ¬ ( m ⊢ w₁ >ᵍ w₂ ) )
  → ( length (proj₁ (flat {m} w₂)) Nat.< length (proj₁ (flat {m} w₁)) )
  → NormLong m nε loc
mk-normL0 {m} {nε} {loc} {w₁} {w₂} ¬e ¬d₀ lt =
  w₁ , w₂ , [] , ( ¬der-★ {m} {nε} {loc} {w₁} {w₂} {[]} ¬d₀ ¬e
                 , ( hlen , z≤n ) )
  where
  lx₁ = length (proj₁ (flat {m} w₁))
  lx₂ = length (proj₁ (flat {m} w₂))

  eq₁ : length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ [])))) ≡ lx₂
  eq₁ = trans (len-ListU {m} {nε} {loc} (w₂ ∷ [])) (+-identityʳ lx₂)

  eq₂ : length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ [])))) ≡ lx₁
  eq₂ = trans (len-ListU {m} {nε} {loc} (w₁ ∷ [])) (+-identityʳ lx₁)

  hlen : length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ []))))
         Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ []))))
  hlen = subst₂ _<_ (sym eq₁) (sym eq₂) lt

-- Purpose: the length-trichotomy case analysis for a distinct-head
--   cons/cons star pair (the witness builder of normL).
-- Used by: normL.
-- Proof idea: see the clause comments.
normL-tri : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { w₁ w₂ : U m } { ws₁ ws₂ : List (U m) }
  → ( ¬e : ¬ ( w₁ ≡ w₂ ) )
  → ( ¬d₀ : ¬ ( m ⊢ w₁ >ᵍ w₂ ) )
  → ( h : length (proj₁ (flat (ListU {m} {nε} {loc} (w₂ ∷ ws₂))))
          Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} (w₁ ∷ ws₁)))) )
  → LongPair m ⊎ NormLong m nε loc
normL-tri {m} {nε} {loc} {w₁} {w₂} {ws₁} {ws₂} ¬e ¬d₀ h
  with tri (length (proj₁ (flat {m} w₂))) (length (proj₁ (flat {m} w₁)))
... | inj₁ lt
    -- |w₂| < |w₁|: no forest needed at all.
    = inj₂ (mk-normL0 {m} {nε} {loc} {w₁} {w₂} ¬e ¬d₀ lt)
... | inj₂ (inj₁ eq)
    -- equal head lengths: the raw inequality forces wlen ws₁ ≥ 1, so a
    -- prefix of weight suc (|w₂| ∸ |w₁|) = 1 exists in ws₁.
    = let lx₁ = length (proj₁ (flat {m} w₁))
          lx₂ = length (proj₁ (flat {m} w₂))
          eqL : wlen (w₂ ∷ ws₂) ≡ lx₂ + wlen ws₂
          eqL = refl
          eqR : wlen (w₁ ∷ ws₁) ≡ lx₁ + wlen ws₁
          eqR = refl
          hsum : lx₂ + wlen ws₂ Nat.< lx₁ + wlen ws₁
          hsum = subst₂ _<_ eqL eqR
                   (subst₂ _<_ (len-ListU (w₂ ∷ ws₂))
                               (len-ListU (w₁ ∷ ws₁)) h)
          p′ = subst (λ z → suc z Nat.≤ wlen ws₁)
                 (sym (m≤n⇒m∸n≡0 (subst (lx₂ Nat.≤_) eq ≤-refl)))
                 (≤-trans (s≤s z≤n)
                   (+-cancelˡ-< lx₁ (wlen ws₂) (wlen ws₁)
                     (subst (λ z → z Nat.+ wlen ws₂ Nat.< lx₁ Nat.+ wlen ws₁)
                       eq hsum)))
          t , (wt , lt) = pref-req {m} {nε} (suc (lx₂ Nat.∸ lx₁)) ws₁ p′
      in inj₂ (mk-normL {m} {nε} {loc} {w₁} {w₂} ¬e ¬d₀
                  (subst (lx₁ Nat.≤_) (sym eq) ≤-refl) t wt lt)
... | inj₂ (inj₂ lt)
    -- |w₂| > |w₁|: h forces wlen ws₁ > |w₂| ∸ |w₁|; pref-req extracts
    -- the bounded prefix t.
    = let lx₁ = length (proj₁ (flat {m} w₁))
          lx₂ = length (proj₁ (flat {m} w₂))
          eqL : wlen (w₂ ∷ ws₂) ≡ lx₂ + wlen ws₂
          eqL = refl
          eqR : wlen (w₁ ∷ ws₁) ≡ lx₁ + wlen ws₁
          eqR = refl
          hsum : lx₂ + wlen ws₂ Nat.< lx₁ + wlen ws₁
          hsum = subst₂ _<_ eqL eqR
                   (subst₂ _<_ (len-ListU (w₂ ∷ ws₂))
                               (len-ListU (w₁ ∷ ws₁)) h)
          p′ = +-cancelˡ-< lx₁ (lx₂ Nat.∸ lx₁) (wlen ws₁)
                 (subst (λ z → z Nat.< lx₁ Nat.+ wlen ws₁)
                   (sym (m+[n∸m]≡n (<⇒≤ lt)))
                   (≤-trans (s≤s (m≤m+n lx₂ (wlen ws₂))) hsum))
          t , (wt , lt₂) = pref-req {m} {nε} (suc (lx₂ Nat.∸ lx₁)) ws₁ p′
      in inj₂ (mk-normL {m} {nε} {loc} {w₁} {w₂} ¬e ¬d₀ (<⇒≤ lt) t wt lt₂)

-- Purpose: the case analysis on the left forest (the recursive core of
--   long-★-normalize; separate top-level clauses per the repo lesson
--   about indexed rule implicits).
-- Used by: long-★-normalize.
-- Proof idea: see the clause comments. Structural recursion on the
--   left forest.
normL : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ }
  → (us vs : List (U m))
  → ( ¬ ( ( m * nε ` loc ) ⊢ ListU {m} {nε} {loc} us
          >ᵍ ListU {m} {nε} {loc} vs ) )
  → length (proj₁ (flat (ListU {m} {nε} {loc} vs)))
    Nat.< length (proj₁ (flat (ListU {m} {nε} {loc} us)))
  → LongPair m ⊎ NormLong m nε loc
normL [] vs ¬der h = ⊥-elim (¬<-0 h)                       -- length-absurd
normL {m} {nε} {loc} (w₁ ∷ ws₁) [] ¬der h
  -- a nonempty-left/empty-right star pair is ALWAYS related
  = ⊥-elim (¬der (GreedyOrder.sub
          (GreedyOrder.star-cons-nil {m} {loc} {nε} {w₁} {ws₁})))
normL {m} {nε} {loc} (w₁ ∷ ws₁) (w₂ ∷ ws₂) ¬der h with tree-≟ w₁ w₂
... | yes e
    -- equal heads (the SAME tree): star-tail lifts any tail
    -- derivation, so the tails inherit the non-derivation; recurse.
    = normL ws₁ ws₂
        (λ d₂ → ¬der (GreedyOrder.sub
           (GreedyOrder.star-tail {m} {loc} {nε} {w₁} {w₂} {ws₁} {ws₂} e d₂)))
        (tail-< {m} {nε} {loc} {w₂} {w₁} {ws₂} {ws₁} (sym e) h)
... | no ¬e
    -- distinct trees: star-tail is blocked, so a derivation of THIS
    -- pair could only be star-head; its absence gives ¬ (w₁ >ᵍ w₂).
    = normL-tri {m} {nε} {loc} {w₁} {w₂} {ws₁} {ws₂} ¬e
        (λ d₀ → ¬der (GreedyOrder.sub
           (GreedyOrder.star-head {m} {loc} {nε} {w₁} {w₂} {ws₁} {ws₂} d₀)))
        h

-- Purpose: unwrap the star ListU constructors (every U (m * nε ` loc)
--   tree is one).
-- Used by: long-★-normalize.
normL-heads : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ }
  → (u v : U ( m * nε ` loc ))
  → ¬ ( ( m * nε ` loc ) ⊢ u >ᵍ v )
  → length (proj₁ (flat v)) Nat.< length (proj₁ (flat u))
  → LongPair m ⊎ NormLong m nε loc
normL-heads {m} {nε} {loc} (ListU us) (ListU vs) ¬d h = normL {m} {nε} {loc} us vs ¬d h

-- Purpose: the star layer of the bounded-witness problem for LongPair:
--   every LongPair at a top-level star is realized in the bounded
--   normal form NormLong. Unlike short-★-normalize the body branch is
--   NEVER reached (see §7 prose); the ⊎ keeps the dual statement shape.
-- Used by: the bounded-witness open item of IsoCheck §5; §5 example.
-- Proof idea: structural recursion on the left forest (normL).
long-★-normalize : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ }
  → LongPair ( m * nε ` loc )
  → LongPair m ⊎ NormLong m nε loc
long-★-normalize {m} {nε} {loc} (u , v , ¬d , h) = normL-heads {m} {nε} {loc} u v ¬d h
```

## 8. Regex-computable bounds: `MaxLen` evidence

The bounds in §4 and §7 are stated in terms of the FOUND trees
(`|w₁| ∸ |w₂| + 1`). Feeding the reduction into a decision procedure
needs a bound computable from the REGEX: `MaxLen r k` is evidence that
every word of `r` has length ≤ `k`, with NO constructor at a star —
matching `maxLen(m* nε) = ∞` in IsoCheck §5 (line ~409), which is
exactly why this layer sits ABOVE the star normalization.

```agda
-- Purpose: constructive upper bound on word lengths, computable for
--   star-free regexes; NO case for _*_ (unbounded there).
-- Used by: len-MaxLen, short-★-bounded, long-★-bounded, the example.
-- Proof idea: N/A (evidence type).
data MaxLen : RE → ℕ → Set where
  ml-ε : MaxLen ε zero
  ml-$ : ∀ { c loc } → MaxLen ( $ c ` loc ) (suc zero)
  ml-● : ∀ { l r i j loc } → MaxLen l i → MaxLen r j
      → MaxLen ( l ● r ` loc ) (i Nat.+ j)
  ml-+ : ∀ { l r i j loc } → MaxLen l i → MaxLen r j
      → MaxLen ( l + r ` loc ) (i Nat.⊔ j)

-- Purpose: every parse tree of r has flat length ≤ the evidenced bound.
-- Used by: short-★-bounded, long-★-bounded, §5 example.
-- Proof idea: induction on the evidence; the §1 flat-transport lemmas
--   convert the recursive bounds; sums/maxima are monotone.
len-MaxLen : ∀ { r : RE } { k : ℕ } → MaxLen r k → (u : U r)
  → length (proj₁ (flat u)) Nat.≤ k
len-MaxLen ml-ε EmptyU = z≤n
len-MaxLen ml-$ (LetterU c) = s≤s z≤n
len-MaxLen (ml-● m₁ m₂) u = len-●e m₁ m₂ u
  where
  len-●e : ∀ { l r : RE } { loc : ℕ } { i j : ℕ }
    → MaxLen l i → MaxLen r j → (u : U ( l ● r ` loc ))
    → length (proj₁ (flat u)) Nat.≤ i Nat.+ j
  len-●e {l} {r} {loc} {i} {j} m₁ m₂ (PairU u v)
    = subst (λ z → z Nat.≤ i Nat.+ j)
        (sym (flat-PairU-len {l} {r} {loc} {u} {v}))
        (+-mono-≤ (len-MaxLen m₁ u) (len-MaxLen m₂ v))
len-MaxLen (ml-+ m₁ m₂) u = len-+e m₁ m₂ u
  where
  len-+e : ∀ { l r : RE } { loc : ℕ } { i j : ℕ }
    → MaxLen l i → MaxLen r j → (u : U ( l + r ` loc ))
    → length (proj₁ (flat u)) Nat.≤ i Nat.⊔ j
  len-+e {l} {r} {loc} {i} {j} m₁ _ (LeftU u)
    = ≤-trans (subst (λ z → z Nat.≤ i) (sym (flat-LeftU-len {l} {r} {loc} {u}))
                        (len-MaxLen m₁ u))
              (m≤m⊔n i j)
  len-+e {l} {r} {loc} {i} {j} _ m₂ (RightU v)
    = ≤-trans (subst (λ z → z Nat.≤ j) (sym (flat-RightU-len {l} {r} {loc} {v}))
                        (len-MaxLen m₂ v))
              (m≤n⊔m i j)

-- Purpose: the normal forms with the tail bound replaced by a NUMBER
--   computed from the regex (k = maxLen of the body).
-- Used by: short-★-bounded, long-★-bounded.
-- Proof idea: N/A (record types).
NormShortB : (m : RE) → (nε : ε∉ m) → (loc : ℕ) → ℕ → Set
NormShortB m nε loc k = Σ[ ns ∈ NormShort m nε loc ]
  ( let _ , _ , t , _ = ns in length t Nat.≤ suc (k Nat.∸ suc zero) )

NormLongB : (m : RE) → (nε : ε∉ m) → (loc : ℕ) → ℕ → Set
NormLongB m nε loc k = Σ[ nl ∈ NormLong m nε loc ]
  ( let _ , _ , t , _ = nl in length t Nat.≤ suc (k Nat.∸ suc zero) )

-- helper: move a witness bound (a ∸ b) to the regex bound (k ∸ 1):
-- heads have length ≤ k (len-MaxLen) and ≥ 1 (len≥1).
∸-bound-trans : ∀ { a b k : ℕ }
  → a Nat.≤ k → suc zero Nat.≤ b
  → suc (a Nat.∸ b) Nat.≤ suc (k Nat.∸ suc zero)
∸-bound-trans a≤k b≥1 = s≤s (∸-mono a≤k b≥1)

-- Purpose: the star reductions with bounds COMPUTABLE FROM THE REGEX:
--   given maxLen evidence for the BODY, the bounded tails of the
--   normal forms have length ≤ suc (k ∸ 1) (the ∸ of two head lengths
--   is ≤ k ∸ 1, heads being in [1 .. k]).
-- Used by: the bounded-witness open item of IsoCheck §5; §5 example.
-- Proof idea: compose the normalizing map with ∸-bound-trans.
short-★-bounded : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { k : ℕ }
  → MaxLen m k
  → ShortPair ( m * nε ` loc )
  → ShortPair m ⊎ NormShortB m nε loc (suc (k Nat.∸ suc zero))
short-★-bounded {m} {nε} {loc} {k} mk sp with short-★-normalize sp
... | inj₁ spm = inj₁ spm
... | inj₂ ns = let w₁ , w₂ , t , _ , _ , _ , bound = ns
                in inj₂ (ns , ≤-trans bound
                              (∸-bound-trans (len-MaxLen mk w₁) (len≥1 {m} nε w₂)))

long-★-bounded : ∀ { m : RE } { nε : ε∉ m } { loc : ℕ } { k : ℕ }
  → MaxLen m k
  → LongPair ( m * nε ` loc )
  → LongPair m ⊎ NormLongB m nε loc (suc (k Nat.∸ suc zero))
long-★-bounded {m} {nε} {loc} {k} mk lp with long-★-normalize lp
... | inj₁ lpm = inj₁ lpm
... | inj₂ nl = let w₁ , w₂ , t , _ , _ , bound = nl
                in inj₂ (nl , ≤-trans bound
                              (∸-bound-trans (len-MaxLen mk w₂) (len≥1 {m} nε w₁)))
```

Note the argument order in the `LongPair` clause: `NormLong`'s ∸ is
`|w₂| ∸ |w₁|` (right head minus left), so the regex bound applies to
`w₂` and the `len≥1` side to `w₁` — dual to the `ShortPair` clause.

Note the argument order in the `LongPair` clause: `NormLong`'s ∸ is
`|w₂| ∸ |w₁|` (right head minus left), so the regex bound applies to
`w₂` and the `len≥1` side to `w₁` — dual to the `ShortPair` clause.

### The example, both sides and with regex bounds (§5 data)

```agda
-- the body has NO LongPair either (dual of no-sp-mb2; 4 rigid cases).
no-lp-mb2 : ¬ LongPair mb2
no-lp-mb2 (u , v , ¬d , h) = go u v ¬d h
  where
  go : (u v : U mb2) → ¬ ( mb2 ⊢ u >ᵍ v )
    → length (proj₁ (flat v)) Nat.< length (proj₁ (flat u)) → ⊥
  go (LeftU (PairU (LetterU 'b') (LetterU 'b')))
     (LeftU (PairU (LetterU 'b') (LetterU 'b'))) ¬d h = ⊥-elim (¬2<2 h)
  go (LeftU (PairU (LetterU 'b') (LetterU 'b')))
     (RightU (LetterU 'b')) ¬d h = ⊥-elim (¬d d₀-★)   -- L >ᵍ R DOES hold
  go (RightU (LetterU 'b'))
     (LeftU (PairU (LetterU 'b') (LetterU 'b'))) ¬d h = ⊥-elim (¬2<1 h)
  go (RightU (LetterU 'b'))
     (RightU (LetterU 'b')) ¬d h = ⊥-elim (¬1<1 h)

-- A real star-layer LongPair at the SAME star as sp-★-raw: forests of
-- lengths (3, 2), heads R-★/L-★ — distinct trees, mutually unrelated
-- (no-ᵍ-rl kills R >ᵍ L), so no star rule concludes the pair.
¬lp-raw : ¬ ( star-★-mb2 ⊢ ListU {mb2} {nε-mb2} {96} (R-★ ∷ L-★ ∷ [])
              >ᵍ ListU {mb2} {nε-mb2} {96} (L-★ ∷ []) )
¬lp-raw dᵍ with inv-★-der {mb2} {nε-mb2} {96} {R-★} {L-★} {L-★ ∷ []} {[]} dᵍ
... | inj₁ d₀ = ⊥-elim (no-ᵍ-rl d₀)
... | inj₂ (e , _)
    = ⊥-elim (RightU≢LeftU {b2b} { $ 'b' ` 94 } { 95 }
                (LetterU 'b')
                (PairU { $ 'b' ` 91 } { $ 'b' ` 92 } { 93 }
                   (LetterU 'b') (LetterU 'b'))
                e)

lp-★-raw : LongPair star-★-mb2
lp-★-raw = ListU {mb2} {nε-mb2} {96} (R-★ ∷ L-★ ∷ [])
         , ListU {mb2} {nε-mb2} {96} (L-★ ∷ [])
         , ( ¬lp-raw , s≤s (s≤s (s≤s z≤n)) )   -- 2 < 3, by computation

-- the reduction computes to the star normal form (body branch absent).
long-★-mb2-right : which-⊎ (long-★-normalize lp-★-raw) ≡ true
long-★-mb2-right = refl

-- maxLen evidence for mb2: maxLen((b●b) + b) = 2 ⊔ 1 = 2 (computes).
ml-mb2 : MaxLen mb2 2
ml-mb2 = ml-+ (ml-● ml-$ ml-$) ml-$

-- every body tree has length ≤ 2 — the bound the normalization feeds on.
len-mb2≤2 : (u : U mb2) → length (proj₁ (flat u)) Nat.≤ 2
len-mb2≤2 = len-MaxLen ml-mb2

-- both bounded pipelines compute end-to-end (regex bound suc (2 ∸ 1) = 2,
-- matching the ∸-bound of the mb2 witnesses — the bound is TIGHT here).
bounded-★-mb2 : which-⊎ (short-★-bounded ml-mb2 sp-★-raw) ≡ true
bounded-★-mb2 = refl

bounded-★-long-mb2 : which-⊎ (long-★-bounded ml-mb2 lp-★-raw) ≡ true
bounded-★-long-mb2 = refl
```

## 9. Status of the bounded-witness problem

Proved here (star layer, BOTH halves + regex bounds):

* every `ShortPair (m * nε ` loc)` yields a witness with FOREST LENGTHS
  BOUNDED — either a `ShortPair m` in the body, or a `star-head` pair
  whose forests have lengths `1` and `≤ |w₁| ∸ |w₂| + 1` (§4);
* every `LongPair (m * nε ` loc)` is realized at the star itself by a
  `NormLong` witness with tail `≤ |w₂| ∸ |w₁| + 1` (§7) — the body
  branch is structurally unreachable on this side;
* given `MaxLen m k` evidence (§8), both tail bounds become the
  regex-computed number `suc (k ∸ 1)`, and every tree length is `≤ k`
  (`len-MaxLen`). `mb2` shows both star layers genuinely firing (its
  body has neither a `ShortPair` nor a `LongPair`), the per-list bound
  of 1 being impossible, and the regex bound being TIGHT (`k = 2`).
* tree equality at the star head is decidable (`tree-≟`, §6).

Still open:
1. the DESCEND lemmas: composing these star-layer results through
   `●`/`+` — a compound pair whose greedy difference lives in a
   sub-derivation, not at the top node;
2. the per-subterm semilinear difference sets (IsoCheck §5 item 3):
   with `MaxLen` bounds the star layer is finite branching, but the
   full decision needs the shape of `{ |u| ∸ |v| }` per subterm;
3. `MaxLen` DECIDABILITY (producing the evidence or proving none
   exists) is immediate by recursion on star-free regexes but unwritten.
