```agda
-- {-# OPTIONS --rewriting --allow-unsolved-metas #-}
{-# OPTIONS --rewriting #-}
module cgp.posix.InMembershipToParseTree where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )

import cgp.Utils as Utils
open Utils using (¬∷≡[])

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ; LeftU ; RightU ; PairU ; ListU ; flat ; unListU ; listU∘unListU )

open import Data.Char using (Char; _≟_)
open import Data.List.Base as ListBase hiding ([_])
open ListBase using (List; []; _∷_; _++_; _∷ʳ_)
[_] : Char → List Char
[_] x = x ∷ []
open import Data.List.Properties using (∷ʳ-++ ; ++-cancelˡ ; ++-identityʳ ; ++-identityˡ ; ∷-injective ; ++-assoc)
open import Relation.Nullary using (¬_ ; contradiction)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
open Eq using (_≡_; refl; trans; sym; cong; subst; _≢_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat using (ℕ)
open import Relation.Nullary.Decidable using (Dec; yes; no)

-- List left cancellation (works with with-abstracted params)
-- IDEA:  Strip matching heads from both sides until xs is gone, yielding ys ≡ zs.
-- USED:  Deriving suffix equalities inside inj2-yes-pfx, noSplitR', noSplitL'
--        and inj₂-help by cancelling a common prefix from a ++-equality.
cancel-left : (xs ys zs : List Char) → xs ++ ys ≡ xs ++ zs → ys ≡ zs
cancel-left [] ys zs refl = refl
cancel-left (x ∷ xs) ys zs p = cancel-left xs ys zs (proj₂ (∷-injective p))

-- Singleton list equality: local [_] notation reduces definitionally to _∷_ [].
-- IDEA:  [x] is defined as x ∷ [], so refl suffices.
-- USED:  Rewriting list-literal goals into constructor form; e.g. in ∈⟦-$$-elim.
[_]≡∷[] : ∀ (x : Char) → [ x ] ≡ x ∷ []
[_]≡∷[] x = refl

-- POSIX parse tree relation

infix 4 _,_⇒_

data _,_⇒_ : ∀ ( w : List Char ) → ( r : RE ) → U r → Set where
  p₁  : [] , ε ⇒ EmptyU
  pc  : ∀ {c : Char} {loc : ℕ}  → [ c ] , $ c ` loc ⇒ LetterU c
  p+l : ∀ { w : List Char } { l r : RE } { loc : ℕ } { v : U l }
    →  w , l ⇒ v
    ------------------------------------------------------------
    → w , l + r ` loc ⇒ LeftU v
  p+r : ∀ { w : List Char } { l r : RE } { loc : ℕ } { v : U r }
    →  w , r ⇒ v
    → ¬ ( w ∈⟦ l ⟧ )
    ------------------------------------------------------------
    → w , l + r ` loc ⇒ RightU v
  ps : ∀ { w₁ w₂ w : List Char } { l r : RE } { loc : ℕ } { v₁ : U l } { v₂ : U r }
    →  w ≡ w₁ ++ w₂
    →  w₁ , l ⇒ v₁
    →  w₂ , r ⇒ v₂
    → ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) × (w₃ ++ w₄ ≡ w₂) × ( (w₁ ++ w₃) ∈⟦ l ⟧ ) × w₄ ∈⟦ r ⟧ )
    -----------------s-------------------------------------------
    → w , l ● r ` loc ⇒ PairU v₁ v₂

  p[] : ∀ { r : RE } {ε∉r : ε∉ r } { loc : ℕ }
    → [] , r * ε∉r ` loc ⇒ ListU []

  p* : ∀ { w₁ w₂ w : List Char } { r : RE } {ε∉r : ε∉ r } { loc : ℕ } {v : U r } { vs : List (U r) }
    →  w ≡ w₁ ++ w₂
    →  w₁ , r ⇒ v
    →  w₂ , r * ε∉r ` loc ⇒ ListU vs
    →  ¬ w₁ ≡ []
    → ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) × (w₃ ++ w₄ ≡ w₂) × ( (w₁ ++ w₃) ∈⟦ r ⟧ ) × w₄ ∈⟦ r * ε∉r ` loc ⟧ )
    -----------------------------------------------------------
    → w , r * ε∉r ` loc ⇒ ListU (v ∷ vs)

-- Elimination lemmas

-- Decidable equality on lists of characters.
-- IDEA:  Pointwise comparison: heads must match, then recurse on tails;
--        different shapes are immediately unequal.
-- USED:  Not directly in ∈⟦→⇒ but available for list-equality decisions.
list≡-decides : (xs ys : List Char) → Dec (xs ≡ ys)
list≡-decides [] [] = yes refl
list≡-decides (x ∷ xs) (y ∷ ys) with x ≟ y | list≡-decides xs ys
... | yes x≡y | yes xs≡ys = yes (Eq.cong₂ _∷_ x≡y xs≡ys)
... | yes x≡y | no xs≢ys = no λ x∷xs≡y∷ys → xs≢ys (proj₂ (∷-injective x∷xs≡y∷ys))
... | no x≢y | _ = no λ x∷xs≡y∷ys → x≢y (proj₁ (∷-injective x∷xs≡y∷ys))
list≡-decides [] (y ∷ ys) = no λ []≡y∷ys → Utils.¬∷≡[] (sym []≡y∷ys)
list≡-decides (x ∷ xs) [] = no Utils.¬∷≡[]

-- Right identity for ++ (stdlib version is left-recursive; this is right-recursive).
-- IDEA:  xs ++ [] ≡ xs by induction; each cons-cell absorbs the empty tail.
-- USED:  Simplifying w₁ ++ [] ≡ prefix goals in ∈⟦-●-decides-empty-aux.
list-idʳ : (xs : List Char) → xs ++ [] ≡ xs
list-idʳ [] = refl
list-idʳ (x ∷ xs) = Eq.cong₂ _∷_ refl (list-idʳ xs)

-- Elimination lemmas

-- Alternation elimination: membership in l+r implies membership in one side.
-- IDEA:  Case analysis on the +L/+R constructors.
-- USED:  ∈⟦→⇒ for l+r extracts the side; p+r needs to know w∉⟦l⟧.
∈⟦-+-elim : ∀ {l r} {w loc} → w ∈⟦ l + r ` loc ⟧ → w ∈⟦ l ⟧ ⊎ w ∈⟦ r ⟧
∈⟦-+-elim {l} {r} {w} {loc} (r +L w∈l) = inj₁ w∈l
∈⟦-+-elim {l} {r} {w} {loc} (l +R w∈r) = inj₂ w∈r

-- Concatenation elimination: membership in l●r yields a split w₁++w₂≡w with w₁∈⟦l⟧, w₂∈⟦r⟧.
-- IDEA:  Project out the sub-components from the _●_⧺_ constructor.
-- USED:  ∈⟦→⇒●-go feeds the split into find-longest-split; ∈⟦-*-search uses it in *-fb.
∈⟦-●-elim : ∀ {l r} {w loc} → w ∈⟦ l ● r ` loc ⟧
  → Σ (List Char) (λ w₁ → Σ (List Char) (λ w₂ → w₁ ∈⟦ l ⟧ × w₂ ∈⟦ r ⟧ × w₁ ++ w₂ ≡ w))
∈⟦-●-elim {l} {r} {w} {loc} (_●_⧺_ {w₁} {w₂} {w} w∈l w∈r w₁w₂≡w) = w₁ , w₂ , w∈l , w∈r , w₁w₂≡w

-- ε elimination: membership in ε forces the word to be empty.
-- IDEA:  The only constructor is ε, which matches [] ∈⟦ ε ⟧; other shapes are impossible.
-- USED:  ∈⟦-decides for ε; ∈⟦→⇒* dispatches [] vs c∷cs; ∈⟦-*-no-split-end checks prefix≢[].
∈⟦-ε-elim : ∀ {w} → w ∈⟦ ε ⟧ → [] ≡ w
∈⟦-ε-elim {[]} ε = refl

-- Star elimination: membership in r* is either ε or r●(r*).
-- IDEA:  Deconstruct _* to expose the +L/+R choice: +L gives ε, +R gives a ●-split.
-- USED:  ∈⟦→⇒* uses it to obtain *-fb (the initial split for find-longest-split).
elim-star : ∀ {r'' nε'' w loc''} → w ∈⟦ r'' * nε'' ` loc'' ⟧ → w ∈⟦ ε ⟧ ⊎ w ∈⟦ r'' ● (r'' * nε'' ` loc'') ` loc'' ⟧
elim-star {r''} {nε''} {[]} {loc''} (_* ((r'' ● (r'' * nε'' ` loc'') ` loc'') +L w∈ε)) = inj₁ w∈ε
elim-star {r''} {nε''} {w} {loc''} (_* (p +R w∈●)) = inj₂ w∈●

-- Proper prefix relation: strict prefix ordering on character lists.
-- IDEA:  Inductive definition: [] is a proper prefix of any non-empty list;
--        if xs ⊏ ys then (x∷xs) ⊏ (x∷ys) extends the prefix relation.
-- USED:  NoShorter predicate requires w₁ ⊏ prefix; ⊏-from-split≢ and ⊏-split
--        convert between splitting and prefix properties throughout the search algorithms.
data _⊏_ : List Char → List Char → Set where
  ⊏-nil : ∀ {x xs} → [] ⊏ (x ∷ xs)
  ⊏-tail : ∀ {x xs ys} → xs ⊏ ys → (x ∷ xs) ⊏ (x ∷ ys)

-- No list is a proper prefix of the empty list.
-- IDEA:  Pattern-match on ⊏-nil/⊏-tail: neither can produce [] as the right argument.
-- USED:  Discharging impossible NoShorter witnesses (e.g. noShorterInit, ⊏-split base case).
⊏-absurd : ∀ {w₁} → w₁ ⊏ [] → ⊥
⊏-absurd ()

-- Split a proper-prefix proof against a list ending in a singleton.
-- IDEA:  Either w₁ is a prefix of xs (before the final d), or w₁ ≡ xs itself.
--        Induction on ⊏ peels matching characters; the ⊏-nil case lands at the split.
-- USED:  Preserving NoShorter when extending prefix by one character in ∈⟦-●-search and ∈⟦-*-search.
⊏-split : ∀ {w₁ xs d} → w₁ ⊏ (xs ++ d ∷ []) → (w₁ ⊏ xs) ⊎ (w₁ ≡ xs)
⊏-split {w₁ = []} {[]} {d} p = inj₂ refl
⊏-split {w₁ = []} {x ∷ xs} {d} p = inj₁ ⊏-nil
⊏-split {w₁ = c ∷ w₁'} {[]} {d} (⊏-tail p) = ⊥-elim (⊏-absurd {w₁ = w₁'} p)
⊏-split {w₁ = c ∷ w₁'} {d ∷ xs} {d₂} (⊏-tail p) with ⊏-split p
⊏-split {w₁ = c ∷ w₁'} {d ∷ xs} {d₂} (⊏-tail p) | inj₁ p⊏ = inj₁ (⊏-tail p⊏)
⊏-split {w₁ = c ∷ w₁'} {d ∷ xs} {d₂} (⊏-tail p) | inj₂ p≡ = inj₂ (cong₂ _∷_ refl p≡)

-- If w₁ splits w and w₁ is not all of w, then w₁ is a proper prefix.
-- IDEA:  From w₁++w₂≡w with w₁≢w, the suffix w₂ must be non-empty; induction on w₁
--        builds ⊏-nil/⊏-tail witnesses by peeling matching heads.
-- USED:  Deriving w₁ ⊏ prefix in NoShorter proofs (noSplitR', noSplitL', ∈⟦-*-no-split-end-●).
⊏-from-split≢ : ∀ {w₁ w₂ w} → w₁ ++ w₂ ≡ w → w₁ ≢ w → w₁ ⊏ w
⊏-from-split≢ {w₁} {[]} {w} w₁++[]≡w w₁≢w = ⊥-elim (w₁≢w (trans (sym (++-identityʳ w₁)) w₁++[]≡w))
⊏-from-split≢ {[]} {d ∷ ds} {d ∷ ds} refl _ = ⊏-nil
⊏-from-split≢ {c ∷ w₁'} {d ∷ ds} {c₂ ∷ w} c∷w₁'++d∷ds≡c₂∷w w₁≢w =
  let c≡c₂ , w₁'++d∷ds≡w = ∷-injective c∷w₁'++d∷ds≡c₂∷w
      w₁'≢w : w₁' ≢ w
      w₁'≢w w₁'≡w = w₁≢w (Eq.cong₂ _∷_ c≡c₂ w₁'≡w)
  in subst (λ x → (c ∷ w₁') ⊏ (x ∷ w)) c≡c₂
     (⊏-tail (⊏-from-split≢ {w₁'} {d ∷ ds} {w} w₁'++d∷ds≡w w₁'≢w))

-- Decidable membership

-- NoShorter invariant: no strict prefix of (prefix++suffix) matching l can complete r.
-- IDEA:  Encodes POSIX "longest-left" constraint. Maintained by search algorithms as the
--        prefix extends, ensuring that no shorter valid split exists.
-- USED:  Threaded through ∈⟦-●-search and ∈⟦-*-search to prune invalid splits.
NoShorter : (l r : RE) (prefix suffix : List Char) → Set
NoShorter l r prefix suffix = ∀ {w₁ w₂} → w₁ ++ w₂ ≡ prefix ++ suffix → w₁ ⊏ prefix → w₁ ∈⟦ l ⟧ → w₂ ∈⟦ r ⟧ → ⊥

-- Cancel-prefix helper: if prefix++w₂ ≡ prefix++(d∷ds) and (d∷ds)∉⟦r⟧ then w₂∉⟦r⟧.
-- IDEA:  cancel-left shows w₂ ≡ d∷ds; rewrite w₂∈⟦r⟧ into contradiction with ¬(d∷ds∈⟦r⟧).
-- USED:  ∈⟦-●-search when ⊏-split returns inj₂ (w₁ ≡ prefix case).
inj2-yes-pfx : (r : RE) → (prefix w2 : List Char) → (d : Char) → (ds : List Char) → prefix ++ w2 ≡ prefix ++ d ∷ ds → ¬((d ∷ ds) ∈⟦ r ⟧) → w2 ∈⟦ r ⟧ → ⊥
inj2-yes-pfx r prefix w2 d ds eq np wr = np (subst (_∈⟦ r ⟧) (cancel-left prefix w2 (d ∷ ds) eq) wr)

-- A non-empty suffix cannot be absorbed: w₁ ≡ w₁++w₂ with w₂≢[] is impossible.
-- IDEA:  Induction on w₁ shows w₂ must be [] by peeling constructors.
-- USED:  Discharging impossible splits in ∈⟦-●-decides-empty and ∈⟦-●-search.
¬_≡_++_˙ : ∀ (w₁ w₂ : List Char) → w₂ ≢ [] → w₁ ≡ w₁ ++ w₂ → ⊥
¬_≡_++_˙ [] w₂ w₂≢[] p = w₂≢[] (sym (trans p (++-identityˡ w₂)))
¬_≡_++_˙ (c ∷ cs) w₂ w₂≢[] p = ¬_≡_++_˙ cs w₂ w₂≢[] (proj₂ (∷-injective p))

-- Mutual recursive decidable membership for all RE constructors.
-- IDEA:  Structural recursion on regex, not on word. For composite regexes (●, *),
--        delegates to search algorithms that scan the word.
-- USED:  Core infrastructure: ∈⟦→⇒ (for +), ∈⟦-●-search, ∈⟦-*-search, ∈⟦-longer-split.
{-# TERMINATING #-}
mutual
  ∈⟦-decides : ∀ {r : RE} {w : List Char} → Dec (w ∈⟦ r ⟧)
  ∈⟦-decides {ε} {[]} = yes ε
  ∈⟦-decides {ε} {c ∷ cs} = no λ p → ≡⊥ (∈⟦-ε-elim p)
    where
      ≡⊥ : [] ≡ (c ∷ cs) → ⊥
      ≡⊥ ()
  ∈⟦-decides {$ c₁ ` loc} {c₂ ∷ []} with c₁ ≟ c₂
  ... | yes c₁≡c₂ = yes (subst (λ c → (c₂ ∷ []) ∈⟦ $ c ` loc ⟧) (sym c₁≡c₂) ($ c₂))
  ... | no ¬c₁≡c₂ = no ($-not-eq ¬c₁≡c₂)
    where
      -- Letter elimination: $c accepts only the singleton [c].
      -- IDEA:  Pattern-match on the $ constructor to recover the character and equalities.
      -- USED:  $-not-eq derives c₁≡c₂ from membership evidence.
      ∈⟦-$$-elim : ∀ {loc c₁ w} → w ∈⟦ $ c₁ ` loc ⟧ → Σ Char (λ c' → (w ≡ c' ∷ []) × (c₁ ≡ c'))
      ∈⟦-$$-elim ($ c) = c , refl , refl
      -- If c₁≢c₂ then [c₂] ∉⟦$c₁⟧.
      -- IDEA:  Eliminate membership to get c₁≡c' and c₂≡c', then transit to c₁≡c₂.
      -- USED:  ∈⟦-decides for $ in the ¬c₁≡c₂ branch.
      $-not-eq : ¬(c₁ ≡ c₂) → ¬((c₂ ∷ []) ∈⟦ $ c₁ ` loc ⟧)
      $-not-eq ¬c₁≡c₂ e =
        let c' , w≡[c'] , c₁≡c' = ∈⟦-$$-elim e
            c₂≡c' = proj₁ (∷-injective w≡[c'])
        in ¬c₁≡c₂ (trans c₁≡c' (sym c₂≡c'))
  ∈⟦-decides {$ c ` loc} {[]} = no λ()
  ∈⟦-decides {$ c₁ ` loc} {c₂ ∷ c₃ ∷ cs} with c₁ ≟ c₂
  ... | yes _ = no λ ()
  ... | no _ = no λ ()
  ∈⟦-decides {l + r ` loc} {w} = +-decides w
    where
      +-decides : (w : List Char) → Dec (w ∈⟦ l + r ` loc ⟧)
      +-decides w with ∈⟦-decides {l} {w}
      ... | yes w∈l = yes (r +L w∈l)
      ... | no ¬w∈l with ∈⟦-decides {r} {w}
      ... | yes w∈r = yes (l +R w∈r)
      ... | no ¬w∈r = no (+-not-eq ¬w∈l ¬w∈r)
        where
          -- If neither side matches, the + regex doesn't match either.
          -- IDEA:  Case analysis on +L/+R; each directly contradicts the corresponding ¬(w∈⟦_⟧).
          -- USED:  ∈⟦-decides for + in the (no,no) branch.
          +-not-eq : ¬(w ∈⟦ l ⟧) → ¬(w ∈⟦ r ⟧) → ¬(w ∈⟦ l + r ` loc ⟧)
          +-not-eq ¬w∈l ¬w∈r (_ +L w∈l') = ¬w∈l w∈l'
          +-not-eq ¬w∈l ¬w∈r (_ +R w∈r') = ¬w∈r w∈r'
  ∈⟦-decides {l ● r ` loc} {w} = ∈⟦-●-decides l r loc w
  ∈⟦-decides {r * nε ` loc} {w} = ∈⟦-*-decides r nε loc w

  -- Decidable membership for concatenation: search over all valid splits.
  -- IDEA:  For non-empty words, delegates to ∈⟦-●-search which scans prefix/suffix;
  --        for empty words, checks whether both sides can match [].
  -- USED:  ∈⟦-decides for l●r; called from ∈⟦→⇒ and search algorithms.
  ∈⟦-●-decides : (l r : RE) (loc : ℕ) (w : List Char) → Dec (w ∈⟦ l ● r ` loc ⟧)
  ∈⟦-●-decides l r loc [] = ∈⟦-●-decides-empty l r loc
    where
      ∈⟦-●-decides-empty : (l r : RE) (loc : ℕ) → Dec ([] ∈⟦ l ● r ` loc ⟧)
      ∈⟦-●-decides-empty l r loc = ∈⟦-●-decides-empty-aux l r loc (∈⟦-decides {l} {[]}) (∈⟦-decides {r} {[]})
        where
            -- If []∉⟦l⟧ then []∉⟦l●r⟧.
          -- IDEA:  Eliminate ● to get []∈⟦l⟧, directly contradicting ¬([]∈⟦l⟧).
          -- USED:  ∈⟦-●-decides-empty-aux when l cannot match [].
          ∈⟦-●-empty-no-l : (l r : RE) (loc : ℕ) → ¬([] ∈⟦ l ⟧) → ([] ∈⟦ l ● r ` loc ⟧) → ⊥
          ∈⟦-●-empty-no-l l r loc ¬p∈l (_●_⧺_ {[]} {[]} {[]} p∈l' _ _) = ¬p∈l p∈l'
         -- If []∉⟦r⟧ then []∉⟦l●r⟧.
          -- IDEA:  Eliminate ● to get []∈⟦r⟧, directly contradicting ¬([]∈⟦r⟧).
          -- USED:  ∈⟦-●-decides-empty-aux when r cannot match [].
          ∈⟦-●-empty-no-r : (l r : RE) (loc : ℕ) → ¬([] ∈⟦ r ⟧) → ([] ∈⟦ l ● r ` loc ⟧) → ⊥
          ∈⟦-●-empty-no-r l r loc ¬p∈r (_●_⧺_ {[]} {[]} {[]} _ p∈r' _) = ¬p∈r p∈r'
         -- Combine decisions on l and r to decide []∈⟦l●r⟧.
          -- IDEA:  []∈⟦l●r⟧ iff []∈⟦l⟧ ∧ []∈⟦r⟧; both must match empty.
          -- USED:  ∈⟦-●-decides for the [] case.
          ∈⟦-●-decides-empty-aux : (l r : RE) (loc : ℕ) → Dec ([] ∈⟦ l ⟧) → Dec ([] ∈⟦ r ⟧) → Dec ([] ∈⟦ l ● r ` loc ⟧)
          ∈⟦-●-decides-empty-aux l r loc (yes p∈l) (yes p∈r) = yes (_●_⧺_ {[]} {[]} {[]} p∈l p∈r refl)
          ∈⟦-●-decides-empty-aux l r loc (no ¬p∈l) _ = no (∈⟦-●-empty-no-l l r loc ¬p∈l)
          ∈⟦-●-decides-empty-aux l r loc _ (no ¬p∈r) = no (∈⟦-●-empty-no-r l r loc ¬p∈r)
  ∈⟦-●-decides l r loc (c ∷ cs) = ∈⟦-●-search l r loc [] (c ∷ cs) noShorterInit
    where
      noShorterInit : NoShorter l r [] (c ∷ cs)
      noShorterInit {w₁} {w₂} _ w₁⊏[] _ _ = ⊥-elim (⊏-absurd w₁⊏[])

  -- Incremental search for a valid ● split, extending prefix character by character.
  -- IDEA:  Maintain NoShorter invariant. At each step, try prefix∈⟦l⟧ ∧ suffix∈⟦r⟧;
  --        if prefix∉⟦l⟧, extend prefix by one character and recurse; if neither, use
  --        ∈⟦-●-no-split-end-r or noSplitL' to show no valid split exists.
  -- USED:  ∈⟦-●-decides for non-empty words.
  ∈⟦-●-search : (l r : RE) (loc : ℕ) (prefix suffix : List Char)
    → NoShorter l r prefix suffix
    → Dec ((prefix ++ suffix) ∈⟦ l ● r ` loc ⟧)
  ∈⟦-●-search l r loc prefix [] noShorter with ∈⟦-decides {l} {prefix} | ∈⟦-decides {r} {[]}
  ... | yes p∈l | yes s∈r = yes (_●_⧺_ {prefix} {[]} {prefix ++ []} p∈l s∈r refl)
  ... | yes p∈l | no ¬s∈r = no (∈⟦-●-no-split-end-r l r loc prefix noShorter ¬s∈r)
  ... | no ¬p∈l | _ = no noSplitEndL
    where
      noSplitEndL : ((prefix ++ []) ∈⟦ l ● r ` loc ⟧) → ⊥
      noSplitEndL p = noSplitL' l r loc prefix noShorter ¬p∈l w₁ w₂ w₁w₂≡w w₁∈l w₂∈r
        where
          elim = ∈⟦-●-elim {l = l} {r = r} {w = prefix ++ []} {loc} p
          w₁ = proj₁ elim
          w₂ = proj₁ (proj₂ elim)
          w₁∈l = proj₁ (proj₂ (proj₂ elim))
          w₂∈r = proj₁ (proj₂ (proj₂ (proj₂ elim)))
          w₁w₂≡w = proj₂ (proj₂ (proj₂ (proj₂ elim)))
  ∈⟦-●-search l r loc prefix (d ∷ ds) noShorter with ∈⟦-decides {l} {prefix} | ∈⟦-decides {r} {d ∷ ds}
  ... | yes p∈l | yes p∈r = yes (_●_⧺_ {prefix} {d ∷ ds} {prefix ++ (d ∷ ds)} p∈l p∈r refl)
  ... | yes p∈l | no ¬p∈r = subst (λ w → Dec (w ∈⟦ l ● r ` loc ⟧)) (++-assoc prefix [ d ] ds) (∈⟦-●-search l r loc (prefix ++ [ d ]) ds noShorter')
    where
      noShorter' : NoShorter l r (prefix ++ [ d ]) ds
      noShorter' {w₁} {w₂} w₁w₂≡w₁' w₁⊏pfx'd w₁∈l w₂∈r with ⊏-split w₁⊏pfx'd
      ... | inj₁ w₁⊏pfx = noShorter (trans w₁w₂≡w₁' (++-assoc prefix [ d ] ds)) w₁⊏pfx w₁∈l w₂∈r
      ... | inj₂ w₁≡pfx rewrite w₁≡pfx = inj2-yes-pfx r prefix w₂ d ds (trans w₁w₂≡w₁' (++-assoc prefix [ d ] ds)) ¬p∈r w₂∈r
  ... | no ¬p∈l | _ = subst (λ w → Dec (w ∈⟦ l ● r ` loc ⟧)) (++-assoc prefix [ d ] ds) (∈⟦-●-search l r loc (prefix ++ [ d ]) ds noShorter')
    where
      noShorter' : NoShorter l r (prefix ++ [ d ]) ds
      noShorter' {w₁} {w₂} w₁w₂≡w₁' w₁⊏pfx'd w₁∈l w₂∈r with ⊏-split {w₁} {prefix} {d} w₁⊏pfx'd
      ... | inj₁ w₁⊏pfx = noShorter (trans w₁w₂≡w₁' (++-assoc prefix [ d ] ds)) w₁⊏pfx w₁∈l w₂∈r
      ... | inj₂ w₁≡pfx = ¬p∈l (subst (_∈⟦ l ⟧) w₁≡pfx w₁∈l)

  -- No valid split when suffix is [] and []∉⟦r⟧.
  -- IDEA:  Eliminate ● to get w₁++w₂≡prefix with w₂∈⟦r⟧. If w₂=[], then []∈⟦r⟧ contradicts ¬s∈r.
  --        If w₂≢[], use NoShorter: w₁ must be a proper prefix of prefix.
  -- USED:  ∈⟦-●-search when prefix∈⟦l⟧ but []∉⟦r⟧.
  ∈⟦-●-no-split-end-r : (l r : RE) (loc : ℕ) (prefix : List Char)
    → NoShorter l r prefix []
    → ¬([] ∈⟦ r ⟧) → ((prefix ++ []) ∈⟦ l ● r ` loc ⟧) → ⊥
  ∈⟦-●-no-split-end-r l r loc prefix noShorter ¬s∈r p = noSplitR' l r loc prefix noShorter ¬s∈r w₁ w₂ w₁∈l w₂∈r w₁w₂≡w
    where
      elim = ∈⟦-●-elim {l = l} {r = r} {w = prefix ++ []} {loc} p
      w₁ = proj₁ elim
      w₂ = proj₁ (proj₂ elim)
      w₁∈l = proj₁ (proj₂ (proj₂ elim))
      w₂∈r = proj₁ (proj₂ (proj₂ (proj₂ elim)))
      w₁w₂≡w = proj₂ (proj₂ (proj₂ (proj₂ elim)))

 -- Helper: from a split w₁++w₂≡prefix with w₁∈⟦l⟧, w₂∈⟦r⟧, derive contradiction.
  -- IDEA:  If w₂=[], then []∈⟦r⟧ contradicts ¬s∈r. If w₂≢[], show w₁≢prefix (cancel-left)
  --        hence w₁⊏prefix, invoking NoShorter.
  -- USED:  ∈⟦-●-no-split-end-r.
  noSplitR' : (l r : RE) (loc : ℕ) (prefix : List Char) → NoShorter l r prefix [] → ¬([] ∈⟦ r ⟧) → (w₁ w₂ : List Char) → w₁ ∈⟦ l ⟧ → w₂ ∈⟦ r ⟧ → w₁ ++ w₂ ≡ prefix ++ [] → ⊥
  noSplitR' l r loc pfx noSh ¬s w₁ [] wl wr _ = ¬s wr
  noSplitR' l r loc prefix noShorter ¬s∈r w₁ (d ∷ ds) w₁∈l w₂∈r w₁w₂≡w =
       noShorter w₁w₂≡w w₁⊏prefix w₁∈l w₂∈r
       where
         w₁≢pfx : w₁ ≢ prefix
         w₁≢pfx w₁≡pfx = Utils.¬∷≡[] (cancel-left prefix (d ∷ ds) [] (trans (sym (cong (_++ d ∷ ds) w₁≡pfx)) w₁w₂≡w))
         w₁⊏prefix : w₁ ⊏ prefix
         w₁⊏prefix = ⊏-from-split≢ (trans w₁w₂≡w (++-identityʳ prefix)) w₁≢pfx

  -- No valid split when suffix is [] and prefix∉⟦l⟧.
  -- IDEA:  Eliminate ● to get w₁++w₂≡prefix. If w₁≡prefix then w₁∈⟦l⟧ contradicts ¬p∈l.
  --        Otherwise use NoShorter.
  -- USED:  ∈⟦-●-search when prefix∉⟦l⟧ and suffix is [].
  ∈⟦-●-no-split-end-l : (l r : RE) (loc : ℕ) (prefix : List Char)
    → NoShorter l r prefix []
    → ¬(prefix ∈⟦ l ⟧) → ((prefix ++ []) ∈⟦ l ● r ` loc ⟧) → ⊥
  ∈⟦-●-no-split-end-l l r loc prefix noShorter ¬p∈l p =
      noSplitL' l r loc prefix noShorter ¬p∈l w₁ w₂ w₁w₂≡w w₁∈l w₂∈r
      where
        elim = ∈⟦-●-elim {l = l} {r = r} {w = prefix ++ []} {loc} p
        w₁ = proj₁ elim
        w₂ = proj₁ (proj₂ elim)
        w₁∈l = proj₁ (proj₂ (proj₂ elim))
        w₂∈r = proj₁ (proj₂ (proj₂ (proj₂ elim)))
        w₁w₂≡w = proj₂ (proj₂ (proj₂ (proj₂ elim)))

  -- Helper: from a split w₁++w₂≡prefix with w₁∈⟦l⟧, w₂∈⟦r⟧, derive contradiction.
  -- IDEA:  If w₁=[], then w₁∈⟦l⟧ with []≡prefix gives []∈⟦l⟧; if prefix≡[], ¬p∈l fires.
  --        If w₁≡prefix, rewrite to get prefix∈⟦l⟧ contradicting ¬p∈l.
  --        If w₁ is short and w₂≢[], use NoShorter.
  -- USED:  ∈⟦-●-no-split-end-l.
  noSplitL' : (l r : RE) (loc : ℕ) (prefix : List Char) → NoShorter l r prefix [] → ¬(prefix ∈⟦ l ⟧) → (w₁ w₂ : List Char) → (w₁ ++ w₂ ≡ prefix ++ []) → w₁ ∈⟦ l ⟧ → w₂ ∈⟦ r ⟧ → ⊥
  noSplitL' l r loc [] noShorter ¬p∈l [] w₂ w₁w₂≡w w₁∈l w₂∈r = ¬p∈l w₁∈l
  noSplitL' l r loc (c ∷ cs) noShorter ¬p∈l [] w₂ w₁w₂≡w w₁∈l w₂∈r = noShorter w₁w₂≡w ⊏-nil w₁∈l w₂∈r
  noSplitL' l r loc prefix noShorter ¬p∈l w₁ [] w₁w₂≡w w₁∈l w₂∈r = ¬p∈l (subst (_∈⟦ l ⟧) w₁≡prefix w₁∈l)
    where
      w₁≡prefix : w₁ ≡ prefix
      w₁≡prefix = trans (sym (++-identityʳ w₁)) (trans w₁w₂≡w (++-identityʳ prefix))
  noSplitL' l r loc prefix noShorter ¬p∈l w₁ (d ∷ ds) w₁w₂≡w w₁∈l w₂∈r =
      noShorter w₁w₂≡w w₁⊏prefix w₁∈l w₂∈r
    where
      w₁≢pfx : w₁ ≢ prefix
      w₁≢pfx w₁≡pfx = Utils.¬∷≡[] {Char} {d} {ds} (sym (cancel-left prefix [] (d ∷ ds) p))
        where
          p : prefix ++ [] ≡ prefix ++ (d ∷ ds)
          p = sym (trans (sym (cong (_++ d ∷ ds) w₁≡pfx)) w₁w₂≡w)
      w₁⊏prefix : w₁ ⊏ prefix
      w₁⊏prefix = ⊏-from-split≢ (trans w₁w₂≡w (++-identityʳ prefix)) w₁≢pfx

  -- Empty word always matches r* (via the ε-branch of the internal +).
  -- IDEA:  r* = (ε + r●r*)* ; take the ε-branch of the outer +, wrapped in _*.
  -- USED:  ∈⟦-*-decides for []; ∈⟦-*-search base cases.
  ∈⟦-*-empty-r* : (r : RE) (nε : ε∉ r) (loc : ℕ) → [] ∈⟦ r * nε ` loc ⟧
  ∈⟦-*-empty-r* r nε loc = _* (_+L_ (r ● (_*_`_ r nε loc) ` loc) ε)

  -- Decidable membership for Kleene star: [] always matches; non-empty delegates to search.
  -- IDEA:  For (c∷cs), scan for a prefix matching r, then recurse on r* for the remainder.
  -- USED:  ∈⟦-decides for r*; ∈⟦-*-search calls it recursively.
  ∈⟦-*-decides : (r : RE) (nε : ε∉ r) (loc : ℕ) (w : List Char) → Dec (w ∈⟦ r * nε ` loc ⟧)
  ∈⟦-*-decides r nε loc [] = yes (∈⟦-*-empty-r* r nε loc)
  ∈⟦-*-decides r nε loc (c ∷ cs) = ∈⟦-*-search r nε loc [] (c ∷ cs) noShorterInit
    where
      noShorterInit : NoShorter r (r * nε ` loc) [] (c ∷ cs)
      noShorterInit {w₁} {w₂} _ w₁⊏[] _ _ = ⊥-elim (⊏-absurd w₁⊏[])

  -- Incremental search for r* membership, extending prefix character by character.
  -- IDEA:  Maintain NoShorter. At each step, if prefix∈⟦r⟧ try suffix∈⟦r*⟧; if prefix∉⟦r⟧,
  --        extend prefix by one character. If suffix=[] and prefix∉⟦r⟧, use ∈⟦-*-no-split-end.
  -- USED:  ∈⟦-*-decides for non-empty words.
  ∈⟦-*-search : (r : RE) (nε : ε∉ r) (loc : ℕ) (prefix suffix : List Char)
    → NoShorter r (r * nε ` loc) prefix suffix
    → Dec ((prefix ++ suffix) ∈⟦ r * nε ` loc ⟧)
  ∈⟦-*-search r nε loc [] [] noShorter = yes (∈⟦-*-empty-r* r nε loc)
  ∈⟦-*-search r nε loc (d ∷ ds) [] noShorter with ∈⟦-decides {r} {d ∷ ds}
  ... | yes p∈r = yes (_* (ε +R (_●_⧺_ {d ∷ ds} {[]} {d ∷ ds ++ []} p∈r (∈⟦-*-empty-r* r nε loc) refl)))
  ... | no ¬p∈r = no (λ p → ∈⟦-*-no-split-end r nε loc (d ∷ ds) noShorter ¬p∈r Utils.¬∷≡[] (subst (_∈⟦ r * nε ` loc ⟧) (++-identityʳ (d ∷ ds)) p))
  ∈⟦-*-search r nε loc prefix (d ∷ ds) noShorter with ∈⟦-decides {r} {prefix}
  ... | no ¬p∈r = subst (λ w → Dec (w ∈⟦ r * nε ` loc ⟧)) (++-assoc prefix [ d ] ds) (∈⟦-*-search r nε loc (prefix ++ [ d ]) ds noShorter')
    where
      noShorter' : NoShorter r (r * nε ` loc) (prefix ++ [ d ]) ds
      noShorter' {w₁} {w₂} w₁w₂≡w₁' w₁⊏pfx'd w₁∈r w₂∈r* = noShorter-help w₁w₂≡w₁' w₁⊏pfx'd w₁∈r w₂∈r*
        where
          noShorter-help : w₁ ++ w₂ ≡ (prefix ++ [ d ]) ++ ds → w₁ ⊏ (prefix ++ [ d ]) → w₁ ∈⟦ r ⟧ → w₂ ∈⟦ r * nε ` loc ⟧ → ⊥
          noShorter-help w₁w₂≡w₁' w₁⊏pfx'd w₁∈r w₂∈r* with ⊏-split {w₁} {prefix} {d} w₁⊏pfx'd
          ... | inj₁ w₁⊏pfx = noShorter (trans w₁w₂≡w₁' (++-assoc prefix [ d ] ds)) w₁⊏pfx w₁∈r w₂∈r*
          ... | inj₂ w₁≡pfx = ¬p∈r (subst (_∈⟦ r ⟧) w₁≡pfx w₁∈r)
  ... | yes p∈r with ∈⟦-*-decides r nε loc (d ∷ ds)
  ... | yes rest∈ = yes (_* (ε +R (_●_⧺_ {prefix} {d ∷ ds} {prefix ++ (d ∷ ds)} p∈r rest∈ refl)))
  ... | no ¬rest∈ = subst (λ w → Dec (w ∈⟦ r * nε ` loc ⟧)) (++-assoc prefix [ d ] ds) (∈⟦-*-search r nε loc (prefix ++ [ d ]) ds noShorter')
    where
      noShorter' : NoShorter r (r * nε ` loc) (prefix ++ [ d ]) ds
      noShorter' {w₁} {w₂} w₁w₂≡w₁' w₁⊏pfx'd w₁∈r w₂∈r* with ⊏-split {w₁} {prefix} {d} w₁⊏pfx'd
      ... | inj₁ w₁⊏pfx = noShorter (trans w₁w₂≡w₁' (++-assoc prefix [ d ] ds)) w₁⊏pfx w₁∈r w₂∈r*
      ... | inj₂ w₁≡pfx = inj₂-help w₁≡pfx w₁w₂≡w₁' w₂∈r*
        where
          inj₂-help : (w₁≡pfx : w₁ ≡ prefix) → (w₁w₂≡w₁' : w₁ ++ w₂ ≡ (prefix ++ [ d ]) ++ ds) → (w₂∈r* : w₂ ∈⟦ r * nε ` loc ⟧) → ⊥
          inj₂-help w₁≡pfx w₁w₂≡w₁' w₂∈r* = ¬rest∈ (subst (_∈⟦ r * nε ` loc ⟧) w₂≡d∷ds w₂∈r*)
            where
              w₂≡d∷ds : w₂ ≡ d ∷ ds
              w₂≡d∷ds = cancel-left prefix w₂ ([ d ] ++ ds) (trans (trans (sym (cong (_++ w₂) w₁≡pfx)) w₁w₂≡w₁') (++-assoc prefix [ d ] ds))

  -- No r* match when suffix=[], prefix≢[], and prefix∉⟦r⟧.
  -- IDEA:  Eliminate _*: if the ε-branch fires, prefix≡[] contradicts prefix≢[].
  --        If the ●-branch fires, use ∈⟦-*-no-split-end-●.
  -- USED:  ∈⟦-*-search when prefix∉⟦r⟧ and suffix=[].
  ∈⟦-*-no-split-end : (r : RE) (nε : ε∉ r) (loc : ℕ) (prefix : List Char)
    → NoShorter r (r * nε ` loc) prefix []
    → ¬(prefix ∈⟦ r ⟧) → prefix ≢ [] → (prefix ∈⟦ r * nε ` loc ⟧) → ⊥
  ∈⟦-*-no-split-end r nε loc prefix noShorter ¬p∈r prefix≢[] (_* ((r ● (r * nε ` loc) ` loc) +L p∈ε)) =
    prefix≢[] (sym (∈⟦-ε-elim p∈ε))
  ∈⟦-*-no-split-end r nε loc prefix noShorter ¬p∈r prefix≢[] (_* (p +R p∈●)) =
    ∈⟦-*-no-split-end-● r nε loc prefix noShorter ¬p∈r p∈●

  -- No r* match when suffix=[] and prefix∉⟦r⟧ but prefix∈⟦r●r*⟧.
  -- IDEA:  Eliminate ●: if w₂=[], then w₁∈⟦r⟧ with w₁≡prefix contradicts ¬(prefix∈⟦r⟧).
  --        If w₂≢[], use NoShorter via ⊏-from-split≢.
  -- USED:  ∈⟦-*-no-split-end when the ●-branch fires.
  ∈⟦-*-no-split-end-● : (r : RE) (nε : ε∉ r) (loc : ℕ) (prefix : List Char)
    → NoShorter r (r * nε ` loc) prefix [] → ¬(prefix ∈⟦ r ⟧)
    → prefix ∈⟦ r ● (r * nε ` loc) ` loc ⟧ → ⊥
  ∈⟦-*-no-split-end-● r nε loc prefix noShorter ¬p∈r p∈● with ∈⟦-●-elim p∈●
  ... | w₁ , [] , w₁∈r , w₂∈r* , w₁w₂≡prefix = ¬p∈r (subst (_∈⟦ r ⟧) (trans (sym (++-identityʳ w₁)) w₁w₂≡prefix) w₁∈r)
  ... | w₁ , d ∷ ds , w₁∈r , w₂∈r* , w₁w₂≡prefix = noShorter (subst (λ w → w₁ ++ (d ∷ ds) ≡ w) (sym (++-identityʳ prefix)) w₁w₂≡prefix) w₁⊏prefix w₁∈r w₂∈r*
    where
      w₁⊏prefix : w₁ ⊏ prefix
      w₁⊏prefix = ⊏-from-split≢ w₁w₂≡prefix (λ w₁≡prefix → ⊥-elim (¬p∈r (subst (_∈⟦ r ⟧) w₁≡prefix w₁∈r)))


-- Main ∈⟦→⇒ function

-- Decide whether a longer valid POSIX split exists beyond a given prefix.
-- IDEA:  Recursively extend prefix by one character. If prefix++[d]∈⟦l⟧ ∧ ds∈⟦r⟧,
--        return [d] as the witness. Otherwise recurse on prefix++[d] with suffix ds.
--        In the no case, show that any candidate split w₃≡d'∷v' must have d'≡d (∷-injective)
--        and reduce to the recursive ¬longer or to ¬(prefix++[d]∈⟦l⟧).
-- USED:  find-longest-split repeatedly calls it to extend the split until maximal.
∈⟦-longer-split : (l r : RE) (prefix suffix : List Char)
  → Dec (∃[ w₃ ] ∃[ w₄ ] (¬ w₃ ≡ []) × (w₃ ++ w₄ ≡ suffix) × ((prefix ++ w₃) ∈⟦ l ⟧) × w₄ ∈⟦ r ⟧)
∈⟦-longer-split l r prefix [] = no (λ { (_ , _ , ¬w₃≡[] , w₃w₄≡[] , _ , _) → ¬w₃≡[] (++-nilˡ w₃w₄≡[]) })
  where
    -- If xs++ys≡[] then xs≡[]: ++ cannot shrink a non-empty left operand.
    -- IDEA:  Induction on xs; c∷xs ++ ys is non-empty.
    -- USED:  ∈⟦-longer-split base case (suffix=[]): rules out w₃≢[].
    ++-nilˡ : ∀ {xs ys} → xs ++ ys ≡ [] → xs ≡ []
    ++-nilˡ {[]} {ys} refl = refl
    ++-nilˡ {c ∷ xs} {ys} ()
∈⟦-longer-split l r prefix (d ∷ ds) with ∈⟦-longer-split l r (prefix ++ [ d ]) ds
... | yes (v , rest , ¬v≡[] , v++rest≡ds , p++dv∈l , rest∈r) =
        yes ((d ∷ v) , rest , (λ ()) ,
             (cong (d ∷_) v++rest≡ds) ,
             (subst (_∈⟦ l ⟧) (++-assoc prefix [ d ] v) p++dv∈l) ,
             rest∈r)
... | no ¬longer with ∈⟦-decides {l} {prefix ++ [ d ]} | ∈⟦-decides {r} {ds}
... | yes p++d∈l | yes ds∈r = yes ([ d ] , ds , (λ ()) , refl , p++d∈l , ds∈r)
... | no ¬p++d∈l | _ = no no-ext
  where
    no-ext : ¬ (∃[ w₃ ] ∃[ w₄ ] (¬ w₃ ≡ []) × (w₃ ++ w₄ ≡ d ∷ ds) × ((prefix ++ w₃) ∈⟦ l ⟧) × w₄ ∈⟦ r ⟧)
    no-ext ([] , _ , ¬[]≡[] , _) = ¬[]≡[] refl
    no-ext (d' ∷ [] , rest , _ , eq , p++dv∈l , rest∈r) =
      let d'≡d , []++rest≡ds = ∷-injective eq
          p++d∈l' = subst (_∈⟦ l ⟧) (cong (λ c → prefix ++ c ∷ []) d'≡d) p++dv∈l
      in ¬p++d∈l p++d∈l'
    no-ext (d' ∷ (c ∷ v'') , rest , _ , eq , p++dv∈l , rest∈r) =
      let d'≡d , cv''++rest≡ds = ∷-injective eq
          p++dv∈l' = subst (_∈⟦ l ⟧) (cong (λ c' → prefix ++ c' ∷ c ∷ v'') d'≡d) p++dv∈l
          p++dv∈l'' = subst (_∈⟦ l ⟧) (sym (++-assoc prefix [ d ] (c ∷ v''))) p++dv∈l'
      in ¬longer ((c ∷ v'') , rest , (λ ()) , cv''++rest≡ds ,
                  p++dv∈l'' ,
                  rest∈r)
... | yes _ | no ¬ds∈r = no no-ext
  where
    no-ext : ¬ (∃[ w₃ ] ∃[ w₄ ] (¬ w₃ ≡ []) × (w₃ ++ w₄ ≡ d ∷ ds) × ((prefix ++ w₃) ∈⟦ l ⟧) × w₄ ∈⟦ r ⟧)
    no-ext ([] , _ , ¬[]≡[] , _) = ¬[]≡[] refl
    no-ext (d' ∷ [] , rest , _ , eq , p++dv∈l , rest∈r) =
      let d'≡d , []++rest≡ds = ∷-injective eq in
      ¬ds∈r (subst (_∈⟦ r ⟧) []++rest≡ds rest∈r)
    no-ext (d' ∷ (c ∷ v'') , rest , _ , eq , p++dv∈l , rest∈r) =
      let d'≡d , cv''++rest≡ds = ∷-injective eq
          p++dv∈l' = subst (_∈⟦ l ⟧) (cong (λ c' → prefix ++ c' ∷ c ∷ v'') d'≡d) p++dv∈l
          p++dv∈l'' = subst (_∈⟦ l ⟧) (sym (++-assoc prefix [ d ] (c ∷ v''))) p++dv∈l'
      in ¬longer ((c ∷ v'') , rest , (λ ()) , cv''++rest≡ds ,
                  p++dv∈l'' ,
                  rest∈r)

-- Starting from a valid split (w₁, w₂), find the POSIX longest-match split.
-- IDEA:  Repeatedly ask ∈⟦-longer-split whether a longer valid split exists.
--        If yes, merge w₃ into the left half and recurse. If no, we're at the maximum.
--        Marked {-# TERMINATING #-} because termination follows from suffix shrinking,
--        not from Agda's structural recursion checker.
-- USED:  ∈⟦→⇒●-go and ∈⟦→⇒*-go to obtain the longest split with longest-ev proof.
{-# TERMINATING #-}
find-longest-split : (l r : RE) (full w₁ w₂ : List Char)
  → w₁ ∈⟦ l ⟧ → w₂ ∈⟦ r ⟧ → w₁ ++ w₂ ≡ full
  → Σ (List Char) (λ w₁' → Σ (List Char) (λ w₂' →
      w₁' ∈⟦ l ⟧ × w₂' ∈⟦ r ⟧ × w₁' ++ w₂' ≡ full ×
      ¬(∃[ w₃ ] ∃[ w₄ ] (¬ w₃ ≡ []) × (w₃ ++ w₄ ≡ w₂') × ((w₁' ++ w₃) ∈⟦ l ⟧) × w₄ ∈⟦ r ⟧)))
find-longest-split l r full w₁ w₂ w₁∈l w₂∈r w₁w₂≡full with ∈⟦-longer-split l r w₁ w₂
... | yes (w₃ , w₄ , ¬w₃≡[] , w₃w₄≡w₂ , w₁w₃∈l , w₄∈r) =
      find-longest-split l r full (w₁ ++ w₃) w₄
        w₁w₃∈l
        w₄∈r
        (trans (++-assoc w₁ w₃ w₄) (trans (cong (w₁ ++_) w₃w₄≡w₂) w₁w₂≡full))
... | no ¬longer = w₁ , w₂ , w₁∈l , w₂∈r , w₁w₂≡full , ¬longer

-- Main construction: from membership evidence w∈⟦r⟧ build a POSIX parse tree proof w,r⇒u.
-- IDEA:  Structural recursion on regex structure. For +, decide which side matches.
--        For ●, use ∈⟦-●-elim then find-longest-split. For *, decompose via elim-star.
--        Marked {-# TERMINATING #-} because the mutual recursion on r is not structurally
--        decreasing in Agda's checker (it goes through the semantic definition of r*).
-- USED:  Top-level entry point for the entire membership-to-parse-tree conversion.
{-# TERMINATING #-}
mutual
  ∈⟦→⇒ : ∀ {r : RE} {w : List Char} → w ∈⟦ r ⟧ → Σ (U r) (λ u → w , r ⇒ u)
  ∈⟦→⇒ {ε} {[]} ε = EmptyU , p₁
  ∈⟦→⇒ {$ c ` loc} {c ∷ []} ($ c) = LetterU c , pc

  ∈⟦→⇒ {l + r ` loc} {w} w∈lr with ∈⟦-decides {l} {w}
  ... | no ¬w∈l = RightU (proj₁ result₂) , p+r (proj₂ result₂) ¬w∈l
    where
      result₂ = ∈⟦→⇒ (plus-right-member w∈lr ¬w∈l)
  ... | yes w∈l = LeftU (proj₁ result₁) , p+l (proj₂ result₁)
    where
      result₁ = ∈⟦→⇒ w∈l

  ∈⟦→⇒ {l ● r ` loc} {w} w∈lr = ∈⟦→⇒●-go l r loc w (∈⟦-●-elim w∈lr)

  ∈⟦→⇒ {r * nε ` loc} {[]} _ = ListU [] , p[]
  ∈⟦→⇒ {r * nε ` loc} {c ∷ cs} w∈r* = ∈⟦→⇒*-go r nε loc (c ∷ cs) (*-fb w∈r*)

  *-fb : ∀ {r : RE} {nε : ε∉ r} {loc : ℕ} {c : Char} {cs : List Char}
    → (c ∷ cs) ∈⟦ r * nε ` loc ⟧
    → Σ (List Char) (λ w₁ → Σ (List Char) (λ w₂ → w₁ ∈⟦ r ⟧ × w₂ ∈⟦ r * nε ` loc ⟧ × w₁ ++ w₂ ≡ c ∷ cs))
  *-fb w∈r* with elim-star w∈r*
  ... | inj₁ w∈ε = ⊥-elim (Utils.¬∷≡[] (sym (∈⟦-ε-elim w∈ε)))
  ... | inj₂ w∈● = ∈⟦-●-elim w∈●

  -- Concatenation case: given a split of full, find the POSIX longest-match split.
  -- IDEA:  Feed the split into find-longest-split to obtain (w₁',w₂') with longest-ev.
  --        Recursively build parse trees for each side, then combine with PairU and ps.
  -- USED:  ∈⟦→⇒ for l●r.
  ∈⟦→⇒●-go : (l r : RE) (loc : ℕ) (full : List Char)
    → Σ (List Char) (λ w₁ → Σ (List Char) (λ w₂ → w₁ ∈⟦ l ⟧ × w₂ ∈⟦ r ⟧ × w₁ ++ w₂ ≡ full))
    → Σ (U (l ● r ` loc)) (λ u → full , (l ● r ` loc) ⇒ u)
  ∈⟦→⇒●-go l r loc full fllbk =
    let (w₁ , w₂ , w₁∈l , w₂∈r , w₁w₂≡full , longest-ev) =
          find-longest-split l r full
            (proj₁ fllbk)
            (proj₁ (proj₂ fllbk))
            (proj₁ (proj₂ (proj₂ fllbk)))
            (proj₁ (proj₂ (proj₂ (proj₂ fllbk))))
            (proj₂ (proj₂ (proj₂ (proj₂ fllbk))))
        (u₁ , w₁⇒u₁) = ∈⟦→⇒ w₁∈l
        (u₂ , w₂⇒u₂) = ∈⟦→⇒ w₂∈r
    in PairU u₁ u₂ , ps (sym w₁w₂≡full) w₁⇒u₁ w₂⇒u₂ longest-ev

  -- If w∈⟦r⟧ and r cannot match ε, then w is non-empty.
  -- IDEA:  If w=[], then []∈⟦r⟧ implies ε∈r, contradicting nε. Otherwise w≡[] is absurd by shape.
  -- USED:  p* requires ¬(w₁≡[]); ∈⟦→⇒*-go uses this to show fw₁≢[].
  ¬prefix∈⟦-≡[] : (r : RE) (w : List Char) → w ∈⟦ r ⟧ → ε∉ r → ¬ w ≡ []
  ¬prefix∈⟦-≡[] r [] p∈r nε refl = ([]∈⟦r⟧→¬ε∉r p∈r) nε
  ¬prefix∈⟦-≡[] r (c ∷ cs) p∈r nε ()

  -- Star case: given a split of full, find the POSIX longest-match split.
  -- IDEA:  Feed the split into find-longest-split (r against r*). Build parse trees for
  --        each side, wrap in ListU(u₁∷unListU u₂), use p* with longest-ev and ¬(fw₁≡[]).
  --        The listU∘unListU rewrite adjusts the ⇒-proof to the right ListU shape.
  -- USED:  ∈⟦→⇒ for r* (non-empty case).
  ∈⟦→⇒*-go : (r : RE) (nε : ε∉ r) (loc : ℕ) (full : List Char)
    → Σ (List Char) (λ w₁ → Σ (List Char) (λ w₂ → w₁ ∈⟦ r ⟧ × w₂ ∈⟦ r * nε ` loc ⟧ × w₁ ++ w₂ ≡ full))
    → Σ (U (r * nε ` loc)) (λ u → full , (r * nε ` loc) ⇒ u)
  ∈⟦→⇒*-go r nε loc full fllbk =
    let (fw₁ , fw₂ , fw₁∈r , fw₂∈r* , fw₁w₂≡full , longest-ev) =
          find-longest-split r (r * nε ` loc) full
            (proj₁ fllbk)
            (proj₁ (proj₂ fllbk))
            (proj₁ (proj₂ (proj₂ fllbk)))
            (proj₁ (proj₂ (proj₂ (proj₂ fllbk))))
            (proj₂ (proj₂ (proj₂ (proj₂ fllbk))))
        (u₁ , w₁⇒u₁) = ∈⟦→⇒ fw₁∈r
        (u₂ , w₂⇒u₂) = ∈⟦→⇒ fw₂∈r*
   in ListU (u₁ ∷ unListU u₂) ,
        p* (sym fw₁w₂≡full) w₁⇒u₁
          (subst (λ u → fw₂ , r * nε ` loc ⇒ u) (sym listU∘unListU) w₂⇒u₂)
          (¬prefix∈⟦-≡[] r fw₁ fw₁∈r nε)
          longest-ev

  plus-right-member : ∀ {l r : RE} {loc : ℕ} {w : List Char}
    → (w∈lr : w ∈⟦ l + r ` loc ⟧) → ¬(w ∈⟦ l ⟧) → w ∈⟦ r ⟧
  plus-right-member (_ +L w∈l) ¬w∈l = ⊥-elim (¬w∈l w∈l)
  plus-right-member (_ +R w∈r) ¬w∈l = w∈r

  plus-right-∈⟦→⇒ : ∀ {l r : RE} {loc : ℕ} {w : List Char} {w∈lr : w ∈⟦ l + r ` loc ⟧} {¬w∈l : ¬(w ∈⟦ l ⟧)}
    → proj₁ (∈⟦→⇒ w∈lr) ≡ RightU {l} {r} {loc} (proj₁ (∈⟦→⇒ (plus-right-member w∈lr ¬w∈l)))
  plus-right-∈⟦→⇒ {l} {r} {loc} {w} {w∈lr} {¬w∈l} with ∈⟦-decides {l} {w}
  ... | no _ = refl
  ... | yes w∈l = ⊥-elim (¬w∈l w∈l)

  ∈⟦→⇒-ε : proj₁ (∈⟦→⇒ {ε} {[]} ε) ≡ EmptyU
  ∈⟦→⇒-ε = refl

  ∈⟦→⇒-$ : (c : Char) (loc : ℕ) → proj₁ (∈⟦→⇒ {$ c ` loc} {c ∷ []} ($ c)) ≡ LetterU c
  ∈⟦→⇒-$ c loc = refl

  ∈⟦→⇒-cat-go-det : (l r : RE) (loc : ℕ) (full : List Char) → (fls₁ fls₂ : Σ (List Char) (λ w₁ → Σ (List Char) (λ w₂ → w₁ ∈⟦ l ⟧ × w₂ ∈⟦ r ⟧ × w₁ ++ w₂ ≡ full))) → ∈⟦→⇒●-go l r loc full fls₁ ≡ ∈⟦→⇒●-go l r loc full fls₂
  ∈⟦→⇒-cat-go-det l r loc full fls₁ fls₂ = {!cat-go-det!}

  ∈⟦→⇒-star-go-det : (r : RE) (nε : ε∉ r) (loc : ℕ) (full : List Char) → (fls₁ fls₂ : Σ (List Char) (λ w₁ → Σ (List Char) (λ w₂ → w₁ ∈⟦ r ⟧ × w₂ ∈⟦ r * nε ` loc ⟧ × w₁ ++ w₂ ≡ full))) → ∈⟦→⇒*-go r nε loc full fls₁ ≡ ∈⟦→⇒*-go r nε loc full fls₂
  ∈⟦→⇒-star-go-det r nε loc full fls₁ fls₂ = {!star-go-det!}
```
