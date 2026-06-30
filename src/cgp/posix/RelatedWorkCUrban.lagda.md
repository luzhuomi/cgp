```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.RelatedWorkCUrban where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )

import cgp.Utils as Utils
open Utils using (¬∷≡[] ;
  foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ∷-inj  ;
  w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ ;
  w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ ;
  ¬m>n→n≡m⊎n>m ;
  len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ ; concatmap-λx→[]-xs≡[] ;
  length≡0→[] ; ¬≡[]→¬length≡0 )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ; LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; flat∘unflat ;  unListU ; listU∘unListU ;  ¬|list-u∷us|≡[] ; _⊢_≟_ ; inv-listU1 )

open import Data.Char using (Char; _≟_)
open import Data.List.Base as ListBase hiding ([_])
open ListBase using (List; []; _∷_; _++_; _∷ʳ_)
[_] : Char → List Char
[_] x = x ∷ []
open import Data.List.Properties using (∷ʳ-++ ; ++-cancelˡ ; ++-identityʳ ; ++-identityˡ ; ∷-injective ; ++-assoc ;   length-++ )
open import Relation.Nullary using (¬_ ; contradiction)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality as Eq hiding ([_])
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst; inspect; _≢_)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ ; proj₁ ; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Nat using (  ℕ ; suc ; zero ; _>_ ; _≥_ ; _≤_  ; _+_ ; _<?_ ) 
open import Relation.Nullary.Decidable using (Dec; yes; no)
import Data.Nat.Properties as NatProperties
open import Data.Nat using (_<_ ; _≤_ ; zero ; suc ; _+_ ; _∸_ ; s<s ; z<s ; z≤n ; s≤s)
open import Data.Empty using (⊥ ; ⊥-elim)
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; <-cmp ; +-suc ; +-identityʳ )


import cgp.posix.Order as PosixOrder
open PosixOrder using ( _⊢_>_ ; len-≡ ; len-> ;
  _⊢_>ⁱ_ ; seq₁ ; seq₂ ;
  choice-ll ; choice-rr ;
  choice-lr ;
  choice-rl ; star-head ; star-cons-nil ; star-tail ;
  >→¬≡
  )

import Relation.Nullary as Nullary 
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)



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


```

POSIX parse tree relation

F. Ausaf, R. Dyckhoff, and C. Urban. “POSIX Lexing with Derivatives of Regular Expressions (Proof Pearl)”. In: Proc. of the 7th International Conference on
Interactive Theorem Proving (ITP). Vol. 9807. LNCS. 2016, pp. 69–86.

has the following definition of POSIX relation

P1

-------------------
([], ε) --> EmptyU


PC

-------------------
([c], $ c) --> LetterU c



P + L

(s, r₁) --> v₁
------------------------
(s, r₁ + r₂) --> LeftU v₁


P + R

(s, r₂) --> v₂   s∉ ⟦r₁⟧  
------------------------
(s, r₁ + r₂) --> RightU v₂



PS

(s₁, r₁) --> v₁     (s₂, r₂) --> v₂
¬∃ ( s₃ , s₄ ) . s₃ ≢ [] ∧ (s₃ ++ s₄) ≡ s₂ ∧ (s₁ ++ s₃) ∈⟦ r₁ ⟧ ∧ s₄ ∈⟦ r₂ ⟧ )
------------------------------------------------------------------------------
(s₁ ++ s₂, r₁ ● r₂) --> PairU v₁ v₂



P[]

---------------------------------------
([], r*) --> ListU []


P*

(s1, r) --> v       (s2, r*) --> ListU vs       |v| ≢ []
¬∃ ( s3 , s4 ) . s3 ≢ [] ∧ (s3 ++ s4) ≡ s2 ∧ (s1 ++ s3) ∈⟦ r ⟧ ∧ s4 ∈⟦ r* ⟧ 
-----------------------------------------------------------------------------
(s1 ++ s2, r* ) --> ListU (v ∷ vs)


It seems that the relationship is weaker. It fixes a particular word.



```agda


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
  --        Then recursively build parse trees for each side, then combine with PairU and ps.
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
```



Lemma : a posix parse tree must be flattened to the indexed word. 

```agda

⇒-member : ∀ { r : RE } { v : U r } { w : List Char} 
    → w , r ⇒ v
    → proj₁ (flat {r} v) ≡ w
⇒-member {ε}             {EmptyU}     {[]}      p₁                 = refl
⇒-member {$ c ` loc}     {LetterU .c} {.c ∷ []} (pc .{c} .{loc})   = refl
⇒-member {l ● r ` loc}   {PairU v u}  {w}       (ps {w₁} {w₂} .{w} .{l} .{r} .{loc} .{v} .{u} w≡w₁++w₂ w₁,l→v w₂,r→u longest-ev) = prf
  where
    ind-hyp-l : proj₁ (flat {l} v) ≡ w₁
    ind-hyp-l = ⇒-member w₁,l→v 
    ind-hyp-r : proj₁ (flat {r} u) ≡ w₂
    ind-hyp-r = ⇒-member w₂,r→u
    prf : proj₁ (flat (PairU {l} {r} {loc} v u)) ≡ w
    prf rewrite  ind-hyp-l |  ind-hyp-r = sym w≡w₁++w₂
⇒-member {l + r ` loc}   {LeftU v}  {w}       (p+l .{w} .{l} .{r} .{loc} .{v} w,l→v)       = ⇒-member w,l→v 
⇒-member {l + r ` loc}   {RightU v} {w}       (p+r .{w} .{l} .{r} .{loc} .{v} w,r→v ¬w∈⟦l⟧) = ⇒-member w,r→v 
⇒-member {r * ε∉r ` loc} {ListU []} {[]}      (p[] .{r} .{ε∉r} .{loc}) = refl 
⇒-member {r * ε∉r ` loc} {ListU (x ∷ xs)} {w} (p* {w₁} {w₂} .{w} .{r} .{ε∉r} .{loc} .{x} .{xs} w≡w₁++w₂ w₁,r→x w₂,r*→list-xs ¬w₁≡[] longest-ev) = prf
  where
    ind-hyp-x : proj₁ (flat {r} x) ≡ w₁
    ind-hyp-x = ⇒-member w₁,r→x
    ind-hyp-list-xs : proj₁ (flat {r * ε∉r ` loc} (ListU xs)) ≡ w₂
    ind-hyp-list-xs = ⇒-member w₂,r*→list-xs 
    prf : proj₁ (flat {r * ε∉r ` loc} (ListU (x ∷ xs))) ≡ w
    prf rewrite  ind-hyp-x |  ind-hyp-list-xs = sym w≡w₁++w₂

```

Lemma : a posix parse tree is the max value in posix ordering > 

```agda

⇒→>-max : ∀ { r : RE } { v : U r } { w : List Char} 
    → w , r ⇒ v
    → ( u : U r )
    → ¬ ( v ≡ u )
    → proj₁ (flat v) ≡ proj₁ (flat u) 
    ------------------
    → ( r ⊢ v > u )
⇒→>-max {ε}           {EmptyU}    {[]}      p₁          EmptyU      ¬empty≡empty       refl   = Nullary.contradiction refl ¬empty≡empty
⇒→>-max {$ c ` loc}   {LetterU _} .{c ∷ []} pc          (LetterU _) ¬letter-c≡letter-c refl = Nullary.contradiction refl ¬letter-c≡letter-c
⇒→>-max {l + r ` loc} {LeftU v}   {w}       (p+l w,l→v) (LeftU u)   ¬left-v≡left-u     |left-v|≡|left-u|  = len-≡  len|left-v|≡len|left-u| (choice-ll v>u )
  where
    len|left-v|≡len|left-u| : length (proj₁ (flat (LeftU {l} {r} {loc} v))) ≡ length (proj₁ (flat (LeftU {l} {r} {loc} u)))
    len|left-v|≡len|left-u| rewrite |left-v|≡|left-u| = refl

    ¬v≡u : ¬ v ≡ u
    ¬v≡u v≡u = ¬left-v≡left-u (cong LeftU v≡u) 

    v>u : l ⊢ v > u
    v>u = ⇒→>-max {l} {v} {w} w,l→v u ¬v≡u |left-v|≡|left-u|

⇒→>-max {l + r ` loc} {RightU v}   {w}       (p+r w,r→v ¬w∈⟦l⟧) (RightU u)   ¬right-v≡right-u     |right-v|≡|right-u|  = len-≡  len|right-v|≡len|right-u| (choice-rr v>u )
  where
    len|right-v|≡len|right-u| : length (proj₁ (flat (RightU {l} {r} {loc} v))) ≡ length (proj₁ (flat (RightU {l} {r} {loc} u)))
    len|right-v|≡len|right-u| rewrite |right-v|≡|right-u| = refl

    ¬v≡u : ¬ v ≡ u
    ¬v≡u v≡u = ¬right-v≡right-u (cong RightU v≡u) 

    v>u : r ⊢ v > u
    v>u = ⇒→>-max {r} {v} {w} w,r→v u ¬v≡u |right-v|≡|right-u|


⇒→>-max {l + r ` loc} {RightU v}   {w}       (p+r w,r→v ¬w∈⟦l⟧) (LeftU u)   ¬right-v≡left-u     |right-v|≡|left-u|  = Nullary.contradiction w∈⟦l⟧ ¬w∈⟦l⟧
  where
    |left-u|≡w : proj₁ (flat {l + r ` loc} (LeftU {l} {r} {loc} u)) ≡ w
    |left-u|≡w rewrite (sym  |right-v|≡|left-u| )  =  ⇒-member (p+r {w} {l} {r} {loc} {v}  w,r→v ¬w∈⟦l⟧)
    w∈⟦l⟧ : w ∈⟦ l ⟧
    w∈⟦l⟧ rewrite (sym |left-u|≡w) =  proj₂ (flat {l} u)  

⇒→>-max {l + r ` loc} {LeftU v}   {w}       (p+l w,l→v) (RightU u)   ¬left-v≡Right-u     |left-v|≡|right-u|  = len-≡  len|left-v|≡len|right-u| (choice-lr len|v|≥len|u| )
  where
    len|left-v|≡len|right-u| : length (proj₁ (flat (LeftU {l} {r} {loc} v))) ≡ length (proj₁ (flat (RightU {l} {r} {loc} u)))
    len|left-v|≡len|right-u| rewrite |left-v|≡|right-u| = refl

    len|v|≥len|u| : length (proj₁ (flat {l} v)) ≥ length (proj₁ (flat {r} u))
    len|v|≥len|u| rewrite |left-v|≡|right-u| = ≤-refl  


⇒→>-max {r * ε∉r ` loc} {ListU []} {[]}             (p[] .{r} .{ε∉r} .{loc}) (ListU []) ¬list-[]≡list-[] |list-[]|≡|list-[]| = Nullary.contradiction refl ¬list-[]≡list-[]

⇒→>-max {r * ε∉r ` loc} {ListU []} {[]}             (p[] .{r} .{ε∉r} .{loc}) (ListU (u ∷ us)) ¬list-[]≡list-u∷us |list-[]|≡|list-u∷us| =  Nullary.contradiction  (sym  |list-[]|≡|list-u∷us|)  (¬|list-u∷us|≡[] {r} {ε∉r} {loc} {u} {us})

⇒→>-max {r * ε∉r ` loc} {ListU (v ∷ vs)}  {w}  (p*  {w₁} {w₂} .{w} {r} {ε∉r} {loc} .{v} .{vs} w≡w₁++w₂ w₁,r→v w₂,r*→list-vs ¬w₁≡[] longest-ev) (ListU []) ¬list-v∷vs≡list-[] |list-v∷vs|≡|list-[]| =  Nullary.contradiction  |list-v∷vs|≡|list-[]| (¬|list-u∷us|≡[] {r} {ε∉r} {loc} {v} {vs}) 

⇒→>-max {r * ε∉r ` loc} {ListU (v ∷ vs)}  {w}  (p*  {w₁} {w₂} .{w} {r} {ε∉r} {loc} .{v} .{vs} w≡w₁++w₂ w₁,r→v w₂,r*→list-vs ¬w₁≡[] longest-ev) (ListU (u ∷ us)) ¬list-v∷vs≡list-u∷us |list-v∷vs|≡|list-u∷us| = len-≡ len|left-v∷vs|≡len|left-u∷us| list-v∷vs>ˡlist-u∷us 
  where
    len|left-v∷vs|≡len|left-u∷us| : length (proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ vs)))) ≡ length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ us))))
    len|left-v∷vs|≡len|left-u∷us| rewrite |list-v∷vs|≡|list-u∷us| = refl
    list-v∷vs>ˡlist-u∷us : (r * ε∉r ` loc) ⊢ ListU (v ∷ vs) >ⁱ ListU (u ∷ us)
    list-v∷vs>ˡlist-u∷us with length (proj₁ (flat v)) <? length (proj₁ (flat u))
    ... | yes len|v|<len|u| rewrite sym (⇒-member w₂,r*→list-vs) | sym (⇒-member w₁,r→v)
          = Nullary.contradiction anti-longest-ev  longest-ev 

        where
          anti-longest-ev-part1 : ∃[ w₅ ] ( ¬ w₅ ≡ [] ) ×
                                          ( (proj₁ (flat {r} v)) ++ w₅ ≡ (proj₁ (flat {r} u)) ) ×
                                          ( (proj₁ (flat {r * ε∉r ` loc} (ListU vs))) ≡ w₅ ++ (proj₁ (flat {r * ε∉r ` loc} (ListU us)))) 
          anti-longest-ev-part1 rewrite sym (⇒-member w₂,r*→list-vs)  = w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ {proj₁ (flat {r} v)} {proj₁ (flat {r * ε∉r ` loc} (ListU vs))} {proj₁ (flat {r} u)} {proj₁ (flat {r * ε∉r ` loc} (ListU us))}  |list-v∷vs|≡|list-u∷us|   len|v|<len|u|
          anti-longest-ev : ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) ×
                                            ( w₃ ++ w₄ ≡ proj₁ (flat {r * ε∉r ` loc} (ListU vs)) ) ×
                                            ( ( (proj₁ (flat {r} v)) ++ w₃ ) ∈⟦ r ⟧ ) ×
                                            ( w₄ ∈⟦ r * ε∉r ` loc ⟧ ) 
          anti-longest-ev = (proj₁ anti-longest-ev-part1 , ( (proj₁ (flat {r * ε∉r ` loc} (ListU us))) ,
                                      ( proj₁ (proj₂ anti-longest-ev-part1 ) ) ,
                                         ( sym (proj₂ (proj₂ (proj₂ anti-longest-ev-part1))) ,
                                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦r⟧  , proj₂ (flat { r * ε∉r ` loc}  (ListU us))   ) ) )
                          where
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦r⟧ : (proj₁ (flat v) ++ proj₁ anti-longest-ev-part1)  ∈⟦ r ⟧
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦r⟧ rewrite (proj₁ (proj₂ (proj₂  anti-longest-ev-part1 ))) =  proj₂ (flat {r} u) 
          
    ... | no ¬len|v|<len|u| with (¬m>n→n≡m⊎n>m ¬len|v|<len|u|)
    ...                      | inj₂ len|v|>len|u| = star-head (len-> len|v|>len|u|)
    ...                      | inj₁ len|v|≡len|u| with r ⊢ v ≟ u
    ...                                            | no ¬v≡u = star-head (⇒→>-max  w₁,r→v u ¬v≡u  (proj₁ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |list-v∷vs|≡|list-u∷us| len|v|≡len|u|)) )
    ...                                            | yes v≡u = star-tail v≡u (⇒→>-max w₂,r*→list-vs (ListU us)  ¬list-vs≡list-us  (proj₂ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |list-v∷vs|≡|list-u∷us| len|v|≡len|u|)))
                                                         where
                                                           ¬list-vs≡list-us : ¬ (ListU {r}  {ε∉r} {loc} vs) ≡ (ListU {r}  {ε∉r} {loc} us)
                                                           ¬list-vs≡list-us list-vs≡list-us =  ¬list-v∷vs≡list-u∷us ( Eq.cong₂ (λ x xs → ListU  {r}  {ε∉r} {loc} (x ∷ xs)) v≡u vs≡us )
                                                             where
                                                               vs≡us : vs ≡ us
                                                               vs≡us = inv-listU1 vs us list-vs≡list-us 


    
⇒→>-max {l ● r ` loc} {PairU {l} {r} {loc} v₁ v₂} {w}   (ps {w₁} {w₂} .{w} .{l} .{r} .{loc} .{v₁} .{v₂} w≡w₁++w₂ w₁,l→v₁ w₂,r→v₂ longest-ev) (PairU u₁ u₂) ¬pair-v₁v₂≡pair-u₁u₂ |pair-v₁v₂|≡|pair-u₁u₂| =
  len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| pair-v₁v₂>ˡpair-u₁u₂ 
  where
    len|pair-v₁v₂|≡len|pair-u₁u₂| : length (proj₁ (flat (PairU  {l} {r} {loc} v₁ v₂))) ≡ length (proj₁ (flat (PairU  {l} {r} {loc} u₁ u₂)))
    len|pair-v₁v₂|≡len|pair-u₁u₂| rewrite |pair-v₁v₂|≡|pair-u₁u₂|  =  refl 
    pair-v₁v₂>ˡpair-u₁u₂ : (l ● r ` loc) ⊢ PairU v₁ v₂ >ⁱ PairU u₁ u₂
    pair-v₁v₂>ˡpair-u₁u₂ with length (proj₁ (flat v₁)) <? length (proj₁ (flat u₁))
    ... | yes len|v₁|<len|u₁| rewrite sym (⇒-member w₂,r→v₂) | sym (⇒-member w₁,l→v₁) =  Nullary.contradiction anti-longest-ev  longest-ev 
        where
          anti-longest-ev-part1 : ∃[ w₅ ] ( ¬ w₅ ≡ [] ) ×
                                          ( (proj₁ (flat {l} v₁)) ++ w₅ ≡ (proj₁ (flat {l} u₁)) ) ×
                                          ( (proj₁ (flat {r} v₂)) ≡ w₅ ++ (proj₁ (flat {r} u₂))) 
          anti-longest-ev-part1 rewrite sym (⇒-member w₂,r→v₂)  = w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄  {proj₁ (flat {l} v₁)} {proj₁ (flat {r} v₂)} {proj₁ (flat {l} u₁)} {proj₁ (flat {r} u₂)} |pair-v₁v₂|≡|pair-u₁u₂|   len|v₁|<len|u₁|
          anti-longest-ev : ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) ×
                                            ( w₃ ++ w₄ ≡ proj₁ (flat {r} v₂) ) ×
                                            ( ( (proj₁ (flat {l} v₁)) ++ w₃ ) ∈⟦ l ⟧ ) ×
                                            ( w₄ ∈⟦ r ⟧ ) 
          anti-longest-ev = (proj₁ anti-longest-ev-part1 , ( (proj₁ (flat {r} u₂)) ,
                                      ( proj₁ (proj₂ anti-longest-ev-part1 ) ) ,
                                         ( sym (proj₂ (proj₂ (proj₂ anti-longest-ev-part1))) ,
                                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦l⟧  , proj₂ (flat {r}  u₂)   ) ) )
                          where
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦l⟧ : (proj₁ (flat v₁) ++ proj₁ anti-longest-ev-part1)  ∈⟦ l ⟧
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦l⟧ rewrite (proj₁ (proj₂ (proj₂  anti-longest-ev-part1 ))) =  proj₂ (flat {l} u₁) 
          
    
    ... | no ¬len|v₁|<len|u₁| with (¬m>n→n≡m⊎n>m ¬len|v₁|<len|u₁|)
    ...                        | inj₂ len|v₁|>len|u₁| = seq₁ (len-> len|v₁|>len|u₁|)
    ...                        | inj₁ len|v₁|≡len|u₁| with l ⊢ v₁ ≟ u₁
    ...                                                | no ¬v₁≡u₁ = seq₁ (⇒→>-max  w₁,l→v₁ u₁ ¬v₁≡u₁ (proj₁ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |pair-v₁v₂|≡|pair-u₁u₂| len|v₁|≡len|u₁|)))
    ...                                                | yes v₁≡u₁ = seq₂ v₁≡u₁ (⇒→>-max w₂,r→v₂ u₂  ¬v₂≡u₂ (proj₂ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |pair-v₁v₂|≡|pair-u₁u₂| len|v₁|≡len|u₁|)) )
                                                             where
                                                               ¬v₂≡u₂ : ¬ v₂ ≡ u₂
                                                               ¬v₂≡u₂ v₂≡u₂ = ¬pair-v₁v₂≡pair-u₁u₂ (Eq.cong₂ (λ x y → (PairU {l} {r} {loc} x y)) v₁≡u₁ v₂≡u₂) 

```
Lemma : the max value in the posix ordering > must be a posix parse tree.



```agda

intersect-memberʳ : ∀ { l r : RE } { v : U r } 
    → proj₁ (flat {r} v) ∈⟦ l ⟧
    → ∃[ u ] ( proj₁ (flat {l} u) ∈⟦ l ⟧ )  × (proj₁ (flat {r} v) ≡  proj₁ (flat {l} u)  )
intersect-memberʳ {l} {r} {v} |v|∈⟦l⟧ = u , |u|∈⟦l⟧ , sym |u|≡|v| 
  where
    u : U l
    u = unflat |v|∈⟦l⟧
    |u|≡|v| : proj₁ (flat u) ≡ proj₁ (flat v)
    |u|≡|v| rewrite flat∘unflat {l} |v|∈⟦l⟧ = refl 
    |u|∈⟦l⟧ : proj₁ (flat u) ∈⟦ l ⟧
    |u|∈⟦l⟧ rewrite |u|≡|v| = |v|∈⟦l⟧
  


>-anti-sym : ∀ { r : RE } { v u : U r }
    → r ⊢ v > u
    → r ⊢ u > v
    ------------
    → v ≡ u

>→¬< : ∀ { r : RE } { v u : U r }
  → r ⊢ v > u
  -------------
  → ¬ r ⊢ u > v
  
>-anti-sym  {ε}           {EmptyU}        {EmptyU}      (len-> 0>0) = Nullary.contradiction 0>0 (<-irrefl refl)
>-anti-sym  {ε}           {EmptyU}        {EmptyU}      (len-≡ refl ())  (len-≡ refl ()) 
>-anti-sym  {$ c ` loc}   {LetterU .c}    {LetterU .c}  (len-> 1>1) = Nullary.contradiction 1>1 (<-irrefl refl)
>-anti-sym  {$ c ` loc}   {LetterU .c}    {LetterU .c}  (len-≡ refl ())  (len-≡ refl ())
>-anti-sym  {r} {v}   {u} (len-> len|v|>len|u|)               (len-> len|u|>len|v|)   = Nullary.contradiction len|v|>len|u| (<⇒≯ len|u|>len|v|)
>-anti-sym  {r} {v}   {u} (len-> len|v|>len|u|)               (len-≡ len|u|≡len|v| _) = Nullary.contradiction len|v|>len|u| (<-irrefl len|u|≡len|v|)
>-anti-sym  {r} {v}   {u} (len-≡ len|v|≡len|u| _)             (len-> len|u|>len|v|)   = Nullary.contradiction len|u|>len|v| (<-irrefl len|v|≡len|u|)

>-anti-sym  {l ● r ` loc} {PairU v₁ v₂}   {PairU u₁ u₂} (len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| (seq₁ v₁>u₁))        (len-≡ len|pair-u₁u₂|≡len|pair-v₁v₂| (seq₁ u₁>v₁))       = Nullary.contradiction v₁>u₁ (>→¬< u₁>v₁)
>-anti-sym  {l ● r ` loc} {PairU v₁ v₂}   {PairU u₁ u₂} (len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| (seq₂ v₁≡u₁ v₂>u₂))  (len-≡ len|pair-u₁u₂|≡len|pair-v₁v₂| (seq₂ u₁≡v₁ u₂>v₂)) = Nullary.contradiction v₂>u₂ (>→¬< u₂>v₂)
>-anti-sym  {l ● r ` loc} {PairU v₁ v₂}   {PairU u₁ u₂} (len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| (seq₂ v₁≡u₁ v₂>u₂))  (len-≡ len|pair-u₁u₂|≡len|pair-v₁v₂| (seq₁ u₁>v₁))       = Nullary.contradiction (sym v₁≡u₁) (>→¬≡ u₁>v₁)
>-anti-sym  {l ● r ` loc} {PairU v₁ v₂}   {PairU u₁ u₂} (len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| (seq₁ v₁>u₁))        (len-≡ len|pair-u₁u₂|≡len|pair-v₁v₂| (seq₂ u₁≡v₁ u₂>v₂)) = Nullary.contradiction (sym u₁≡v₁) (>→¬≡ v₁>u₁)

>-anti-sym  {l + r ` loc}   {LeftU v}     {LeftU u}           (len-≡ len|left-v|≡len|left-u|   (choice-ll v>u))  (len-≡ len|left-u|≡len|left-v| (choice-ll u>v)) = Nullary.contradiction v>u (>→¬< u>v)
>-anti-sym  {l + r ` loc}   {LeftU v}     {RightU u}          (len-≡ len|left-v|≡len|right-u|  (choice-lr len|v|≥len|u|))  (len-≡ len|right-u|≡len|left-v| (choice-rl len|u|>len|v|)) = Nullary.contradiction len|v|≥len|u| (<⇒≱  len|u|>len|v|)
>-anti-sym  {l + r ` loc}   {RightU v}    {LeftU u}           (len-≡ len|right-v|≡len|left-u|  (choice-rl len|v|>len|u|))  (len-≡ len|left-u|≡len|right-v| (choice-lr len|u|≥len|v|)) = Nullary.contradiction len|u|≥len|v| (<⇒≱  len|v|>len|u|)
>-anti-sym  {l + r ` loc}   {RightU v}    {RightU u}          (len-≡ len|right-v|≡len|right-u|  (choice-rr v>u))  (len-≡ len|right-u|≡len|right-v| (choice-rr u>v)) = Nullary.contradiction v>u (>→¬< u>v)
>-anti-sym  {r * ε∉r ` loc} {ListU []}    {ListU []}          (len-≡ refl ())  (len-≡ refl ())
>-anti-sym  {r * ε∉r ` loc} {ListU (v ∷ vs)} {ListU (u ∷ us)} (len-≡ len|list-v∷vs|≡len|list-u∷us| (star-head v>u)) (len-≡ len|list-u∷us|≡len|list-v∷vs| (star-head u>v)) = Nullary.contradiction v>u (>→¬< u>v)
>-anti-sym  {r * ε∉r ` loc} {ListU (v ∷ vs)} {ListU (u ∷ us)} (len-≡ len|list-v∷vs|≡len|list-u∷us| (star-head v>u)) (len-≡ len|list-u∷us|≡len|list-v∷vs| (star-tail u≡v _)) = Nullary.contradiction (sym u≡v) (>→¬≡ v>u)
>-anti-sym  {r * ε∉r ` loc} {ListU (v ∷ vs)} {ListU (u ∷ us)} (len-≡ len|list-v∷vs|≡len|list-u∷us| (star-tail v≡u _)) (len-≡ len|list-u∷us|≡len|list-v∷vs| (star-head u>v)) = Nullary.contradiction (sym v≡u) (>→¬≡ u>v)
>-anti-sym  {r * ε∉r ` loc} {ListU (v ∷ vs)} {ListU (u ∷ us)} (len-≡ len|list-v∷vs|≡len|list-u∷us| (star-tail v≡u vs>us)) (len-≡ len|list-u∷us|≡len|list-v∷vs| (star-tail u≡v us>vs)) =  Nullary.contradiction vs>us (>→¬< us>vs) 



>→¬< {r} {v} {u} v>u u>v = (>→¬≡ v>u) (>-anti-sym v>u u>v)


-- this can be moved to Utils
++-¬[]→> : ∀ { A : Set } { xs ys : List A }
  → ¬ ys ≡ []
  --------------------------------
  → length (xs ++ ys) > length xs
++-¬[]→> {A} {xs} {[]}     ¬ys≡[]  = Nullary.contradiction refl ¬ys≡[]   
++-¬[]→> {A} {[]} {y ∷ ys} ¬yys≡[] = s≤s z≤n
++-¬[]→> {A} {x ∷ xs } {y ∷ ys} ¬yys≡[] = s≤s ind-hyp
  where
    ind-hyp : length (xs ++ (y ∷ ys)) > length xs
    ind-hyp = ++-¬[]→> {A} {xs} {y ∷ ys} ¬yys≡[]

  

{-# TERMINATING #-}
>-max→⇒ :  ∀ { r : RE } { v : U r } 
  → ( ∀ ( u : U r )
      → proj₁ ( flat {r} v ) ≡ proj₁ (flat {r} u )
      →  r ⊢ v > u )
  -----------------------------------
  → proj₁ (flat {r} v) , r ⇒ v

>-max→⇒ {ε}           {EmptyU}      max-ev = p₁
>-max→⇒ {$ c ` loc}   {LetterU .c}  max-ev = pc
>-max→⇒ {l + r ` loc} {LeftU v}     max-ev = p+l |v|,l⇒v
  where
    ∀u→|v|≡|u|→v>u : ( u : U l ) → proj₁ (flat {l} v) ≡ proj₁ (flat {l} u)  → l ⊢ v > u
    ∀u→|v|≡|u|→v>u u |v|≡|u| with max-ev (LeftU u) |v|≡|u|
    ... | len-≡ len|left-v|≡len|left-u| (choice-ll v>u) = v>u
    ... | len-> len|left-v|>len|left-u|                 = Nullary.contradiction len|left-v|>len|left-u|  (<-irrefl (sym len|left-v|≣len|left-u|))
        where
          len|left-v|≣len|left-u| : length (proj₁ (flat {l} v)) ≡ length (proj₁ (flat {l} u))
          len|left-v|≣len|left-u| rewrite  |v|≡|u| = refl 
    |v|,l⇒v : proj₁ (flat {l} v) , l ⇒ v
    |v|,l⇒v = >-max→⇒  {l} {v} ∀u→|v|≡|u|→v>u

>-max→⇒ {l + r ` loc} {RightU v}     max-ev = p+r |v|,r⇒v ¬|v|∈⟦l⟧ 
  where
    ∀u→|v|≡|u|→v>u : ( u : U r ) →  proj₁ (flat {r} v) ≡ proj₁ (flat {r} u)  → r ⊢ v > u
    ∀u→|v|≡|u|→v>u u |v|≡|u| with max-ev (RightU u) |v|≡|u|
    ... | len-≡ len|right-v|≡len|right-u| (choice-rr v>u) = v>u
    ... | len-> len|right-v|>len|right-u|                 =  Nullary.contradiction len|right-v|>len|right-u|  (<-irrefl (sym len|right-v|≣len|right-u|)) 
        where
          len|right-v|≣len|right-u| : length (proj₁ (flat {r} v)) ≡ length (proj₁ (flat {r} u))
          len|right-v|≣len|right-u| rewrite  |v|≡|u| = refl 
    
  
    |v|,r⇒v : proj₁ (flat {r} v) , r ⇒ v
    |v|,r⇒v = >-max→⇒  {r} {v} ∀u→|v|≡|u|→v>u 
    
    ¬|v|∈⟦l⟧ : ¬ proj₁ (flat {r} v) ∈⟦ l ⟧
    ¬|v|∈⟦l⟧ |v|∈⟦l⟧ with intersect-memberʳ {l} {r} {v} |v|∈⟦l⟧
    ... |  u , |u|∈⟦l⟧ , |v|≡|u| = >→¬< ( max-ev (LeftU {l} {r} {loc} u) |v|≡|u| ) left-u>right-v 
      where
        len|v|≡len|u| : length (proj₁ (flat {r} v)) ≡ length (proj₁ (flat {l} u))
        len|v|≡len|u| rewrite |v|≡|u| = refl 
        len|right-v|≡len|left-u| : length (proj₁ (flat {l + r ` loc} (RightU v))) ≡ length (proj₁ (flat {l + r ` loc} (LeftU u)))
        len|right-v|≡len|left-u| rewrite |v|≡|u| = refl 
        left-u>right-v : l + r ` loc ⊢ LeftU {l} {r} {loc} u > RightU {l} {r} {loc} v
        left-u>right-v = len-≡ ( sym len|right-v|≡len|left-u|) (choice-lr (≤-reflexive (len|right-v|≡len|left-u|)) )

>-max→⇒ {l ● r ` loc} {PairU v₁ v₂} max-ev  = ps {proj₁ (flat v₁)} {proj₁ (flat v₂)} {(proj₁ (flat v₁)) ++ (proj₁ (flat v₂))} {l} {r} {loc} {v₁} {v₂} refl |v₁|,l⇒v₁ |v₂|,r⇒v₂ longest-ev
  where
    ∀u₁→|v₁|≡|u₁|→v₁>u₁ : ( u₁ : U l ) → proj₁ (flat {l} v₁) ≡ proj₁ (flat {l} u₁)  → l ⊢ v₁ > u₁
    ∀u₁→|v₁|≡|u₁|→v₁>u₁ u₁ |v₁|≡|u₁| with max-ev (PairU u₁ v₂) (cong (λ x → x ++ (proj₁ (flat {r} v₂) )) |v₁|≡|u₁|)
    ... | len-> len|pair-v₁v₂|>len|pair-u₁v₂| =  Nullary.contradiction  len|v₁|>len|u₁| (<-irrefl (sym len|v₁|≡len|u₁|))
      -- len->  len|v₁|>len|u₁| -- why this also works? because eventually it leads to contradiciton? 
      where
        len|v₁|≡len|u₁| : length (proj₁ (flat v₁)) ≡ length (proj₁ (flat u₁))
        len|v₁|≡len|u₁| rewrite |v₁|≡|u₁| = refl 
        len|v₁|>len|u₁| : length (proj₁ (flat v₁)) > length (proj₁ (flat u₁))
        len|v₁|>len|u₁| = len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ { (proj₁ (flat v₁)) } { (proj₁ (flat u₁)) } {  (proj₁ (flat v₂))}  len|pair-v₁v₂|>len|pair-u₁v₂|
        
    ... | len-≡ len|pair-v₁v₂|≡len|pair-u₁v₂| (seq₂ v₁≡u₁ v₂>v₂ )  = Nullary.contradiction refl (>→¬≡ v₂>v₂ )
    ... | len-≡ len|pair-v₁v₂|≡len|pair-u₁v₂| (seq₁ v₁>u₁)  = v₁>u₁
    
    |v₁|,l⇒v₁ :  proj₁ (flat {l} v₁) , l ⇒ v₁
    |v₁|,l⇒v₁ =  >-max→⇒  {l} {v₁} ∀u₁→|v₁|≡|u₁|→v₁>u₁ 

    ∀u₂→|v₂|≡|u₂|→v₂>u₂ : ( u₂ : U r ) → proj₁ (flat {r} v₂) ≡ proj₁ (flat {r} u₂) → r ⊢ v₂ > u₂
    ∀u₂→|v₂|≡|u₂|→v₂>u₂ u₂ |v₂|≡|u₂|  with max-ev (PairU v₁ u₂) (cong (λ x → (proj₁ (flat {l} v₁) ++ x ) ) |v₂|≡|u₂| ) 
    ... | len-> len|pair-v₁v₂|>len|pair-v₁u₂| = Nullary.contradiction len|v₂|>len|u₂| (<-irrefl (sym (cong length  |v₂|≡|u₂| )))
      where

        len|pair-v₁u₂|≡len|v₁|+len|u₂| :  length (proj₁ (flat {l ● r ` loc} (PairU v₁ u₂))) ≡ length (proj₁ (flat {l} v₁)) + length (proj₁ (flat {r} u₂))
        len|pair-v₁u₂|≡len|v₁|+len|u₂| =  length-++ (proj₁ (flat {l} v₁)) 

        len|pair-v₁v₂|≡len|v₁|+len|v₂| :  length (proj₁ (flat {l ● r ` loc} (PairU v₁ v₂))) ≡ length (proj₁ (flat {l} v₁)) + length (proj₁ (flat {r} v₂))
        len|pair-v₁v₂|≡len|v₁|+len|v₂| =  length-++ (proj₁ (flat {l} v₁)) 


        len|v₂|>len|u₂| : length (proj₁ (flat v₂)) > length (proj₁ (flat u₂))
        len|v₂|>len|u₂| rewrite len|pair-v₁v₂|≡len|v₁|+len|v₂| | len|pair-v₁u₂|≡len|v₁|+len|u₂|  = +-cancelˡ-< (length (proj₁ (flat {l} v₁)))  (length (proj₁ (flat {r} u₂)))  (length (proj₁ (flat {r} v₂))) len|pair-v₁v₂|>len|pair-v₁u₂| 
    ... | len-≡ len|pair-v₁v₂|≡len|pair-v₁u₂| (seq₂ refl v₂>u₂)  = v₂>u₂ 
    ... | len-≡ len|pair-v₁v₂|≡len|pair-v₁u₂| (seq₁ v₁>v₁) =  Nullary.contradiction refl (>→¬≡ v₁>v₁ )

    |v₂|,r⇒v₂ :  proj₁ (flat {r} v₂) , r ⇒ v₂
    |v₂|,r⇒v₂ =  >-max→⇒  {r} {v₂} ∀u₂→|v₂|≡|u₂|→v₂>u₂

    longest-ev :  ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) ×
                      ( w₃ ++ w₄ ≡ proj₁ (flat v₂)) ×
                      ((proj₁ (flat {l} v₁) ++ w₃) ∈⟦ l ⟧) ×
                      (w₄ ∈⟦ r ⟧))
    longest-ev ( w₃ , w₄ , ¬w₃≡[] , w₃++w₄≡|v₂| , |v₁|++w₃∈⟦l⟧ , w₄∈⟦r⟧) = (>→¬<  pair-v₁v₂>pair-u₁u₂) pair-u₁u₂>pair-v₁v₂ 

      {-
      the gist of the contradiction 
       w₃++w₄≡|v₂| hence |v₁| ++ w₃ ++ w₄ ≡ |v₁| ++ |v₂|
       find u₁ u₂ such that |u₁| ≡ |v₁| ++ w₃ , since |v₁|++w₃∈⟦l⟧ ;
            |u₂| ≡ w₄.
            Hence 
       apply max-ev (PairU u₁ u₂)  (|u₁| ++ |u₂| ≡ |v₁| ++ |v₂|)
       we have (PairU v₁ v₂) > (PairU u₁ u₂)
       However, we can also show that (PairU u₁ u₂) > (PairU v₁ v₂) via seq₁ (len-> len-|u₁|>len-|v₁|) 
      -} 
      where
        u₁ : U l
        u₁ = unflat |v₁|++w₃∈⟦l⟧
        u₂ : U r
        u₂ = unflat w₄∈⟦r⟧
        |u₂|≡w₄ : proj₁ (flat {r} u₂) ≡ w₄
        |u₂|≡w₄ rewrite flat∘unflat {r} {w₄} w₄∈⟦r⟧ = refl
        |u₁|≡|v₁|++w₃ : proj₁ (flat {l} u₁) ≡ (proj₁ (flat {l} v₁)) ++ w₃
        |u₁|≡|v₁|++w₃ rewrite flat∘unflat {l} {(proj₁ (flat {l} v₁)) ++ w₃}  |v₁|++w₃∈⟦l⟧ = refl 
        |v₁|++|v₂|≡|u₁|++|u₂| : (proj₁ (flat v₁)) ++ (proj₁ (flat v₂)) ≡ (proj₁ (flat u₁)) ++ (proj₁ (flat u₂))
        |v₁|++|v₂|≡|u₁|++|u₂| =
          begin
            (proj₁ (flat v₁)) ++ (proj₁ (flat v₂))
          ≡⟨ cong ((proj₁ (flat v₁)) ++_ ) (sym w₃++w₄≡|v₂| ) ⟩
            (proj₁ (flat v₁)) ++ (w₃ ++ w₄)
          ≡⟨ sym (++-assoc (proj₁ (flat v₁)) w₃ w₄)  ⟩
            ((proj₁ (flat v₁)) ++ w₃ ) ++ w₄
          ≡⟨ cong ( _++ w₄ ) (sym |u₁|≡|v₁|++w₃)  ⟩ 
            (proj₁ (flat u₁)) ++ w₄ 
          ≡⟨ cong ((proj₁ (flat u₁)) ++_ ) (sym |u₂|≡w₄) ⟩ 
            (proj₁ (flat u₁)) ++ (proj₁ (flat u₂))
          ∎ 
        pair-v₁v₂>pair-u₁u₂ : l ● r ` loc ⊢ PairU v₁ v₂ > PairU u₁ u₂
        pair-v₁v₂>pair-u₁u₂ = max-ev (PairU u₁ u₂) |v₁|++|v₂|≡|u₁|++|u₂|

        pair-u₁u₂>pair-v₁v₂ : l ● r ` loc ⊢ PairU u₁ u₂ > PairU v₁ v₂
        pair-u₁u₂>pair-v₁v₂ = len-≡  len-|pair-u₁u₂|≡len-|pair-v₁v₂| (seq₁ (len-> len-|u₁|>len-|v₁| ))
          where
            len-|pair-u₁u₂|≡len-|pair-v₁v₂| : length (proj₁ (flat (PairU {l} {r} {loc} u₁ u₂))) ≡ length (proj₁ (flat (PairU {l} {r} {loc}  v₁ v₂)))
            len-|pair-u₁u₂|≡len-|pair-v₁v₂| rewrite (sym |v₁|++|v₂|≡|u₁|++|u₂|) = refl
            len-|u₁|>len-|v₁| : length (proj₁ (flat u₁)) > length (proj₁ (flat v₁))
            len-|u₁|>len-|v₁| rewrite |u₁|≡|v₁|++w₃ = ++-¬[]→> {Char} {proj₁ (flat v₁)} {w₃} ¬w₃≡[]


>-max→⇒ {r * ε∉r ` loc} {ListU []} max-ev = p[]
{-
  where
    ex : ∃[ u ] ( ParseTree.ParseTreeOf r u ) × ¬ ( proj₁ (flat {r} u)) ≡ []
    ex with ParseTree.r-∃u r
    ... | u , ParseTree.parseTreeOf .{r} .{u} = u , ( ParseTree.parseTreeOf {r} {u} , ¬|u|≡[])
      where
        ¬|u|≡[] : ¬ ( proj₁ (flat {r} u)) ≡ []
        ¬|u|≡[] |u|≡[] = ([]∈⟦r⟧→¬ε∉r []∈⟦r⟧) ε∉r
          where
            []∈⟦r⟧ : [] ∈⟦ r ⟧
            []∈⟦r⟧ rewrite (sym |u|≡[] ) =  proj₂ (flat {r} u)
-} 
    
>-max→⇒ {r * ε∉r ` loc} {ListU (v ∷ vs)} max-ev =
  p* {proj₁ (flat v)} {proj₁ (flat (ListU {r} {ε∉r} {loc} vs))} {proj₁ (flat v) ++ proj₁ (flat (ListU {r} {ε∉r} {loc} vs)) } refl |v|,r⇒v |list-vs|,r*⇒list-vs  ¬|v|≡[] longest-ev
  where
    ¬|v|≡[] : ¬ proj₁ (flat v) ≡ []
    ¬|v|≡[] |v|≡[] = ([]∈⟦r⟧→¬ε∉r []∈⟦r⟧) ε∉r 
      where
        []∈⟦r⟧ : [] ∈⟦ r ⟧
        []∈⟦r⟧ rewrite (sym |v|≡[] ) =  proj₂ (flat {r} v)


    ∀u→|v|≡|u|→v>u : ( u : U r ) → proj₁ (flat {r} v) ≡ proj₁ (flat {r} u)  → r ⊢ v > u
    ∀u→|v|≡|u|→v>u u |v|≡|u| with max-ev (ListU (u ∷ vs)) (cong (λ x → x ++ (proj₁ (flat {r * ε∉r ` loc } (ListU vs)))) |v|≡|u|)
    ... | len-> len|list-v∷vs|>len|list-u∷vs| = Nullary.contradiction len|list-v∷vs|>len|list-u∷vs| (<-irrefl (sym len|list-v∷vs|≡len|list-u∷vs|)) 
      where
        |list-v∷vs|≡|list-u∷vs| : (proj₁ (flat (ListU   {r} {ε∉r} {loc}  (v ∷ vs)))) ≡ (proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ vs))))
        |list-v∷vs|≡|list-u∷vs| rewrite  |v|≡|u| = refl 

        len|list-v∷vs|≡len|list-u∷vs| : length (proj₁ (flat (ListU   {r} {ε∉r} {loc}  (v ∷ vs)))) ≡ length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ vs))))
        len|list-v∷vs|≡len|list-u∷vs| rewrite |list-v∷vs|≡|list-u∷vs|  = refl
    ... | len-≡ len|list-v∷vs|≡len|list-u∷vs| (star-tail v≡u vs>vs) =  Nullary.contradiction refl (>→¬≡ vs>vs )
    ... | len-≡ len|list-v∷vs|≡len|list-u∷vs| (star-head v>u) = v>u

    |v|,r⇒v : proj₁ (flat {r} v) , r ⇒ v
    |v|,r⇒v =  >-max→⇒  {r} {v} ∀u→|v|≡|u|→v>u 


    ∀list-us→|list-vs|≡|list-us|→list-vs>list-us : ( list-us : U ( r * ε∉r ` loc ) )
      → proj₁ (flat {r * ε∉r ` loc} (ListU vs) ) ≡ proj₁ (flat {r * ε∉r ` loc} list-us)
      → (r * ε∉r ` loc) ⊢ (ListU vs) > list-us
    ∀list-us→|list-vs|≡|list-us|→list-vs>list-us (ListU us) |list-vs|≡|list-us| with max-ev (ListU (v ∷ us)) (cong (λ x → (proj₁ (flat {r} v)) ++ x ) |list-vs|≡|list-us|)
    ... | len-> len|list-v∷vs|>len|list-v∷us| = Nullary.contradiction len|list-v∷vs|>len|list-v∷us| (<-irrefl (sym len|list-v∷vs|≡len|list-v∷us|)) 
      where
        |list-v∷vs|≡|list-v∷us| : (proj₁ (flat (ListU   {r} {ε∉r} {loc}  (v ∷ vs)))) ≡ (proj₁ (flat (ListU  {r} {ε∉r} {loc} (v ∷ us))))
        |list-v∷vs|≡|list-v∷us| rewrite  |list-vs|≡|list-us| = refl
        
        len|list-v∷vs|≡len|list-v∷us| : length (proj₁ (flat (ListU   {r} {ε∉r} {loc}  (v ∷ vs)))) ≡ length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (v ∷ us))))
        len|list-v∷vs|≡len|list-v∷us| rewrite  |list-v∷vs|≡|list-v∷us| = refl
    ... | len-≡ len|list-v∷vs|≡len|list-v∷us| (star-head v>v) = Nullary.contradiction refl (>→¬≡ v>v)
    ... | len-≡ len|list-v∷vs|≡len|list-v∷us| (star-tail v≡v list-vs>list-us) = list-vs>list-us


    |list-vs|,r*⇒list-vs : proj₁ (flat {r * ε∉r ` loc} (ListU vs)) , (r * ε∉r ` loc) ⇒ (ListU {r} {ε∉r} {loc} vs)
    |list-vs|,r*⇒list-vs =  >-max→⇒  {r * ε∉r ` loc} {ListU vs} ∀list-us→|list-vs|≡|list-us|→list-vs>list-us

    longest-ev : ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) ×
                     ( w₃ ++ w₄ ≡ proj₁ (flat (ListU  {r} {ε∉r} {loc} vs)) ) ×
                     ( ((proj₁ (flat {r} v)) ++ w₃) ∈⟦ r ⟧ ) ×
                     ( w₄ ∈⟦  r * ε∉r ` loc ⟧ ) )
    longest-ev ( w₃ , w₄ , ¬w₃≡[] , w₃++w₄≡|list-vs| , |v|++w₃∈⟦r⟧ , w₄∈⟦r*⟧ ) = (>→¬<  list-v∷vs>list-u∷us )  list-u∷us>list-v∷vs
      where
        u : U r
        u = unflat |v|++w₃∈⟦r⟧

        list-us : U ( r * ε∉r ` loc )
        list-us = unflat  w₄∈⟦r*⟧

        |list-us|≡w₄ : proj₁ (flat {r * ε∉r ` loc} list-us ) ≡ w₄
        |list-us|≡w₄ rewrite flat∘unflat {r * ε∉r ` loc} {w₄}  w₄∈⟦r*⟧ = refl

        |u|≡|v|++w₃ : proj₁ (flat {r} u) ≡ (proj₁ (flat {r} v)) ++ w₃
        |u|≡|v|++w₃ rewrite flat∘unflat {r} {(proj₁ (flat {r} v)) ++ w₃}  |v|++w₃∈⟦r⟧ = refl

        |v|++|list-vs|≡|u|++|list-us| : (proj₁ (flat v)) ++ (proj₁ (flat (ListU vs))) ≡ (proj₁ (flat u)) ++ (proj₁ (flat list-us))
        |v|++|list-vs|≡|u|++|list-us| =
          begin
            (proj₁ (flat v)) ++ (proj₁ (flat (ListU vs)))
          ≡⟨  cong ((proj₁ (flat v)) ++_ ) (sym w₃++w₄≡|list-vs| ) ⟩
            (proj₁ (flat v)) ++ (w₃ ++ w₄)
          ≡⟨ sym (++-assoc (proj₁ (flat v)) w₃ w₄)  ⟩
            ((proj₁ (flat v)) ++ w₃) ++ w₄
          ≡⟨ cong ( _++ w₄ ) (sym |u|≡|v|++w₃)  ⟩
            (proj₁ (flat u)) ++ w₄
          ≡⟨ cong ((proj₁ (flat u)) ++_ ) (sym |list-us|≡w₄) ⟩ 
            (proj₁ (flat u)) ++ (proj₁ (flat list-us))
          ∎

        |list-v∷vs|≡|list-u∷us| : proj₁ (flat (ListU  {r} {ε∉r} {loc} (v ∷ vs))) ≡ proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ (unListU list-us))))
        |list-v∷vs|≡|list-u∷us| rewrite  |v|++|list-vs|≡|u|++|list-us| |  sym (listU∘unListU {r} {ε∉r} {loc} {unflat w₄∈⟦r*⟧})  = refl 
        list-v∷vs>list-u∷us : r * ε∉r ` loc ⊢ ListU  {r} {ε∉r} {loc} ( v ∷ vs) > ListU  {r} {ε∉r} {loc} (u ∷ (unListU list-us))
        list-v∷vs>list-u∷us = max-ev (ListU (u ∷ (unListU list-us)) ) |list-v∷vs|≡|list-u∷us|

        list-u∷us>list-v∷vs : r * ε∉r ` loc ⊢ ListU  {r} {ε∉r} {loc} ( u ∷ (unListU list-us)) > ListU  {r} {ε∉r} {loc} (v ∷ vs)
        list-u∷us>list-v∷vs = len-≡ (sym len-|list-v∷vs|≡len-|list-u∷us|) (star-head (len-> len-|u|>len-|v|) )
          where
            len-|list-v∷vs|≡len-|list-u∷us| : length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (v ∷ vs)))) ≡ length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ (unListU list-us)))))
            len-|list-v∷vs|≡len-|list-u∷us| rewrite (sym |list-v∷vs|≡|list-u∷us|)   = refl 
            len-|u|>len-|v| :  length (proj₁ (flat u)) > length (proj₁ (flat v))
            len-|u|>len-|v| rewrite |u|≡|v|++w₃ = ++-¬[]→> {Char} {proj₁ (flat v)} {w₃}  ¬w₃≡[]           
```

