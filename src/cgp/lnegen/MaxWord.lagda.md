```agda
{-# OPTIONS --rewriting  #-}
-- {-# OPTIONS --rewriting --allow-unsolved-metas #-}
module cgp.lnegen.MaxWord where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ¬≡[]→length>0 ; ¬≡0→>0 ; length≡0→[] ; n≡0→¬n>0 
 )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; unListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ; inv-pairU ) 

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU≢[] ; Flat-[] ; flat-[] ; proj₁flat-v≡[]→ε∈r )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ; 
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ; mkinjFstSoundEv ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ;
  concatmap-pdinstance-snd ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with 
  ) 


import cgp.lnegen.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; 
  advance-pdi*-with-c ; 
  pdUMany[_,_]; pdUMany-aux ;
  mkinjLetter ; mkinjLetterSound 
  ) 

import cgp.lnegen.Order as Order
open Order -- TODO: we should only whitelist those are used here 

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _+_ ; _∸_ ; _≤_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; _≟_ ; m+n≤o⇒m≤o∸n ; m≤o∸n⇒m+n≤o ; m+n≤o⇒n≤o ; +-identityʳ ; +-identityˡ ; m≤m+n ; m≤n+m ; +-comm ; m+n≡0⇒m≡0 ; m+n≡0⇒n≡0 )



import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ; length-++ ; ++-assoc )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map)

import Relation.Nullary as Nullary
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Data.Empty using (⊥ ; ⊥-elim)
open Data.Empty

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

open import Function using (_∘_ ; flip ; case_of_)


```



```agda
data ≥-Max : ∀ { r : RE } → List Char → U r  → Set where 
  ≥-max : ∀ { r : RE }
        → ( w : List Char )
        → ( u : U r )
        → proj₁ (flat u) ≡ w 
        → ( ( v : U r )
          →  proj₁ (flat v) ≡ w 
          → r ⊢ u ≥ v )
        → ≥-Max {r} w u


≥-max-pair-fst-prefix→> : ∀ { l r : RE } { loc : ℕ } → (u : U l) → (v : U r)
  → ≥-Max {l ● r ` loc} (proj₁ (flat (PairU {l} {r} {loc} u v))) (PairU u v)
  → ( u' : U l )
  → ( v' : U r )
--   → ¬ ( ∃[ c ] ∃[ w ] ( proj₁ (flat u') ≡ proj₁ (flat u) ++ ( c ∷ w ) ) × ( proj₁ (flat v) ) ≡ (c ∷ w ++ (proj₁ (flat v'))) ) 
  → ( Σ[ c ∈ Char ] Σ[ w ∈ List Char ] ( ( proj₁ (flat u') ≡ proj₁ (flat u) ++ ( c ∷ w ) ) × ( ( proj₁ (flat v) ) ≡ (c ∷ w ++ (proj₁ (flat v'))) ) ) )
  → l ⊢ u > u' 
≥-max-pair-fst-prefix→> {l = l} {r = r} {loc} u v (≥-max _ _ _ μ) u' v' ((c , w , wu'≡ , wv≡)) =
  helper (μ (PairU u' v') same-word)
  where
    same-word : proj₁ (flat {l ● r ` loc} (PairU u' v')) ≡ proj₁ (flat {l ● r ` loc} (PairU u v))
    same-word = trans (trans (cong (λ x → x ++ proj₁ (flat v')) wu'≡)
                             (++-assoc (proj₁ (flat u)) (c ∷ w) (proj₁ (flat v'))))
                        (cong (λ x → proj₁ (flat u) ++ x) (sym wv≡))
    u≢u' : ¬ (u ≡ u')
    u≢u' u≡u' with ++-cancelˡ (proj₁ (flat u)) (c ∷ w) []
                      (trans (trans (sym wu'≡) (sym (cong (λ x → proj₁ (flat x)) u≡u')))
                            (sym (++-identityʳ (proj₁ (flat u)))))
    ... | ()
    helper : l ● r ` loc ⊢ PairU u v ≥ PairU u' v' → l ⊢ u > u'
    helper (inj₂ refl) = ⊥-elim (u≢u' (proj₁ (inv-pairU {l} {r} {loc} u v u' v' refl)))
    helper (inj₁ (be _ _ (seq₁ u>u'))) = u>u'
    helper (inj₁ (be _ _ (seq₂ u≡u' _))) = ⊥-elim (u≢u' u≡u')
    helper (inj₁ (bne _ _ (seq₁ u>u'))) = u>u'
    helper (inj₁ (bne _ _ (seq₂ u≡u' _))) = ⊥-elim (u≢u' u≡u')
    helper (inj₁ (lne len>0 len'≡0)) rewrite trans (sym (cong length same-word)) len'≡0 = ⊥-elim (Nullary.contradiction len>0 (λ { () }))

-- each partial derivative p is unique
-- inj is ≥-Max-Preserve is given an u which is max, and another v,
-- we must have inj u ≥ inj v 
data ≥-Max-Preserve : ∀ { r : RE } { c : Char } → PDInstance r c → Set where
  ≥-max-pres : ∀ { p r : RE } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ( w : List Char )
      → ≥-Max w u
      → ≥-Max (c ∷ w) (inj u) )
    → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)

≥-max-word : ∀ {r : RE} {w : List Char} {u : U r} → ≥-Max w u → proj₁ (flat u) ≡ w
≥-max-word (≥-max _ _ eq _) = eq

≥-max-pres-left-helper : (p l r : RE) (loc : ℕ) (c : Char) (inj : U p → U l)
  → (u : U p) (w : List Char)
  → ≥-Max (c ∷ w) (inj u)
  → ≥-Max (c ∷ w) (LeftU {l} {r} {loc} (inj u))
≥-max-pres-left-helper p l r loc c inj u w (≥-max _ _ flat-inj-u≡c∷w μ') =
  ≥-max (c ∷ w) (LeftU {l} {r} {loc} (inj u))
    flat-inj-u≡c∷w
    (λ { (LeftU v₁) flat-left-v₁≡c∷w → left-mono-≥ (μ' v₁ flat-left-v₁≡c∷w)
       ; (RightU v₂) flat-right-v₂≡c∷w →
         inj₁ (bne
           (subst (λ x → length x Nat.> 0) (sym flat-inj-u≡c∷w) (Nat.s≤s Nat.z≤n))
           (subst (λ x → length x Nat.> 0) (sym flat-right-v₂≡c∷w) (Nat.s≤s Nat.z≤n))
           (choice-lr {l} {r} {loc} {v₁ = inj u} {v₂ = v₂}))
       })

≥-max-pres-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-left pdi)
≥-max-pres-left {l} {r} {loc} {c} (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres u→w→max-u→max-inj-u) =
  ≥-max-pres (λ u w maxu → ≥-max-pres-left-helper p l r loc c inj u w (u→w→max-u→max-inj-u u w maxu))

{-
-- unprovable. we need a different conclusion which says it is only maximal if the word is not inhabiting in l.
≥-max-pres-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance r c )
  → ≥-Max-Preserve {r} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-right pdi)
≥-max-pres-right {l} {r} {loc} {c} (pdinstance {p} .{r} .{c} inj s-ev) (≥-max-pres u→w→max-u→max-inj-u) =
  ≥-max-pres (λ u w maxu → {!!} )        
-} 

proj₁-flat-LeftU : ∀ {l r : RE} {loc : ℕ} (v₁ : U l) → proj₁ (flat {l + r ` loc} (LeftU v₁)) ≡ proj₁ (flat v₁)
proj₁-flat-LeftU {ε} {r} {loc} EmptyU = refl
proj₁-flat-LeftU {$ c ` loc} {r} {loc'} (LetterU c) = refl
proj₁-flat-LeftU {l₁ + l₂ ` loc} {r} {loc'} (LeftU v₁) = refl
proj₁-flat-LeftU {l₁ + l₂ ` loc} {r} {loc'} (RightU v₁) = refl
proj₁-flat-LeftU {l₁ ● l₂ ` loc} {r} {loc'} (PairU v₁ v₂) = refl
proj₁-flat-LeftU {l₁ * nε ` loc} {r} {loc'} (ListU vs) = refl

≥-max-pres-right : ∀ { p l r  : RE } { loc : ℕ } { c : Char }
  { inj : U p → U r }
  { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
  → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
  → ( u : U p )
  → ( w : List Char )
  → ≥-Max w u
  → ¬ ( (c ∷ w) ∈⟦ l ⟧ )
  → ≥-Max {l + r ` loc} (c ∷ w) (RightU (inj u))
≥-max-pres-right-helper : (p r l : RE) (loc : ℕ) (c : Char) (inj : U p → U r)
  → (u : U p) (w : List Char)
  → ¬ ((c ∷ w) ∈⟦ l ⟧)
  → ≥-Max {r} (c ∷ w) (inj u)
  → ≥-Max {l + r ` loc} (c ∷ w) (RightU {l} {r} {loc} (inj u))
≥-max-pres-right-helper p r l loc c inj u w ¬c∷w∈l (≥-max _ _ flat-inj-u≡c∷w μ') =
  ≥-max (c ∷ w) (RightU {l} {r} {loc} (inj u))
    flat-inj-u≡c∷w
    (λ { (LeftU v₁) flat-left-v₁≡c∷w →
           let xs = proj₁ (flat {l} v₁)
               xs∈⟦l⟧ = proj₂ (flat {l} v₁)
               eq : xs ≡ c ∷ w
               eq = trans (sym (proj₁-flat-LeftU {l} {r} {loc} v₁)) flat-left-v₁≡c∷w
           in ⊥-elim (¬c∷w∈l (subst (λ x → x ∈⟦ l ⟧) eq xs∈⟦l⟧))
       ; (RightU v₂) flat-right-v₂≡c∷w →
           right-mono-≥ (μ' v₂ flat-right-v₂≡c∷w)
       })

≥-max-pres-right {p} {l} {r} {loc} {c} {inj} {sound-ev} (≥-max-pres preserve) u w max-u ¬c∷w∈l =
  ≥-max-pres-right-helper p r l loc c inj u w ¬c∷w∈l (preserve u w max-u) 


-- ≥-max-pres-fst: Lifting maximality through pdinstance on the first component.
-- Statement: If PairU u₁ u₂ is maximal in p●r for word w, and inj : U p → U l preserves
--   maximality (≥-Max-Preserve), then PairU (inj u₁) u₂ is maximal in l●r for word c∷w.
--   Additional premises: u₂ is maximal in r for its own word, and dom ensures inj u₁ > v₁
--   whenever v₁ doesn't match the expected prefix or empty word.
-- Usage: Core lemma for two-level LNE ordering (lnegen), used when constructing the
--   composite pdinstance's maximality from component-wise maximality on the left factor.
-- Proof idea: (1) Show flat(PairU (inj u₁) u₂) ≡ c∷w via sound-ev and max-pair.
--   (2) For competitor PairU v₁ v₂, case on length(flat v₁): if 0, use dom to get
--   inj u₁ > v₁ (since v₁ is empty); if non-zero, check if flat v₁ ≡ c∷flat u₁ via
--   list-≟: if yes, use inj-u₁-max to compare first component, then cancel to compare
--   second; if no, invoke dom directly for strict dominance.

≥-max-pres-fst : ∀ { p l r : RE } { loc : ℕ } { c : Char }
  { inj : U p → U l }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {l} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max-Preserve {l} {c} (pdinstance inj sound-ev)
  → ( u₁ : U p ) ( u₂ : U r )
  → ( w : List Char )
  → ≥-Max {p ● r ` loc} w (PairU u₁ u₂)
  → ≥-Max {r} (proj₁ (flat u₂)) u₂
  → ( ∀ ( v₁ : U l ) → proj₁ (flat {l} v₁) ≢ c ∷ proj₁ (flat {p} u₁) → proj₁ (flat {l} v₁) ≢ [] → l ⊢ inj u₁ > v₁ )
  → ≥-Max {l ● r ` loc} (c ∷ w) (PairU (inj u₁) u₂)
≥-max-pres-fst {p} {l} {r} {loc} {c} {inj} {sound-ev} (≥-max-pres preserve) u₁ u₂ w max-pair max-u₂ dom =
  ≥-max (c ∷ w) (PairU (inj u₁) u₂) flat-inj-u₁-u₂≡c∷w helper
  where
    flat-inj-u₁-u₂≡c∷w : proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} (inj u₁) u₂)) ≡ c ∷ w
    flat-inj-u₁-u₂≡c∷w =
      begin
        proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} (inj u₁) u₂))
      ≡⟨ refl ⟩
        proj₁ (flat {l} (inj u₁)) ++ proj₁ (flat {r} u₂)
      ≡⟨ cong (_++ proj₁ (flat {r} u₂)) (sound-ev u₁) ⟩
        c ∷ proj₁ (flat {p} u₁) ++ proj₁ (flat {r} u₂)
      ≡⟨ cong (c ∷_) (begin
          proj₁ (flat {p} u₁) ++ proj₁ (flat {r} u₂)
        ≡⟨ refl ⟩
          proj₁ (flat {p ● r ` loc} (PairU {p} {r} {loc} u₁ u₂))
        ≡⟨ ≥-max-word max-pair ⟩
          w
        ∎) ⟩
        c ∷ w
      ∎

    -- ≥-max-pair-all: Extract the comparison function μ from ≥-max.
    -- Statement: Given ≥-Max w u and a competitor v with flat v ≡ w, yields l'●r'⊢ u ≥ v.
    -- Usage: Used in ≥-max-pres-fst (to get u₁-max) and ≥-max-pres-snd (as ≥-max-μ).
    -- Proof idea: Pattern-match on ≥-max to expose the underlying μ function.
    ≥-max-pair-all : ∀ { l' r' : RE } { loc' : ℕ } { w' : List Char } { u : U (l' ● r' ` loc') }
      → ≥-Max w' u → ( v : U (l' ● r' ` loc') ) → proj₁ (flat v) ≡ w' → l' ● r' ` loc' ⊢ u ≥ v
    ≥-max-pair-all (≥-max _ _ _ μ) v flat-v≡w = μ v flat-v≡w

    -- flat-pair-cong: Congruence of flat under first-component equality.
    -- Statement: If proj₁(flat u₁) ≡ proj₁(flat u₁'), then flat(PairU u₁ u₂) ≡ flat(PairU u₁' u₂).
    -- Usage: Used in u₁-max to show flat(PairU v₁ u₂) ≡ w when flat v₁ ≡ flat u₁.
    -- Proof idea: Unfold flat of PairU to concat, apply cong to the first operand, re-fold.
    flat-pair-cong : ∀ {l' r' : RE} {loc' : ℕ} {u₁ u₁' : U l'} {u₂ : U r'}
      → proj₁ (flat u₁) ≡ proj₁ (flat u₁')
      → proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} u₁ u₂)) ≡ proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} u₁' u₂))
    flat-pair-cong {l'} {r'} {loc'} {u₁} {u₁'} {u₂} eq =
      begin
        proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} u₁ u₂))
      ≡⟨ refl ⟩
        proj₁ (flat {l'} u₁) ++ proj₁ (flat {r'} u₂)
      ≡⟨ cong (_++ proj₁ (flat {r'} u₂)) eq ⟩
        proj₁ (flat {l'} u₁') ++ proj₁ (flat {r'} u₂)
      ≡⟨ refl ⟩
        proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} u₁' u₂))
      ∎

    -- len-flat-pair: Length of flat(PairU a b) is sum of component lengths.
    -- Statement: length(proj₁(flat(PairU a b))) ≡ length(proj₁(flat a)) + length(proj₁(flat b)).
    -- Usage: Used in extract-≥-fst to decompose length zero of pair into component lengths.
    -- Proof idea: Unfold flat of PairU to concat, apply length-++, done.
    len-flat-pair : ∀ {l' r' : RE} {loc' : ℕ} {a : U l'} {b : U r'}
      → length (proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} a b))) ≡ length (proj₁ (flat {l'} a)) + length (proj₁ (flat {r'} b))
    len-flat-pair {l'} {r'} {loc'} {a = a} {b = b} =
      begin
        length (proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} a b)))
      ≡⟨ cong length (begin
          proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} a b))
        ≡⟨ refl ⟩
          proj₁ (flat {l'} a) ++ proj₁ (flat {r'} b)
        ∎) ⟩
        length (proj₁ (flat {l'} a) ++ proj₁ (flat {r'} b))
      ≡⟨ length-++ (proj₁ (flat {l'} a)) {proj₁ (flat {r'} b)} ⟩
        length (proj₁ (flat {l'} a)) + length (proj₁ (flat {r'} b))
      ∎

    -- extract-≥-fst: Project pair-wise ≥ to first-component ≥.
    -- Statement: If l'●r' ⊢ PairU u₁ u₂ ≥ PairU u₁' u₂, then l' ⊢ u₁ ≥ u₁'.
    -- Usage: Used to derive u₁-max from max-pair (extract maximality of u₁ from PairU u₁ u₂).
    -- Proof idea: Case analysis on the order constructor: seq₁→inj₁, seq₂→inj₂, lne→
    --   decompose length zero of pair to show both components zero, then reconstruct lne.
    extract-≥-fst : (l' r' : RE) (loc' : ℕ) (u₁ u₁' : U l') (u₂ : U r')
      → l' ● r' ` loc' ⊢ PairU u₁ u₂ ≥ PairU u₁' u₂ → l' ⊢ u₁ ≥ u₁'
    extract-≥-fst _ _ _ _ _ _ (inj₁ (be _ _ (seq₁ u₁>u₁'))) = inj₁ u₁>u₁'
    extract-≥-fst _ _ _ _ _ _ (inj₁ (be _ _ (seq₂ u₁≡u' _))) = inj₂ u₁≡u'
    extract-≥-fst _ _ _ _ _ _ (inj₁ (bne _ _ (seq₁ u₁>u₁'))) = inj₁ u₁>u₁'
    extract-≥-fst _ _ _ _ _ _ (inj₁ (bne _ _ (seq₂ u₁≡u' _))) = inj₂ u₁≡u'
    extract-≥-fst l' r' loc' u₁ u₁' u₂ (inj₁ (lne len>0 len'≡0)) =
      let len-u₂≡0 = m+n≡0⇒n≡0 (length (proj₁ (flat {l'} u₁')))
                               (trans (sym (len-flat-pair {l'} {r'} {loc'} {a = u₁'} {b = u₂})) len'≡0)
          len-u₁>0 = subst (λ x → x Nat.> 0)
                           (trans (cong (λ y → length (proj₁ (flat {l'} u₁)) + y) len-u₂≡0)
                                  (+-identityʳ (length (proj₁ (flat {l'} u₁)))))
                           (subst (λ x → x Nat.> 0)
                                  (len-flat-pair {l'} {r'} {loc'} {a = u₁} {b = u₂})
                                  len>0)
          len-u₁'≡0 = m+n≡0⇒m≡0 (length (proj₁ (flat {l'} u₁')))
                               (trans (sym (len-flat-pair {l'} {r'} {loc'} {a = u₁'} {b = u₂})) len'≡0)
      in inj₁ (lne len-u₁>0 len-u₁'≡0)
    extract-≥-fst _ _ _ _ _ _ (inj₂ refl) = inj₂ refl

    -- u₁-max: u₁ is maximal in p for its own word.
    -- Statement: ≥-Max (proj₁(flat u₁)) u₁, extracted from max-pair.
    -- Usage: Seed for inj-u₁-max (applied with preserve to lift to l).
    -- Proof idea: For any competitor v₁, construct PairU v₁ u₂, use max-pair to get ≥,
    --   then extract-≥-fst to project to first component.
    u₁-max : ≥-Max {p} (proj₁ (flat {p} u₁)) u₁
    u₁-max = ≥-max (proj₁ (flat {p} u₁)) u₁ refl λ v₁ flat-v₁≡flat-u₁ →
      extract-≥-fst p r loc u₁ v₁ u₂ (≥-max-pair-all max-pair (PairU {p} {r} {loc} v₁ u₂)
        (trans (flat-pair-cong {p} {r} {loc} flat-v₁≡flat-u₁) (≥-max-word max-pair)))

    -- inj-u₁-max: inj u₁ is maximal in l for c∷flat u₁.
    -- Statement: ≥-Max (c ∷ proj₁(flat u₁)) (inj u₁), from ≥-Max-Preserve applied to u₁-max.
    -- Usage: Used in helper-inj to compare v₁ against inj u₁ when flat v₁ ≡ c∷flat u₁.
    -- Proof idea: Direct application of preserve (from ≥-max-pres) to u₁-max.
    inj-u₁-max : ≥-Max {l} (c ∷ proj₁ (flat u₁)) (inj u₁)
    inj-u₁-max = preserve u₁ (proj₁ (flat u₁)) u₁-max

    len>0-inj : length (proj₁ (flat {l} (inj u₁))) Nat.> 0
    len>0-inj rewrite sound-ev u₁ = Nat.s≤s Nat.z≤n

    len>0-pair-inj : length (proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} (inj u₁) u₂))) Nat.> 0
    len>0-pair-inj rewrite flat-inj-u₁-u₂≡c∷w = Nat.s≤s Nat.z≤n

    flat-inj-u₁-u₂≡c∷w' : c ∷ proj₁ (flat {p} u₁) ++ proj₁ (flat {r} u₂) ≡ c ∷ w
    flat-inj-u₁-u₂≡c∷w' = subst (λ x → x ++ proj₁ (flat {r} u₂) ≡ c ∷ w) (sound-ev u₁) flat-inj-u₁-u₂≡c∷w

    len>0-pair-v : (v : U (l ● r ` loc)) → proj₁ (flat {l ● r ` loc} v) ≡ c ∷ w → length (proj₁ (flat {l ● r ` loc} v)) Nat.> 0
    len>0-pair-v v eq = subst (λ x → suc zero ≤ x) (cong length (sym eq)) (Nat.s≤s Nat.z≤n)

    list-≟ : (xs ys : List Char) → Dec (xs ≡ ys)
    list-≟ [] [] = yes refl
    list-≟ [] (_ ∷ _) = no (λ ())
    list-≟ (_ ∷ _) [] = no (λ ())
    list-≟ (x ∷ xs) (y ∷ ys) with x Char.≟ y | list-≟ xs ys
    ... | yes x≡y | yes xs≡ys = yes (cong₂ _∷_ x≡y xs≡ys)
    ... | no ¬x≡y | _         = no (λ eq → ¬x≡y (proj₁ (Utils.∷-inj eq)))
    ... | yes _   | no ¬xs≡ys = no (λ eq → ¬xs≡ys (proj₂ (Utils.∷-inj eq)))

    -- helper-inj-μ: First components equal (v₁ ≡ inj u₁), compare second components via μ.
    -- Statement: Given inj u₁ ≡ v₁, flat(PairU v₁ v₂) ≡ c∷w, and u₂ ≥ v₂,
    --   yields PairU (inj u₁) u₂ ≥ PairU v₁ v₂.
    -- Usage: Called from helper-inj-eq-inj when first components are equal.
    -- Proof idea: If u₂ > v₂, use seq₂; if u₂ ≡ v₂ and v₁ ≡ inj u₁, use refl on pair.
    helper-inj-μ : (v₁ : U l) (v₂ : U r) → inj u₁ ≡ v₁ → proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} v₁ v₂)) ≡ c ∷ w
      → r ⊢ u₂ ≥ v₂ → l ● r ` loc ⊢ PairU (inj u₁) u₂ ≥ PairU v₁ v₂
    helper-inj-μ v₁ v₂ eq-inj flat-v≡c∷w (inj₁ u₂>v₂) =
      inj₁ (bne {l ● r ` loc} {PairU (inj u₁) u₂} {PairU v₁ v₂}
        len>0-pair-inj (len>0-pair-v (PairU {l} {r} {loc} v₁ v₂) flat-v≡c∷w)
        (seq₂ {l} {r} {loc} {inj u₁} {v₁} {u₂} {v₂} eq-inj u₂>v₂))
    helper-inj-μ v₁ v₂ eq-inj flat-v≡c∷w (inj₂ eq-u₂) =
      inj₂ (cong₂ (PairU {l} {r} {loc}) eq-inj eq-u₂)

    -- helper-inj-eq-inj: First components equal (v₁ ≡ inj u₁), derive v₂-word then use u₂-max.
    -- Statement: Given inj u₁ ≡ v₁, flat(PairU v₁ v₂) ≡ c∷w, flat v₂ ≡ flat u₂, and max-u₂,
    --   yields PairU (inj u₁) u₂ ≥ PairU v₁ v₂.
    -- Usage: Called from helper-inj when μ-inj yields inj u₁ ≡ v₁.
    -- Proof idea: Unfold ≥-max on max-u₂ to get μ, then apply to v₂ with v₂-word,
    --   pass result to helper-inj-μ.
    helper-inj-eq-inj : (v₁ : U l) (v₂ : U r) → inj u₁ ≡ v₁ → proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} v₁ v₂)) ≡ c ∷ w
      → proj₁ (flat {r} v₂) ≡ proj₁ (flat {r} u₂) → ≥-Max {r} (proj₁ (flat {r} u₂)) u₂ → l ● r ` loc ⊢ PairU (inj u₁) u₂ ≥ PairU v₁ v₂
    helper-inj-eq-inj v₁ v₂ eq-inj flat-v≡c∷w v₂-word max-u₂'
      with max-u₂'
    ... | ≥-max _ _ _ μ-u₂ = helper-inj-μ v₁ v₂ eq-inj flat-v≡c∷w (μ-u₂ v₂ v₂-word)

    -- helper-inj: flat v₁ matches the expected prefix c∷flat u₁, compare via inj-u₁-max.
    -- Statement: Given flat v₁ ≡ c∷flat u₁ and flat(PairU v₁ v₂) ≡ c∷w,
    --   yields PairU (inj u₁) u₂ ≥ PairU v₁ v₂.
    -- Usage: Called from helper when list-≟ confirms flat v₁ ≡ c∷flat u₁.
    -- Proof idea: Apply inj-u₁-max to v₁ with eq: if inj u₁ > v₁, use seq₁;
    --   if inj u₁ ≡ v₁, cancel the common prefix to derive flat v₂ ≡ flat u₂,
    --   then delegate to helper-inj-eq-inj.
    helper-inj : (v₁ : U l) (v₂ : U r) → proj₁ (flat {l} v₁) ≡ c ∷ proj₁ (flat {p} u₁) → proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} v₁ v₂)) ≡ c ∷ w → l ● r ` loc ⊢ PairU (inj u₁) u₂ ≥ PairU v₁ v₂
    helper-inj v₁ v₂ eq flat-v≡c∷w
      with inj-u₁-max
    ... | ≥-max _ _ _ μ-inj
      with μ-inj v₁ eq
    ...   | inj₁ inj-u₁>v₁ =
      inj₁ (bne {l ● r ` loc} {PairU (inj u₁) u₂} {PairU v₁ v₂}
        len>0-pair-inj (len>0-pair-v (PairU {l} {r} {loc} v₁ v₂) flat-v≡c∷w)
        (seq₁ {l} {r} {loc} {inj u₁} {v₁} {u₂} {v₂} inj-u₁>v₁))
    ...   | inj₂ eq-inj =
      let v₂-word : proj₁ (flat {r} v₂) ≡ proj₁ (flat {r} u₂)
          v₂-word = ++-cancelˡ (c ∷ proj₁ (flat {p} u₁)) (proj₁ (flat {r} v₂)) (proj₁ (flat {r} u₂))
            (sym (trans flat-inj-u₁-u₂≡c∷w'
              (trans (sym flat-v≡c∷w)
                (cong (_++ proj₁ (flat {r} v₂)) eq))))
      in helper-inj-eq-inj v₁ v₂ eq-inj flat-v≡c∷w v₂-word max-u₂

    -- helper: Main competitor handler for ≥-max-pres-fst.
    -- Statement: For any competitor v with flat v ≡ c∷w, shows PairU (inj u₁) u₂ ≥ v.
    -- Usage: Passed as μ to ≥-max constructor in the conclusion of ≥-max-pres-fst.
    -- Proof idea: Case on length(flat v₁): (a) if 0, v₁ is empty → dom gives inj u₁ > v₁
    --   (since flat v₁ is empty, not c∷flat u₁); (b) if non-zero, check flat v₁ ≟ c∷flat u₁:
    --   if yes, delegate to helper-inj; if no, dom gives inj u₁ > v₁ directly.
    helper : ( v : U (l ● r ` loc) ) → proj₁ (flat {l ● r ` loc} v) ≡ c ∷ w → l ● r ` loc ⊢ PairU (inj u₁) u₂ ≥ v
    helper (PairU v₁ v₂) flat-v≡c∷w
      with length (proj₁ (flat {l} v₁)) Nat.≟ 0
    ... | yes len-v₁≡0 =
      inj₁ (bne {l ● r ` loc} {PairU (inj u₁) u₂} {PairU v₁ v₂}
        len>0-pair-inj (len>0-pair-v (PairU {l} {r} {loc} v₁ v₂) flat-v≡c∷w)
        (seq₁ {l} {r} {loc} {inj u₁} {v₁} {u₂} {v₂}
          (lne {l} {inj u₁} {v₁} len>0-inj len-v₁≡0)))
    ... | no ¬len-v₁≡0
      with list-≟ (proj₁ (flat {l} v₁)) (c ∷ proj₁ (flat {p} u₁))
    ...   | yes eq = helper-inj v₁ v₂ eq flat-v≡c∷w
    ...   | no ¬eq =
      let ¬[] : proj₁ (flat {l} v₁) ≢ []
          ¬[] eq = ¬len-v₁≡0 (cong length eq)
      in inj₁ (bne {l ● r ` loc} {PairU (inj u₁) u₂} {PairU v₁ v₂}
           len>0-pair-inj (len>0-pair-v (PairU {l} {r} {loc} v₁ v₂) flat-v≡c∷w)
           (seq₁ {l} {r} {loc} {inj u₁} {v₁} {u₂} {v₂} (dom v₁ ¬eq ¬[])))
  

  
-- ≥-max-pres-snd: Lifting maximality through pdinstance on the second component.
-- Statement: If e₁ is maximal in l for [], u₂ is maximal in p for w, inj : U p → U r preserves
--   maximality (≥-Max-Preserve), and no non-empty split of c∷w exists across l and r,
--   then PairU e₁ (inj u₂) is maximal in l●r for c∷w.
-- Usage: Core lemma for two-level LNE ordering (lnegen), used when the second component
--   carries the non-empty word and the first is constrained to empty by the split premise.
-- Proof idea: (1) Show flat(PairU e₁ (inj u₂)) ≡ c∷w via flat e₁ ≡ [] and sound-ev.
--   (2) For competitor PairU v₁ v₂, case on length(flat v₁): if 0, flat v₂ ≡ c∷w by
--   cancellation → both components maximal → lift to pair via pair-≥-from-comp;
--   if non-zero, v₁ and v₂ witness a non-empty split of c∷w, contradicting ¬split.

≥-max-pres-snd : ∀ { p l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  { inj : U p → U r }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {r} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
  → ( e₁ : U l) ( u₂ : U p )
  → ( w : List Char )
  → ≥-Max {l} [] e₁
  → ≥-Max {p} w u₂
  → ¬ ( ∃[ w₁ ] ∃[ w₂ ] ( ¬ w₁ ≡ [] ) × ( w₁ ++ w₂ ≡ c ∷ w ) × ( w₁ ∈⟦ l ⟧ ) × ( w₂ ∈⟦ r ⟧ ))
  → ≥-Max { l ● r ` loc } ( c ∷ w) (mkinjSnd {l} {r} {p} {loc} inj e₁ u₂)
≥-max-pres-snd {p} {l} {r} {ε∈l} {loc} {c} {inj} {sound-ev} (≥-max-pres preserve) e₁ u₂ w max-e₁ max-u₂ ¬split =
  ≥-max (c ∷ w) (mkinjSnd {l} {r} {p} {loc} inj e₁ u₂) flat-mkinjSnd≡c∷w helper
  where
    -- flat-e₁≡[]: e₁ produces the empty word.
    -- Statement: proj₁(flat e₁) ≡ [], extracted from max-e₁.
    -- Usage: Used in flat-mkinjSnd≡c∷w to simplify flat(PairU e₁ (inj u₂)) to flat(inj u₂).
    -- Proof idea: Pattern-match on ≥-max to extract the flat equality field.
    flat-e₁≡[] : proj₁ (flat {l} e₁) ≡ []
    flat-e₁≡[] = ≥-max-word max-e₁

    -- flat-mkinjSnd≡c∷w: The constructed pair produces the expected word c∷w.
    -- Statement: proj₁(flat(PairU e₁ (inj u₂))) ≡ c∷w.
    -- Usage: Passed as flat-eq to ≥-max constructor in the conclusion of ≥-max-pres-snd.
    -- Proof idea: Unfold flat of PairU to concat, substitute flat e₁ ≡ [], cancel left
    --   identity, apply sound-ev for inj u₂, then substitute flat u₂ ≡ w.
    flat-mkinjSnd≡c∷w : proj₁ (flat {l ● r ` loc} (mkinjSnd {l} {r} {p} {loc} inj e₁ u₂)) ≡ c ∷ w
    flat-mkinjSnd≡c∷w =
      begin
        proj₁ (flat {l ● r ` loc} (mkinjSnd {l} {r} {p} {loc} inj e₁ u₂))
      ≡⟨ refl ⟩
        proj₁ (flat {l} e₁) ++ proj₁ (flat {r} (inj u₂))
      ≡⟨ cong (_++ proj₁ (flat {r} (inj u₂))) flat-e₁≡[] ⟩
        [] ++ proj₁ (flat {r} (inj u₂))
      ≡⟨ ++-identityˡ (proj₁ (flat {r} (inj u₂))) ⟩
        proj₁ (flat {r} (inj u₂))
      ≡⟨ sound-ev u₂ ⟩
        c ∷ proj₁ (flat {p} u₂)
      ≡⟨ cong (c ∷_) (≥-max-word max-u₂) ⟩
        c ∷ w
      ∎

    -- len>0-pair-e₁: The pair (e₁, inj u₂) has non-empty flat word.
    -- Statement: length(proj₁(flat(PairU e₁ (inj u₂)))) > 0.
    -- Usage: Length proof for bne constructor in pair-≥-from-comp (seq₁ and seq₂ cases).
    -- Proof idea: Rewrite with flat-mkinjSnd≡c∷w; length(c∷w) = 1 > 0.
    len>0-pair-e₁ : length (proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} e₁ (inj u₂)))) Nat.> 0
    len>0-pair-e₁ rewrite flat-mkinjSnd≡c∷w = Nat.s≤s Nat.z≤n

    -- len>0-pair-v: Any competitor v with flat v ≡ c∷w has non-empty flat word.
    -- Statement: For any v with flat v ≡ c∷w, length(flat v) > 0.
    -- Usage: Second argument of bne in pair-≥-from-comp.
    -- Proof idea: Subst length(c∷w) = 1 > 0 via the given equality.
    len>0-pair-v : (v : U (l ● r ` loc)) → proj₁ (flat {l ● r ` loc} v) ≡ c ∷ w → length (proj₁ (flat {l ● r ` loc} v)) Nat.> 0
    len>0-pair-v v eq = subst (λ x → suc zero ≤ x) (cong length (sym eq)) (Nat.s≤s Nat.z≤n)

    -- ≥-max-μ: Extract the comparison function μ from ≥-max (general version).
    -- Statement: Given ≥-Max w u and competitor v with flat v ≡ w, yields r' ⊢ u ≥ v.
    -- Usage: Used in helper to apply max-e₁ and inj-u₂-max to competitors v₁ and v₂.
    -- Proof idea: Pattern-match on ≥-max to expose the underlying μ function.
    ≥-max-μ : ∀ {r' : RE} {w' : List Char} {u : U r'} → ≥-Max {r'} w' u → (v : U r') → proj₁ (flat {r'} v) ≡ w' → r' ⊢ u ≥ v
    ≥-max-μ (≥-max _ _ _ μ) v flat-v≡w = μ v flat-v≡w

    -- pair-≥-from-comp: Lift component-wise ≥ to pair ≥ for non-empty words.
    -- Statement: Given l ⊢ e₁ ≥ v₁ and r ⊢ inj u₂ ≥ v₂ and flat(PairU v₁ v₂) ≡ c∷w,
    --   yields l●r ⊢ PairU e₁ (inj u₂) ≥ PairU v₁ v₂.
    -- Usage: Used in helper to combine e₁ ≥ v₁ and inj u₂ ≥ v₂ into pair comparison.
    -- Proof idea: Case on the two component comparisons: (a) e₁ > v₁ → seq₁;
    --   (b) e₁ ≡ v₁ and inj u₂ > v₂ → seq₂; (c) both equal → refl. All use bne
    --   since c∷w is non-empty.
    pair-≥-from-comp : (v₁ : U l) (v₂ : U r)
      → l ⊢ e₁ ≥ v₁
      → r ⊢ inj u₂ ≥ v₂
      → proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} v₁ v₂)) ≡ c ∷ w
      → l ● r ` loc ⊢ PairU {l} {r} {loc} e₁ (inj u₂) ≥ PairU {l} {r} {loc} v₁ v₂
    pair-≥-from-comp v₁ v₂ (inj₁ e₁>v₁) _ flat-v≡c∷w =
      inj₁ (bne {l ● r ` loc} {PairU {l} {r} {loc} e₁ (inj u₂)} {PairU {l} {r} {loc} v₁ v₂}
        len>0-pair-e₁ (len>0-pair-v (PairU {l} {r} {loc} v₁ v₂) flat-v≡c∷w)
        (seq₁ {l} {r} {loc} {e₁} {v₁} {inj u₂} {v₂} e₁>v₁))
    pair-≥-from-comp v₁ v₂ (inj₂ refl) (inj₁ inj-u₂>v₂) flat-v≡c∷w =
      inj₁ (bne {l ● r ` loc} {PairU {l} {r} {loc} e₁ (inj u₂)} {PairU {l} {r} {loc} v₁ v₂}
        len>0-pair-e₁ (len>0-pair-v (PairU {l} {r} {loc} v₁ v₂) flat-v≡c∷w)
        (seq₂ {l} {r} {loc} {e₁} {v₁} {inj u₂} {v₂} refl inj-u₂>v₂))
    pair-≥-from-comp _ _ (inj₂ refl) (inj₂ refl) _ =
      inj₂ refl

    -- inj-u₂-max: inj u₂ is maximal in r for c∷w.
    -- Statement: ≥-Max (c ∷ w) (inj u₂), from ≥-Max-Preserve applied to max-u₂.
    -- Usage: Used in helper to compare v₂ against inj u₂ when flat v₂ ≡ c∷w.
    -- Proof idea: Direct application of preserve (from ≥-max-pres) to max-u₂.
    inj-u₂-max : ≥-Max {r} (c ∷ w) (inj u₂)
    inj-u₂-max = preserve u₂ w max-u₂

    -- helper: Main competitor handler for ≥-max-pres-snd.
    -- Statement: For any competitor v with flat v ≡ c∷w, shows PairU e₁ (inj u₂) ≥ v.
    -- Usage: Passed as μ to ≥-max constructor in the conclusion of ≥-max-pres-snd.
    -- Proof idea: Case on length(flat v₁): (a) if 0, flat v₁ ≡ [] → cancel to get
    --   flat v₂ ≡ c∷w → both components maximal → lift via pair-≥-from-comp;
    --   (b) if non-zero, flat v₁ and flat v₂ witness a non-empty split of c∷w,
    --   contradicting ¬split via proj₂(flat v₁) ∈⟦l⟧ and proj₂(flat v₂) ∈⟦r⟧.
    helper : (v : U (l ● r ` loc)) → proj₁ (flat {l ● r ` loc} v) ≡ c ∷ w → l ● r ` loc ⊢ mkinjSnd {l} {r} {p} {loc} inj e₁ u₂ ≥ v
    helper (PairU v₁ v₂) flat-v≡c∷w
      with length (proj₁ (flat {l} v₁)) Nat.≟ 0
    ... | yes len-v₁≡0 =
      let flat-v₁≡[] = length≡0→[] len-v₁≡0
          flat-v₂≡c∷w : proj₁ (flat {r} v₂) ≡ c ∷ w
          flat-v₂≡c∷w =
            begin
              proj₁ (flat {r} v₂)
            ≡⟨ sym (++-identityˡ (proj₁ (flat {r} v₂))) ⟩
              [] ++ proj₁ (flat {r} v₂)
            ≡⟨ cong (_++ proj₁ (flat {r} v₂)) (sym flat-v₁≡[]) ⟩
              proj₁ (flat {l} v₁) ++ proj₁ (flat {r} v₂)
            ≡⟨ flat-v≡c∷w ⟩
              c ∷ w
            ∎
      in pair-≥-from-comp v₁ v₂
           (≥-max-μ max-e₁ v₁ flat-v₁≡[])
           (≥-max-μ inj-u₂-max v₂ flat-v₂≡c∷w)
           flat-v≡c∷w
    ... | no ¬len-v₁≡0 =
      let ¬[] : proj₁ (flat {l} v₁) ≢ []
          ¬[] eq = ¬len-v₁≡0 (cong length eq)
      in ⊥-elim (¬split (proj₁ (flat {l} v₁) ,
        (proj₁ (flat {r} v₂) ,
          (¬[] ,
            (flat-v≡c∷w , (proj₂ (flat {l} v₁) , proj₂ (flat {r} v₂)))))))   



-- ≥-max-pres-star: Lifting maximality through pdinstance on a star (list) parse tree.
-- Statement: If PairU u us is maximal in p●r* for w, us is maximal in r* for flat(us),
--   and inj : U p → U r preserves maximality and dominates competitors whose word ≠ c∷flat(u),
--   then mkinjList inj (PairU u us) is maximal in r* for c∷w.
-- Usage: Core lemma for two-level LNE ordering (lnegen), used when the first element of the
--   star tree carries the distinguished character c and subsequent elements may or may not match.
-- Proof idea: (1) Show flat(mkinjList ...) ≡ c∷w via sound-ev and max-pair.
--   (2) For competitor ListU(ws), case on length of head w₁:
--   (a) if 0, inj u > w₁ by lne (len>0 vs 0) → star-head;
--   (b) if non-zero, check flat(w₁) ≟ c∷flat(u): if yes, compare heads via inj-u-max;
--       if inj u > w₁ → star-head; if inj u ≡ w₁ → cancel, recurse on tail via max-us;
--       if no, use dom premise directly → star-head.

≥-max-pres-star : ∀ { p r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  { inj : U p → U r }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {r} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
  → ( u : U p ) → ( us : U (r * ε∉r ` loc)  )
  → ( w : List Char )
  → ≥-Max { p ● (r * ε∉r ` loc ) ` loc } w (PairU u us)
  → ≥-Max {r * ε∉r ` loc} (proj₁ (flat us)) us
  → ( ∀ ( v : U r ) → proj₁ (flat {r} v) ≢ c ∷ proj₁ (flat {p} u) → r ⊢ inj u > v )
  → ≥-Max {r * ε∉r ` loc} (c ∷ w) (mkinjList inj (PairU u us))
≥-max-pres-star {p} {r} {ε∉r} {loc} {c} {inj} {sound-ev} (≥-max-pres preserve) u (ListU vs) w max-pair max-us dom =
  ≥-max (c ∷ w) (mkinjList inj (PairU u (ListU vs))) flat-mkinj≡c∷w helper
  where
    -- flat-mkinj≡c∷w: The constructed star parse tree produces the expected word c∷w.
    -- Statement: proj₁(flat(mkinjList inj (PairU u (ListU vs)))) ≡ c∷w.
    -- Usage: Passed as flat-eq to ≥-max constructor in the conclusion of ≥-max-pres-star.
    -- Proof idea: Unfold flat of mkinjList to concat, apply sound-ev for inj u,
    --   recombine into flat(PairU u (ListU vs)), then substitute with ≥-max-word max-pair.
    flat-mkinj≡c∷w : proj₁ (flat {r * ε∉r ` loc} (mkinjList inj (PairU u (ListU vs)))) ≡ c ∷ w
    flat-mkinj≡c∷w =
      begin
        proj₁ (flat {r * ε∉r ` loc} (mkinjList inj (PairU u (ListU vs))))
      ≡⟨ refl ⟩
        proj₁ (flat {r} (inj u)) ++ proj₁ (flat {r * ε∉r ` loc} (ListU vs))
      ≡⟨ cong (_++ proj₁ (flat {r * ε∉r ` loc} (ListU vs))) (sound-ev u) ⟩
        c ∷ proj₁ (flat {p} u) ++ proj₁ (flat {r * ε∉r ` loc} (ListU vs))
      ≡⟨ refl ⟩
        c ∷ proj₁ (flat {p ● (r * ε∉r ` loc) ` loc} (PairU {p} {r * ε∉r ` loc} {loc} u (ListU vs)))
      ≡⟨ cong (c ∷_) (≥-max-word max-pair) ⟩
        c ∷ w
      ∎

    -- flat-mkinj≡c∷w': Intermediate equality relating expanded form to c∷w.
    -- Statement: c∷proj₁(flat u) ++ proj₁(flat(ListU vs)) ≡ c∷w.
    -- Usage: Used in helper-inj to simplify the tail equality when canceling the head.
    -- Proof idea: Same derivation as flat-mkinj≡c∷w but without the mkinjList unfolding step.
    flat-mkinj≡c∷w' : c ∷ proj₁ (flat {p} u) ++ proj₁ (flat {r * ε∉r ` loc} (ListU vs)) ≡ c ∷ w
    flat-mkinj≡c∷w' =
      begin
        c ∷ proj₁ (flat {p} u) ++ proj₁ (flat {r * ε∉r ` loc} (ListU vs))
      ≡⟨ refl ⟩
        c ∷ proj₁ (flat {p ● (r * ε∉r ` loc) ` loc} (PairU {p} {r * ε∉r ` loc} {loc} u (ListU vs)))
      ≡⟨ cong (c ∷_) (≥-max-word max-pair) ⟩
        c ∷ w
      ∎

    -- ≥-max-pair-all: Extract the comparison function μ from ≥-max (generalized version).
    -- Statement: Given ≥-Max w' u and competitor v with flat v ≡ w', yields r' ⊢ u ≥ v.
    -- Usage: Used in u-max to apply max-pair to the competitor PairU v (ListU vs).
    -- Proof idea: Pattern-match on ≥-max to expose the underlying μ function.
    ≥-max-pair-all : ∀ { l' r' : RE } { loc' : ℕ } { w' : List Char } { u : U (l' ● r' ` loc') }
      → ≥-Max w' u → ( v : U (l' ● r' ` loc') ) → proj₁ (flat v) ≡ w' → l' ● r' ` loc' ⊢ u ≥ v
    ≥-max-pair-all (≥-max _ _ _ μ) v flat-v≡w = μ v flat-v≡w

    -- len-flat-pair: Length of flat(PairU a b) decomposes as sum of component lengths.
    -- Statement: length(flat(PairU a b)) ≡ length(flat a) + length(flat b).
    -- Usage: Used in extract-≥-fst to decompose length of pair when reasoning about lne.
    -- Proof idea: Unfold flat to concat, apply length-++ lemma.
    len-flat-pair : ∀ {l' r' : RE} {loc' : ℕ} {a : U l'} {b : U r'}
      → length (proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} a b))) ≡ length (proj₁ (flat {l'} a)) + length (proj₁ (flat {r'} b))
    len-flat-pair {l'} {r'} {loc'} {a = a} {b = b} =
      begin
        length (proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} a b)))
      ≡⟨ cong length (begin
          proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} a b))
        ≡⟨ refl ⟩
          proj₁ (flat {l'} a) ++ proj₁ (flat {r'} b)
        ∎) ⟩
        length (proj₁ (flat {l'} a) ++ proj₁ (flat {r'} b))
      ≡⟨ length-++ (proj₁ (flat {l'} a)) {proj₁ (flat {r'} b)} ⟩
        length (proj₁ (flat {l'} a)) + length (proj₁ (flat {r'} b))
      ∎

    -- extract-≥-fst: Extract first-component ≥ from pair ≥ when second components match.
    -- Statement: If PairU u₁ u₂ ≥ PairU u₁' u₂ (with same u₂), then u₁ ≥ u₁'.
    -- Usage: Used in u-max to show u ≥ v by showing PairU u (ListU vs) ≥ PairU v (ListU vs).
    -- Proof idea: Case on the pair comparison: (a) seq₁ → extract first >;
    --   (b) seq₂ → extract first ≡; (c) lne with len≡0 on pair → decompose via len-flat-pair
    --   to get len(u₂)≡0, then show lne on first component; (d) refl → refl.
    extract-≥-fst : (l' r' : RE) (loc' : ℕ) (u₁ u₁' : U l') (u₂ : U r')
      → l' ● r' ` loc' ⊢ PairU u₁ u₂ ≥ PairU u₁' u₂ → l' ⊢ u₁ ≥ u₁'
    extract-≥-fst _ _ _ _ _ _ (inj₁ (be _ _ (seq₁ u₁>u₁'))) = inj₁ u₁>u₁'
    extract-≥-fst _ _ _ _ _ _ (inj₁ (be _ _ (seq₂ u₁≡u' _))) = inj₂ u₁≡u'
    extract-≥-fst _ _ _ _ _ _ (inj₁ (bne _ _ (seq₁ u₁>u₁'))) = inj₁ u₁>u₁'
    extract-≥-fst _ _ _ _ _ _ (inj₁ (bne _ _ (seq₂ u₁≡u' _))) = inj₂ u₁≡u'
    extract-≥-fst l' r' loc' u₁ u₁' u₂ (inj₁ (lne len>0 len'≡0)) =
      let len-u₂≡0 = m+n≡0⇒n≡0 (length (proj₁ (flat {l'} u₁')))
                               (trans (sym (len-flat-pair {l'} {r'} {loc'} {a = u₁'} {b = u₂})) len'≡0)
          len-u₁>0 = subst (λ x → x Nat.> 0)
                           (trans (cong (λ y → length (proj₁ (flat {l'} u₁)) + y) len-u₂≡0)
                                  (+-identityʳ (length (proj₁ (flat {l'} u₁)))))
                           (subst (λ x → x Nat.> 0)
                                  (len-flat-pair {l'} {r'} {loc'} {a = u₁} {b = u₂})
                                  len>0)
          len-u₁'≡0 = m+n≡0⇒m≡0 (length (proj₁ (flat {l'} u₁')))
                               (trans (sym (len-flat-pair {l'} {r'} {loc'} {a = u₁'} {b = u₂})) len'≡0)
      in inj₁ (lne len-u₁>0 len-u₁'≡0)
    extract-≥-fst _ _ _ _ _ _ (inj₂ refl) = inj₂ refl

    -- u-max: u is maximal in p for its own word.
    -- Statement: ≥-Max (proj₁(flat u)) u.
    -- Usage: Feeds into inj-u-max via preserve, which is then used in helper-inj to compare w₁ against inj u.
    -- Proof idea: Show flat u ≡ flat u, then for competitor v with flat v ≡ flat u,
    --   construct PairU v (ListU vs) as competitor for PairU u (ListU vs) using flat-pair-cong,
    --   apply max-pair, then extract first component via extract-≥-fst.
    u-max : ≥-Max {p} (proj₁ (flat {p} u)) u
    u-max = ≥-max (proj₁ (flat {p} u)) u refl λ v flat-v≡flat-u →
      extract-≥-fst p (r * ε∉r ` loc) loc u v (ListU {r} {ε∉r} {loc} vs)
        (≥-max-pair-all max-pair (PairU {p} {r * ε∉r ` loc} {loc} v (ListU {r} {ε∉r} {loc} vs))
          (begin
            proj₁ (flat {p ● (r * ε∉r ` loc) ` loc} (PairU {p} {r * ε∉r ` loc} {loc} v (ListU {r} {ε∉r} {loc} vs)))
          ≡⟨ cong (_++ proj₁ (flat {r * ε∉r ` loc} (ListU {r} {ε∉r} {loc} vs))) flat-v≡flat-u ⟩
            proj₁ (flat {p ● (r * ε∉r ` loc) ` loc} (PairU {p} {r * ε∉r ` loc} {loc} u (ListU {r} {ε∉r} {loc} vs)))
          ≡⟨ ≥-max-word max-pair ⟩
            w
          ∎))

    -- inj-u-max: inj u is maximal in r for c∷flat(u).
    -- Statement: ≥-Max (c ∷ proj₁(flat u)) (inj u).
    -- Usage: Used in helper-inj to case-split competitors w₁ against inj u when flat(w₁) ≡ c∷flat(u).
    -- Proof idea: Apply preserve (from ≥-max-pres) to u-max.
    inj-u-max : ≥-Max {r} (c ∷ proj₁ (flat {p} u)) (inj u)
    inj-u-max = preserve u (proj₁ (flat {p} u)) u-max

    -- len>0-inj: inj u has non-empty flat word.
    -- Statement: length(proj₁(flat(inj u))) > 0.
    -- Usage: Used in helper (case len-w₁≡0) to show lne inj u > w₁.
    -- Proof idea: Rewrite with sound-ev (flat(inj u) = c∷flat u), length(c∷flat u) = 1 > 0.
    len>0-inj : length (proj₁ (flat {r} (inj u))) Nat.> 0
    len>0-inj rewrite sound-ev u = Nat.s≤s Nat.z≤n

    -- len>0-list-inj: The constructed star tree has non-empty flat word.
    -- Statement: length(proj₁(flat(mkinjList ...))) > 0.
    -- Usage: First length argument of bne in helper and helper-inj-μ (for star-head/star-tail).
    -- Proof idea: Rewrite with flat-mkinj≡c∷w; length(c∷w) = 1 > 0.
    len>0-list-inj : length (proj₁ (flat {r * ε∉r ` loc} (mkinjList inj (PairU u (ListU vs))))) Nat.> 0
    len>0-list-inj rewrite flat-mkinj≡c∷w = Nat.s≤s Nat.z≤n

    -- len>0-list-v: Competitor with flat v ≡ c∷w has non-empty flat word.
    -- Statement: For any v with flat v ≡ c∷w, length(flat v) > 0.
    -- Usage: Second length argument of bne in helper and helper-inj-μ.
    -- Proof idea: Subst length(c∷w) = 1 > 0 via the given equality.
    len>0-list-v : (v : U (r * ε∉r ` loc)) → proj₁ (flat {r * ε∉r ` loc} v) ≡ c ∷ w → length (proj₁ (flat {r * ε∉r ` loc} v)) Nat.> 0
    len>0-list-v v eq = subst (λ x → suc zero ≤ x) (cong length (sym eq)) (Nat.s≤s Nat.z≤n)

    -- list-≟: Decision procedure for list equality on Char.
    -- Statement: Decidable equality for List Char.
    -- Usage: Used in helper to check whether flat(w₁) ≡ c∷flat(u) for case-splitting.
    -- Proof idea: Standard recursive structural equality on lists, using Char.≟ for elements.
    list-≟ : (xs ys : List Char) → Dec (xs ≡ ys)
    list-≟ [] [] = yes refl
    list-≟ [] (_ ∷ _) = no (λ ())
    list-≟ (_ ∷ _) [] = no (λ ())
    list-≟ (x ∷ xs) (y ∷ ys) with x Char.≟ y | list-≟ xs ys
    ... | yes x≡y | yes xs≡ys = yes (cong₂ _∷_ x≡y xs≡ys)
    ... | no ¬x≡y | _         = no (λ eq → ¬x≡y (proj₁ (Utils.∷-inj eq)))
    ... | yes _   | no ¬xs≡ys = no (λ eq → ¬xs≡ys (proj₂ (Utils.∷-inj eq)))

    -- ≥-max-μ: Extract the comparison function μ from ≥-max (local version for r*).
    -- Statement: Given ≥-Max w' u and competitor v with flat v ≡ w', yields r' ⊢ u ≥ v.
    -- Usage: Used in helper-inj to apply max-us to ListU ws'.
    -- Proof idea: Pattern-match on ≥-max to expose the underlying μ function.
    ≥-max-μ : ∀ {r' : RE} {w' : List Char} {u : U r'} → ≥-Max {r'} w' u → (v : U r') → proj₁ (flat {r'} v) ≡ w' → r' ⊢ u ≥ v
    ≥-max-μ (≥-max _ _ _ μ) v flat-v≡w = μ v flat-v≡w

    -- helper-inj-μ: Handle star competitor when head matches inj u exactly (equality case).
    -- Statement: Given inj u ≡ w₁ and tail comparison vs ≥ ws', shows mkinjList ≥ ListU(w₁∷ws').
    -- Usage: Called by helper-inj when inj u ≡ w₁, after canceling head equality to get tail comparison.
    -- Proof idea: Case on vs ≥ ws': (a) if strict >, wrap with star-tail;
    --   (b) if equal, reassemble via cong₂ using eq-inj for head and unListU for tail.
    helper-inj-μ : (w₁ : U r) (ws' : List (U r)) → inj u ≡ w₁ → proj₁ (flat {r * ε∉r ` loc} (ListU {r} {ε∉r} {loc} (w₁ ∷ ws'))) ≡ c ∷ w
      → r * ε∉r ` loc ⊢ ListU {r} {ε∉r} {loc} vs ≥ ListU {r} {ε∉r} {loc} ws'
      → r * ε∉r ` loc ⊢ mkinjList inj (PairU u (ListU vs)) ≥ ListU {r} {ε∉r} {loc} (w₁ ∷ ws')
    helper-inj-μ w₁ ws' eq-inj flat-v≡c∷w (inj₁ us>ws') =
      inj₁ (bne {r * ε∉r ` loc} {mkinjList inj (PairU u (ListU vs))} {ListU {r} {ε∉r} {loc} (w₁ ∷ ws')}
        len>0-list-inj (len>0-list-v (ListU {r} {ε∉r} {loc} (w₁ ∷ ws')) flat-v≡c∷w)
        (star-tail {r} {loc} {ε∉r} {inj u} {w₁} {vs} {ws'} eq-inj us>ws'))
    helper-inj-μ w₁ ws' eq-inj flat-v≡c∷w (inj₂ eq-us) =
      inj₂ (cong₂ (λ x xs → ListU {r} {ε∉r} {loc} (x ∷ xs)) eq-inj (cong unListU eq-us))

    -- helper-inj: Handle star competitor when head word matches c∷flat(u).
    -- Statement: Given flat(w₁) ≡ c∷flat(u) and flat(ListU(w₁∷ws')) ≡ c∷w,
    --   shows mkinjList ≥ ListU(w₁∷ws').
    -- Usage: Called by helper (case no ¬len-w₁≡0, yes eq) when head word matches.
    -- Proof idea: Case-split inj-u-max on w₁: (a) if inj u > w₁ → star-head;
    --   (b) if inj u ≡ w₁ → cancel head from both sides to get tail equality,
    --   then recurse via helper-inj-μ using max-us on tail.
    helper-inj : (w₁ : U r) (ws' : List (U r)) → proj₁ (flat {r} w₁) ≡ c ∷ proj₁ (flat {p} u) → proj₁ (flat {r * ε∉r ` loc} (ListU {r} {ε∉r} {loc} (w₁ ∷ ws'))) ≡ c ∷ w
      → r * ε∉r ` loc ⊢ mkinjList inj (PairU u (ListU vs)) ≥ ListU {r} {ε∉r} {loc} (w₁ ∷ ws')
    helper-inj w₁ ws' eq flat-v≡c∷w
      with inj-u-max
    ... | ≥-max _ _ _ μ-inj
      with μ-inj w₁ eq
    ...   | inj₁ inj-u>w₁ =
      inj₁ (bne {r * ε∉r ` loc} {mkinjList inj (PairU u (ListU vs))} {ListU {r} {ε∉r} {loc} (w₁ ∷ ws')}
        len>0-list-inj (len>0-list-v (ListU {r} {ε∉r} {loc} (w₁ ∷ ws')) flat-v≡c∷w)
        (star-head {r} {loc} {ε∉r} {inj u} {w₁} {vs} {ws'} inj-u>w₁))
    ...   | inj₂ eq-inj =
      let tail-eq = ++-cancelˡ (c ∷ proj₁ (flat {p} u))
            (proj₁ (flat {r * ε∉r ` loc} (ListU {r} {ε∉r} {loc} ws')))
            (proj₁ (flat {r * ε∉r ` loc} (ListU {r} {ε∉r} {loc} vs)))
            (sym (trans flat-mkinj≡c∷w'
              (trans (sym flat-v≡c∷w)
                (cong (_++ proj₁ (flat {r * ε∉r ` loc} (ListU {r} {ε∉r} {loc} ws'))) eq))))
      in helper-inj-μ w₁ ws' eq-inj flat-v≡c∷w
           (≥-max-μ max-us (ListU {r} {ε∉r} {loc} ws') tail-eq)

    -- helper: Main competitor handler for ≥-max-pres-star.
    -- Statement: For any competitor v with flat v ≡ c∷w, shows mkinjList ≥ v.
    -- Usage: Passed as μ to ≥-max constructor in the conclusion of ≥-max-pres-star.
    -- Proof idea: Case on v: (a) empty list → impossible (flat ≠ c∷w);
    --   (b) non-empty ListU(w₁∷ws') → case on length(flat w₁):
    --   (i) if 0, inj u > w₁ by lne (len>0 vs 0) → star-head;
    --   (ii) if non-zero, check flat(w₁) ≟ c∷flat(u):
    --        if yes, delegate to helper-inj; if no, use dom premise → star-head.
    helper : (v : U (r * ε∉r ` loc)) → proj₁ (flat {r * ε∉r ` loc} v) ≡ c ∷ w → r * ε∉r ` loc ⊢ mkinjList inj (PairU u (ListU vs)) ≥ v
    helper (ListU []) ()
    helper (ListU (w₁ ∷ ws')) flat-v≡c∷w
      with length (proj₁ (flat {r} w₁)) Nat.≟ 0
    ... | yes len-w₁≡0 =
      inj₁ (bne {r * ε∉r ` loc} {mkinjList inj (PairU u (ListU vs))} {ListU {r} {ε∉r} {loc} (w₁ ∷ ws')}
        len>0-list-inj (len>0-list-v (ListU {r} {ε∉r} {loc} (w₁ ∷ ws')) flat-v≡c∷w)
        (star-head {r} {loc} {ε∉r} {inj u} {w₁} {vs} {ws'} (lne {r} {inj u} {w₁} len>0-inj len-w₁≡0)))
    ... | no ¬len-w₁≡0
      with list-≟ (proj₁ (flat {r} w₁)) (c ∷ proj₁ (flat {p} u))
    ...   | yes eq = helper-inj w₁ ws' eq flat-v≡c∷w
    ...   | no ¬eq =
      inj₁ (bne {r * ε∉r ` loc} {mkinjList inj (PairU u (ListU vs))} {ListU {r} {ε∉r} {loc} (w₁ ∷ ws')}
        len>0-list-inj (len>0-list-v (ListU {r} {ε∉r} {loc} (w₁ ∷ ws')) flat-v≡c∷w)
        (star-head {r} {loc} {ε∉r} {inj u} {w₁} {vs} {ws'} (dom w₁ ¬eq)))


```
