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

    ≥-max-pair-all : ∀ { l' r' : RE } { loc' : ℕ } { w' : List Char } { u : U (l' ● r' ` loc') }
      → ≥-Max w' u → ( v : U (l' ● r' ` loc') ) → proj₁ (flat v) ≡ w' → l' ● r' ` loc' ⊢ u ≥ v
    ≥-max-pair-all (≥-max _ _ _ μ) v flat-v≡w = μ v flat-v≡w

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

    u₁-max : ≥-Max {p} (proj₁ (flat {p} u₁)) u₁
    u₁-max = ≥-max (proj₁ (flat {p} u₁)) u₁ refl λ v₁ flat-v₁≡flat-u₁ →
      extract-≥-fst p r loc u₁ v₁ u₂ (≥-max-pair-all max-pair (PairU {p} {r} {loc} v₁ u₂)
        (trans (flat-pair-cong {p} {r} {loc} flat-v₁≡flat-u₁) (≥-max-word max-pair)))

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

    helper-inj-μ : (v₁ : U l) (v₂ : U r) → inj u₁ ≡ v₁ → proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} v₁ v₂)) ≡ c ∷ w
      → r ⊢ u₂ ≥ v₂ → l ● r ` loc ⊢ PairU (inj u₁) u₂ ≥ PairU v₁ v₂
    helper-inj-μ v₁ v₂ eq-inj flat-v≡c∷w (inj₁ u₂>v₂) =
      inj₁ (bne {l ● r ` loc} {PairU (inj u₁) u₂} {PairU v₁ v₂}
        len>0-pair-inj (len>0-pair-v (PairU {l} {r} {loc} v₁ v₂) flat-v≡c∷w)
        (seq₂ {l} {r} {loc} {inj u₁} {v₁} {u₂} {v₂} eq-inj u₂>v₂))
    helper-inj-μ v₁ v₂ eq-inj flat-v≡c∷w (inj₂ eq-u₂) =
      inj₂ (cong₂ (PairU {l} {r} {loc}) eq-inj eq-u₂)

    helper-inj-eq-inj : (v₁ : U l) (v₂ : U r) → inj u₁ ≡ v₁ → proj₁ (flat {l ● r ` loc} (PairU {l} {r} {loc} v₁ v₂)) ≡ c ∷ w
      → proj₁ (flat {r} v₂) ≡ proj₁ (flat {r} u₂) → ≥-Max {r} (proj₁ (flat {r} u₂)) u₂ → l ● r ` loc ⊢ PairU (inj u₁) u₂ ≥ PairU v₁ v₂
    helper-inj-eq-inj v₁ v₂ eq-inj flat-v≡c∷w v₂-word max-u₂'
      with max-u₂'
    ... | ≥-max _ _ _ μ-u₂ = helper-inj-μ v₁ v₂ eq-inj flat-v≡c∷w (μ-u₂ v₂ v₂-word)

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
  

  


```
