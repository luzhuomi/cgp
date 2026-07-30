```agda
{-# OPTIONS --rewriting  #-}
-- {-# OPTIONS --rewriting --allow-unsolved-metas #-}
module cgp.lnegen.MaxWord where

import Agda.Primitive as Prim
open Prim using (Level)

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ¬≡[]→length>0 ; ¬≡0→>0 ; length≡0→[] ; n≡0→¬n>0 
 )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r ; []∈⟦r⟧→ε∈r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; unListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ; flat-Uε≡[] ; inv-pairU ) 

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; mkAllEmptyU≢[] ; Flat-[] ; flat-[] ; proj₁flat-v≡[]→ε∈r )

import cgp.Recons as Recons
open Recons using ( Recons ; recons )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ; 
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ; mkinjFstSoundEv ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ; mkinjSndSoundEv ; 
  concatmap-pdinstance-snd ; concatmap-pdinstance-snd-[]≡[] ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with 
  ) 


import cgp.lnegen.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; pdU● ; pdU-complete ; 
  advance-pdi*-with-c ; 
  pdUMany[_,_]; pdUMany-aux ;
  mkinjLetter ; mkinjLetterSound ;
  parseAll[_,_] ; buildU ;
  pdUMany-complete ; buildU-complete ; buildU-sound ; 
  Bijective ; bijective ; pdU-bijective
  ) 

import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional.Properties as MembershipProperties
open MembershipProperties using (∈-concat⁺′ ; ∈-concat⁻′ ; ∈-map⁺ ; ∈-map⁻)

import cgp.lnegen.Order as Order
open Order -- TODO: we should only whitelist those are used here 

import cgp.lnegen.ExtendedOrder as ExtendedOrder
open ExtendedOrder using (
  pdU-sorted ;
  Ex>-sorted ; ex>-nil ; ex>-cons ;
  Ex>-maybe ; ex>-nothing ; ex>-just ;
  >-pdi-trans ;
  _,_⊢_>_ ; >-pdi )

import Data.Char as Char
open Char using (Char ; toℕ )

import Data.Char.Properties as CharProperties
open CharProperties using (≈⇒≡ ; _≈?_ ; ≈-reflexive)

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _+_ ; _∸_ ; _≤_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; _≟_ ; m+n≤o⇒m≤o∸n ; m≤o∸n⇒m+n≤o ; m+n≤o⇒n≤o ; +-identityʳ ; +-identityˡ ; m≤m+n ; m≤n+m ; +-comm ; m+n≡0⇒m≡0 ; m+n≡0⇒n≡0 ; ≡ᵇ⇒≡ ; ≡⇒≡ᵇ )



import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong; subst)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Function as Function
open Function using (case_of_)

import Data.Product as Product
open Product using (Σ; _,_; ∃; ∃-syntax; _×_)
open Σ using (proj₁ ; proj₂)

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; tail; concatMap ; _∷ʳ_ ; length ; foldr )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ; length-++ ; ++-assoc ; ∷-injective ; ≡-dec )


open import Data.List.Relation.Unary.Any using (Any; here; there ; map)

import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)

import Data.List.Membership.Propositional.Properties as MembershipProperties
open MembershipProperties using (∈-concat⁺′ ; ∈-concat⁻′ ; ∈-map⁺ ; ∈-map⁻ ; ∈-++⁻)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst; inspect)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map ; lookup)
import Data.List.Relation.Unary.All.Properties as AllProperties
open AllProperties using (++⁺)

import Relation.Nullary as Nullary
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Data.Empty using (⊥ ; ⊥-elim)
open Data.Empty

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?; map′)

open import Function using (_∘_ ; flip ; case_of_)


import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )


import cgp.lnegen.Efn as Efn
open Efn using ( Efn ; efn-ε ; efn-● ) 
```



```agda
-- Purpose: Define what it means for a parse tree u to be maximal for word w
-- Used by: ≥-max-word, ≥-max-pair-fst-prefix→>3, ≥-max-pres-left-helper, >-wellfounded, ≥-Max-PDInstance, parseAll-head-isMax
-- Proof idea: N/A (data type definition with single constructor ≥-max)
data ≥-Max : ∀ { r : RE } → List Char → U r  → Set where 
  ≥-max : ∀ { r : RE }
        → ( w : List Char )
        → ( u : U r )
        → proj₁ (flat u) ≡ w 
        → ( ( v : U r )
          →  proj₁ (flat v) ≡ w 
          → r ⊢ u ≥ v )
        → ≥-Max {r} w u

-- we need to use this lemma in dom-lemma-weak
-- no, this is bogus, not in use, we use the variant >2 and >3 below (with better names)
-- reriting FRONTIER
≥-max-pair-fst-prefix→> : ∀ { l r : RE } { loc : ℕ } → (u : U l) → (v : U r)
  → ≥-Max {l ● r ` loc} (proj₁ (flat (PairU {l} {r} {loc} u v))) (PairU u v)
  → ( u' : U l )
  → ( v' : U r )
--   → ¬ ( ∃[ c ] ∃[ w ]   ( proj₁ (flat u') ≡ proj₁ (flat u) ++ ( c ∷ w ) )
--                       × ( proj₁ (flat v)) ≡ (c ∷ w ++ (proj₁ (flat v') )) ) 
  → ( ∃[ c ] ∃[ w ]   ( proj₁ (flat u') ≡ proj₁ (flat u) ++ ( c ∷ w ) )
                    × ( proj₁ (flat v)) ≡ (c ∷ w ++ (proj₁ (flat v')) ) ) 
  -- → ( Σ[ c ∈ Char ] Σ[ w ∈ List Char ] ( ( proj₁ (flat u') ≡ proj₁ (flat u) ++ ( c ∷ w ) ) × ( ( proj₁ (flat v) ) ≡ (c ∷ w ++ (proj₁ (flat v'))) ) ) )
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


-- is this used?
≥-max-pair-fst-prefix→>2 : ∀ { l r : RE } { loc : ℕ } → (u : U l) → (v : U r)
  → ≥-Max {l ● r ` loc} (proj₁ (flat (PairU {l} {r} {loc} u v))) (PairU u v)
  → ( u' : U l )
  → ( v' : U r )
  → (proj₁ (flat (PairU {l} {r} {loc} u' v'))) ≡ (proj₁ (flat (PairU {l} {r} {loc} u v)))
  → l ⊢ u ≥ u' 
≥-max-pair-fst-prefix→>2 {l = l} {r = r} {loc} u v (≥-max _ _ _ μ) u' v' |u'v'|≡|uv| =
  helper (μ (PairU u' v') same-word)
  where
    same-word : proj₁ (flat {l ● r ` loc} (PairU u' v')) ≡ proj₁ (flat {l ● r ` loc} (PairU u v))
    same-word =  |u'v'|≡|uv| 
    helper : l ● r ` loc ⊢ PairU u v ≥ PairU u' v' → l ⊢ u ≥ u'
    helper (inj₂ refl) = inj₂ refl 
    helper (inj₁ (be _ _ (seq₁ u>u'))) = inj₁ u>u'
    helper (inj₁ (be _ _ (seq₂ u≡u' _))) = inj₂ u≡u' 
    helper (inj₁ (bne _ _ (seq₁ u>u'))) = inj₁ u>u'
    helper (inj₁ (bne _ _ (seq₂ u≡u' _))) = inj₂ u≡u'  
    helper (inj₁ (lne len>0 len'≡0)) rewrite trans (sym (cong length same-word)) len'≡0 = ⊥-elim (Nullary.contradiction len>0 (λ { () })) 


-- we need this to get ≥-Max u from ≥-Max (PairU u v)  -- there seems to be similar lemma below
≥-max-pair-fst-prefix→>3 : ∀ { l r : RE } { loc : ℕ } → (u : U l) → (v : U r)
  → ≥-Max {l ● r ` loc} (proj₁ (flat (PairU {l} {r} {loc} u v))) (PairU u v)
  → ≥-Max {l} (proj₁ (flat u)) u 
≥-max-pair-fst-prefix→>3 {l} {r} {loc} u v m@(≥-max _ _ _ μ) = ≥-max (proj₁ (flat u)) u refl prf
  where
    prf : (v₁ : U l)
      → proj₁ (flat v₁) ≡ proj₁ (flat u)
      → l ⊢ u ≥ v₁
    prf v₁ |v₁|≡|u| = ≥-max-pair-fst-prefix→>2 u v m v₁ v |v₁v|≡|uv|
      where
        |v₁v|≡|uv| : proj₁ (flat (PairU {l} {r} {loc} v₁ v)) ≡ proj₁ (flat (PairU {l} {r} {loc} u v))
        |v₁v|≡|uv| rewrite |v₁|≡|u| = refl              


-- ≥-max-pair-fst-prefix→>4 : ∀ { p l r : RE } { loc : ℕ } → (u : U p) → (v : U r)
--   → ≥-Max {p ● r ` loc} (proj₁ (flat (PairU {p} {r} {loc} u v))) (PairU u v)


-- each partial derivative p is unique
-- inj is ≥-Max-Preserve is given an u which is max, and another v,
-- we must have inj u ≥ inj v



-- Purpose: Extract the word-equality proof from a ≥-Max proof
-- Used by: max-pair→max-snd
-- Proof idea: Direct pattern matching on ≥-max constructor
≥-max-word : ∀ {r : RE} {w : List Char} {u : U r} → ≥-Max w u → proj₁ (flat u) ≡ w
≥-max-word (≥-max _ _ eq _) = eq

-- Purpose: Lift ≥-Max from inj u to LeftU (inj u) in a + regex
-- Used by: ≥-max-pres-left-pdi
-- Proof idea: If v is LeftU, use left-mono; if v is RightU, LeftU > RightU by choice
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


-- Purpose: Inverse of ≥-max-pres-left-helper: extract ≥-Max of inj u from LeftU (inj u)
-- Used by: (internal helper, not called externally in this file)
-- Proof idea: Wrap any competitor v into LeftU v and use the original ≥-Max
≥-max-pres-left-helper-inv : (p l r : RE) (loc : ℕ) (c : Char) (inj : U p → U l)
  → (u : U p) (w : List Char)
  → ≥-Max (c ∷ w) (LeftU {l} {r} {loc} (inj u))
  → ≥-Max (c ∷ w) (inj u)
≥-max-pres-left-helper-inv p l r loc c inj u w (≥-max _ _ flat-left-inj-u≡c∷w μ') =
  ≥-max (c ∷ w) (inj u)
    flat-left-inj-u≡c∷w prf
  where
    prf : (v : U l) → proj₁ (flat v) ≡ c ∷ w → l ⊢ inj u ≥ v
    prf v |v|≡c∷w with μ' (LeftU {l} {r} {loc} v) |v|≡c∷w
    ... | inj₂ refl  = inj₂ refl
    ... | inj₁ (bne len|left-inj-u|>0 len|left-v|>0 (choice-ll inj-u>ⁱv))     =  inj₁ inj-u>ⁱv
    ... | inj₁ (lne len|left-inj-u|>0 len|left-v|≡0) = Nullary.contradiction |left-v|≡[] ¬|left-v|≡[] 
      where
        |left-v|≡[] : proj₁ (flat (LeftU {l} {r} {loc} v)) ≡ []
        |left-v|≡[] = length≡0→[] len|left-v|≡0 
        ¬|left-v|≡[] : ¬ ( proj₁ (flat (LeftU {l} {r} {loc} v)) ≡ []) 
        ¬|left-v|≡[] rewrite  |v|≡c∷w =  Utils.¬∷≡[]
        
    ... | inj₁ (be len|left-inj-u|≡0 len|left-v|≡0 _ ) =  Nullary.contradiction |left-v|≡[] ¬|left-v|≡[] 
      where
        |left-v|≡[] : proj₁ (flat (LeftU {l} {r} {loc} v)) ≡ []
        |left-v|≡[] = length≡0→[] len|left-v|≡0 
        ¬|left-v|≡[] : ¬ ( proj₁ (flat (LeftU {l} {r} {loc} v)) ≡ []) 
        ¬|left-v|≡[] rewrite  |v|≡c∷w =  Utils.¬∷≡[]






-- Purpose: proj₁ of flat for LeftU equals proj₁ of flat of the inner tree
-- Used by: ≥-max-pres-right-helper, ≥-max-pres-left-helper-inv
-- Proof idea: Structural induction on U constructor (refl in each case)
proj₁-flat-LeftU : ∀ {l r : RE} {loc : ℕ} (v₁ : U l) → proj₁ (flat {l + r ` loc} (LeftU v₁)) ≡ proj₁ (flat v₁)
proj₁-flat-LeftU {ε} {r} {loc} EmptyU = refl
proj₁-flat-LeftU {$ c ` loc} {r} {loc'} (LetterU c) = refl
proj₁-flat-LeftU {l₁ + l₂ ` loc} {r} {loc'} (LeftU v₁) = refl
proj₁-flat-LeftU {l₁ + l₂ ` loc} {r} {loc'} (RightU v₁) = refl
proj₁-flat-LeftU {l₁ ● l₂ ` loc} {r} {loc'} (PairU v₁ v₂) = refl
proj₁-flat-LeftU {l₁ * nε ` loc} {r} {loc'} (ListU vs) = refl

  



-- len-flat-pair (top-level): length of flat(PairU a b) decomposes as sum of component lengths.
-- Needed by extract-≥-snd.
len-flat-pair : ∀ {l' r' : RE} {loc' : ℕ} {a : U l'} {b : U r'}
  → length (proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} a b))) ≡ length (proj₁ (flat {l'} a)) + length (proj₁ (flat {r'} b))
len-flat-pair {l'} {r'} {loc'} {a = a} {b = b} with flat {l'} a | flat {r'} b
... | xs , xs∈l | ys , ys∈r = length-++ xs {ys}

-- extract-≥-snd: Project pair-wise ≥ to second-component ≥.
-- If the first components are the same and the second components have the same flat,
-- then the order on the pair gives the order on the second.
extract-≥-snd : ∀ {l' r' : RE} {loc' : ℕ} {u₁ : U l'} {u₂ u₂' : U r'}
  → proj₁ (flat {r'} u₂) ≡ proj₁ (flat {r'} u₂')
  → l' ● r' ` loc' ⊢ PairU u₁ u₂ ≥ PairU u₁ u₂' → r' ⊢ u₂ ≥ u₂'
extract-≥-snd _ (inj₁ (be _ _ (seq₁ u₁>u₁))) = ⊥-elim (>→¬≡ u₁>u₁ refl)
extract-≥-snd _ (inj₁ (be _ _ (seq₂ refl u₂>u₂'))) = inj₁ u₂>u₂'
extract-≥-snd _ (inj₁ (bne _ _ (seq₁ u₁>u₁))) = ⊥-elim (>→¬≡ u₁>u₁ refl)
extract-≥-snd _ (inj₁ (bne _ _ (seq₂ refl u₂>u₂'))) = inj₁ u₂>u₂'
extract-≥-snd {l'} {r'} {loc'} {u₁} {u₂} {u₂'} flat-eq (inj₁ (lne len>0 len0)) =
  let len-pair≡0 = trans (sym (len-flat-pair {l'} {r'} {loc'} {a = u₁} {b = u₂'})) len0
      len-pair>0 = subst (λ x → x Nat.> 0)
        (trans (len-flat-pair {l'} {r'} {loc'} {a = u₁} {b = u₂})
               (cong (λ x → length (proj₁ (flat {l'} u₁)) + x) (cong length flat-eq)))
        len>0
  in ⊥-elim (n≡0→¬n>0 len-pair≡0 len-pair>0)
extract-≥-snd _ (inj₂ refl) = inj₂ refl

-- max-pair→max-snd: Extract maximality of the second component from pair maximality.
-- If PairU u₁ u₂ is maximal for w, then u₂ is maximal for its own word.
max-pair→max-snd : ∀ {p r : RE} {loc : ℕ} {u₁ : U p} {u₂ : U r} {w : List Char}
  → ≥-Max {p ● r ` loc} w (PairU u₁ u₂) → ≥-Max {r} (proj₁ (flat {r} u₂)) u₂
max-pair→max-snd {p} {r} {loc} {u₁} {u₂} {w} max-pair =
  ≥-max (proj₁ (flat {r} u₂)) u₂ refl (λ v₂ flat-v₂≡flat-u₂ →
    let flat-pair-v≡w : proj₁ (flat {p ● r ` loc} (PairU {p} {r} {loc} u₁ v₂)) ≡ w
        flat-pair-v≡w =
          begin
            proj₁ (flat {p ● r ` loc} (PairU {p} {r} {loc} u₁ v₂))
          ≡⟨ refl ⟩
            proj₁ (flat {p} u₁) ++ proj₁ (flat {r} v₂)
          ≡⟨ cong (proj₁ (flat {p} u₁) ++_) flat-v₂≡flat-u₂ ⟩
            proj₁ (flat {p} u₁) ++ proj₁ (flat {r} u₂)
          ≡⟨ ≥-max-word max-pair ⟩
            w
          ∎
    in extract-≥-snd (sym flat-v₂≡flat-u₂) (≥-max-pair-all max-pair (PairU {p} {r} {loc} u₁ v₂) flat-pair-v≡w))
  where
    ≥-max-pair-all : ∀ { l' r' : RE } { loc' : ℕ } { w' : List Char } { u : U (l' ● r' ` loc') }
      → ≥-Max w' u → ( v : U (l' ● r' ` loc') ) → proj₁ (flat v) ≡ w' → l' ● r' ` loc' ⊢ u ≥ v
    ≥-max-pair-all (≥-max _ _ _ μ) v flat-v≡w = μ v flat-v≡w


-- >-sorted-first>all: First element of a >-sorted list is greater than all elements in the tail.
>-sorted-first>all : ∀ {r : RE} {u : U r} {us : List (U r)}
  → >-sorted (u ∷ us)
  → (v : U r) → v ∈ us
  → r ⊢ u > v
>-sorted-first>all (>-cons _ (>-just u>v)) _ (here refl) = u>v
>-sorted-first>all (>-cons s (>-just u>head)) _ (there v∈tail) =
  >-trans u>head (>-sorted-first>all s _ v∈tail)
-- >-sorted-first>all (>-cons >-nil >-nothing) _ ()

-- >-sorted-first≥all: First element of a >-sorted list is ≥ all elements in the list.
>-sorted-first≥all : ∀ {r : RE} {u : U r} {us : List (U r)}
  → >-sorted (u ∷ us)
  → (v : U r) → v ∈ (u ∷ us)
  → r ⊢ u ≥ v
>-sorted-first≥all _ v (here refl) = inj₂ refl
>-sorted-first≥all sorted v (there v∈us) = inj₁ (>-sorted-first>all sorted v v∈us)

mkAllEmptyU-first-≥-Max : ∀ {l} (ε∈l : ε∈ l) {e₁ : U l} {es₁ : List (U l)}
  → proj₁ (flat {l} e₁) ≡ []
  → mkAllEmptyU ε∈l ≡ e₁ ∷ es₁
  → >-sorted (e₁ ∷ es₁)
  → ≥-Max {l} [] e₁
mkAllEmptyU-first-≥-Max {l} ε∈l {e₁} {es₁} flat-e₁≡[] mkAllEmptyU≡ sorted =
  ≥-max [] e₁ flat-e₁≡[]
    (λ v flat-v≡[] →
      let v∈mkAllEmptyU : v ∈ mkAllEmptyU ε∈l
          v∈mkAllEmptyU = mkAllEmptyU-complete ε∈l v (flat-[] v flat-v≡[])
          v∈es : v ∈ (e₁ ∷ es₁)
          v∈es = subst (λ x → v ∈ x) mkAllEmptyU≡ v∈mkAllEmptyU
      in helper v v∈es)
  where
    helper : (v : U l) → v ∈ (e₁ ∷ es₁) → l ⊢ e₁ ≥ v
    helper v (here refl) = inj₂ refl
    helper v (there v∈es₁) = inj₁ (>-sorted-first>all sorted _ v∈es₁)



      
-- Purpose: nothing cannot equal just x (absurd pattern)
-- Used by: first-inhabit-++-just-left-pres, first-inhabit-++-just-right-pres, first-inhabit-++-nothing-left, head-map-LeftU-++-map-RightU
-- Proof idea: Pattern matching on impossible constructor
¬nothing≡just : ∀ {A : Set} {x : A} → ¬ nothing ≡ just x
¬nothing≡just ()

-- Purpose: Injectivity of just constructor
-- Used by: first-inhabit-yes-eq-full, first-inhabit-++-just-left-pdi, first-inhabit-++-just-right-decompose, first-inhabit-++-just-left-pres′
-- Proof idea: Pattern matching on refl
just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

-- Purpose: head of a non-empty list is just the first element
-- Used by: (standalone helper for head reasoning)
-- Proof idea: Reflexivity
head-x∷xs≡just-x : ∀ { A : Set} {x : A } { xs : List A } → head ( x ∷ xs ) ≡ just x
head-x∷xs≡just-x {A} {x} {xs} = refl 


-- Purpose: If partial derivative is empty, then c∷w is not in the language
-- Used by: (helper for contradiction in pdU reasoning)
-- Proof idea: Use pdU-complete to get Any Recons, contradicting empty list
pdU≡[]→¬c∷w∈l : ∀ {l c} {w : List Char} → pdU[ l , c ] ≡ [] → ¬ ((c ∷ w) ∈⟦ l ⟧)
pdU≡[]→¬c∷w∈l {l} {c} {w} pdU≡[] c∷w∈l =
  let u = unflat c∷w∈l
      eq : proj₁ (flat {l} u) ≡ c ∷ w
      eq = cong proj₁ (flat∘unflat c∷w∈l)
      any-recons : Any (Recons {l} {c} u) pdU[ l , c ]
      any-recons = pdU-complete {l} {c} {w} u eq
  in ⊥-elim (¬Any[] (subst (λ x → Any (Recons {l} {c} u) x) pdU≡[] any-recons))

-- Purpose: pdU of a letter regex is empty for mismatching character
-- Used by: first-pdU-accept-w-isMax-$
-- Proof idea: Decision on c' ≟ c, no case gives refl
pdU[$c]≡[] : ∀ {c' c : Char} {loc : ℕ} → c ≢ c' → pdU[ $ c' ` loc , c ] ≡ []
pdU[$c]≡[] {c'} {c} ¬c≡c' with c' Char.≟ c
... | yes c'≡c = ⊥-elim (¬c≡c' (sym c'≡c))
... | no  _    = refl

-- Purpose: pdU of a letter regex is singleton list for matching character
-- Used by: first-pdU-accept-w-isMax-$
-- Proof idea: Decision on c' ≟ c' yields yes refl, then refl
pdU[$c]≡∷ : ∀ {c' : Char} {loc : ℕ} → pdU[ $ c' ` loc , c' ] ≡ [ pdinstance mkinjLetter mkinjLetterSound ]
pdU[$c]≡∷ {c'} {loc} with c' Char.≟ c'
... | yes refl = refl
... | no ¬c≡c = ⊥-elim (¬c≡c refl)

-- Purpose: If c∷[] is in a letter regex, then c must equal the regex character
-- Used by: first-pdU-accept-w-isMax
-- Proof idea: Decision on toℕ c ≟ toℕ c₀, then ≈⇒≡
c≡c'-from-∈$ : ∀ {c c' : Char} {loc : ℕ} → (c ∷ []) ∈⟦ $ c' ` loc ⟧ → c ≡ c'
c≡c'-from-∈$ {c} {c'} ( $_ c₀ ) with (toℕ c ≟ toℕ c₀)
... | yes tc≡tc₀ = sym (≈⇒≡ tc≡tc₀)
... | no ¬tc≡tc₀ = ⊥-elim (¬tc≡tc₀ refl)

-- just-inj: injectivity of just constructor
just-inj : ∀ {a : Set} {x y : a} → just x ≡ just y → x ≡ y
just-inj refl = refl

-- not in used
head-++-[]-right-∷ : ∀ {a b c : Set} {f : a → c} {g : b → c} {x : b} {xs : List b}
  → head (List.map f [] ++ List.map g (x ∷ xs)) ≡ just (g x)
head-++-[]-right-∷ = refl

-- not in used 
-- head-pdU-+-left: If the left list is non-empty, the head of the concatenated list is the left-wrapped head.
head-pdU-+-left : ∀ {l r : RE} {loc : ℕ} {c : Char} {pdi_l : PDInstance l c} {pdis_l : List (PDInstance l c)} {pdU-r : List (PDInstance r c)} {pdi : PDInstance (l + r ` loc) c}
  → head (List.map pdinstance-left (pdi_l ∷ pdis_l) ++ List.map pdinstance-right pdU-r) ≡ just pdi
  → pdi ≡ pdinstance-left pdi_l
head-pdU-+-left eq = sym (just-injective eq)

-- not in used

-- head-pdU-+-right: If the left list is empty and right is non-empty, the head is the right-wrapped head.
head-pdU-+-right : ∀ {l r : RE} {loc : ℕ} {c : Char} {pdi_r : PDInstance r c} {pdis_r : List (PDInstance r c)} {pdi : PDInstance (l + r ` loc) c}
  → head (List.map pdinstance-left [] ++ List.map pdinstance-right (pdi_r ∷ pdis_r)) ≡ just pdi
  → pdi ≡ pdinstance-right pdi_r
head-pdU-+-right eq = just-inj (sym eq)

-- head-concatmap-empty: The head of concatMap of pdinstance-snd over empty pdis is nothing.
-- Needed for the l ● r case when pdU[r,c] is empty. really? not in used now. 
-- Purpose: concatMap over empty pdis yields nothing at head
-- Used by: (internal helper for ● case when pdU[r,c] is empty)
-- Proof idea: concatMap over any xs with [] produces [], head of [] is nothing
head-concatmap-empty : ∀ {l r : RE} {loc : ℕ} {c : Char}
  → (xs : List (∃[ e ] (Flat-[] l e)))
  → head (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x []) xs) ≡ nothing
head-concatmap-empty [] = refl
head-concatmap-empty (x ∷ xs) = head-concatmap-empty xs

-- compiled but not in used

-- compiled but not in used

-- first-char-lemma: Extract c∷cs form from non-empty list with known first char.
-- compiled but not in used

-- find-recons: Extract Recons proof from Any. -- not in use?
-- compiled but not in used

-- dom-lemma: If inj u₁ is the first reconstruction of the first pdi in pdU[l,c],
-- and v₁ has a c-word different from c∷flat u₁, then l ⊢ inj u₁ > v₁.
-- extract-Recons: Extract the pdi and membership proof from Any (Recons v₁) pdis.
-- Purpose: Extract a specific pdi and Recons proof from Any Recons evidence
-- Used by: first-pdU-accept-w-isMax-●-no, first-pdU-accept-w-isMax-●-yes, first-pdU-accept-w-isMax-*
-- Proof idea: Induction on Any, threading membership evidence
extract-Recons : ∀ {r c v₁} {pdis : List (PDInstance r c)}
  → Any (Recons {r} {c} v₁) pdis
  → ∃ λ pdi → pdi ∈ pdis × Recons v₁ pdi
extract-Recons (here recons-v₁) = _ , here refl , recons-v₁
extract-Recons (there v₁∈pdis) with extract-Recons v₁∈pdis
... | pdi , pdi∈ , recons-v₁ = pdi , there pdi∈ , recons-v₁


-- ------ >-wellfounded lemma ----------------------

-- extract-any turns an Any proof into the witnessing element, the proof it satisfies P,
-- and the membership evidence. Used to extract a reconstructing PDInstance* from
-- pdUMany-complete.
-- Purpose: Convert Any P xs into concrete witness x with P x and membership
-- Used by: parseAll-complete
-- Proof idea: Induction on Any, extracting head or recursing on tail
extract-any : ∀ {A : Set} {P : A → Set} {xs : List A}
  → Any P xs
  → ∃[ x ] (P x × x ∈ xs)
extract-any (here px) = _ , px , here refl
extract-any (there p) with extract-any p
... | x , px , x∈xs = x , px , there x∈xs

-- this should be moved to Partial Derivative.lagda.md
-- parseAll-complete: every parse tree u for w occurs in parseAll[ r , w ].
-- Proof: pdUMany-complete gives a PDInstance* that reconstructs u; buildU-complete
-- shows u is built by that PDInstance*; map and concat membership lift this to parseAll.
-- Purpose: Every parse tree for w is in parseAll
-- Used by: >-wellfounded, head-pdUparseAll→first-inhabit
-- Proof idea: pdUMany-complete → buildU-complete → ∈-concat/∈-map
parseAll-complete : ∀ {r : RE} {w : List Char} (u : U r)
  → proj₁ (flat u) ≡ w
  → u ∈ parseAll[ r , w ]
parseAll-complete {r} {w} u flat-u≡w =
  subst (λ x → u ∈ parseAll[ r , x ]) flat-u≡w helper
  where
    helper : u ∈ parseAll[ r , proj₁ (flat u) ]
    helper
      with extract-any (pdUMany-complete u)
    ... | pdi , recons*-u-pdi , pdi∈pdUMany =
      ∈-concat⁺′ (buildU-complete u pdi recons*-u-pdi) (∈-map⁺ buildU pdi∈pdUMany)

-- this should be moved to Partial Derivative.lagda.md
-- parseAll-sound: every element of parseAll[ r , w ] flattens to w.
-- Proof: each buildU pdi only contains trees flattening to w (buildU-sound), and
-- parseAll is a concatenation of such buildU results.
-- Purpose: Elements of parseAll flatten to the queried word
-- Used by: ∈?-parseAll, parseAll-nonempty, first-parseAll-isMax
-- Proof idea: ∈-concat⁻ → ∈-map⁻ → buildU-sound
parseAll-sound : ∀ {r : RE} {w : List Char} (u : U r)
  → u ∈ parseAll[ r , w ]
  → proj₁ (flat u) ≡ w
parseAll-sound {r} {w} u u∈parseAll
  with ∈-concat⁻′ (List.map buildU (pdUMany[ r , w ])) u∈parseAll
... | ys , u∈ys , ys∈map-buildU-pdUMany
  with ∈-map⁻ buildU ys∈map-buildU-pdUMany
... | pdi , pdi∈pdUMany , ys≡buildU-pdi =
  lookup (buildU-sound pdi) (subst (λ zs → u ∈ zs) ys≡buildU-pdi u∈ys)

-- parseAll-nonempty: if w ∈⟦ r ⟧ then parseAll[ r , w ] is non-empty.
-- Proof: unflat w∈r is a parse tree for w, and parseAll-complete puts it in the list.
-- Purpose: parseAll is non-empty for accepted words
-- Used by: >-wellfounded
-- Proof idea: unflat gives a parse tree, parseAll-complete puts it in the list
parseAll-nonempty : ∀ {r : RE} {w : List Char}
  → w ∈⟦ r ⟧
  → parseAll[ r , w ] ≢ []
parseAll-nonempty {r} {w} w∈r = extract-nonempty (parseAll-complete (unflat w∈r) flat-unflat≡w)
  where
    flat-unflat≡w : proj₁ (flat (unflat w∈r)) ≡ w
    flat-unflat≡w = cong proj₁ (flat∘unflat w∈r)

    extract-nonempty : ∀ {A : Set} {x : A} {xs : List A} → x ∈ xs → xs ≢ []
    extract-nonempty (here refl) ()
    extract-nonempty (there p) = λ ()

-- pick returns the greater of two parse trees according to the total LNE order.
-- Purpose: Return the greater of two parse trees under LNE order
-- Used by: maximum
-- Proof idea: Trichotomy on >-order, returning the greater or either if equal
pick : ∀ {r : RE} → U r → U r → U r
pick v best
  with >-trichotomy best v
... | inj₁ best>v   = best
... | inj₂ (inj₁ v>best) = v
... | inj₂ (inj₂ best≡v) = best

-- pick preserves the flattened word: if both candidates flatten to w, so does the pick.
-- Purpose: pick returns a tree that flattens to the same word
-- Used by: maximum-flat
-- Proof idea: Trichotomy gives one of {best, v}, both flatten to w
pick-preserves-flat : ∀ {r : RE} {w : List Char} (v best : U r)
  → proj₁ (flat v) ≡ w
  → proj₁ (flat best) ≡ w
  → proj₁ (flat (pick v best)) ≡ w
pick-preserves-flat v best flat-v≡w flat-best≡w
  with >-trichotomy best v
... | inj₁ best>v = flat-best≡w
... | inj₂ (inj₁ v>best) = flat-v≡w
... | inj₂ (inj₂ best≡v) = flat-best≡w

-- maximum selects the largest element of a non-empty list of parse trees using foldr
-- and the total LNE order. Used to obtain the maximal parse tree from parseAll.
-- Purpose: Compute the maximal element of a non-empty list under LNE order
-- Used by: >-wellfounded, parseAll-head-isMax, first-pdU-accept-w-isMax-●-no, first-pdU-accept-w-isMax-●-yes, first-pdU-accept-w-isMax-*
-- Proof idea: foldr with pick, base element is head
maximum : ∀ {r : RE} (us : List (U r)) → us ≢ [] → U r
maximum [] neq = ⊥-elim (neq refl)
maximum (u ∷ us) neq = foldr pick u us

-- parseAll-all-sound: every element of parseAll[ r , w ] flattens to w.
-- Purpose: All elements of parseAll satisfy flat ≡ w
-- Used by: >-wellfounded
-- Proof idea: buildU-sound for each pdi in pdUMany, then ++⁺
parseAll-all-sound : ∀ {r : RE} {w : List Char}
  → All (λ u → proj₁ (flat u) ≡ w) (parseAll[ r , w ])
parseAll-all-sound {r} {w} =
  all-buildU-sound (pdUMany[ r , w ])
  where
    all-buildU-sound : (pdis : List (PDInstance* r w))
      → All (λ u → proj₁ (flat u) ≡ w) (concatMap buildU pdis)
    all-buildU-sound [] = []
    all-buildU-sound (pdi ∷ pdis) = ++⁺ (buildU-sound pdi) (all-buildU-sound pdis)

-- maximum-flat: if all elements of a non-empty list flatten to w, so does their maximum.
-- Purpose: maximum preserves the flattened word
-- Used by: >-wellfounded
-- Proof idea: Induction on foldr with pick-preserves-flat
maximum-flat : ∀ {r : RE} {w : List Char} (us : List (U r)) (neq : us ≢ [])
  → All (λ u → proj₁ (flat u) ≡ w) us
  → proj₁ (flat (maximum us neq)) ≡ w
maximum-flat {r} {w} [] neq _ = ⊥-elim (neq refl)
maximum-flat {r} {w} (u ∷ us) neq all-flat = foldr-flat u us all-flat
  where
    foldr-flat : (u : U r) (us : List (U r))
      → All (λ u → proj₁ (flat u) ≡ w) (u ∷ us)
      → proj₁ (flat (foldr pick u us)) ≡ w
    foldr-flat u [] (flat-u≡w ∷ []) = flat-u≡w
    foldr-flat u (v ∷ us) (flat-u≡w ∷ flat-v≡w ∷ all-flat) =
      pick-preserves-flat v (foldr pick u us)
        flat-v≡w
        (foldr-flat u us (flat-u≡w ∷ all-flat))

-- maximum-≥-all: the element returned by maximum is ≥ every element of the list.
maximum-≥-all : ∀ {r : RE} (us : List (U r)) (neq : us ≢ []) (v : U r)
  → v ∈ us
  → r ⊢ maximum us neq ≥ v
maximum-≥-all [] neq _ _ = ⊥-elim (neq refl)
maximum-≥-all {r} (u ∷ us) neq v v∈ = foldr-≥ u us v v∈
  where
    foldr-≥ : (u : U r) (us : List (U r)) (v : U r)
      → v ∈ (u ∷ us)
      → r ⊢ foldr pick u us ≥ v
    foldr-≥ u [] .u (here refl) = ≥-refl
    foldr-≥ u [] v (there ())
    foldr-≥ u (w ∷ us) .u (here refl)
      with >-trichotomy (foldr pick u us) w
    ... | inj₁ best>w = foldr-≥ u us u (here refl)
    ... | inj₂ (inj₁ w>best) = ≥-trans (inj₁ w>best) (foldr-≥ u us u (here refl))
    ... | inj₂ (inj₂ best≡w) = foldr-≥ u us u (here refl)
    foldr-≥ u (w ∷ us) .w (there (here refl))
      with >-trichotomy (foldr pick u us) w
    ... | inj₁ best>w = inj₁ best>w
    ... | inj₂ (inj₁ w>best) = ≥-refl
    ... | inj₂ (inj₂ best≡w) = inj₂ best≡w
    foldr-≥ u (w ∷ us) v (there (there v∈''))
      with >-trichotomy (foldr pick u us) w
    ... | inj₁ best>w = foldr-≥ u us v (there v∈'')
    ... | inj₂ (inj₁ w>best) = ≥-trans (inj₁ w>best) (foldr-≥ u us v (there v∈''))
    ... | inj₂ (inj₂ best≡w) = foldr-≥ u us v (there v∈'')

-- >-wellfounded: every word w ∈⟦ r ⟧ has a ≥-Max parse tree under the LNE order.
-- Proof: enumerate all parse trees with parseAll, take their maximum using the total
-- order, and use parseAll-completeness to show every competitor appears in the list.
>-wellfounded : ∀ { r : RE} { w : List Char }
  → w ∈⟦ r ⟧
  → ∃[ v ] ( ≥-Max {r}  w v )
>-wellfounded {r} {w} w∈r =
  let v = maximum (parseAll[ r , w ]) (parseAll-nonempty w∈r)
  in v , ≥-max w v (maximum-flat _ _ (parseAll-all-sound {r} {w}))
       (λ u flat-u≡w → maximum-≥-all _ _ u (parseAll-complete u flat-u≡w))

```



```agda



-- ∈?-parseAll: decide word membership via the derivative-based parser.
-- w ∈⟦ r ⟧ iff parseAll[ r , w ] is non-empty (parseAll-nonempty / parseAll-sound).
-- Purpose: Decidable word membership via parseAll
-- Used by: _∈?⟦_⟧, parseAll-no→[]
-- Proof idea: If parseAll is non-empty, extract word; else contradict nonempty lemma
∈?-parseAll : ( w : List Char ) → ( r : RE ) → Dec ( w ∈⟦ r ⟧ )
∈?-parseAll w r with parseAll[ r , w ] in eq
... | [] = no (λ w∈r → parseAll-nonempty w∈r eq)
... | (u ∷ us) = yes (subst (λ x → x ∈⟦ r ⟧) (parseAll-sound u (subst (λ x → u ∈ x) (sym eq) (here refl))) (proj₂ (flat u)))

-- Purpose: Infix alias for ∈?-parseAll
-- Used by: first-inhabit, first-inhabit-just-∈, first-inhabit-just-first
-- Proof idea: Direct alias
_∈?⟦_⟧ : ( w : List Char ) → ( r : RE ) → Dec ( w ∈⟦ r ⟧ )
_∈?⟦_⟧ =  ∈?-parseAll


-- Purpose: Local preservation property for pdinstance: if inj preserves ≥-Max then ≥-Max-Preserve-Local holds
-- Used by: pdU-preseve-local, ≥-Max-Preserve-Local-map-left, ≥-Max-Preserve-Local-map-fst
-- Proof idea: N/A (data type definition)
data ≥-Max-Preserve-Local : ∀ { r : RE } { c : Char } → PDInstance r c → Set where
  ≥-max-pres-local : ∀ { p r : RE } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ≥-Max {p} (proj₁ (flat u)) u
      → ( v : U p ) 
      → p ⊢ u ≥ v
      → r ⊢ inj u ≥ inj v ) 
    → ≥-Max-Preserve-Local {r} {c} (pdinstance inj sound-ev)




-- Purpose: Lift ≥-Max-Preserve-Local through pdinstance-left mapping
-- Used by: pdU-preseve-local (+ case)
-- Proof idea: Induction on pdis, LeftU > LeftU by choice-ll and inner >
≥-Max-Preserve-Local-map-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdis : List (PDInstance l c ))
  → All (≥-Max-Preserve-Local {l} {c}) pdis
  → All (≥-Max-Preserve-Local {l + r ` loc} {c}) (List.map pdinstance-left pdis)
≥-Max-Preserve-Local-map-left {l} {r} {loc} {c} [] [] = []
≥-Max-Preserve-Local-map-left {l} {r} {loc} {c} ((pdinstance {p} .{l} .{c} inj sound-ev) ∷ pdis ) ((≥-max-pres-local u→max-u→v→u≥v→inju≥injv) ∷ pxs ) = ≥-max-pres-local ev ∷  ≥-Max-Preserve-Local-map-left pdis pxs  
  where    
    ev : (u : U p)
       → ≥-Max (proj₁ (flat u)) u
       → (v : U p)
       → p ⊢ u ≥ v
       → (l + r ` loc) ⊢ LeftU (inj u) ≥ LeftU (inj v)
    ev u max-u@(≥-max .{p} w .(u) |u|≡w v→|v|≡w→u≥v)  v u≥v with u→max-u→v→u≥v→inju≥injv u max-u v u≥v 
    ... | inj₂ inju≡injv = inj₂ (cong LeftU inju≡injv)
    ... | inj₁ inju>injv = inj₁ (bne (len>0-inj u) (len>0-inj v) (choice-ll inju>injv) )
      where
        len>0-inj : ∀ (x : U p ) → length (proj₁ (flat {l} (inj x))) Nat.> 0
        len>0-inj x rewrite sound-ev x = Nat.s≤s Nat.z≤n





-- Purpose: Lift ≥-Max-Preserve-Local through pdinstance-right mapping
-- Used by: pdU-preseve-local (+ case)
-- Proof idea: Induction on pdis, RightU > RightU by choice-rr and inner >
≥-Max-Preserve-Local-map-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdis : List (PDInstance r c ))
  → All (≥-Max-Preserve-Local {r} {c}) pdis
  → All (≥-Max-Preserve-Local {l + r ` loc} {c}) (List.map pdinstance-right pdis)
≥-Max-Preserve-Local-map-right {l} {r} {loc} {c} [] [] = []
≥-Max-Preserve-Local-map-right {l} {r} {loc} {c} ((pdinstance {p} .{r} .{c} inj sound-ev) ∷ pdis ) ((≥-max-pres-local u→max-u→v→u≥v→inju≥injv) ∷ pxs ) = ≥-max-pres-local ev ∷  ≥-Max-Preserve-Local-map-right pdis pxs  
  where    
    ev : (u : U p)
       → ≥-Max (proj₁ (flat u)) u
       → (v : U p)
       → p ⊢ u ≥ v
       → (l + r ` loc) ⊢ RightU (inj u) ≥ RightU (inj v)
    ev u max-u@(≥-max .{p} w .(u) |u|≡w v→|v|≡w→u≥v)  v  u≥v with u→max-u→v→u≥v→inju≥injv u max-u v u≥v
    ... | inj₂ inju≡injv = inj₂ (cong RightU inju≡injv)
    ... | inj₁ inju>injv = inj₁ (bne (len>0-inj u) (len>0-inj v) (choice-rr inju>injv) )
      where
        len>0-inj : ∀ (x : U p ) → length (proj₁ (flat {r} (inj x))) Nat.> 0
        len>0-inj x rewrite sound-ev x = Nat.s≤s Nat.z≤n



-- Decidable equality for List Char
_≟C_ : (xs ys : List Char) → Dec (xs ≡ ys)
_≟C_ = ≡-dec Char._≟_



-- Purpose: Lift ≥-Max-Preserve-Local through pdinstance-fst for ● regex
-- Used by: pdU-preseve-local (● case), first-pdU-accept-w-isMax-●-no, first-pdU-accept-w-isMax-●-yes
-- Proof idea: Case analysis on ≥ relation using bijectivity and pair decomposition
≥-Max-Preserve-Local-map-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdis : List (PDInstance l c ) )
  → All (Bijective {l} {c}) pdis 
  → All (≥-Max-Preserve-Local {l} {c}) pdis
  → All (≥-Max-Preserve-Local {l ● r ` loc} {c}) (List.map (pdinstance-fst {l} {r} {loc} {c}) pdis)
≥-Max-Preserve-Local-map-fst [] [] [] = []
≥-Max-Preserve-Local-map-fst {l} {r} {loc} {c} ((pdinstance {p} .{l} .{c}  inj sound-ev) ∷ pdis) ((bijective u→v→u≡v→inju≡injv u→v→inju≡injv→u≡v ) ∷ bijects)  ((≥-max-pres-local u→max-u→v→u≥v→inju≥injv) ∷ max-preses ) =  ≥-max-pres-local ev ∷ ≥-Max-Preserve-Local-map-fst pdis bijects  max-preses 
  where
    injFst : U (p ● r ` loc)   → U (l ● r ` loc )
    injFst = mkinjFst inj
    injFstsound-ev : ∀ ( u : U ( p ● r ` loc) ) → (proj₁ (flat { l ● r ` loc } (injFst u )) ≡ c ∷ (proj₁ (flat { p ● r ` loc } u)))
    injFstsound-ev = mkinjFstSoundEv inj sound-ev


    ev : (u₁u₂ : U (p ● r ` loc))
      → ≥-Max (Product.proj₁ (flat u₁u₂)) u₁u₂
      → (v₁v₂ : U (p ● r ` loc))
      → (p ● r ` loc) ⊢ u₁u₂ ≥ v₁v₂ 
      → (l ● r ` loc) ⊢ injFst u₁u₂ ≥ injFst v₁v₂
    ev (PairU u₁ u₂) (≥-max {.p ● .r ` loc} w (PairU .u₁ .u₂) |u₁u₂|≡w v₁v₂→|v₁v₂|≡w→u₁u₂≥v₁v₂) (PairU v₁ v₂) (inj₂ u₁u₂≡v₁v₂) rewrite proj₁ (inv-pairU u₁ u₂ v₁ v₂ u₁u₂≡v₁v₂) | proj₂ (inv-pairU u₁ u₂ v₁ v₂ u₁u₂≡v₁v₂) = inj₂ refl
    ev (PairU u₁ u₂) max-pair-u₁u₂@(≥-max {.p ● .r ` loc} w (PairU .u₁ .u₂) |u₁u₂|≡w v₁v₂→|v₁v₂|≡w→u₁u₂≥v₁v₂) (PairU v₁ v₂) (inj₁ (bne len|u₁u₂|>0 len|v₁v₂|>0 (seq₁ u₁>v₁)))
      with u→max-u→v→u≥v→inju≥injv u₁  (≥-max-pair-fst-prefix→>3 u₁ u₂ max-pair-u₁u₂) v₁ (inj₁ u₁>v₁)
    ... | inj₂ inju₁≡injv₁ = Nullary.contradiction ( u→v→inju≡injv→u≡v u₁ v₁  inju₁≡injv₁ ) (>→¬≡  u₁>v₁ ) 
    ... | inj₁ inju₁>injv₁ = inj₁ (bne len|inj-u₁u₂|>0 len|inj-v₁v₂|>0 (seq₁  inju₁>injv₁) ) -- these two holes are easy
      where
        len|inj-u₁u₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₁) u₂) ))  Nat.> 0
        len|inj-u₁u₂|>0 rewrite ( injFstsound-ev (PairU {p} {r} {loc} u₁ u₂) ) = Nat.s≤s Nat.z≤n 
        len|inj-v₁v₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj v₁) v₂) ))  Nat.> 0
        len|inj-v₁v₂|>0  rewrite ( injFstsound-ev (PairU {p} {r} {loc} v₁ v₂) ) = Nat.s≤s Nat.z≤n
    ev (PairU u₁ u₂) max-pair-u₁u₂@(≥-max {.p ● .r ` loc} w (PairU .u₁ .u₂) |u₁u₂|≡w v₁v₂→|v₁v₂|≡w→u₁u₂≥v₁v₂) (PairU v₁ v₂) (inj₁ (bne len|u₁u₂|>0 len|v₁v₂|>0 (seq₂ u₁≡v₁ u₂>v₂))) = prf  -- we should have bne seq₂ since inj is bijective 
      where
        len|inj-u₁u₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₁) u₂) ))  Nat.> 0
        len|inj-u₁u₂|>0 rewrite ( injFstsound-ev (PairU {p} {r} {loc} u₁ u₂) ) = Nat.s≤s Nat.z≤n 
        len|inj-v₁v₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj v₁) v₂) ))  Nat.> 0
        len|inj-v₁v₂|>0  rewrite ( injFstsound-ev (PairU {p} {r} {loc} v₁ v₂) ) = Nat.s≤s Nat.z≤n
      
        prf : (l ● r ` loc) ⊢ PairU (inj u₁) u₂ ≥ PairU (inj v₁) v₂ 
        prf = inj₁ (bne len|inj-u₁u₂|>0 len|inj-v₁v₂|>0 (seq₂ (u→v→u≡v→inju≡injv u₁ v₁ u₁≡v₁) u₂>v₂) )       
    ev (PairU u₁ u₂) max-pair-u₁u₂@(≥-max {.p ● .r ` loc} w (PairU .u₁ .u₂) |u₁u₂|≡w v₁v₂→|v₁v₂|≡w→u₁u₂≥v₁v₂) (PairU v₁ v₂) (inj₁ (lne len|u₁u₂|>0 len|v₁v₂|≡0)) with proj₁ (flat {p} u₁) ≟C [] 
    ... | yes |u₁|≡[]  = prf 
      where
        |v₁|≡[] : proj₁ (flat v₁) ≡ []
        |v₁|≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) (length≡0→[]  len|v₁v₂|≡0 ) 
        |v₂|≡[] : proj₁ (flat v₂) ≡ []
        |v₂|≡[] = ++-conicalʳ (proj₁ (flat v₁)) (proj₁ (flat v₂)) (length≡0→[]  len|v₁v₂|≡0 ) 
        max-u₁ : ≥-Max {p} (proj₁ (flat u₁)) u₁
        max-u₁  =  ≥-max-pair-fst-prefix→>3 u₁ u₂  max-pair-u₁u₂
        |u₁|≡|v₁| : proj₁ (flat u₁) ≡ proj₁ (flat v₁)
        |u₁|≡|v₁| = trans |u₁|≡[] (sym |v₁|≡[]) 
        len|inj-u₁u₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₁) u₂) ))  Nat.> 0
        len|inj-u₁u₂|>0 rewrite ( injFstsound-ev (PairU {p} {r} {loc} u₁ u₂) ) = Nat.s≤s Nat.z≤n 
        len|inj-v₁v₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj v₁) v₂) ))  Nat.> 0
        len|inj-v₁v₂|>0  rewrite ( injFstsound-ev (PairU {p} {r} {loc} v₁ v₂) ) = Nat.s≤s Nat.z≤n
        len|u₂|>0 : length (proj₁ (flat {r} u₂)) Nat.> 0
        len|u₂|>0 rewrite |u₁|≡[] = Utils.0+nat→>0 len|u₁u₂|>0   -- from len|u₁u₂|>0 and |u₁|≡[] we should have len|u₂|>0
        u₁≥v₁ : p ⊢ u₁ ≥ v₁
        u₁≥v₁ with  max-u₁
        ... | ≥-max w .u₁ |u₁|≡w v→|v|≡w→u₁≥v = v→|v|≡w→u₁≥v v₁ (sym  |u₁|≡|v₁| )  
        prf : (l ● r ` loc) ⊢ PairU (inj u₁) u₂ ≥ PairU (inj v₁) v₂ 
        prf with u→max-u→v→u≥v→inju≥injv u₁ max-u₁ v₁ u₁≥v₁
        ... | inj₂ inju₁≡injv₁ =  inj₁ (bne len|inj-u₁u₂|>0 len|inj-v₁v₂|>0 (seq₂ inju₁≡injv₁ (lne len|u₂|>0 (Utils.[]→length≡0 |v₂|≡[]) )))
        ... | inj₁ inju₁>injv₁ =  inj₁ (bne len|inj-u₁u₂|>0 len|inj-v₁v₂|>0 (seq₁ inju₁>injv₁) ) 
    ... | no ¬|u₁|≡[]  = prf
      where
        -- case ¬|u₁|≡[], we have u₁>v₁ via lne, similar prove as the bne case above
        |v₁|≡[] : proj₁ (flat v₁) ≡ []
        |v₁|≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) (length≡0→[]  len|v₁v₂|≡0 )
        u₁>v₁ : p ⊢ u₁ > v₁
        u₁>v₁ = lne (Utils.¬≡[]→length>0 ¬|u₁|≡[]) (Utils.[]→length≡0  |v₁|≡[])
        max-u₁ : ≥-Max {p} (proj₁ (flat u₁)) u₁
        max-u₁  =  ≥-max-pair-fst-prefix→>3 u₁ u₂  max-pair-u₁u₂        
        len|inj-u₁u₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₁) u₂) ))  Nat.> 0
        len|inj-u₁u₂|>0 rewrite ( injFstsound-ev (PairU {p} {r} {loc} u₁ u₂) ) = Nat.s≤s Nat.z≤n 
        len|inj-v₁v₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj v₁) v₂) ))  Nat.> 0
        len|inj-v₁v₂|>0  rewrite ( injFstsound-ev (PairU {p} {r} {loc} v₁ v₂) ) = Nat.s≤s Nat.z≤n
        prf : (l ● r ` loc) ⊢ PairU (inj u₁) u₂ ≥ PairU (inj v₁) v₂ 
        prf with u→max-u→v→u≥v→inju≥injv u₁ max-u₁ v₁ (inj₁ u₁>v₁)
        ... | inj₂ inju₁≡injv₁ =  Nullary.contradiction ( u→v→inju≡injv→u≡v u₁ v₁ inju₁≡injv₁ ) (>→¬≡  u₁>v₁ )   
        ... | inj₁ inju₁>injv₁ =  inj₁ (bne len|inj-u₁u₂|>0 len|inj-v₁v₂|>0 (seq₁ inju₁>injv₁) )  

          
    ev (PairU u₁ u₂) max-pair-u₁u₂@(≥-max {.p ● .r ` loc} w (PairU .u₁ .u₂) |u₁u₂|≡w v₁v₂→|v₁v₂|≡w→u₁u₂≥v₁v₂) (PairU v₁ v₂) (inj₁ (be len|u₁u₂|≡len|v₁v₂| len|v₁v₂|≡0 (seq₁ u₁>v₁))) = prf  
      -- be case similar to the the bne case above.
      where
        |u₁|≡[] : proj₁ (flat u₁) ≡ []
        |u₁|≡[] = ++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat u₂)) (length≡0→[] (trans len|u₁u₂|≡len|v₁v₂| len|v₁v₂|≡0 ) ) 
        |u₂|≡[] : proj₁ (flat u₂) ≡ []
        |u₂|≡[] = ++-conicalʳ (proj₁ (flat u₁)) (proj₁ (flat u₂)) (length≡0→[] (trans len|u₁u₂|≡len|v₁v₂| len|v₁v₂|≡0 )  ) 
        
        |v₁|≡[] : proj₁ (flat v₁) ≡ []
        |v₁|≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) (length≡0→[]  len|v₁v₂|≡0 ) 
        |v₂|≡[] : proj₁ (flat v₂) ≡ []
        |v₂|≡[] = ++-conicalʳ (proj₁ (flat v₁)) (proj₁ (flat v₂)) (length≡0→[]  len|v₁v₂|≡0 ) 
        max-u₁ : ≥-Max {p} (proj₁ (flat u₁)) u₁
        max-u₁  =  ≥-max-pair-fst-prefix→>3 u₁ u₂  max-pair-u₁u₂
        |u₁|≡|v₁| : proj₁ (flat u₁) ≡ proj₁ (flat v₁)
        |u₁|≡|v₁| = trans |u₁|≡[] (sym |v₁|≡[])
        u₁≥v₁ : p ⊢ u₁ ≥ v₁
        u₁≥v₁ with  max-u₁
        ... | ≥-max w .u₁ |u₁|≡w v→|v|≡w→u₁≥v = v→|v|≡w→u₁≥v v₁ (sym  |u₁|≡|v₁| )  
        
        len|inj-u₁u₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₁) u₂) ))  Nat.> 0
        len|inj-u₁u₂|>0 rewrite ( injFstsound-ev (PairU {p} {r} {loc} u₁ u₂) ) = Nat.s≤s Nat.z≤n 
        len|inj-v₁v₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj v₁) v₂) ))  Nat.> 0
        len|inj-v₁v₂|>0  rewrite ( injFstsound-ev (PairU {p} {r} {loc} v₁ v₂) ) = Nat.s≤s Nat.z≤n
        prf : (l ● r ` loc) ⊢ PairU (inj u₁) u₂ ≥ PairU (inj v₁) v₂ 
        prf with u→max-u→v→u≥v→inju≥injv u₁ max-u₁ v₁ u₁≥v₁
        ... | inj₂ inju₁≡injv₁ =  Nullary.contradiction ( u→v→inju≡injv→u≡v u₁ v₁ inju₁≡injv₁ ) (>→¬≡  u₁>v₁ )    
        ... | inj₁ inju₁>injv₁ =  inj₁ (bne len|inj-u₁u₂|>0 len|inj-v₁v₂|>0 (seq₁ inju₁>injv₁) ) 

    ev (PairU u₁ u₂) max-pair-u₁u₂@(≥-max {.p ● .r ` loc} w (PairU .u₁ .u₂) |u₁u₂|≡w v₁v₂→|v₁v₂|≡w→u₁u₂≥v₁v₂) (PairU v₁ v₂) (inj₁ (be len|u₁u₂|≡0 len|v₁v₂|≡0 (seq₂ u₁≡v₁ u₂>v₂))) =  prf  -- we should have bne seq₂ since inj is bijective 
      where
        len|inj-u₁u₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₁) u₂) ))  Nat.> 0
        len|inj-u₁u₂|>0 rewrite ( injFstsound-ev (PairU {p} {r} {loc} u₁ u₂) ) = Nat.s≤s Nat.z≤n 
        len|inj-v₁v₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj v₁) v₂) ))  Nat.> 0
        len|inj-v₁v₂|>0  rewrite ( injFstsound-ev (PairU {p} {r} {loc} v₁ v₂) ) = Nat.s≤s Nat.z≤n
      
        prf : (l ● r ` loc) ⊢ PairU (inj u₁) u₂ ≥ PairU (inj v₁) v₂ 
        prf = inj₁ (bne len|inj-u₁u₂|>0 len|inj-v₁v₂|>0 (seq₂ (u→v→u≡v→inju≡injv u₁ v₁ u₁≡v₁) u₂>v₂) )  



-- Purpose: Lift ≥-Max-Preserve-Local through mk-snd-pdi (singleton case)
-- Used by: ≥-Max-Preserve-Local-concatmap-pdinstance-inc-pdinstance-snd
-- Proof idea: seq₂ with inner ≥ via bijectivity, length > 0 from sound-ev
≥-Max-Preserve-Local-mk-snd-pdi : ∀ { l r : RE } { loc : ℕ } { c : Char }
   → ( e-flat-[]-e : (∃[ e ] Flat-[] l e)  )
   → ( pdi : PDInstance r c )
   → Bijective {r} {c} pdi 
   → ≥-Max-Preserve-Local {r} {c} pdi 
   -------------------------------------------------------------------
   → ≥-Max-Preserve-Local (mk-snd-pdi {l} {r} {loc} {c} e-flat-[]-e pdi) 
≥-Max-Preserve-Local-mk-snd-pdi {l} {r} {loc} {c} (e , flat-[] e' proj₁∘flate≡[]) (pdinstance {p} {r} {c} inj s-ev) (bijective u→v→u≡v→inju≡injv u→v→inju≡injv→u≡v ) (≥-max-pres-local u→max-u→v→u≥v→inju≥injv) = ≥-max-pres-local local-max-ev
  where
    injSnd :  U p → U (l ● r ` loc)
    injSnd = mkinjSnd {l} {r} {p} {loc} inj e
  
    injSnd-s-ev : ( u : U p ) → proj₁ (flat (injSnd u)) ≡ c ∷ proj₁ (flat u ) 
    injSnd-s-ev u = mkinjSndSoundEv {p} {l} {r} {loc} {c} inj s-ev e ( flat-[] e' proj₁∘flate≡[] ) u


    local-max-ev : (u : U p)
      → ≥-Max (Product.proj₁ (flat u)) u
      → (v : U p)
      → p ⊢ u ≥ v
      → (l ● r ` loc) ⊢ mkinjSnd inj e u ≥ mkinjSnd inj e v
    local-max-ev u (≥-max .{p} w .u |u|≡w v→|v|≡w→u≥v) v (inj₂ u≡v) rewrite u≡v = inj₂ refl
    local-max-ev u max-u@(≥-max .{p} w .u |u|≡w v→|v|≡w→u≥v) v (inj₁ u>v) = inj₁ (bne len|e-inj-u|>0 len|e-inj-v|>0 (seq₂ refl inju>injv  ))
      where
        len|e-inj-u|>0 : length (proj₁ (flat (PairU {l} {r} {loc} e (inj u))))  Nat.> 0
        len|e-inj-u|>0 rewrite  injSnd-s-ev u = Nat.s≤s Nat.z≤n 
        len|e-inj-v|>0 : length (proj₁ (flat (PairU {l} {r} {loc} e (inj v))))  Nat.> 0
        len|e-inj-v|>0 rewrite  injSnd-s-ev v = Nat.s≤s Nat.z≤n 
        inju>injv : r ⊢ inj u > inj v
        inju>injv with u→max-u→v→u≥v→inju≥injv u max-u v (inj₁ u>v)
        ... | inj₂ inju≡injv =  Nullary.contradiction ( u→v→inju≡injv→u≡v u v inju≡injv ) (>→¬≡  u>v )  
        ... | inj₁ inju>injv = inju>injv         

-- Purpose: Lift ≥-Max-Preserve-Local through mk-snd-pdi for a list of pdis
-- Used by: ≥-Max-Preserve-Local-concatmap-pdinstance-snd-sub
-- Proof idea: Induction on pdis, applying ≥-Max-Preserve-Local-mk-snd-pdi per element
≥-Max-Preserve-Local-concatmap-pdinstance-inc-pdinstance-snd : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( e-flat-[]-e : ∃[ e ] Flat-[] l e )
  → ( pdis : List (PDInstance r c ) )
  → All (Bijective {r} {c}) pdis  
  → All (≥-Max-Preserve-Local {r} {c}) pdis
  ---------------------------------------------------------------------------
  → All (≥-Max-Preserve-Local { l ● r ` loc } {c}) (List.map  (mk-snd-pdi e-flat-[]-e ) pdis )
≥-Max-Preserve-Local-concatmap-pdinstance-inc-pdinstance-snd e-flat-[]-e []    []       [] = []
≥-Max-Preserve-Local-concatmap-pdinstance-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e-flat-[]-e (pdi ∷ pdis) (bijective-pdi ∷ all-bijective-pdis) (max-pres-pdi ∷ all-max-pres-pdis) =
  ≥-Max-Preserve-Local-mk-snd-pdi e-flat-[]-e pdi bijective-pdi max-pres-pdi  ∷ ≥-Max-Preserve-Local-concatmap-pdinstance-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  e-flat-[]-e pdis all-bijective-pdis all-max-pres-pdis   

-- Purpose: Sub-lemma for concatmap-pdinstance-snd preservation over empty-tree list
-- Used by: ≥-Max-Preserve-Local-concatmap-pdinstance-snd
-- Proof idea: Induction on e-flat-[]-es, splitting into head+tail via all-concat
≥-Max-Preserve-Local-concatmap-pdinstance-snd-sub :  ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( e-flat-[]-es  : List ( ∃[ e ] Flat-[] l e ) )
  → ( pdis : List (PDInstance r c ) )
  → All (Bijective {r} {c}) pdis  
  → All (≥-Max-Preserve-Local {r} {c}) pdis 
  -----------------------------------------------------------------------------------------------------
  → All (≥-Max-Preserve-Local { l ● r ` loc } {c}) (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) e-flat-[]-es)
≥-Max-Preserve-Local-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} [] _ _ _  = []  
≥-Max-Preserve-Local-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} ( e-flat-[]-e ∷ e-flat-[]-es ) pdis all-bijective-pdis all-max-pres-pdis =   all-concat  (≥-Max-Preserve-Local-concatmap-pdinstance-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  e-flat-[]-e pdis all-bijective-pdis all-max-pres-pdis ) (≥-Max-Preserve-Local-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} e-flat-[]-es pdis all-bijective-pdis all-max-pres-pdis )  
  


-- Purpose: ≥-Max-Preserve-Local is preserved through concatmap-pdinstance-snd
-- Used by: pdU-preseve-local (●, ε∈l case), first-pdU-accept-w-isMax-●-yes
-- Proof idea: Reduce to concatmap-snd-sub via zip-es-flat-[]-es from mkAllEmptyU
≥-Max-Preserve-Local-concatmap-pdinstance-snd : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( pdis : List (PDInstance r c ) )
  → All (Bijective {r} {c}) pdis
  → All (≥-Max-Preserve-Local {r} {c}) pdis  
  → All (≥-Max-Preserve-Local { l ● r ` loc } {c}) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  pdis)
≥-Max-Preserve-Local-concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis all-biject-pdis all-max-pres-local-pdis = ≥-Max-Preserve-Local-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es) pdis all-biject-pdis  all-max-pres-local-pdis   
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l    
  



```


```agda

-- Purpose: ≥-Max-Preserve-Local is preserved through pdinstance-star
-- Used by: pdU-preseve-local (* case)
-- Proof idea: Induction on pdis, star-head/star-tail ordering from inner >
≥-Max-Preserve-Local-map-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  → ( pdis : List (PDInstance r c ) )
  → All (Bijective {r} {c}) pdis
  → All (≥-Max-Preserve-Local {r} {c}) pdis
  → All (≥-Max-Preserve-Local {r * ε∉r ` loc} {c}) (List.map (pdinstance-star {r} {ε∉r} {loc} {c}) pdis)
≥-Max-Preserve-Local-map-star [] [] [] = []
≥-Max-Preserve-Local-map-star {r} {ε∉r} {loc} {c} ((pdinstance {p} .{r} .{c} inj sound-ev) ∷ pdis) ((bijective u→v→u≡v→inju≡injv u→v→inju≡injv→u≡v) ∷ bijects) ((≥-max-pres-local u→max-u→v→u≥v→inju≥injv) ∷ max-preses) =
  ≥-max-pres-local ev ∷ ≥-Max-Preserve-Local-map-star pdis bijects max-preses
  where
    len>0-injList : ∀ (x : U p) (xs : List (U r))
      → length (proj₁ (flat (mkinjList inj (PairU {p} {r * ε∉r ` loc} {loc} x (ListU xs))))) Nat.> 0
    len>0-injList x xs rewrite PDI.mkinjListSoundEv inj sound-ev (PairU {p} {r * ε∉r ` loc} {loc} x (ListU xs)) = Nat.s≤s Nat.z≤n

    ev : (u' : U (p ● (r * ε∉r ` loc) ` loc))
       → ≥-Max (proj₁ (flat u')) u'
       → (v' : U (p ● (r * ε∉r ` loc) ` loc))
       → (p ● (r * ε∉r ` loc) ` loc) ⊢ u' ≥ v'
       → (r * ε∉r ` loc) ⊢ mkinjList inj u' ≥ mkinjList inj v'
    ev (PairU u₁ (ListU us)) max-pair (PairU v₁ (ListU vs)) (inj₂ u'≡v')
      rewrite proj₁ (inv-pairU u₁ (ListU us) v₁ (ListU vs) u'≡v')
            | cong unListU (proj₂ (inv-pairU u₁ (ListU us) v₁ (ListU vs) u'≡v')) = inj₂ refl
    ev (PairU u₁ (ListU us)) max-pair (PairU v₁ (ListU vs)) (inj₁ (bne len|u'|>0 len|v'|>0 (seq₁ u₁>v₁)))
      with u→max-u→v→u≥v→inju≥injv u₁ (≥-max-pair-fst-prefix→>3 u₁ (ListU us) max-pair) v₁ (inj₁ u₁>v₁)
    ... | inj₂ inju₁≡injv₁ = Nullary.contradiction (u→v→inju≡injv→u≡v u₁ v₁ inju₁≡injv₁) (>→¬≡ u₁>v₁)
    ... | inj₁ inju₁>injv₁ = inj₁ (bne (len>0-injList u₁ us) (len>0-injList v₁ vs) (star-head inju₁>injv₁))
    ev (PairU u₁ (ListU us)) max-pair (PairU v₁ (ListU vs)) (inj₁ (bne len|u'|>0 len|v'|>0 (seq₂ u₁≡v₁ listus>listvs)))
      = inj₁ (bne (len>0-injList u₁ us) (len>0-injList v₁ vs) (star-tail (cong inj u₁≡v₁) listus>listvs))
    ev (PairU u₁ (ListU us)) max-pair (PairU v₁ (ListU vs)) (inj₁ (be len|u'|≡len|v'| len|v'|≡0 (seq₁ u₁>v₁)))
      with u→max-u→v→u≥v→inju≥injv u₁ (≥-max-pair-fst-prefix→>3 u₁ (ListU us) max-pair) v₁ (inj₁ u₁>v₁)
    ... | inj₂ inju₁≡injv₁ = Nullary.contradiction (u→v→inju≡injv→u≡v u₁ v₁ inju₁≡injv₁) (>→¬≡ u₁>v₁)
    ... | inj₁ inju₁>injv₁ = inj₁ (bne (len>0-injList u₁ us) (len>0-injList v₁ vs) (star-head inju₁>injv₁))
    ev (PairU u₁ (ListU us)) max-pair (PairU v₁ (ListU vs)) (inj₁ (be len|u'|≡len|v'| len|v'|≡0 (seq₂ u₁≡v₁ listus>listvs)))
      = inj₁ (bne (len>0-injList u₁ us) (len>0-injList v₁ vs) (star-tail (cong inj u₁≡v₁) listus>listvs))
    ev (PairU u₁ (ListU us)) max-pair (PairU v₁ (ListU vs)) (inj₁ (lne len|u'|>0 len|v'|≡0)) with proj₁ (flat {p} u₁) ≟C []
    ... | no ¬|u₁|≡[] = prf
      where
        |v₁|≡[] : proj₁ (flat v₁) ≡ []
        |v₁|≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat (ListU vs))) (length≡0→[] len|v'|≡0)
        u₁>v₁ : p ⊢ u₁ > v₁
        u₁>v₁ = lne (Utils.¬≡[]→length>0 ¬|u₁|≡[]) (Utils.[]→length≡0 |v₁|≡[])
        prf : (r * ε∉r ` loc) ⊢ mkinjList inj (PairU u₁ (ListU us)) ≥ mkinjList inj (PairU v₁ (ListU vs))
        prf with u→max-u→v→u≥v→inju≥injv u₁ (≥-max-pair-fst-prefix→>3 u₁ (ListU us) max-pair) v₁ (inj₁ u₁>v₁)
        ... | inj₂ inju₁≡injv₁ = Nullary.contradiction (u→v→inju≡injv→u≡v u₁ v₁ inju₁≡injv₁) (>→¬≡ u₁>v₁)
        ... | inj₁ inju₁>injv₁ = inj₁ (bne (len>0-injList u₁ us) (len>0-injList v₁ vs) (star-head inju₁>injv₁))
    ... | yes |u₁|≡[] = prf
      where
        |v₁|≡[] : proj₁ (flat v₁) ≡ []
        |v₁|≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat (ListU vs))) (length≡0→[] len|v'|≡0)
        |list-vs|≡[] : proj₁ (flat (ListU vs)) ≡ []
        |list-vs|≡[] = ++-conicalʳ (proj₁ (flat v₁)) (proj₁ (flat (ListU vs))) (length≡0→[] len|v'|≡0)
        len|list-us|>0 : length (proj₁ (flat (ListU us))) Nat.> 0
        len|list-us|>0 = subst (λ n → n Nat.> 0) eq len|u'|>0
          where
            eq : length (proj₁ (flat (PairU {p} {r * ε∉r ` loc} {loc} u₁ (ListU us)))) ≡ length (proj₁ (flat (ListU us)))
            eq = trans (len-flat-pair {p} {r * ε∉r ` loc} {loc} {u₁} {ListU us}) (cong (λ x → x + length (proj₁ (flat (ListU us)))) (cong length |u₁|≡[]))
        listus>listvs : (r * ε∉r ` loc) ⊢ ListU us > ListU vs
        listus>listvs = lne len|list-us|>0 (Utils.[]→length≡0 |list-vs|≡[])
        |u₁|≡|v₁| : proj₁ (flat u₁) ≡ proj₁ (flat v₁)
        |u₁|≡|v₁| = trans |u₁|≡[] (sym |v₁|≡[])
        u₁≥v₁ : p ⊢ u₁ ≥ v₁
        u₁≥v₁ with ≥-max-pair-fst-prefix→>3 u₁ (ListU us) max-pair
        ... | ≥-max w .u₁ |u₁|≡w dom = dom v₁ (sym |u₁|≡|v₁|)
        prf : (r * ε∉r ` loc) ⊢ mkinjList inj (PairU u₁ (ListU us)) ≥ mkinjList inj (PairU v₁ (ListU vs))
        prf with u→max-u→v→u≥v→inju≥injv u₁ (≥-max-pair-fst-prefix→>3 u₁ (ListU us) max-pair) v₁ u₁≥v₁
        ... | inj₂ inju₁≡injv₁ = inj₁ (bne (len>0-injList u₁ us) (len>0-injList v₁ vs) (star-tail inju₁≡injv₁ listus>listvs))
        ... | inj₁ inju₁>injv₁ = inj₁ (bne (len>0-injList u₁ us) (len>0-injList v₁ vs) (star-head inju₁>injv₁))


-- Purpose: All pdis in pdU[r,c] satisfy ≥-Max-Preserve-Local (structural induction on r)
-- Used by: ∈→pres-local, first-pdU-accept-w-isMax-●-no, first-pdU-accept-w-isMax-●-yes, first-pdU-accept-w-isMax-*
-- Proof idea: Induction on RE structure, using map-left, map-fst, concatmap-snd, map-star
pdU-preseve-local : ∀ { r : RE } { c : Char }
  → All ≥-Max-Preserve-Local pdU[ r , c ]
pdU-preseve-local {ε} {c} = []   
pdU-preseve-local {$ c ` loc} {c'} with c Char.≟ c'
... | no ¬c≡c' = [] 
... | yes c≡c' rewrite c≡c'  = (≥-max-pres-local ev ) ∷ []
  where
    ev : (u : U ε)
       → ≥-Max (proj₁ (flat u)) u
       → (v : U ε)
       → ε ⊢ u ≥ v 
       → ($ c' ` loc) ⊢ mkinjLetter u ≥ mkinjLetter v
    ev EmptyU max-empty EmptyU (inj₁ empty>empty) = Nullary.contradiction refl (>→¬≡  empty>empty )
    ev EmptyU max-empty EmptyU (inj₂ refl) = inj₂ refl        
pdU-preseve-local {l + r  ` loc} {c} = all-concat (≥-Max-Preserve-Local-map-left pdU[ l , c ] ind-hyp-l ) (≥-Max-Preserve-Local-map-right pdU[ r , c ] ind-hyp-r ) 
  where
    ind-hyp-l : All ≥-Max-Preserve-Local pdU[ l , c ]
    ind-hyp-l = pdU-preseve-local {l} {c}
    ind-hyp-r : All ≥-Max-Preserve-Local pdU[ r , c ]
    ind-hyp-r = pdU-preseve-local {r} {c}
pdU-preseve-local {l ● r  ` loc} {c} with ε∈? l 
... | no ¬ε∈l = ≥-Max-Preserve-Local-map-fst pdU[ l , c ] pdU-bijective  ind-hyp-l 
  where
    ind-hyp-l : All ≥-Max-Preserve-Local pdU[ l , c ]
    ind-hyp-l = pdU-preseve-local {l} {c}
... | yes ε∈l = all-concat (≥-Max-Preserve-Local-map-fst pdU[ l , c ] pdU-bijective  ind-hyp-l) (≥-Max-Preserve-Local-concatmap-pdinstance-snd pdU[ r , c ] pdU-bijective ind-hyp-r ) 
  where
    ind-hyp-l : All ≥-Max-Preserve-Local pdU[ l , c ]
    ind-hyp-l = pdU-preseve-local {l} {c}
    ind-hyp-r : All ≥-Max-Preserve-Local pdU[ r , c ]
    ind-hyp-r = pdU-preseve-local {r} {c}
pdU-preseve-local {r * ε∉r ` loc} {c} = ≥-Max-Preserve-Local-map-star pdU[ r , c ] pdU-bijective ind-hyp-r
  where
    ind-hyp-r : All ≥-Max-Preserve-Local pdU[ r , c ]
    ind-hyp-r = pdU-preseve-local {r} {c}
```

-- next we note that pdU[ r , c ] is sorted  but pdUMany[ r , w ] is not sorted.

-- we want to show

-- the left most parse tree generated by parseAll[ r , w ] is the max 


-- we should have a similar pdUMany-preserve-local lemma
-- we need this and another invariant lemma for each pdUMany[ , ] to prove first-concatMap-buildU-pdUMany-isMax 

```agda

-- Purpose: Extract the source regex of a PDInstance
-- Used by: first-inhabit-cons, first-inhabit-just→c∷w∈r, parseAll-pdU-decomp
-- Proof idea: Pattern matching on pdinstance to extract p
pdi-src : ∀ { r : RE } { c : Char } → PDInstance r c → RE
pdi-src (pdinstance {p} {r} {c} inj sound-ev) = p

-- Purpose: Extract the injection function from a PDInstance
-- Used by: ≥-max-pdi≡-helper, first-inhabit-++-just-left-pdi, head-map-inj→head-src
-- Proof idea: Pattern matching on pdinstance to extract inj
pdi-inj : ∀ { r : RE } { c : Char } → ( g : PDInstance r c ) → U (pdi-src g) → U r
pdi-inj (pdinstance {p} {r} {c} inj sound-ev) = inj

-- Purpose: Extract the source regex of a PDInstance*
-- Used by: buildU-≡-map-inj-parseAll-[], concatMap-buildU-pdUMany-aux-lemma
-- Proof idea: Pattern matching on pdinstance* to extract p
pdi*-src : ∀ { r : RE } { pref : List Char } → PDInstance* r pref → RE
pdi*-src (pdinstance* {p} {r} {pref} inj s-ev) = p

-- Purpose: Extract the injection function from a PDInstance*
-- Used by: concatMap-buildU-pdUMany-aux-lemma, concatMap-buildU-pdUMany-aux-lemma-step
-- Proof idea: Pattern matching on pdinstance* to extract inj
pdi*-inj : ∀ { r : RE } { pref : List Char } → ( pdi* : PDInstance* r pref ) → U (pdi*-src pdi*) → U r
pdi*-inj (pdinstance* {p} {r} {pref} inj s-ev) = inj


-- Purpose: (Mutual block) Find first pdi in list whose source accepts w
-- Used by: first-inhabit-yes-eq-full, first-inhabit-no-eq, first-inhabit-just-∈, first-inhabit-just-first
-- Proof idea: (Mutual recursion) Check head membership, return just or recurse
mutual
  first-inhabit-cons : ∀ { r : RE } { c : Char } { w : List Char }
    → ( pdi' : PDInstance r c ) ( pdis : List (PDInstance r c) )
    → Dec ( w ∈⟦ pdi-src pdi' ⟧ )
    → Maybe (PDInstance r c)
  first-inhabit-cons {r} {c} {w} pdi' pdis (no _) = first-inhabit r c w pdis
  first-inhabit-cons {r} {c} {w} pdi' pdis (yes _) = just pdi'

  first-inhabit : ∀ ( r : RE ) ( c : Char ) ( w : List Char ) → List (PDInstance r c) → Maybe (PDInstance r c)
  first-inhabit r c w [] = nothing
  first-inhabit r c w (pdi' ∷ pdis) = first-inhabit-cons pdi' pdis (w ∈?⟦ pdi-src pdi' ⟧)


-- First pdi of an Ex>-sorted list is greater than all subsequent pdis.
Ex>-sorted-first>all : ∀ {r : RE} {c : Char} {pdi : PDInstance r c} {pdis : List (PDInstance r c)}
  → Ex>-sorted (pdi ∷ pdis)
  → (pdi' : PDInstance r c) → pdi' ∈ pdis
  → r , c ⊢ pdi > pdi'
Ex>-sorted-first>all (ex>-cons _ (ex>-just pdi>pdi₂)) pdi' (here refl) = pdi>pdi₂
Ex>-sorted-first>all {r} {c} (ex>-cons sorted (ex>-just pdi>pdi₂)) pdi' (there pdi'∈pdis')
  with Ex>-sorted-first>all sorted pdi' pdi'∈pdis'
... | pdi₂>pdi' = >-pdi-trans pdi>pdi₂ pdi₂>pdi'


-- Purpose: Contradiction when nothing equals just x
-- Used by: first-inhabit-++-just-left-pres, first-inhabit-++-just-right-decompose, first-inhabit-nothing→¬Any-accept-aux
-- Proof idea: Absurd pattern
nothing≢just : ∀ { A : Set } { x : A } → nothing ≡ just x → ⊥
nothing≢just ()

-- NOTE: first-inhabit-def and first-inhabit-yes-eq referencing first-inhabit-cons
-- are removed. The original first-inhabit definition with direct pattern matching
-- on pdinstance works correctly with Agda 2.7 `with`.


-- Full yes equality: first-inhabit directly equals just pdi'.
first-inhabit-yes-eq-full : ∀ { r : RE } { c : Char } { w : List Char }
  → ( pdi' : PDInstance r c ) ( pdis : List (PDInstance r c) )
  → w ∈⟦ pdi-src pdi' ⟧
  → first-inhabit r c w (pdi' ∷ pdis) ≡ just pdi'
first-inhabit-yes-eq-full {r} {c} {w} (pdinstance {p} .{r} .{c} inj sev) pdis w∈src
  with w ∈?⟦ p ⟧ in d-eq
... | yes _ rewrite d-eq = refl
... | no ¬w∈src' = ⊥-elim (¬w∈src' w∈src)


-- first-inhabit recurses on the tail exactly when the head source rejects w.
-- Purpose: first-inhabit skips head when head source rejects w
-- Used by: first-inhabit-just-∈-aux, first-inhabit-just-first-aux, first-inhabit-nothing→¬Any-accept-aux
-- Proof idea: With on membership decision, yes→absurd, no→refl
first-inhabit-no-eq : ∀ { r : RE } { c : Char } { w : List Char }
  → ( pdi' : PDInstance r c ) ( pdis : List (PDInstance r c) )
  → ¬ ( w ∈⟦ pdi-src pdi' ⟧ )
  → first-inhabit r c w (pdi' ∷ pdis) ≡ first-inhabit r c w pdis
first-inhabit-no-eq {r} {c} {w} (pdinstance {p} .{r} .{c} inj sev) pdis ¬w∈src
  with w ∈?⟦ p ⟧
... | yes w∈src = ⊥-elim (¬w∈src w∈src)
... | no _ = refl


-- Purpose: first-inhabit returns just pdi implies pdi ∈ pdis and w ∈ src(pdi), and conversely
-- Used by: head-pdUparseAll→first-inhabit
-- Proof idea: Mutual induction on Any and first-inhabit structure
mutual
  -- first-inhabit returns a pdi that is in the list and whose source accepts w.
  first-inhabit-just-∈ : ∀ { r : RE } { c : Char } { w : List Char }
    → ( pdis : List (PDInstance r c) ) ( pdi : PDInstance r c )
    → first-inhabit r c w pdis ≡ just pdi
    → ( pdi ∈ pdis ) × ( w ∈⟦ pdi-src pdi ⟧ )
  first-inhabit-just-∈ [] _ ()
  first-inhabit-just-∈ {w = w} (pdi' ∷ pdis) pdi eq =
    first-inhabit-just-∈-aux pdi' pdis pdi eq (w ∈?⟦ pdi-src pdi' ⟧)

  first-inhabit-just-∈-aux : ∀ { r : RE } { c : Char } { w : List Char }
    → ( pdi' : PDInstance r c ) ( pdis : List (PDInstance r c) ) ( pdi : PDInstance r c )
    → first-inhabit r c w (pdi' ∷ pdis) ≡ just pdi
    → Dec ( w ∈⟦ pdi-src pdi' ⟧ )
    → ( pdi ∈ (pdi' ∷ pdis) ) × ( w ∈⟦ pdi-src pdi ⟧ )
  first-inhabit-just-∈-aux {r} {c} {w} pdi' pdis pdi eq (yes w∈src') rewrite first-inhabit-yes-eq-full pdi' pdis w∈src'
    with just-injective eq
  ... | pdi'≡pdi = here (sym pdi'≡pdi) , subst (λ x → w ∈⟦ pdi-src x ⟧) pdi'≡pdi w∈src'
  first-inhabit-just-∈-aux {w = w} pdi' pdis pdi eq (no ¬w∈src') rewrite first-inhabit-no-eq pdi' pdis ¬w∈src'
    with first-inhabit-just-∈ pdis pdi eq
  ... | pdi∈pdis , w∈src = there pdi∈pdis , w∈src

  -- The pdi returned by first-inhabit is either equal to, or greater than,
  -- any other pdi in the list that also accepts w (using Ex>-sortedness).
  first-inhabit-just-first : ∀ { r : RE } { c : Char } { w : List Char }
    → ( pdis : List (PDInstance r c) ) ( pdi : PDInstance r c )
    → first-inhabit r c w pdis ≡ just pdi
    → ( pdi' : PDInstance r c ) → pdi' ∈ pdis → w ∈⟦ pdi-src pdi' ⟧
    → Ex>-sorted pdis
    → ( pdi ≡ pdi' ) ⊎ ( r , c ⊢ pdi > pdi' )
  first-inhabit-just-first [] _ () _ _ _ _
  first-inhabit-just-first {w = w} (pdi₀ ∷ pdis) pdi eq pdi' pdi'∈ w∈src' sorted =
    first-inhabit-just-first-aux pdi₀ pdis pdi eq pdi' pdi'∈ w∈src' sorted (w ∈?⟦ pdi-src pdi₀ ⟧)

  first-inhabit-just-first-aux : ∀ { r : RE } { c : Char } { w : List Char }
    → ( pdi₀ : PDInstance r c ) ( pdis : List (PDInstance r c) ) ( pdi : PDInstance r c )
    → first-inhabit r c w (pdi₀ ∷ pdis) ≡ just pdi
    → ( pdi' : PDInstance r c ) → pdi' ∈ (pdi₀ ∷ pdis) → w ∈⟦ pdi-src pdi' ⟧
    → Ex>-sorted (pdi₀ ∷ pdis)
    → Dec ( w ∈⟦ pdi-src pdi₀ ⟧ )
    → ( pdi ≡ pdi' ) ⊎ ( r , c ⊢ pdi > pdi' )
  first-inhabit-just-first-aux {r} {c} pdi₀ pdis pdi eq pdi' pdi'∈ w∈src' sorted (yes w∈src₀) rewrite first-inhabit-yes-eq-full pdi₀ pdis w∈src₀
    with just-injective eq | pdi'∈
  ... | pdi₀≡pdi | here refl = inj₁ (sym pdi₀≡pdi)
  ... | pdi₀≡pdi | there pdi'∈tail rewrite sym pdi₀≡pdi = inj₂ (Ex>-sorted-first>all sorted pdi' pdi'∈tail)
  first-inhabit-just-first-aux {w = w} pdi₀ pdis pdi eq pdi' pdi'∈ w∈src' sorted (no ¬w∈src₀) rewrite first-inhabit-no-eq pdi₀ pdis ¬w∈src₀
    with pdi'∈ | sorted
  ... | here refl | _ = ⊥-elim (¬w∈src₀ w∈src')
  ... | there pdi'∈tail | ex>-cons sorted-tail _ = first-inhabit-just-first pdis pdi eq pdi' pdi'∈tail w∈src' sorted-tail



-- extract the ≥-Max-Preserve-Local evidence of a pdi from its membership in pdU[ r , c ]
∈→pres-local : ∀ { r : RE } { c : Char } ( g : PDInstance r c ) → g ∈ pdU[ r , c ] → ≥-Max-Preserve-Local g
∈→pres-local {r} {c} g g∈ = go pdU[ r , c ] (pdU-preseve-local {r} {c}) g∈
  where
    go : ( pdis : List (PDInstance r c) ) → All ≥-Max-Preserve-Local pdis → g ∈ pdis → ≥-Max-Preserve-Local g
    go [] [] ()
    go (pdi ∷ pdis) (pres ∷ all-pres) (here refl) = pres
    go (pdi ∷ pdis) (pres ∷ all-pres) (there g∈') = go pdis all-pres g∈'





-- ●-decomp : every pd from a ●-target is a fst-pdi or a snd-pdi
-- Strategy: use subst *before* any with-pattern, then delegate to helpers
-- that pattern-match on the substituted list membership.
-- Key insight: compute subst (λ xs → g' ∈ xs) (sym pdU●-no/yes) g'∈
-- in the main clause, then pass result to helpers.

-- Purpose: Decompose membership in concatMap into element + membership in image
-- Used by: concatmap-snd-decomp-aux
-- Proof idea: Use ∈-++⁻ to split head vs tail, recurse on tail
∈-concatMap⁻ : ∀ { A B : Set } { f : A → List B } { y : B } { xs : List A }
  → y ∈ concatMap f xs
  → ∃[ x ] ( x ∈ xs × y ∈ f x )
∈-concatMap⁻ {xs = []} ()
∈-concatMap⁻ {f = f} {y} {x ∷ xs} y∈ with ∈-++⁻ (f x) y∈
... | inj₁ y∈fx = x , here refl , y∈fx
... | inj₂ y∈rest with ∈-concatMap⁻ y∈rest
...   | (x' , x'∈xs , y∈fx') = x' , there x'∈xs , y∈fx'

-- Decompose membership in concatmap-pdinstance-snd:
-- Uses ∈-concatMap⁻ to decompose g' ∈ concatMap f es into ∃ ef . ef ∈ es × g' ∈ f ef
-- then uses ∈-map⁻ on g' ∈ List.map (mk-snd-pdi ef) pdis
-- (Kept as useful standalone lemma for future ●-decomp proof)
concatmap-snd-decomp-aux : ∀ {l r : RE} {loc : ℕ} {c : Char} {pdis : List (PDInstance r c)}
  → (g' : PDInstance (l ● r ` loc) c)
  → (es : List (∃[ e ] (Flat-[] l e)))
  → g' ∈ concatMap (λ ef → List.map (mk-snd-pdi {l} {r} {loc} {c} ef) pdis) es
  → ∃[ ef ] ∃[ gₕ' ] (ef ∈ es × gₕ' ∈ pdis × g' ≡ mk-snd-pdi {l} {r} {loc} {c} ef gₕ')
concatmap-snd-decomp-aux {l} {r} {loc} {c} {pdis} g' es g'∈ with ∈-concatMap⁻ g'∈
... | (ef , ef∈es , g'∈ef-pdis) with ∈-map⁻ (mk-snd-pdi {l} {r} {loc} {c} ef) g'∈ef-pdis
...   | (gₕ' , gₕ'∈ , g'≡snd) = ef , gₕ' , ef∈es , gₕ'∈ , g'≡snd

-- Purpose: Decompose membership in concatmap-pdinstance-snd into components
-- Used by: first-inhabit-++-just-left-pdi-there-yes
-- Proof idea: Rewrite concatmap to concatMap, then ∈-concatMap⁻ and ∈-map⁻
concatmap-snd-decomp : ∀ {l r : RE} {ε∈l : ε∈ l} {loc : ℕ} {c : Char}
  → (g' : PDInstance (l ● r ` loc) c)
  → g' ∈ concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ]
  → ∃[ ef ] ∃[ gₕ' ] (ef ∈ zip-es-flat-[]-es {l} {ε∈l} (mkAllEmptyU {l} ε∈l) (mkAllEmptyU-sound {l} ε∈l) × gₕ' ∈ pdU[ r , c ] × g' ≡ mk-snd-pdi {l} {r} {loc} {c} ef gₕ')
concatmap-snd-decomp {l = l} {r = r} {ε∈l = ε∈l} {loc = loc} {c = c} g' g'∈snd = concatmap-snd-decomp-aux g' zip-es (subst (λ ys → g' ∈ ys) (sym concatmap-snd≡cm) g'∈snd)
  where
  zip-es : List (∃[ e ] (Flat-[] l e))
  zip-es = zip-es-flat-[]-es {l} {ε∈l} (mkAllEmptyU {l} ε∈l) (mkAllEmptyU-sound {l} ε∈l)

  concatmap-snd≡cm : concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ]
    ≡ concatMap (λ ef → List.map (mk-snd-pdi {l} {r} {loc} {c} ef) pdU[ r , c ]) zip-es
  concatmap-snd≡cm = refl

-- ●-decomp : every pd from a ●-target is a fst-pdi or a snd-pdi
-- Proved by with on ε∈? l, then subst using equality proofs that
-- connect pdU[l●r,c] to branch-specific form.

-- Equality: pdU[l●r,c] ≡ List.map pdinstance-fst pdU[l,c]  when ε∉l
-- Equality: pdU[l●r,c] ≡ List.map pdinstance-fst pdU[l,c] ++ concatmap-pdinstance-snd ...  when ε∈l
-- These equalities chain pdU[●] = pdU●(ε∈?l) = branch-specific form.
-- The first link (pdU[●] = pdU●) is refl but lives in a mutual block,
-- so `refl` doesn't reduce. We work around this by using `with` on
-- ε∈? l and constructing the equality inside each branch where
-- `it : ε∈? l ≡ branch` lets us use `cong pdU● it`.

-- Purpose: Decompose pdi in fst-mapped list (ε∉l case)
-- Used by: ●-decomp-yes, ●-decomp
-- Proof idea: ∈-map⁻ on pdinstance-fst, must be fst branch
●-decomp-no : ∀ {l r : RE} {loc : ℕ} {c : Char}
  → (g' : PDInstance (l ● r ` loc) c)
  → g' ∈ List.map pdinstance-fst pdU[ l , c ]
  → (∃[ gₕ' ] (g' ≡ pdinstance-fst {l} {r} {loc} {c} gₕ'))
    ⊎ (∃[ e ] ∃[ fl ] ∃[ gₕ' ] (g' ≡ mk-snd-pdi {l} {r} {loc} {c} (e , fl) gₕ'))
●-decomp-no g' g'∈ = inj₁
  (proj₁ (∈-map⁻ pdinstance-fst g'∈)
  , proj₂ (proj₂ (∈-map⁻ pdinstance-fst g'∈)))

-- Purpose: Decompose pdi in concatenated fst+snd lists (ε∈l case)
-- Used by: ●-decomp
-- Proof idea: ∈-++⁻ to fst or snd, delegate to ●-decomp-no or concatmap-snd-decomp
●-decomp-yes : ∀ {l r : RE} {loc : ℕ} {c : Char} {ε∈l}
  → (g' : PDInstance (l ● r ` loc) c)
  → g' ∈ List.map pdinstance-fst pdU[ l , c ] ++ concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ]
  → (∃[ gₕ' ] (g' ≡ pdinstance-fst {l} {r} {loc} {c} gₕ'))
    ⊎ (∃[ e ] ∃[ fl ] ∃[ gₕ' ] (g' ≡ mk-snd-pdi {l} {r} {loc} {c} (e , fl) gₕ'))
●-decomp-yes {l} {r} {loc} {c} {ε∈l} g' g'∈ with ∈-++⁻ (List.map pdinstance-fst pdU[ l , c ]) g'∈
... | inj₁ g'∈fst = ●-decomp-no {l} {r} {loc} {c} g' g'∈fst
... | inj₂ g'∈snd with concatmap-snd-decomp {l} {r} {ε∈l} {loc} {c} g' g'∈snd
... | (ef , gₕ'' , ef∈xs , gₕ''∈ , g'≡snd) = inj₂ (proj₁ ef , proj₂ ef , gₕ'' , g'≡snd)

-- Approach: with + where helpers (DEMONSTRATING THE FAILURE)
--
-- The idea: `with ε∈? l` case-splits, then a `where` helper constructs
-- the equality pdU[l●r,c] ≡ branch-specific, then `subst` transforms g'∈.
--
-- Agda desugars `with ε∈? l | it ε∈? l` into a helper function:
--   ●-decomp-hlp : ∀ (l : RE) {r} {loc} {c} (it : ε∈? l ≡ ε∈? l)
--                  (g' : PDInstance (l ● r ` loc) c)
--                  (g'∈ : g' ∈ pdU[ l ● r ` loc , c ]) → ...
--
-- Problem 1: `l` becomes an EXPLICIT parameter, so references in the
-- `where` block resolve to the helper-parameter.
-- Problem 2: Even with `l` in scope, the `refl` proofs are stuck because
-- `pdU` and `pdU●` are mutual — `refl : pdU[l●r,c] ≡ pdU●(ε∈?l)` is
-- valid but doesn't reduce. ∈-map⁻ / ∈-++⁻ need to pattern-match on the
-- proof, and the `subst` term blocks that.
--
-- Attempted code (commented out so file compiles):
-- ●-decomp {l} {r} {loc} {c} g' g'∈ with ε∈? l | Function.it ε∈? l
-- ... | no ¬ε∈l | it = ●-decomp-no g' (subst _ (sym eq-no) g'∈)
-- ... | yes ε∈l | it = ●-decomp-yes g'(subst _ (sym eq-yes) g'∈)
--   where
--     eq-no : pdU[ l ● r ` loc , c ] ≡ List.map pdinstance-fst pdU[ l , c ]
--     eq-no = trans (cong _ it) pdU●-def
--       where
--         pdU●-def : pdU[ l ● r ` loc , c ] ≡ pdU● (no ¬ε∈l)
--         pdU●-def  = refl      -- STUCK: mutual block
--     eq-yes : pdU[ l ● r ` loc , c ] ≡ List.map pdinstance-fst pdU[ l , c ] ++ concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ]
--     eq-yes = trans (cong _ it) pdU●-def
--       where
--         pdU●-def : pdU[ l ● r ` loc , c ] ≡ pdU● (yes ε∈l)
--         pdU●-def = refl      -- STUCK: mutual block

-- Purpose: Every pdi in pdU[l●r,c] is either a fst-pdi or snd-pdi
-- Used by: (standalone decomposition lemma for ● analysis)
-- Proof idea: Case split on ε∈? l, delegate to ●-decomp-no or ●-decomp-yes
●-decomp : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( g' : PDInstance (l ● r ` loc) c )
    → g' ∈ pdU[ l ● r ` loc , c ]
    → ( ∃[ gₕ' ] ( g' ≡ pdinstance-fst {l} {r} {loc} {c} gₕ' ) )
    ⊎ ( ∃[ e ] ∃[ fl ] ∃[ gₕ' ] ( g' ≡ mk-snd-pdi {l} {r} {loc} {c} (e , fl) gₕ' ) )
●-decomp {l} {r} {loc} {c} g' g'∈ with ε∈? l
... | no ¬ε∈l = ●-decomp-no g' g'∈
... | yes ε∈l = ●-decomp-yes g' g'∈


-- Purpose: Build All P (map f xs) from pointwise membership proofs
-- Used by: (utility lemma for All proofs over mapped lists)
-- Proof idea: Induction on xs, threading there constructor
all-map-∈ : ∀ { A B : Set } { P : B → Set } ( f : A → B ) ( xs : List A )
  → ( ∀ ( x : A ) → x ∈ xs → P ( f x ) )
  → All P ( List.map f xs )
all-map-∈ f [] h = []
all-map-∈ f (x ∷ xs) h = h x (here refl) ∷ all-map-∈ f xs (λ x' x'∈xs → h x' (there x'∈xs))


```


does the following definition make sense and is helpful?

A pdinstance is suffix w maximal iff given the max parse tree of w w.r.t to some p, say u,  inject u gives us the maximal parse tree of r.
```agda

-- Purpose: PDInstance is suffix-w-maximal: injecting max parse tree of w yields max of c∷w
-- Used by: ≥-max-pres-left-pdi, ≥-max-pres-right-pdi, first-pdU-accept-w-isMax, ≥-Max-PDInstance-u
-- Proof idea: N/A (data type definition)
data ≥-Max-PDInstance : ∀ { r : RE } { c : Char } → ( List Char )  → PDInstance r c → Set where
  ≥-max-pdi : ∀ { p r : RE } { c : Char }  { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( u : U p )
    → ( w : List Char )    
    → ≥-Max w u
    → ≥-Max (c ∷ w) (inj u)
    → ≥-Max-PDInstance {r} {c} w (pdinstance inj sound-ev) 



```
can we prove that the first pdistance that we ever find in pdU[ r , c ] from left to right that reconstruct
unflat c ∷ w is ≥-Max-PDInstance!


```agda
-- Strategy for this lemma and the overall parseAll-max route:
--
-- We prove by induction on r using pdU-completeness + pdU-sorted.
-- The first pdi in pdU[r,c] that accepts the suffix w is suffix-maximal.
--
-- The proof is mutually recursive with first-concatMap-buildU-pdUMany-isMax / first-parseAll-isMax:
-- constructing the maximal parse tree u at the pdi's source may require the
-- maximality of parseAll for the suffix w at that source (e.g., concat sources).


-- Purpose: pdU● for ε∉l is just map of pdinstance-fst
-- Used by: first-pdU-accept-w-isMax-●-no
-- Proof idea: Reflexivity
pdU●-no : ∀ { l r : RE } { loc : ℕ } { c : Char } → (¬ε∈l : ¬ ε∈ l) → pdU● {l} {r} {loc} {c} (no ¬ε∈l) ≡ List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ]
pdU●-no ¬ε∈l = refl

-- Purpose: pdU● for ε∈l is fst-map ++ concatmap-snd
-- Used by: first-pdU-accept-w-isMax-●-yes
-- Proof idea: Reflexivity
pdU●-yes : ∀ { l r : RE } { loc : ℕ } { c : Char } → (ε∈l : ε∈ l) → pdU● {l} {r} {loc} {c} (yes ε∈l) ≡ List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ] ++ concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ]
pdU●-yes ε∈l = refl

-- Purpose: first-inhabit on empty list returns nothing
-- Used by: (internal helper for first-inhabit reasoning)
-- Proof idea: Reflexivity
first-inhabit-nil-nothing : ∀ { r : RE } { c : Char } { w : List Char }
  → first-inhabit r c w [] ≡ nothing
first-inhabit-nil-nothing = refl

-- Purpose: first-inhabit on xs ++ ys equals just pdil if first-inhabit on xs is just pdil
-- Used by: (internal helper for ++ reasoning)
-- Proof idea: Induction on xs, case on membership decision
first-inhabit-++-just : ∀ { r : RE } { c : Char } { w : List Char }
  → ( xs ys : List (PDInstance r c) ) ( pdil : PDInstance r c )
  → first-inhabit r c w xs ≡ just pdil
  → first-inhabit r c w (xs ++ ys) ≡ just pdil
first-inhabit-++-just [] ys pdil ()
first-inhabit-++-just {w = w} (x ∷ xs) ys pdil eq with w ∈?⟦ pdi-src x ⟧
... | yes w∈src-x rewrite first-inhabit-yes-eq-full x xs w∈src-x rewrite sym eq = refl
... | no ¬w∈src-x rewrite first-inhabit-no-eq x (xs ++ ys) ¬w∈src-x
  rewrite first-inhabit-++-just xs ys pdil eq = refl



-- Purpose: pdi-src is preserved through pdinstance-left wrapping
-- Used by: (internal helper for source extraction)
-- Proof idea: Reflexivity after pattern matching on pdinstance
pdi-src-pres-left : ∀ {l r : RE} {loc : ℕ} {c : Char} (x : PDInstance l c)
  → pdi-src (pdinstance-left {l} {r} {loc}  x) ≡ pdi-src x
pdi-src-pres-left (pdinstance {p} inj s-ev) = refl


-- Core: first-inhabit on (map left xs ++ map right ys) preserves result from xs.
-- Purpose: first-inhabit on + regex preserves left result when left is non-empty
-- Used by: ≥-Max-Preserve-Local-map-star, first-pdU-accept-w-isMax-+
-- Proof idea: Mutual induction, decide w ∈ src(head), yes→base, no→recurse
mutual
  first-inhabit-++-just-left-pres : ∀ {l r : RE} {loc : ℕ} {c : Char} (w : List Char)
    → (xs : List (PDInstance l c))
    → (ys : List (PDInstance r c))
    → (pdil' : PDInstance l c)
    → first-inhabit l c w xs ≡ just pdil'
    → first-inhabit (l + r ` loc) c w ((List.map pdinstance-left xs) ++ (List.map pdinstance-right ys)) ≡ just (pdinstance-left pdil')

  first-inhabit-++-just-left-pres′ : ∀ {l r : RE} {loc : ℕ} {c : Char} (w : List Char)
    → (x : PDInstance l c) (xs : List (PDInstance l c)) (ys : List (PDInstance r c))
    → (pdil' : PDInstance l c)
    → first-inhabit l c w (x ∷ xs) ≡ just pdil'
    → Dec (w ∈⟦ pdi-src x ⟧)
    → first-inhabit (l + r ` loc) c w ((List.map pdinstance-left (x ∷ xs)) ++ (List.map pdinstance-right ys)) ≡ just (pdinstance-left pdil')

  first-inhabit-++-just-left-pres w [] ys pdil' eq = ⊥-elim (nothing≢just eq)
  first-inhabit-++-just-left-pres w (x ∷ xs) ys pdil' eq =
    first-inhabit-++-just-left-pres′ w x xs ys pdil' eq (w ∈?⟦ pdi-src x ⟧)

  first-inhabit-++-just-left-pres′ {l} {r} {loc} {c} w (pdinstance {p} .{l} .{c} inj s-ev) xs ys pdil' eq (yes w∈src-x) =
    trans base-yes (cong just (cong pdinstance-left x≡pdil'))
    where
      x≡pdil' : pdinstance inj s-ev ≡ pdil'
      x≡pdil' = just-injective (trans (sym (first-inhabit-yes-eq-full (pdinstance inj s-ev) _ w∈src-x)) eq)

      base-yes : first-inhabit (l + r ` loc) c w (List.map pdinstance-left (pdinstance inj s-ev ∷ xs) ++ List.map pdinstance-right ys) ≡ just (pdinstance-left (pdinstance inj s-ev))
      base-yes = first-inhabit-yes-eq-full (pdinstance-left (pdinstance inj s-ev)) _ w∈src-x
  first-inhabit-++-just-left-pres′ {l} {r} {loc} {c} w (pdinstance {p} .{l} .{c} inj s-ev) xs ys pdil' eq (no ¬w∈src-x) =
    trans base-no (first-inhabit-++-just-left-pres w xs ys pdil' eq-xs)
    where
      base-no-eq : first-inhabit l c w (pdinstance inj s-ev ∷ xs) ≡ first-inhabit l c w xs
      base-no-eq = first-inhabit-no-eq (pdinstance inj s-ev) xs ¬w∈src-x

      eq-xs : first-inhabit l c w xs ≡ just pdil'
      eq-xs rewrite base-no-eq = eq

      base-no : first-inhabit (l + r ` loc) c w (List.map pdinstance-left (pdinstance inj s-ev ∷ xs) ++ List.map pdinstance-right ys) ≡ first-inhabit (l + r ` loc) c w (List.map pdinstance-left xs ++ List.map pdinstance-right ys)
      base-no = first-inhabit-no-eq (pdinstance-left (pdinstance inj s-ev)) _ ¬w∈src-x


-- Purpose: If head pdi of l accepts w, first-inhabit on + returns left-wrapped head
-- Used by: (internal helper for + case analysis)
-- Proof idea: first-inhabit-yes-eq-full on head, then first-inhabit-++-just-left-pres
first-inhabit-++-just-left-pdi-there-yes : ∀ {l r : RE} {loc : ℕ} {c : Char} {w : List Char}
  → {c∷w∈⟦l⟧ : (c ∷ w) ∈⟦ l ⟧}
  → {pdi : PDInstance (l + r ` loc) c}
  → {eq : first-inhabit (l + r ` loc) c w (pdU[ l + r ` loc , c ]) ≡ just pdi}
  → (tail-pdis : List (PDInstance l c))
  → (head-pdi : PDInstance l c)
  → (pdu-lc-eq : pdU[ l , c ] ≡ head-pdi ∷ tail-pdis) -- can we not use this premise? 
  → w ∈⟦ pdi-src head-pdi ⟧
  → ∃[ pdil ] first-inhabit l c w (pdU[ l , c ]) ≡ just pdil × pdi ≡ pdinstance-left pdil -- can pdU[l , c] be head-pid ∷ tail-pdis? 
first-inhabit-++-just-left-pdi-there-yes {l} {r} {loc} {c} {w} {c∷w∈⟦l⟧} {pdi} {eq} tail-pdis head-pdi pdu-lc-eq  w∈src =
  ( head-pdi , eq-left , pdi≡left )
  where
    eq-left : first-inhabit l c w (pdU[ l , c ]) ≡ just head-pdi
    eq-left rewrite pdu-lc-eq = first-inhabit-yes-eq-full head-pdi tail-pdis w∈src

    pdu-lr-c≡maps : pdU[ l + r ` loc , c ] ≡ List.map pdinstance-left pdU[ l , c ] ++ List.map pdinstance-right pdU[ r , c ]
    pdu-lr-c≡maps = refl

    eq-left+right : first-inhabit (l + r ` loc) c w (List.map pdinstance-left pdU[ l , c ] ++ List.map pdinstance-right pdU[ r , c ]) ≡ just (pdinstance-left head-pdi)
    eq-left+right = first-inhabit-++-just-left-pres w (pdU[ l , c ]) (pdU[ r , c ]) head-pdi eq-left

    just-left-head≡just-pdi : just (pdinstance-left head-pdi) ≡ just pdi
    just-left-head≡just-pdi = trans (trans (sym eq-left+right) (sym (cong (λ x → first-inhabit (l + r ` loc) c w x) pdu-lr-c≡maps))) eq

    pdi≡left : pdi ≡ pdinstance-left head-pdi
    pdi≡left = just-injective (sym just-left-head≡just-pdi)
    
-- Extract w ∈⟦ pdi-src pdi ⟧ from a Recons witness.
recons-w∈src : ∀ {l : RE} {c : Char} {w : List Char}
  → {c∷w∈⟦l⟧ : (c ∷ w) ∈⟦ l ⟧}
  → (pdi : PDInstance l c)
  → Recons {l} {c} (unflat {l} {(c ∷ w)} c∷w∈⟦l⟧) pdi
  → w ∈⟦ pdi-src pdi ⟧
recons-w∈src {l} {c} {w} {c∷w∈⟦l⟧} (pdinstance {p} inj sound-ev) (recons .{p} .{l} .{c} {w'} .{inj} .{sound-ev} .(unflat {l} {(c ∷ w)} c∷w∈⟦l⟧) (w'∈p , inj∘unflatw'∈p≡unflat-c∷w∈⟦l⟧) ) =
  subst (λ x → x ∈⟦ p ⟧) (sym w≡w') w'∈p 
  where
    c∷w'≡c∷w : c ∷ w' ≡ c ∷ w
    c∷w'≡c∷w =
      begin
        c ∷ w'
       ≡⟨ cong (λ x → c ∷ (proj₁ x)) (sym (flat∘unflat {p} w'∈p)) ⟩
        c ∷ (proj₁ (flat (unflat w'∈p)) )
       ≡⟨ sym (sound-ev (unflat w'∈p)) ⟩
        proj₁ (flat (inj (unflat w'∈p)))
       ≡⟨ cong (λ x → (proj₁ (flat x))) inj∘unflatw'∈p≡unflat-c∷w∈⟦l⟧ ⟩
        (proj₁ (flat (unflat c∷w∈⟦l⟧ )))
       ≡⟨ cong (λ x → (proj₁ x)) (flat∘unflat {l} c∷w∈⟦l⟧ ) ⟩ 
        c ∷ w 
      ∎ 
  
    cw≡cw' : c ∷ w ≡ c ∷ w'
    cw≡cw' = sym c∷w'≡c∷w 

    w≡w' : w ≡ w'
    w≡w' = proj₂ (∷-injective cw≡cw')

-- Any reconstructable pdi implies first-inhabit returns just.
Any→just : ∀ {l : RE} {c : Char} {w : List Char}
  → {c∷w∈⟦l⟧ : (c ∷ w) ∈⟦ l ⟧}
  → (pdis : List (PDInstance l c))
  → Any (Recons {l} {c} (unflat {l} {(c ∷ w)} c∷w∈⟦l⟧)) pdis
  → ∃[ pdi ] ( pdi ∈ pdis) × first-inhabit l c w pdis ≡ just pdi 
Any→just {w = w} [] ar = ⊥-elim (¬Any[] ar)
Any→just {l} {c} {w} {c∷w∈⟦l⟧ = c∷w∈⟦l⟧} (pdi ∷ pdis) (here r) =  pdi , ( here refl , first-inhabit-yes-eq-full pdi pdis (recons-w∈src {l} {c} {w} {c∷w∈⟦l⟧} pdi r) ) 
Any→just {l} {c} {w} {c∷w∈⟦l⟧} (pdi ∷ pdis) (there ar) with w ∈?⟦ pdi-src pdi ⟧
... | yes w∈src = pdi , here refl , refl -- first-inhabit-yes-eq-full pdi pdis w∈src
... | no ¬w∈src = proj₁ ind-hyp , there (proj₁ (proj₂ ind-hyp))  ,  ev 
  where
    ind-hyp : ∃[ qdi ] (qdi ∈ pdis) × (first-inhabit l c w pdis ≡ just qdi )
    ind-hyp = Any→just {l} {c} {w} {c∷w∈⟦l⟧} pdis ar
    ev : first-inhabit l c w pdis ≡ just (Product.proj₁ ind-hyp)
    ev = proj₂ (proj₂ ind-hyp ) 



-- Right-side preservation: first-inhabit on the right-mapped list returns the mapped pdir.
mutual
  first-inhabit-++-just-right-pres : ∀ {l r : RE} {loc : ℕ} {c : Char} {w : List Char}
    → (ys : List (PDInstance r c))
    → (pdir' : PDInstance r c)
    → first-inhabit r c w ys ≡ just pdir'
    → first-inhabit (l + r ` loc) c w (List.map pdinstance-right ys) ≡ just (pdinstance-right pdir')
  first-inhabit-++-just-right-pres {l} {r} {loc} {c} [] pdir' ()
  first-inhabit-++-just-right-pres {l} {r} {loc} {c} {w = w} (y@(pdinstance {p} .{r} .{c} inj s-ev) ∷ ys) pdir' eq =
    first-inhabit-++-just-right-pres′ y ys pdir' eq (w ∈?⟦ p ⟧)

  first-inhabit-++-just-right-pres′ : ∀ {l r : RE} {loc : ℕ} {c : Char} {w : List Char}
    → (y : PDInstance r c) (ys : List (PDInstance r c))
    → (pdir' : PDInstance r c)
    → first-inhabit r c w (y ∷ ys) ≡ just pdir'
    → Dec (w ∈⟦ pdi-src y ⟧)
    → first-inhabit (l + r ` loc) c w (List.map pdinstance-right (y ∷ ys)) ≡ just (pdinstance-right pdir')
  first-inhabit-++-just-right-pres′ {l} {r} {loc} {c} {w = w} (pdinstance {p} .{r} .{c} inj s-ev) ys pdir' eq (yes w∈src) =
    trans base-yes (cong just (cong pdinstance-right y≡pdir'))
    where
      y≡pdir' : pdinstance inj s-ev ≡ pdir'
      y≡pdir' = just-injective (trans (sym (first-inhabit-yes-eq-full (pdinstance inj s-ev) ys w∈src)) eq)

      base-yes : first-inhabit (l + r ` loc) c w (List.map pdinstance-right (pdinstance inj s-ev ∷ ys)) ≡ just (pdinstance-right (pdinstance inj s-ev))
      base-yes = first-inhabit-yes-eq-full (pdinstance-right (pdinstance inj s-ev)) (List.map pdinstance-right ys) w∈src
  first-inhabit-++-just-right-pres′ {l} {r} {loc} {c} {w = w} (pdinstance {p} .{r} .{c} inj s-ev) ys pdir' eq (no ¬w∈src) =
    trans base-no (first-inhabit-++-just-right-pres ys pdir' eq-ys)
    where
      eq-ys : first-inhabit r c w ys ≡ just pdir'
      eq-ys rewrite first-inhabit-no-eq (pdinstance inj s-ev) ys ¬w∈src = eq

      base-no : first-inhabit (l + r ` loc) c w (List.map pdinstance-right (pdinstance inj s-ev ∷ ys)) ≡ first-inhabit (l + r ` loc) c w (List.map pdinstance-right ys)
      base-no = first-inhabit-no-eq (pdinstance-right (pdinstance inj s-ev)) (List.map pdinstance-right ys) ¬w∈src

-- Decompose right-side combined result: if first-inhabit on right map is just pdi,
-- then pdi ≡ pdinstance-right pdir and first-inhabit on r is just pdir.
-- Purpose: first-inhabit on right-wrapped list decomposes to inner first-inhabit
-- Used by: first-inhabit-++-just-right-pres
-- Proof idea: Mutual induction on right list, using right-injectivity
mutual
  first-inhabit-++-just-right-decompose : ∀ {l r : RE} {loc : ℕ} {c : Char} {w : List Char}
    → (ys : List (PDInstance r c))
    → (pdi : PDInstance (l + r ` loc) c)
    → first-inhabit (l + r ` loc) c w (List.map pdinstance-right ys) ≡ just pdi
    → ∃[ pdir ] first-inhabit r c w ys ≡ just pdir × pdi ≡ pdinstance-right pdir
  first-inhabit-++-just-right-decompose {l} {r} {loc} {c} [] pdi eq =
    ⊥-elim (nothing≢just eq)
  first-inhabit-++-just-right-decompose {l} {r} {loc} {c} {w = w} (y@(pdinstance {p} .{r} .{c} inj s-ev) ∷ ys) pdi eq =
    first-inhabit-++-just-right-decompose-aux y ys pdi eq (w ∈?⟦ p ⟧)

  first-inhabit-++-just-right-decompose-aux : ∀ {l r : RE} {loc : ℕ} {c : Char} {w : List Char}
    → (y : PDInstance r c) (ys : List (PDInstance r c))
    → (pdi : PDInstance (l + r ` loc) c)
    → first-inhabit (l + r ` loc) c w (List.map pdinstance-right (y ∷ ys)) ≡ just pdi
    → Dec (w ∈⟦ pdi-src y ⟧)
    → ∃[ pdir ] first-inhabit r c w (y ∷ ys) ≡ just pdir × pdi ≡ pdinstance-right pdir
  first-inhabit-++-just-right-decompose-aux {l} {r} {loc} {c} {w = w} (pdinstance {p} .{r} .{c} inj s-ev) ys pdi eq (yes w∈src) =
    (pdinstance inj s-ev , eq-y , pdi≡right-y)
    where
      eq-y : first-inhabit r c w (pdinstance inj s-ev ∷ ys) ≡ just (pdinstance inj s-ev)
      eq-y rewrite first-inhabit-yes-eq-full (pdinstance inj s-ev) ys w∈src = refl

      eq-right-y : first-inhabit (l + r ` loc) c w (List.map pdinstance-right (pdinstance inj s-ev ∷ ys)) ≡ just (pdinstance-right (pdinstance inj s-ev))
      eq-right-y = first-inhabit-yes-eq-full (pdinstance-right (pdinstance inj s-ev)) (List.map pdinstance-right ys) w∈src

      pdi≡right-y : pdi ≡ pdinstance-right (pdinstance inj s-ev)
      pdi≡right-y = just-injective (trans (sym eq) eq-right-y)
  first-inhabit-++-just-right-decompose-aux {l} {r} {loc} {c} {w = w} (pdinstance {p} .{r} .{c} inj s-ev) ys pdi eq (no ¬w∈src) =
    pdir , eq-tail-r , pdi≡right
    where
      eq-tail : first-inhabit (l + r ` loc) c w (List.map pdinstance-right ys) ≡ just pdi
      eq-tail = trans (sym (first-inhabit-no-eq (pdinstance-right (pdinstance inj s-ev)) (List.map pdinstance-right ys) ¬w∈src)) eq

      decomp : ∃[ pdir ] first-inhabit r c w ys ≡ just pdir × pdi ≡ pdinstance-right pdir
      decomp = first-inhabit-++-just-right-decompose ys pdi eq-tail

      pdir : PDInstance r c
      pdir = proj₁ decomp

      eq-tail-r : first-inhabit r c w (pdinstance inj s-ev ∷ ys) ≡ just pdir
      eq-tail-r = trans (first-inhabit-no-eq (pdinstance inj s-ev) ys ¬w∈src) (proj₁ (proj₂ decomp))

      pdi≡right : pdi ≡ pdinstance-right pdir
      pdi≡right = proj₂ (proj₂ decomp)

-- If first-inhabit on a list is nothing, then no pdi in the list accepts w.
-- Purpose: first-inhabit returns nothing iff no pdi in list accepts w
-- Used by: first-inhabit-nothing→¬c∷w∈r
-- Proof idea: Mutual induction on Any, contradiction with membership decision
mutual
  first-inhabit-nothing→¬Any-accept : ∀ { r : RE } { c : Char } { w : List Char }
    → ( pdis : List (PDInstance r c) )
    → first-inhabit r c w pdis ≡ nothing
    → ¬ Any (λ pdi → w ∈⟦ pdi-src pdi ⟧) pdis
  first-inhabit-nothing→¬Any-accept [] eq-nothing ()
  first-inhabit-nothing→¬Any-accept {w = w} (pdi' ∷ pdis) eq-nothing any-accept =
    first-inhabit-nothing→¬Any-accept-aux pdi' pdis eq-nothing any-accept (w ∈?⟦ pdi-src pdi' ⟧)

  first-inhabit-nothing→¬Any-accept-aux : ∀ { r : RE } { c : Char } { w : List Char }
    → ( pdi' : PDInstance r c ) ( pdis : List (PDInstance r c) )
    → first-inhabit r c w (pdi' ∷ pdis) ≡ nothing
    → Any (λ pdi → w ∈⟦ pdi-src pdi ⟧) (pdi' ∷ pdis)
    → Dec ( w ∈⟦ pdi-src pdi' ⟧ )
    → ⊥
  first-inhabit-nothing→¬Any-accept-aux pdi' pdis eq-nothing (here w∈src) (yes _) =
    nothing≢just (trans (sym eq-nothing) (first-inhabit-yes-eq-full pdi' pdis w∈src))
  first-inhabit-nothing→¬Any-accept-aux pdi' pdis eq-nothing (here w∈src) (no ¬w∈src) =
    ⊥-elim (¬w∈src w∈src)
  first-inhabit-nothing→¬Any-accept-aux pdi' pdis eq-nothing (there any-accept) (yes w∈src') =
    nothing≢just (trans (sym eq-nothing) (first-inhabit-yes-eq-full pdi' pdis w∈src'))
  first-inhabit-nothing→¬Any-accept-aux pdi' pdis eq-nothing (there any-accept) (no ¬w∈src') =
    first-inhabit-nothing→¬Any-accept pdis
      (trans (sym (first-inhabit-no-eq pdi' pdis ¬w∈src')) eq-nothing)
      any-accept

-- If first-inhabit on pdU is nothing, then c ∷ w cannot be in r.
first-inhabit-nothing→¬c∷w∈r : ∀ { r : RE } { c : Char } { w : List Char }
  → first-inhabit r c w (pdU[ r , c ]) ≡ nothing
  → ¬ ((c ∷ w) ∈⟦ r ⟧)
first-inhabit-nothing→¬c∷w∈r {r} {c} {w} eq-nothing c∷w∈r
  with pdU-complete (unflat c∷w∈r) (cong proj₁ (flat∘unflat c∷w∈r))
... | any-recons =
  first-inhabit-nothing→¬Any-accept (pdU[ r , c ]) eq-nothing any-accept
  where
    any-accept : Any (λ pdi → w ∈⟦ pdi-src pdi ⟧) (pdU[ r , c ])
    any-accept = Data.List.Relation.Unary.Any.map recons→w∈src any-recons
      where
        recons→w∈src : {pdi : PDInstance r c} → Recons (unflat {r} {(c ∷ w)} c∷w∈r) pdi → w ∈⟦ pdi-src pdi ⟧
        recons→w∈src {pdinstance {p} .{r} .{c} inj s-ev} (recons .{p} .{r} .{c} {w'} .{inj} .{s-ev} .(unflat {r} {(c ∷ w)} c∷w∈r) (w'∈p , inj∘unflat≡u)) =
          subst (λ x → x ∈⟦ p ⟧) (sym w≡w') w'∈p
          where
            w≡w' : w ≡ w'
            w≡w' = proj₂ (∷-injective (
              begin
                c ∷ w
              ≡⟨ sym (cong proj₁ (flat∘unflat c∷w∈r)) ⟩
                proj₁ (flat (unflat c∷w∈r))
              ≡⟨ cong (λ x → proj₁ (flat x)) (sym inj∘unflat≡u) ⟩
                proj₁ (flat (inj (unflat w'∈p)))
              ≡⟨ s-ev (unflat w'∈p) ⟩
                c ∷ proj₁ (flat (unflat w'∈p))
              ≡⟨ cong (c ∷_) (cong proj₁ (flat∘unflat w'∈p)) ⟩
                c ∷ w'
              ∎))


-- we prove first-inhabit-++-just-left-pdi using the following sub lemma
-- Purpose: Any Recons in left pdis implies first-inhabit on + returns left-wrapped pdi
-- Used by: first-inhabit-++-just-left-pdi
-- Proof idea: Induction on Any Recons, use first-inhabit-yes-eq-full for here
first-inhabit-++-just-left-any : ∀ {l r : RE} {loc : ℕ} {c : Char} {w : List Char}
  → (c∷w∈⟦l⟧ : (c ∷ w) ∈⟦ l ⟧)
  → ( pdisˡ : List (PDInstance l c ) )
  → ( pdisʳ : List (PDInstance r c ) )
  → Any (Recons {l} {c} (unflat {l} {c ∷ w} c∷w∈⟦l⟧)) pdisˡ 
  → ∃[ pdi ] ( first-inhabit ( l + r ` loc ) c w ( (List.map (λ x → pdinstance-left {l} {r} {loc} x ) pdisˡ ) ++ (List.map (λ x → pdinstance-right {l} {r} {loc} x ) pdisʳ ) )  ≡ just (pdinstance-left {l} {r} {loc} pdi) )
              ×
               ( first-inhabit l c w pdisˡ ≡ just pdi )
first-inhabit-++-just-left-any {l} {r} {loc} {c} {w} c∷w∈⟦l⟧ [] pdisʳ  ar =  Nullary.contradiction ar ¬Any[]
first-inhabit-++-just-left-any {l} {r} {loc} {c} {w} c∷w∈⟦l⟧ (pdi₀@(pdinstance {p} .{l} .{c} inj sound-ev) ∷ pdisˡ) pdisʳ (here (recons {p} .{l} .{c} {w'} .{inj} .{sound-ev} .(unflat {l} {c ∷ w} c∷w∈⟦l⟧) (w'∈p , inj∘unflatw'∈p≡unflat-c∷w∈⟦l⟧)) )  =  pdi₀ , eq-left+right , eq-left 
    where
      c∷w'≡c∷w : c ∷ w' ≡ c ∷ w
      c∷w'≡c∷w =
        begin
          c ∷ w'
        ≡⟨ cong (λ x → c ∷ (proj₁ x)) (sym (flat∘unflat {p} w'∈p)) ⟩
          c ∷ (proj₁ (flat (unflat w'∈p)) )
        ≡⟨ sym (sound-ev (unflat w'∈p)) ⟩
          proj₁ (flat (inj (unflat w'∈p)))
        ≡⟨ cong (λ x → (proj₁ (flat x))) inj∘unflatw'∈p≡unflat-c∷w∈⟦l⟧ ⟩
          (proj₁ (flat (unflat c∷w∈⟦l⟧ )))
        ≡⟨ cong (λ x → (proj₁ x)) (flat∘unflat {l} c∷w∈⟦l⟧ ) ⟩ 
          c ∷ w 
        ∎ 
      w'≡w : w' ≡ w
      w'≡w = proj₂ (∷-injective c∷w'≡c∷w ) 
      w∈p : w ∈⟦ p ⟧
      w∈p rewrite sym w'≡w = w'∈p  
  
      eq-left : first-inhabit l c w (pdi₀ ∷ pdisˡ) ≡ just pdi₀
      eq-left = first-inhabit-yes-eq-full pdi₀ pdisˡ w∈p
  
      eq-left+right : ( first-inhabit ( l + r ` loc ) c w ( (List.map (λ x → pdinstance-left {l} {r} {loc} x ) (pdi₀ ∷ pdisˡ) ) ++ (List.map (λ x → pdinstance-right {l} {r} {loc} x ) pdisʳ ) )  ≡ just (pdinstance-left {l} {r} {loc} pdi₀) )
      eq-left+right = first-inhabit-++-just-left-pres {l} {r} {loc} {c} w (pdi₀ ∷ pdisˡ)  pdisʳ  pdi₀ eq-left
first-inhabit-++-just-left-any {l} {r} {loc} {c} {w} c∷w∈⟦l⟧ (pdi₀@(pdinstance {p} .{l} .{c} inj sound-ev) ∷ pdisˡ) pdisʳ (there ar)  with w ∈?⟦ p ⟧
... | no ¬w∈p with first-inhabit-++-just-left-any {l} {r} {loc} {c} {w} c∷w∈⟦l⟧ pdisˡ pdisʳ ar -- ¬w ∈ (pdi-src pdi₀), we apply ind hyp
...            | py , first-inhabit-map-left++map-right-eq-py , first-inhabit-eq-py  = py , first-inhabit-map-left++map-right-eq-py  , first-inhabit-eq-py
first-inhabit-++-just-left-any {l} {r} {loc} {c} {w} c∷w∈⟦l⟧ (pdi₀@(pdinstance {p} .{l} .{c} inj sound-ev) ∷ pdisˡ) pdisʳ (there ar) | yes w∈p =
    pdi₀ , refl , refl  -- w ∈ (pdi-src pdi₀), we have can apply the here case using the newly discovered c ∷ w ∈ l that found in pdi₀

-- Purpose: first-inhabit on + returns left-wrapped pdi if c∷w ∈ l
-- Used by: first-pdU-accept-w-isMax-+-left
-- Proof idea: Use first-inhabit-++-just-left-any with pdU-complete, then injectivity
first-inhabit-++-just-left-pdi : ∀ { l r : RE } { loc : ℕ } { c : Char } { w : List Char }
  → (c∷w∈⟦l⟧ : ((c ∷ w) ∈⟦ l ⟧) ) -- we don't know whether unflat c∷w∈⟦l⟧ is the first / left most
  → ( pdi : PDInstance (l + r ` loc) c )
  → first-inhabit (l + r ` loc) c w (pdU[ l + r ` loc , c ]) ≡ just pdi
  → ∃[ pdil ] first-inhabit l c w (pdU[ l , c ]) ≡ just pdil × pdi ≡ pdinstance-left pdil
first-inhabit-++-just-left-pdi {l} {r} {loc} {c} {w} c∷w∈⟦l⟧ pdi first-inhabit-cw-pdu-lr-c≡just-pdi with 
   first-inhabit-++-just-left-any {l} {r} {loc} {c} {w} c∷w∈⟦l⟧ pdU[ l , c ] pdU[ r , c ] ( pdU-complete {l} {c} (unflat {l} {c ∷ w} c∷w∈⟦l⟧) (cong proj₁ (flat∘unflat c∷w∈⟦l⟧)) )
... | py , first-inhabit-map-left++map-right-eq-py , first-inhabit-eq-py  = py , first-inhabit-eq-py  , ev
  where
    just-pdi≡just-left-py : just pdi ≡ just (pdinstance-left py)
    just-pdi≡just-left-py =
      begin
        just pdi
      ≡⟨ sym first-inhabit-cw-pdu-lr-c≡just-pdi ⟩
        first-inhabit ( l + r ` loc ) c w ((List.map (λ x → pdinstance-left {l} {r} {loc} x ) pdU[ l , c ] ) ++ (List.map (λ x → pdinstance-right {l} {r} {loc} x ) pdU[ r , c ] ))
      ≡⟨  first-inhabit-map-left++map-right-eq-py  ⟩ 
       just (pdinstance-left py)
      ∎ 
      
    ev :  pdi ≡ pdinstance-left py
    ev = just-injective    just-pdi≡just-left-py
    

-- Purpose: ≥-Max-PDInstance is preserved through pdinstance-left
-- Used by: first-pdU-accept-w-isMax-+-right, first-pdU-accept-w-isMax-+-left
-- Proof idea: Apply ≥-max-pres-left-helper to inner ≥-Max
≥-max-pres-left-pdi : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdil : PDInstance l c ) (w : List Char)
  → (c∷w∈l : (c ∷ w) ∈⟦ l ⟧)
  → ≥-Max-PDInstance {l} {c} w pdil
  → ≥-Max-PDInstance {l + r ` loc} {c} w (pdinstance-left pdil)
≥-max-pres-left-pdi {l} {r} {loc} {c} (pdinstance inj s-ev) w c∷w∈l (≥-max-pdi u w μ-w μ-c∷w) =
  ≥-max-pdi u w μ-w (≥-max-pres-left-helper (pdi-src (pdinstance inj s-ev)) l r loc c inj u w μ-c∷w)

-- When left is nothing, combined result falls through to right.

-- Invariance lemmas for concatmap-pdinstance-snd under the ε∈ proof.
-- The list of empty parse trees and its soundness evidence are uniquely
-- determined by the regex; these align the parameter ε∈l with the proof
-- generated by the ε∈? l decision.

-- Purpose: Uniqueness of identity proofs (funext-level for propositional equality)
-- Used by: Flat-[]-irrelevant
-- Proof idea: Pattern matching on both refl
UIP : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
UIP refl refl = refl

-- Purpose: Flat-[] proof is unique for given regex and parse tree
-- Used by: zip-es-Flat-[]-irrelevant
-- Proof idea: UIP on the underlying equality proof
Flat-[]-irrelevant : ∀ {l : RE} {e : U l} (fl fl' : Flat-[] l e) → fl ≡ fl'
Flat-[]-irrelevant (flat-[] e p) (flat-[] .e q) = cong (flat-[] e) (UIP p q)

-- Purpose: mkAllEmptyU output is independent of which ε∈ proof is given
-- Used by: zip-es-irrelevant, parseAll-[]-yes
-- Proof idea: Structural induction on RE, case analysis on ε∈ constructors
mkAllEmptyU-irrelevant : ∀ {l : RE} (p q : ε∈ l) → mkAllEmptyU p ≡ mkAllEmptyU q
mkAllEmptyU-irrelevant {ε} ε∈ε ε∈ε = refl
mkAllEmptyU-irrelevant {$ c ` loc} () ()
mkAllEmptyU-irrelevant {l + r ` loc} (ε∈ p + p_r) (ε∈ q + q_r) =
  cong₂ (λ xs ys → List.map LeftU xs ++ List.map RightU ys)
    (mkAllEmptyU-irrelevant p q)
    (mkAllEmptyU-irrelevant p_r q_r)
mkAllEmptyU-irrelevant {l + r ` loc} (ε∈ p + p_r) (ε∈ q <+ ¬q_r) = ⊥-elim ((ε∉r→¬ε∈r ¬q_r) p_r)
mkAllEmptyU-irrelevant {l + r ` loc} (ε∈ p + p_r) (ε∈ ¬q_l +> q_r) = ⊥-elim ((ε∉r→¬ε∈r ¬q_l) p)
mkAllEmptyU-irrelevant {l + r ` loc} (ε∈ p <+ ¬p_r) (ε∈ q + q_r) = ⊥-elim ((ε∉r→¬ε∈r ¬p_r) q_r)
mkAllEmptyU-irrelevant {l + r ` loc} (ε∈ p <+ ¬p_r) (ε∈ q <+ ¬q_r) =
  cong (List.map LeftU) (mkAllEmptyU-irrelevant p q)
mkAllEmptyU-irrelevant {l + r ` loc} (ε∈ p <+ ¬p_r) (ε∈ ¬q_l +> q_r) = ⊥-elim ((ε∉r→¬ε∈r ¬p_r) q_r)
mkAllEmptyU-irrelevant {l + r ` loc} (ε∈ ¬p_l +> p_r) (ε∈ q + q_r) = ⊥-elim ((ε∉r→¬ε∈r ¬p_l) q)
mkAllEmptyU-irrelevant {l + r ` loc} (ε∈ ¬p_l +> p_r) (ε∈ q <+ ¬q_r) = ⊥-elim ((ε∉r→¬ε∈r ¬p_l) q)
mkAllEmptyU-irrelevant {l + r ` loc} (ε∈ ¬p_l +> p_r) (ε∈ ¬q_l +> q_r) =
  cong (List.map RightU) (mkAllEmptyU-irrelevant p_r q_r)
mkAllEmptyU-irrelevant {l ● r ` loc} (ε∈ p ● p_r) (ε∈ q ● q_r) =
  cong₂ (λ us vs → concatMap (λ u → List.map (λ v → PairU u v) vs) us)
    (mkAllEmptyU-irrelevant p q)
    (mkAllEmptyU-irrelevant p_r q_r)
mkAllEmptyU-irrelevant {r * nε ` loc} ε∈* ε∈* = refl

-- Purpose: zip-es-flat-[]-es is independent of ε∈l proof
-- Used by: zip-es-irrelevant
-- Proof idea: Reflexivity (ε∈l is unused in the output structure)
zip-es-ε∈l-irrelevant : ∀ {l : RE} {es : List (U l)} (p q : ε∈ l) (fl : All (Flat-[] l) es)
  → zip-es-flat-[]-es {ε∈l = p} es fl ≡ zip-es-flat-[]-es {ε∈l = q} es fl
zip-es-ε∈l-irrelevant p q fl = refl

-- Purpose: zip-es-flat-[]-es is independent of Flat-[] proof, only depends on list
-- Used by: zip-es-irrelevant
-- Proof idea: Induction on es, Flat-[]-irrelevant for each element
zip-es-Flat-[]-irrelevant : ∀ {l : RE} (ε∈l : ε∈ l) {es es' : List (U l)}
  → (eq : es ≡ es')
  → (fl : All (Flat-[] l) es) (fl' : All (Flat-[] l) es')
  → zip-es-flat-[]-es {ε∈l = ε∈l} es fl ≡ zip-es-flat-[]-es {ε∈l = ε∈l} es' fl'
zip-es-Flat-[]-irrelevant ε∈l refl [] [] = refl
zip-es-Flat-[]-irrelevant ε∈l refl (fl ∷ fls) (fl' ∷ fls') =
  cong₂ (λ f rest → (_ , f) ∷ rest)
    (Flat-[]-irrelevant fl fl')
    (zip-es-Flat-[]-irrelevant ε∈l refl fls fls')

-- Purpose: zip-es-flat-[]-es is independent of which ε∈ proof is given
-- Used by: concatmap-pdinstance-snd-ε∈-irrelevant
-- Proof idea: Combine mkAllEmptyU-irrelevant and zip-es-Flat-[]-irrelevant
zip-es-irrelevant : ∀ {l : RE} (p q : ε∈ l)
  → zip-es-flat-[]-es {ε∈l = p} (mkAllEmptyU p) (mkAllEmptyU-sound p)
  ≡ zip-es-flat-[]-es {ε∈l = q} (mkAllEmptyU q) (mkAllEmptyU-sound q)
zip-es-irrelevant p q =
  trans
    (zip-es-Flat-[]-irrelevant p (mkAllEmptyU-irrelevant p q) (mkAllEmptyU-sound p) (mkAllEmptyU-sound q))
    (zip-es-ε∈l-irrelevant p q (mkAllEmptyU-sound q))

-- Purpose: concatmap-pdinstance-snd is independent of ε∈ proof
-- Used by: ●-yes-list-≡
-- Proof idea: Congruence over zip-es-irrelevant
concatmap-pdinstance-snd-ε∈-irrelevant : ∀ {l r : RE} {loc : ℕ} {c : Char} {pdis : List (PDInstance r c)}
  → (p q : ε∈ l)
  → concatmap-pdinstance-snd {l} {r} {p} {loc} {c} pdis ≡ concatmap-pdinstance-snd {l} {r} {q} {loc} {c} pdis
concatmap-pdinstance-snd-ε∈-irrelevant {l} {r} {loc} {c} {pdis} p q =
  cong (λ xs → concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x pdis) xs) (zip-es-irrelevant p q)

●-yes-list-≡ : ∀ {l r : RE} {loc : ℕ} {c : Char} (p q : ε∈ l)
  → List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ] ++ concatmap-pdinstance-snd {l} {r} {p} {loc} {c} pdU[ r , c ]
  ≡ List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ] ++ concatmap-pdinstance-snd {l} {r} {q} {loc} {c} pdU[ r , c ]
●-yes-list-≡ {l} {r} {loc} {c} p q = cong (λ xs → List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ] ++ xs) (concatmap-pdinstance-snd-ε∈-irrelevant p q)

mutual
  -- Purpose: (Mutual block) If left is nothing, first-inhabit on + falls through to right
-- Used by: first-pdU-accept-w-isMax-+-right
-- Proof idea: Induction on xs, case on membership decision
  first-inhabit-++-nothing-left : ∀ {l r : RE} {loc : ℕ} {c : Char} (w : List Char)
    → (xs : List (PDInstance l c)) (ys : List (PDInstance r c))
    → first-inhabit l c w xs ≡ nothing
    → first-inhabit (l + r ` loc) c w (List.map pdinstance-left xs ++ List.map pdinstance-right ys)
    ≡ first-inhabit (l + r ` loc) c w (List.map pdinstance-right ys)

  first-inhabit-++-nothing-left′ : ∀ {l r : RE} {loc : ℕ} {c : Char} (w : List Char)
    → (x : PDInstance l c) (xs : List (PDInstance l c)) (ys : List (PDInstance r c))
    → first-inhabit l c w (x ∷ xs) ≡ nothing
    → Dec (w ∈⟦ pdi-src x ⟧)
    → first-inhabit (l + r ` loc) c w (List.map pdinstance-left (x ∷ xs) ++ List.map pdinstance-right ys)
    ≡ first-inhabit (l + r ` loc) c w (List.map pdinstance-right ys)

  first-inhabit-++-nothing-left w [] ys eq = refl

  first-inhabit-++-nothing-left w (x ∷ xs) ys eq =
    first-inhabit-++-nothing-left′ w x xs ys eq (w ∈?⟦ pdi-src x ⟧)

  first-inhabit-++-nothing-left′ {l} {r} {loc} {c} w (pdinstance {p} .{l} .{c} inj s-ev) xs ys eq (yes w∈src) =
    ⊥-elim (nothing≢just (trans (sym eq) (first-inhabit-yes-eq-full (pdinstance inj s-ev) xs w∈src)))
  first-inhabit-++-nothing-left′ {l} {r} {loc} {c} w (pdinstance {p} .{l} .{c} inj s-ev) xs ys eq (no ¬w∈src) =
    trans base-no (first-inhabit-++-nothing-left w xs ys eq-xs)
    where
      base-no-eq : first-inhabit l c w (pdinstance inj s-ev ∷ xs) ≡ first-inhabit l c w xs
      base-no-eq = first-inhabit-no-eq (pdinstance inj s-ev) xs ¬w∈src

      eq-xs : first-inhabit l c w xs ≡ nothing
      eq-xs rewrite base-no-eq = eq

      base-no : first-inhabit (l + r ` loc) c w (List.map pdinstance-left (pdinstance inj s-ev ∷ xs) ++ List.map pdinstance-right ys)
        ≡ first-inhabit (l + r ` loc) c w (List.map pdinstance-left xs ++ List.map pdinstance-right ys)
      base-no = first-inhabit-no-eq (pdinstance-left (pdinstance inj s-ev)) _ ¬w∈src

-- Lift maximality through pdinstance-right.
  -- Purpose: ≥-Max-PDInstance is preserved through pdinstance-right when left rejects
-- Used by: first-pdU-accept-w-isMax-+-right
-- Proof idea: Apply ≥-max-pres-right-helper to inner ≥-Max
  ≥-max-pres-right-pdi : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( pdir : PDInstance r c ) (w : List Char)
    → (c∷w∈r : (c ∷ w) ∈⟦ r ⟧)
    → ¬ ((c ∷ w) ∈⟦ l ⟧)
    → ≥-Max-PDInstance {r} {c} w pdir
    → ≥-Max-PDInstance {l + r ` loc} {c} w (pdinstance-right pdir)
  ≥-max-pres-right-pdi {l} {r} {loc} {c} (pdinstance inj s-ev) w c∷w∈r ¬c∷w∈l (≥-max-pdi u w μ-w μ-c∷w) =
    ≥-max-pdi u w μ-w (≥-max-pres-right-helper _ l r loc c inj u w ¬c∷w∈l μ-c∷w)
  
  -- Purpose: Lift ≥-Max from inj u to RightU (inj u) when left rejects c∷w
-- Used by: ≥-max-pres-right-pdi
-- Proof idea: LeftU case impossible by ¬c∷w∈l; RightU case by right-mono-≥
  ≥-max-pres-right-helper : (p l r : RE) (loc : ℕ) (c : Char) (inj : U p → U r)
    → (u : U p) (w : List Char)
    → ¬ ((c ∷ w) ∈⟦ l ⟧)
    → ≥-Max (c ∷ w) (inj u)
    → ≥-Max (c ∷ w) (RightU {l} {r} {loc} (inj u))
  ≥-max-pres-right-helper p l r loc c inj u w ¬c∷w∈l (≥-max _ _ flat-inj-u≡c∷w μ') =
    ≥-max (c ∷ w) (RightU {l} {r} {loc} (inj u))
      flat-inj-u≡c∷w
      (λ { (LeftU v₁) flat-left-v₁≡c∷w →
             let eq : proj₁ (flat {l} v₁) ≡ c ∷ w
                 eq = trans (sym (proj₁-flat-LeftU {l} {r} {loc} v₁)) flat-left-v₁≡c∷w in
             ⊥-elim (¬c∷w∈l (subst (λ x → x ∈⟦ l ⟧) eq (proj₂ (flat {l} v₁))))
         ; (RightU v₂) flat-right-v₂≡c∷w →
             right-mono-≥ (μ' v₂ flat-right-v₂≡c∷w)
         })
  

  -- Purpose: first-inhabit on + returns max pdi when c∷w ∈ r (case analysis on left)
-- Used by: first-pdU-accept-w-isMax-+
-- Proof idea: If left just, use ≥-max-pres-left-pdi; if left nothing, use ≥-max-pres-right-pdi
  first-pdU-accept-w-isMax-+-right : ∀ { l r : RE } { loc : ℕ} { c : Char }
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ r ⟧)
    → ( pdi : PDInstance (l + r ` loc) c)
    → (first-inhabit (l + r ` loc) c w  pdU[ l + r ` loc , c ]) ≡ just pdi
    → ≥-Max-PDInstance {l + r ` loc} {c} w pdi
  first-pdU-accept-w-isMax-+-right {l} {r} {loc} {c} w c∷w∈r pdi eq
    with first-inhabit l c w (pdU[ l , c ]) in d-eq
  ... | just pdil =
    subst (λ x → ≥-Max-PDInstance {l + r ` loc} {c} w x) (sym pdi≡left) max-left
    where
      pdu-lr-c≡maps : pdU[ l + r ` loc , c ] ≡ List.map pdinstance-left (pdU[ l , c ]) ++ List.map pdinstance-right (pdU[ r , c ])
      pdu-lr-c≡maps = refl

      eq-just : first-inhabit l c w (pdU[ l , c ]) ≡ just pdil
      eq-just = d-eq

      eq-left+right : first-inhabit (l + r ` loc) c w (pdU[ l + r ` loc , c ]) ≡ just (pdinstance-left pdil)
      eq-left+right =
        trans
          (cong (λ x → first-inhabit (l + r ` loc) c w x) (sym pdu-lr-c≡maps))
          (first-inhabit-++-just-left-pres w (pdU[ l , c ]) (pdU[ r , c ]) pdil eq-just)

      just-pdi≡just-left-pdil : just pdi ≡ just (pdinstance-left pdil)
      just-pdi≡just-left-pdil = trans (sym eq) eq-left+right

      pdi≡left : pdi ≡ pdinstance-left pdil
      pdi≡left = just-injective just-pdi≡just-left-pdil

      c∷w∈l : (c ∷ w) ∈⟦ l ⟧
      c∷w∈l = first-inhabit-just→c∷w∈r pdil eq-just
        where
          first-inhabit-just→c∷w∈r : ∀ { r : RE } { c : Char } { w : List Char }
            → ( pdi : PDInstance r c )
            → first-inhabit r c w (pdU[ r , c ]) ≡ just pdi
            → (c ∷ w) ∈⟦ r ⟧
          first-inhabit-just→c∷w∈r {r} {c} {w} pdi eq =
            helper pdi (proj₂ (first-inhabit-just-∈ (pdU[ r , c ]) pdi eq))
            where
              helper : ∀ (pdi : PDInstance r c) → w ∈⟦ pdi-src pdi ⟧ → (c ∷ w) ∈⟦ r ⟧
              helper (pdinstance {p} .{r} .{c} inj s-ev) w∈p =
                subst (λ x → x ∈⟦ r ⟧) word-eq (proj₂ (flat (inj (unflat w∈p))))
                where
                  word-eq : proj₁ (flat (inj (unflat w∈p))) ≡ c ∷ w
                  word-eq =
                    begin
                      proj₁ (flat (inj (unflat w∈p)))
                    ≡⟨ s-ev (unflat w∈p) ⟩
                      c ∷ proj₁ (flat (unflat w∈p))
                    ≡⟨ cong (c ∷_) (cong proj₁ (flat∘unflat w∈p)) ⟩
                      c ∷ w
                    ∎

      max-left : ≥-Max-PDInstance {l + r ` loc} {c} w (pdinstance-left pdil)
      max-left = ≥-max-pres-left-pdi pdil w c∷w∈l (first-pdU-accept-w-isMax {l} {c} w c∷w∈l pdil eq-just)
  ... | nothing =
    subst (λ x → ≥-Max-PDInstance {l + r ` loc} {c} w x) (sym pdi≡right) max-right
    where
      eq-nothing : first-inhabit l c w (pdU[ l , c ]) ≡ nothing
      eq-nothing = d-eq

      eq-right : first-inhabit (l + r ` loc) c w (List.map pdinstance-right (pdU[ r , c ])) ≡ just pdi
      eq-right = trans (sym (first-inhabit-++-nothing-left w (pdU[ l , c ]) (pdU[ r , c ]) eq-nothing)) eq

      decomp : ∃[ pdir ] first-inhabit r c w (pdU[ r , c ]) ≡ just pdir × pdi ≡ pdinstance-right pdir
      decomp = first-inhabit-++-just-right-decompose (pdU[ r , c ]) pdi eq-right

      pdir : PDInstance r c
      pdir = proj₁ decomp

      eq-r : first-inhabit r c w (pdU[ r , c ]) ≡ just pdir
      eq-r = proj₁ (proj₂ decomp)

      pdi≡right : pdi ≡ pdinstance-right pdir
      pdi≡right = proj₂ (proj₂ decomp)

      ¬c∷w∈l : ¬ ((c ∷ w) ∈⟦ l ⟧)
      ¬c∷w∈l = first-inhabit-nothing→¬c∷w∈r eq-nothing

      max-right : ≥-Max-PDInstance {l + r ` loc} {c} w (pdinstance-right pdir)
      max-right = ≥-max-pres-right-pdi pdir w c∷w∈r ¬c∷w∈l (first-pdU-accept-w-isMax {r} {c} w c∷w∈r pdir eq-r)

  -- Purpose: first-inhabit on pdU[r,c] returns a ≥-Max-PDInstance (main induction on r)
-- Used by: ≥-max-pres-left-pdi, first-pdU-accept-w-isMax-+-right, first-pdU-accept-w-isMax-+-left, parseAll-head-isMax
-- Proof idea: Structural induction on RE: ε (absurd), $ (direct), + (decompose), ● (fst/snd), * (star)
  first-pdU-accept-w-isMax : ∀ { r : RE } { c : Char }
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ r ⟧)
    → ( pdi : PDInstance r c)
    → (first-inhabit r c w  pdU[ r , c ]) ≡ just pdi
    → ≥-Max-PDInstance {r} {c} w pdi
  first-pdU-accept-w-isMax {ε} {c} w ()
  first-pdU-accept-w-isMax {$ c' ` loc} {c} [] c∷[]∈$c pdi eq rewrite c≡c'-from-∈$ c∷[]∈$c =
    first-pdU-accept-w-isMax-$ {c'} loc pdi eq
  first-pdU-accept-w-isMax {$ c' ` loc} {c} (w₁ ∷ _) ()
  first-pdU-accept-w-isMax {l + r ` loc} {c} w c∷w∈+ pdi eq = first-pdU-accept-w-isMax-+ w c∷w∈+ pdi eq
  first-pdU-accept-w-isMax {l ● r ` loc} {c} w c∷w∈● pdi eq with ε∈? l
  ... | yes ε∈l = first-pdU-accept-w-isMax-●-yes ε∈l w c∷w∈● pdi eq
  ... | no ¬ε∈l = first-pdU-accept-w-isMax-●-no ¬ε∈l w c∷w∈● pdi eq
  first-pdU-accept-w-isMax {r' * nε ` loc} {c} w c∷w∈* pdi eq = first-pdU-accept-w-isMax-* w c∷w∈* pdi eq

  -- Helper for $ c case
  -- Purpose: Base case for letter regex: first-inhabit on [$c,c'] is max
-- Used by: first-pdU-accept-w-isMax
-- Proof idea: Direct construction with ≥-max-pdi for EmptyU and LetterU
  first-pdU-accept-w-isMax-$ : ∀ { c' : Char } → ( loc : ℕ ) ( pdi : PDInstance ($ c' ` loc) c' )
    → (first-inhabit ($ c' ` loc) c' []  pdU[ $ c' ` loc , c' ]) ≡ just pdi
    → ≥-Max-PDInstance { $ c' ` loc } { c' } [] pdi
  first-pdU-accept-w-isMax-$ {c'} loc pdi eq with c' Char.≟ c' in d-eq
  ... | yes refl rewrite pdU[$c]≡∷ {c'} {loc} =
    subst (λ x → ≥-Max-PDInstance { $ c' ` loc } { c' } [] x)
          (sym (just-injective (trans (sym eq) eq-concrete)))
          (≥-max-pdi EmptyU [] max-empty max-letter)
    where
      max-empty : ≥-Max {ε} [] EmptyU
      max-empty = ≥-max [] EmptyU (sym (flat-Uε≡[] EmptyU)) (λ { EmptyU _ → inj₂ refl })

      max-letter : ≥-Max { $ c' ` loc } (c' ∷ []) (LetterU c')
      max-letter = ≥-max (c' ∷ []) (LetterU c') refl (λ { (LetterU _) _ → inj₂ refl })

      eq-concrete : first-inhabit ($ c' ` loc) c' [] [ pdinstance mkinjLetter mkinjLetterSound ] ≡ just (pdinstance mkinjLetter mkinjLetterSound)
      eq-concrete = first-inhabit-yes-eq-full (pdinstance mkinjLetter mkinjLetterSound) [] ε

  ... | no ¬c'≡c' = ⊥-elim (¬c'≡c' refl)

  -- Helper for + case
  -- Purpose: + case: first-inhabit on + regex returns max pdi
-- Used by: first-pdU-accept-w-isMax
-- Proof idea: +-elim to left or right, delegate to +-left or +-right
  first-pdU-accept-w-isMax-+ : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ l + r ` loc ⟧)
    → ( pdi : PDInstance (l + r ` loc) c)
    → (first-inhabit (l + r ` loc) c w  pdU[ l + r ` loc , c ]) ≡ just pdi
    → ≥-Max-PDInstance {l + r ` loc} {c} w pdi
  first-pdU-accept-w-isMax-+ {l} {r} {loc} {c} w c∷w∈+ pdi eq with +-elim c∷w∈+
  ... | inj₁ cw∈l = first-pdU-accept-w-isMax-+-left w cw∈l pdi eq
  ... | inj₂ cw∈r = first-pdU-accept-w-isMax-+-right w cw∈r pdi eq

  -- Purpose: Decompose word membership in + regex to left or right
-- Used by: first-pdU-accept-w-isMax-+
-- Proof idea: Pattern matching on +L or +R constructor
  +-elim : ∀ {l r : RE} {loc : ℕ} {w : List Char} → w ∈⟦ l + r ` loc ⟧ → w ∈⟦ l ⟧ ⊎ w ∈⟦ r ⟧
  +-elim {l} {r} (_+L_ {l} {xs = w} {loc} .r w∈l) = inj₁ w∈l
  +-elim {l} {r} (_+R_ {r} {xs = w} {loc} .l w∈r) = inj₂ w∈r

  -- Purpose: + left case: if c∷w ∈ l, first-inhabit returns left-wrapped max pdi
-- Used by: first-pdU-accept-w-isMax-+
-- Proof idea: first-inhabit-++-just-left-pdi to extract left pdil, then ≥-max-pres-left-pdi
  first-pdU-accept-w-isMax-+-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ l ⟧)
    → ( pdi : PDInstance (l + r ` loc) c)
    → (first-inhabit (l + r ` loc) c w  pdU[ l + r ` loc , c ]) ≡ just pdi
    → ≥-Max-PDInstance {l + r ` loc} {c} w pdi
  first-pdU-accept-w-isMax-+-left {l} {r} {loc} {c} w c∷w∈l pdi eq =
    subst (λ x → ≥-Max-PDInstance {l + r ` loc} {c} w x) (sym pdi≡left) max-left
    where
      pdil : PDInstance l c
      pdil = proj₁ (first-inhabit-++-just-left-pdi c∷w∈l pdi eq)

      eq-left : first-inhabit l c w (pdU[ l , c ]) ≡ just pdil
      eq-left = proj₁ (proj₂ (first-inhabit-++-just-left-pdi c∷w∈l pdi eq))

      max-left : ≥-Max-PDInstance {l + r ` loc} {c} w (pdinstance-left pdil)
      max-left = ≥-max-pres-left-pdi pdil w c∷w∈l (first-pdU-accept-w-isMax {l} {c} w c∷w∈l pdil eq-left)

      pdi≡left : pdi ≡ pdinstance-left pdil
      pdi≡left = proj₂ (proj₂ (first-inhabit-++-just-left-pdi c∷w∈l pdi eq))

  -- Lifting the order pdi-src pdi ⊢ u ≥ u' to the target regex of pdi when pdi ≡ pdi'.
  -- Used in the first-pdU-accept-w-isMax-●-no, ●-yes, and * cases.
  ≥-max-pdi≡-helper : ∀ { regex : RE } { c : Char } { w : List Char }
    → ( pdi : PDInstance regex c )
    → ( u : U (pdi-src pdi) )
    → ( u-max : ≥-Max {pdi-src pdi} w u )
    → ( max-pdi : ≥-Max-Preserve-Local pdi )
    → ( v : U regex )
    → ( u' : U (pdi-src pdi) )
    → ( pdi-u'≡v : pdi-inj pdi u' ≡ v )
    → ( flat-u'≡w : proj₁ (flat {pdi-src pdi} u') ≡ w )
    → regex ⊢ pdi-inj pdi u ≥ v
  ≥-max-pdi≡-helper {regex} {c} {w} pdi u (≥-max .w .u flat-u≡w ev) (≥-max-pres-local f) v u' pdi-u'≡v flat-u'≡w =
    let u-max' = subst (λ x → ≥-Max {pdi-src pdi} x u) (sym flat-u≡w) (≥-max w u flat-u≡w ev)
    in subst (λ x → regex ⊢ pdi-inj pdi u ≥ x) pdi-u'≡v (f u u-max' u' (ev u' flat-u'≡w))

  -- Helper for ● case, ¬ε∈l
  -- Purpose: ● case, ε∉l: first-inhabit on fst-map returns max pdi
-- Used by: first-pdU-accept-w-isMax
-- Proof idea: Build max u via parseAll at source, show dominance via pdi≡or>
  first-pdU-accept-w-isMax-●-no : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( ¬ε∈l : ¬ ε∈ l )
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ l ● r ` loc ⟧)
    → ( pdi : PDInstance (l ● r ` loc) c)
    → (first-inhabit (l ● r ` loc) c w  (List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ])) ≡ just pdi
    → ≥-Max-PDInstance {l ● r ` loc} {c} w pdi
  first-pdU-accept-w-isMax-●-no {l} {r} {loc} {c} ¬ε∈l w c∷w∈● pdi@(pdinstance {p} .{l ● r ` loc} .{c} inj s-ev) eq with ε∈? l in ε∈?l-eq
  ... | yes ε∈l = ⊥-elim (¬ε∈l ε∈l)
  ... | no ¬ε∈l' =
    let pdi∈ = proj₁ (first-inhabit-just-∈ (List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ]) pdi eq)
        w∈src = proj₂ (first-inhabit-just-∈ (List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ]) pdi eq)
        u = maximum (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈src)
        flat-u≡w = maximum-flat (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈src) (parseAll-all-sound {p} {w})
        flat-inj-u≡c∷w : proj₁ (flat (pdi-inj pdi u)) ≡ c ∷ w
        flat-inj-u≡c∷w = trans (s-ev u) (cong (c ∷_) flat-u≡w)
        u-max : ≥-Max {p} w u
        u-max = ≥-max w u flat-u≡w (λ v' flat-v'≡w → maximum-≥-all (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈src) v' (parseAll-complete {p} {w} v' flat-v'≡w))
        μ-w = u-max
        max-pres-pdis = ≥-Max-Preserve-Local-map-fst pdU[ l , c ] pdU-bijective (pdU-preseve-local {l} {c})
        max-pdi = All.lookup max-pres-pdis pdi∈
        sorted = ExtendedOrder.map-fst-ex-sorted pdU[ l , c ] (pdU-sorted {l} {c})
        μ-c∷w = ≥-max (c ∷ w) (pdi-inj pdi u) flat-inj-u≡c∷w λ v flat-v≡c∷w →
          let v-recons = subst (λ xs → Any (Recons v) xs) (trans (cong pdU● ε∈?l-eq) (pdU●-no ¬ε∈l')) (pdU-complete v flat-v≡c∷w)
          in case extract-Recons v-recons of λ where
            (pdi'@(pdinstance {p'} .{l ● r ` loc} .{c} inj' s-ev') , pdi'∈ , recons .v (w'∈ , pdi'-u'≡v)) →
              let u' = unflat w'∈
                  flat-u'≡w : proj₁ (flat {p'} u') ≡ w
                  flat-u'≡w = sym (proj₂ (∷-injective (trans (sym flat-v≡c∷w) (trans (cong proj₁ (cong flat (sym pdi'-u'≡v))) (s-ev' u')))))
                  w'≡w : _ ≡ w
                  w'≡w = trans (sym (cong proj₁ (flat∘unflat {p'} w'∈))) flat-u'≡w
                  w∈src' : w ∈⟦ p' ⟧
                  w∈src' = subst (λ x → x ∈⟦ p' ⟧) w'≡w w'∈
                  pdi≡or> = first-inhabit-just-first (List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ]) pdi eq pdi' pdi'∈ w∈src' sorted
              in case pdi≡or> of λ where
                (inj₂ pdi>pdi') →
                  inj₁ (case pdi>pdi' of λ where
                    (>-pdi _ _ ev) → ev (pdi-inj pdi u) v
                      (recons (pdi-inj pdi u) (proj₂ (flat {p} u) , cong (pdi-inj pdi) (unflat∘proj₂∘flat {p} {u})))
                      (recons v (w'∈ , pdi'-u'≡v)))
                (inj₁ pdi≡pdi') → case pdi≡pdi' of λ where
                  refl → ≥-max-pdi≡-helper pdi u u-max max-pdi v u' pdi'-u'≡v flat-u'≡w
    in ≥-max-pdi u w μ-w μ-c∷w

  -- Helper for ● case, ε∈l
  -- Purpose: ● case, ε∈l: first-inhabit on fst++snd returns max pdi
-- Used by: first-pdU-accept-w-isMax
-- Proof idea: Same pattern as ●-no but with combined pdU-eq for subst
  first-pdU-accept-w-isMax-●-yes : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( ε∈l : ε∈ l )
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ l ● r ` loc ⟧)
    → ( pdi : PDInstance (l ● r ` loc) c)
    → (first-inhabit (l ● r ` loc) c w  (List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ] ++ concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ])) ≡ just pdi
    → ≥-Max-PDInstance {l ● r ` loc} {c} w pdi
  first-pdU-accept-w-isMax-●-yes {l} {r} {loc} {c} ε∈l w c∷w∈● pdi@(pdinstance {p} .{l ● r ` loc} .{c} inj s-ev) eq
    with ε∈? l in ε∈?l-eq
  ... | no ¬ε∈l = ⊥-elim (¬ε∈l ε∈l)
  ... | yes ε∈l' =
    let left = List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ]
        right = concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ]
        input = left ++ right
        pdU-yes-eq : pdU● (yes ε∈l') ≡ input
        pdU-yes-eq = trans (pdU●-yes ε∈l') (●-yes-list-≡ ε∈l' ε∈l)
        pdU-eq : pdU[ l ● r ` loc , c ] ≡ input
        pdU-eq = trans (cong pdU● ε∈?l-eq) pdU-yes-eq
        pdi∈ = proj₁ (first-inhabit-just-∈ input pdi eq)
        w∈src = proj₂ (first-inhabit-just-∈ input pdi eq)
        u = maximum (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈src)
        flat-u≡w = maximum-flat (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈src) (parseAll-all-sound {p} {w})
        flat-inj-u≡c∷w : proj₁ (flat (pdi-inj pdi u)) ≡ c ∷ w
        flat-inj-u≡c∷w = trans (s-ev u) (cong (c ∷_) flat-u≡w)
        u-max : ≥-Max {p} w u
        u-max = ≥-max w u flat-u≡w (λ v' flat-v'≡w → maximum-≥-all (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈src) v' (parseAll-complete {p} {w} v' flat-v'≡w))
        μ-w = u-max
        max-pdi = All.lookup
          (all-concat
            (≥-Max-Preserve-Local-map-fst pdU[ l , c ] (pdU-bijective {l} {c}) (pdU-preseve-local {l} {c}))
            (≥-Max-Preserve-Local-concatmap-pdinstance-snd {ε∈l = ε∈l} pdU[ r , c ] (pdU-bijective {r} {c}) (pdU-preseve-local {r} {c})))
          pdi∈
        sorted-input = subst Ex>-sorted pdU-eq (pdU-sorted {l ● r ` loc} {c})
        μ-c∷w = ≥-max (c ∷ w) (pdi-inj pdi u) flat-inj-u≡c∷w λ v flat-v≡c∷w →
          let v-recons = subst (λ xs → Any (Recons v) xs) pdU-eq (pdU-complete v flat-v≡c∷w)
          in case extract-Recons v-recons of λ where
            (pdi'@(pdinstance {p'} .{l ● r ` loc} .{c} inj' s-ev') , pdi'∈ , recons .v (w'∈ , pdi'-u'≡v)) →
              let u' = unflat w'∈
                  flat-u'≡w : proj₁ (flat {p'} u') ≡ w
                  flat-u'≡w = sym (proj₂ (∷-injective (trans (sym flat-v≡c∷w) (trans (cong proj₁ (cong flat (sym pdi'-u'≡v))) (s-ev' u')))))
                  w'≡w : _ ≡ w
                  w'≡w = trans (sym (cong proj₁ (flat∘unflat {p'} w'∈))) flat-u'≡w
                  w∈src' : w ∈⟦ p' ⟧
                  w∈src' = subst (λ x → x ∈⟦ p' ⟧) w'≡w w'∈
                  pdi≡or> = first-inhabit-just-first input pdi eq pdi' pdi'∈ w∈src' sorted-input
              in case pdi≡or> of λ where
                (inj₂ pdi>pdi') →
                  inj₁ (case pdi>pdi' of λ where
                    (>-pdi _ _ ev) → ev (pdi-inj pdi u) v
                      (recons (pdi-inj pdi u) (proj₂ (flat {p} u) , cong (pdi-inj pdi) (unflat∘proj₂∘flat {p} {u})))
                      (recons v (w'∈ , pdi'-u'≡v)))
                (inj₁ pdi≡pdi') → case pdi≡pdi' of λ where
                  refl → ≥-max-pdi≡-helper pdi u u-max max-pdi v u' pdi'-u'≡v flat-u'≡w
    in ≥-max-pdi u w μ-w μ-c∷w

  -- Helper for * case
  -- Purpose: * case: first-inhabit on star regex returns max pdi
-- Used by: first-pdU-accept-w-isMax
-- Proof idea: Build max u at source, show dominance via pdi≡or> and ≥-max-pdi≡-helper
  first-pdU-accept-w-isMax-* : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { c : Char }
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ r * nε ` loc ⟧)
    → ( pdi : PDInstance (r * nε ` loc) c)
    → (first-inhabit (r * nε ` loc) c w  pdU[ r * nε ` loc , c ]) ≡ just pdi
    → ≥-Max-PDInstance {r * nε ` loc} {c} w pdi
  first-pdU-accept-w-isMax-* {r} {nε} {loc} {c} w c∷w∈* pdi@(pdinstance {p} .{r * nε ` loc} .{c} inj s-ev) eq =
    let pdis = pdU[ r * nε ` loc , c ]
        pdi∈ = proj₁ (first-inhabit-just-∈ pdis pdi eq)
        w∈src = proj₂ (first-inhabit-just-∈ pdis pdi eq)
        u = maximum (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈src)
        flat-u≡w = maximum-flat (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈src) (parseAll-all-sound {p} {w})
        flat-inj-u≡c∷w : proj₁ (flat (pdi-inj pdi u)) ≡ c ∷ w
        flat-inj-u≡c∷w = trans (s-ev u) (cong (c ∷_) flat-u≡w)
        u-max : ≥-Max {p} w u
        u-max = ≥-max w u flat-u≡w (λ v' flat-v'≡w → maximum-≥-all (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈src) v' (parseAll-complete {p} {w} v' flat-v'≡w))
        μ-w = u-max
        max-pdi = All.lookup (pdU-preseve-local {r * nε ` loc} {c}) pdi∈
        sorted = pdU-sorted {r * nε ` loc} {c}
        μ-c∷w = ≥-max (c ∷ w) (pdi-inj pdi u) flat-inj-u≡c∷w λ v flat-v≡c∷w →
          let v-recons = pdU-complete v flat-v≡c∷w
          in case extract-Recons v-recons of λ where
            (pdi'@(pdinstance {p'} .{r * nε ` loc} .{c} inj' s-ev') , pdi'∈ , recons .v (w'∈ , pdi'-u'≡v)) →
              let u' = unflat w'∈
                  flat-u'≡w : proj₁ (flat {p'} u') ≡ w
                  flat-u'≡w = sym (proj₂ (∷-injective (trans (sym flat-v≡c∷w) (trans (cong proj₁ (cong flat (sym pdi'-u'≡v))) (s-ev' u')))))
                  w'≡w : _ ≡ w
                  w'≡w = trans (sym (cong proj₁ (flat∘unflat {p'} w'∈))) flat-u'≡w
                  w∈src' : w ∈⟦ p' ⟧
                  w∈src' = subst (λ x → x ∈⟦ p' ⟧) w'≡w w'∈
                  pdi≡or> = first-inhabit-just-first pdis pdi eq pdi' pdi'∈ w∈src' sorted
              in case pdi≡or> of λ where
                (inj₂ pdi>pdi') →
                  inj₁ (case pdi>pdi' of λ where
                    (>-pdi _ _ ev) → ev (pdi-inj pdi u) v
                      (recons (pdi-inj pdi u) (proj₂ (flat {p} u) , cong (pdi-inj pdi) (unflat∘proj₂∘flat {p} {u})))
                      (recons v (w'∈ , pdi'-u'≡v)))
                (inj₁ pdi≡pdi') → case pdi≡pdi' of λ where
                  refl → ≥-max-pdi≡-helper pdi u u-max max-pdi v u' pdi'-u'≡v flat-u'≡w
    in ≥-max-pdi u w μ-w μ-c∷w

  -- Purpose: Extract the [] equality from Flat-[] proof
-- Used by: +[]-mkAllEmptyU-first-max
-- Proof idea: Pattern matching on flat-[] constructor
  flat-[]-proj : ∀ {r' : RE} {e' : U r'} → Flat-[] r' e' → proj₁ (flat e') ≡ []
  flat-[]-proj (flat-[] _ prf') = prf'

  -- Purpose: First element of mkAllEmptyU for + regex is ≥-Max for []
-- Used by: parseAll-head-isMax (base case for empty word)
-- Proof idea: Use mkAllEmptyU-first-≥-Max with sortedness and flat-[] proof
  +[]-mkAllEmptyU-first-max : ∀ (l r : RE) (loc : ℕ) (prf : ε∈ (l + r ` loc)) (e : U (l + r ` loc)) (es : List (U (l + r ` loc)))
    → mkAllEmptyU prf ≡ e ∷ es
    → ≥-Max [] e
  +[]-mkAllEmptyU-first-max l r loc prf e es eq-mk =
    let sound = subst (All (Flat-[] (l + r ` loc))) eq-mk (mkAllEmptyU-sound prf)
        e-flat = flat-[]-proj (All.head sound)
        sorted = subst (>-sorted {l + r ` loc}) eq-mk (mkAllEmptyU-sorted prf)
    in mkAllEmptyU-first-≥-Max prf e-flat eq-mk sorted

  -- Purpose: Decompose non-empty list into head ∷ tail
-- Used by: parseAll-head-isMax
-- Proof idea: Induction on list structure
  head-tail : ∀ {A : Set} {xs : List A} → xs ≢ [] → Σ[ x ∈ A ] Σ[ xs' ∈ List A ] xs ≡ x ∷ xs'
  head-tail {A} {[]} ¬[] = ⊥-elim (¬[] refl)
  head-tail {A} {x ∷ xs} _ = x , xs , refl

  -- these functions can be moved to Utils
 -- Purpose: map identity function is identity
-- Used by: buildU-≡-map-inj-buildU-root, parseAll-[]-yes
-- Proof idea: Induction on xs
  map-id : ∀ {A : Set} (xs : List A) → List.map (λ x → x) xs ≡ xs
  map-id [] = refl
  map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

 -- Purpose: Pointwise equality of functions implies map equality
-- Used by: concatMap-buildU-advance-lift-pdi*-left, advance-lift-pdi*-left-eq
-- Proof idea: Induction on xs
  map-cong : ∀ {A B : Set} {f g : A → B} {xs : List A}
    → (∀ x → f x ≡ g x)
    → List.map f xs ≡ List.map g xs
  map-cong {xs = []} _ = refl
  map-cong {xs = x ∷ xs} h = cong₂ _∷_ (h x) (map-cong h)

 -- Purpose: map distributes over function composition
-- Used by: buildU-≡-map-inj-buildU-root, buildU-lift-pdi*-left, concatMap-buildU-pdUMany-aux-lemma-step
-- Proof idea: Induction on xs
  map-∘-eq : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
    → List.map (g ∘ f) xs ≡ List.map g (List.map f xs)
  map-∘-eq f g [] = refl
  map-∘-eq f g (x ∷ xs) = cong₂ _∷_ refl (map-∘-eq f g xs)

 -- Purpose: concatMap distributes over function composition
-- Used by: parseAll-pdU-decomp, concatMap-buildU-advance-lift-pdi*-left
-- Proof idea: Induction on xs
  concatMap-∘-eq : ∀ {A B C : Set} (f : A → B) (g : B → List C) (xs : List A)
    → List.concatMap (g ∘ f) xs ≡ List.concatMap g (List.map f xs)
  concatMap-∘-eq f g []       = refl
  concatMap-∘-eq f g (x ∷ xs) = cong (g (f x) ++_) (concatMap-∘-eq f g xs)

  
  -- map distributes over ++
 -- Purpose: map distributes over list concatenation
-- Used by: concatMap-++-distrib, concatMap-advance-lift-pdi*-left-eq
-- Proof idea: Induction on xs
  map-++-distrib : ∀ {A B : Set} (f : A → B) (xs ys : List A)
    → List.map f (xs ++ ys) ≡ List.map f xs ++ List.map f ys
  map-++-distrib f []       ys = refl
  map-++-distrib f (x ∷ xs) ys = cong (f x ∷_) (map-++-distrib f xs ys)
  
 -- Purpose: map and concatMap commute: concatMap (map f ∘ g) = map f ∘ concatMap g
-- Used by: concatMap-buildU-pdUMany-aux-lemma-step, concatMap-buildU-advance-lift-pdi*-left
-- Proof idea: Induction on xs using map-++-distrib
  concatMap-map-commute : ∀ {A B C : Set} (f : B → C) (g : A → List B) (xs : List A)
    → List.concatMap (List.map f ∘ g) xs ≡ List.map f (List.concatMap g xs)
  concatMap-map-commute f g [] = refl
  concatMap-map-commute f g (x ∷ xs) =
        -- cong₂ _++_ refl (concatMap-map-commute f g xs)
        trans (cong (List.map f (g x) ++_) (concatMap-map-commute f g xs))
          (sym (map-++-distrib f (g x) (List.concatMap g xs)))

 -- Purpose: Pointwise equality of list-valued functions implies concatMap equality
-- Used by: parseAll-pdU-decomp, concatMap-buildU-pdUMany-aux-+
-- Proof idea: Induction on xs
  concatMap-cong : ∀ {A B : Set} {f g : A → List B} {xs : List A}
    → (∀ x → f x ≡ g x)
    → List.concatMap f xs ≡ List.concatMap g xs
  concatMap-cong {xs = []} _ = refl
  concatMap-cong {A} {B} {f} {g} {xs = x ∷ xs} h =
    cong₂ _++_ (h x) (concatMap-cong {A} {B} {f} {g} {xs = xs} h)

 -- Purpose: concat distributes over list concatenation
-- Used by: concatMap-++-distrib
-- Proof idea: Induction on xs using ++-assoc
  concat-++ : ∀ {A : Set} (xs ys : List (List A))
    → List.concat (xs ++ ys) ≡ List.concat xs ++ List.concat ys
  concat-++ [] ys = refl
  concat-++ (x ∷ xs) ys =
    trans (cong (x ++_) (concat-++ xs ys))
          (sym (++-assoc x (List.concat xs) (List.concat ys)))

 -- Purpose: concatMap distributes over list concatenation
-- Used by: concatMap-buildU-pdUMany-aux-lemma-step, concatMap-buildU-pdUMany-aux-+
-- Proof idea: concat (map f (xs++ys)) = concat (map f xs ++ map f ys) = concat xs ++ concat ys
  concatMap-++-distrib : ∀ {A B : Set} (f : A → List B) (xs ys : List A)
    → List.concatMap f (xs ++ ys) ≡ List.concatMap f xs ++ List.concatMap f ys
  concatMap-++-distrib f xs ys =
    trans (cong List.concat (map-++-distrib f xs ys))
          (concat-++ (List.map f xs) (List.map f ys))

  -- pdUMany-aux distributes over list concatenation
 -- Purpose: pdUMany-aux distributes over list concatenation
-- Used by: (internal helper for pdUMany reasoning)
-- Proof idea: Induction on w, using concatMap-++-distrib
  pdUMany-aux-++-distrib : ∀ {r : RE} {pref : List Char} (w : List Char) (pdis₁ pdis₂ : List (PDInstance* r pref))
    → pdUMany-aux {r} {pref} w (pdis₁ ++ pdis₂)
      ≡ pdUMany-aux {r} {pref} w pdis₁ ++ pdUMany-aux {r} {pref} w pdis₂
  pdUMany-aux-++-distrib {r} {pref} [] pdis₁ pdis₂ rewrite (++-identityʳ pref) = refl
  pdUMany-aux-++-distrib {r} {pref} (c ∷ cs) pdis₁ pdis₂ =
    let adv₁ = List.concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis₁
        adv₂ = List.concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis₂
        adv-eq = concatMap-++-distrib (advance-pdi*-with-c {r} {pref} {c}) pdis₁ pdis₂
    in trans (cong (pdUMany-aux {r} {pref ∷ʳ c} cs) adv-eq)
             (pdUMany-aux-++-distrib {r} {pref ∷ʳ c} cs adv₁ adv₂)

  -- parseAll[ p , [] ] = buildU (root pdi*)
  -- Purpose: parseAll for empty word equals buildU of root PDInstance*
-- Used by: parseAll-[]-yes
-- Proof idea: ++-identityʳ from parseAll definition
  parseAll-[]≡buildU-root : ∀ {p : RE} → parseAll[ p , [] ] ≡ buildU (pdinstance* {p} {p} {[]} (λ u → u) (λ u → refl))
  parseAll-[]≡buildU-root {p} = ++-identityʳ _

  -- buildU pdi* = map inj (buildU root-p)  (both check ε∈? p)
  -- Purpose: buildU of pdi* equals map inj of buildU at source
-- Used by: buildU-≡-map-inj-parseAll-[]
-- Proof idea: Case on ε∈? p, map-∘-eq or refl
  buildU-≡-map-inj-buildU-root : ∀ {p r : RE} {pref : List Char} (inj : U p → U r) (s-ev : ∀ u → proj₁ (flat {r} (inj u)) ≡ pref ++ proj₁ (flat {p} u))
    → buildU (pdinstance* {p} {r} {pref} inj s-ev) ≡ List.map inj (buildU (pdinstance* {p} {p} {[]} (λ u → u) (λ u → refl)))
  buildU-≡-map-inj-buildU-root {p} inj s-ev with ε∈? p
  ... | yes ε∈p = map-∘-eq (λ u → u) inj (mkAllEmptyU ε∈p)
  ... | no ¬ε∈p = refl

  -- Base case: buildU on a single pdi* equals map inj (parseAll[src, []])
  -- Purpose: buildU of pdi* equals map inj of parseAll at source for empty word
-- Used by: concatMap-buildU-pdUMany-aux-lemma (base case)
-- Proof idea: Combine buildU-≡-map-inj-buildU-root with parseAll-[]≡buildU-root
  buildU-≡-map-inj-parseAll-[] : ∀ {r : RE} {pref : List Char} (pdi* : PDInstance* r pref)
    → buildU pdi* ≡ List.map (pdi*-inj pdi*) (parseAll[ pdi*-src pdi* , [] ])
  buildU-≡-map-inj-parseAll-[] (pdinstance* {p} {r} {pref} inj s-ev) =
    trans (buildU-≡-map-inj-buildU-root inj s-ev)
          (cong (List.map inj) (sym (parseAll-[]≡buildU-root {p})))

  -- Decomposition: parseAll[d, c∷cs] = concatMap (map (pdi-inj pdi) ∘ parseAll[pdi-src pdi, cs]) (pdU[d, c])
  -- Purpose: parseAll for c∷cs decomposes into concatMap over pdU[d,c]
-- Used by: parseAll-head-isMax (inductive step)
-- Proof idea: Chain equalities through concatMap-buildU-pdUMany-aux-lemma
  parseAll-pdU-decomp : ∀ {d : RE} (c : Char) (cs : List Char)
    → parseAll[ d , c ∷ cs ]
      ≡ List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , cs ])) (pdU[ d , c ])
  parseAll-pdU-decomp {d} c cs =
    let root-d : PDInstance* d []
        root-d = pdinstance* {d} {d} {[]} (λ u → u) (λ u → refl)

        pdis' : List (PDInstance* d ([] ∷ʳ c))
        pdis' = List.concatMap (advance-pdi*-with-c {d} {[]} {c}) (root-d ∷ [])

        ih : List.concatMap buildU (pdUMany-aux {d} {[] ∷ʳ c} cs pdis')
          ≡ List.concatMap g pdis'
        ih = concatMap-buildU-pdUMany-aux-lemma {d} {[] ∷ʳ c} cs pdis'
    in
      trans
        refl
        (trans
          refl
          (trans
            ih
            (trans
              refl
              (trans
                step1
                (trans
                  (sym (concatMap-∘-eq comp-f g pdU-list))
                  (concatMap-cong {xs = pdU-list} g∘comp-f≡h))))))
      where
        comp-f : PDInstance d c → PDInstance* d ([] ∷ʳ c)
        comp-f = compose-pdi-with {d} {d} {[]} {c} (λ u → u) (λ u → refl)

        g : PDInstance* d ([] ∷ʳ c) → List (U d)
        g = λ pdi*' → List.map (pdi*-inj pdi*') (parseAll[ pdi*-src pdi*' , cs ])

        h : PDInstance d c → List (U d)
        h = λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , cs ])

        g∘comp-f≡h : ∀ (pdi : PDInstance d c) → g (comp-f pdi) ≡ h pdi
        g∘comp-f≡h (pdinstance {p} .{d} .{c} p→d _) =
          trans (map-∘-eq p→d (λ u → u) (parseAll[ p , cs ]))
                (map-id (List.map p→d (parseAll[ p , cs ])))

        pdU-list : List (PDInstance d c)
        pdU-list = pdU[ d , c ]

        step1 : List.concatMap g (List.map comp-f pdU-list ++ []) ≡ List.concatMap g (List.map comp-f pdU-list)
        step1 = cong (List.concatMap g) (++-identityʳ (List.map comp-f pdU-list))

  -- Step: connects the IH result to the goal for c ∷ cs
  -- Purpose: Step lemma connecting IH to goal in concatMap-buildU-pdUMany-aux-lemma
-- Used by: concatMap-buildU-pdUMany-aux-lemma
-- Proof idea: Induction on pdis, decompose via parseAll-pdU-decomp
  concatMap-buildU-pdUMany-aux-lemma-step :
    ∀ {r : RE} {pref : List Char} (c : Char) (cs : List Char) (pdis : List (PDInstance* r pref))
    → List.concatMap (λ pdi*' → List.map (pdi*-inj pdi*') (parseAll[ pdi*-src pdi*' , cs ]))
        (List.concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    ≡ List.concatMap (λ pdi* → List.map (pdi*-inj pdi*) (parseAll[ pdi*-src pdi* , c ∷ cs ])) pdis
  concatMap-buildU-pdUMany-aux-lemma-step {r} {pref} c cs [] = refl
  concatMap-buildU-pdUMany-aux-lemma-step {r} {pref} c cs (pdi*@(pdinstance* {d} .{r} .{pref} d→r s-ev) ∷ pdis) =
    let ih = concatMap-buildU-pdUMany-aux-lemma-step c cs pdis
    in
      trans
        (cong (List.concatMap g) (advance-split pdi* pdis))
        (trans
          (concatMap-++-distrib g (advance-pdi*-with-c {r} {pref} {c} pdi*) (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis))
          (cong₂ _++_ left-side≡goal ih))
      where
        comp-f : PDInstance d c → PDInstance* r (pref ∷ʳ c)
        comp-f = compose-pdi-with {r} {d} {pref} {c} d→r s-ev

        g : PDInstance* r (pref ∷ʳ c) → List (U r)
        g = λ pdi*' → List.map (pdi*-inj pdi*') (parseAll[ pdi*-src pdi*' , cs ])

        advance-split : ∀ (p : PDInstance* r pref) (ps : List (PDInstance* r pref))
          → concatMap (advance-pdi*-with-c {r} {pref} {c}) (p ∷ ps)
            ≡ advance-pdi*-with-c {r} {pref} {c} p ++ concatMap (advance-pdi*-with-c {r} {pref} {c}) ps
        advance-split p ps = refl

        left-side : List (U r)
        left-side = List.concatMap g (advance-pdi*-with-c {r} {pref} {c} pdi*)

        left-goal : List (U r)
        left-goal = List.map d→r (parseAll[ d , c ∷ cs ])

        adv-equals-map-comp-f : advance-pdi*-with-c {r} {pref} {c} pdi*
          ≡ List.map comp-f (pdU[ d , c ])
        adv-equals-map-comp-f = refl

        left-side≡left-side' : left-side ≡ List.concatMap g (List.map comp-f (pdU[ d , c ]))
        left-side≡left-side' = cong (List.concatMap g) adv-equals-map-comp-f

        g∘comp-f≡map : ∀ (pdi : PDInstance d c) → g (comp-f pdi) ≡ List.map d→r (List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , cs ]))
        g∘comp-f≡map (pdinstance {p} .{d} .{c} p→d _) = map-∘-eq p→d d→r (parseAll[ p , cs ])

        g∘comp-f≡map-cong : List.concatMap g (List.map comp-f (pdU[ d , c ]))
          ≡ List.concatMap (λ pdi → List.map d→r (List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , cs ]))) (pdU[ d , c ])
        g∘comp-f≡map-cong = trans (sym (concatMap-∘-eq comp-f g (pdU[ d , c ])))
                             (concatMap-cong {xs = pdU[ d , c ]} g∘comp-f≡map)

        factor-out : List.concatMap (λ pdi → List.map d→r (List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , cs ]))) (pdU[ d , c ])
          ≡ List.map d→r (List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , cs ])) (pdU[ d , c ]))
        factor-out = concatMap-map-commute d→r (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , cs ])) (pdU[ d , c ])

        decomp-lemma : List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , cs ])) (pdU[ d , c ])
          ≡ parseAll[ d , c ∷ cs ]
        decomp-lemma = sym (parseAll-pdU-decomp {d} c cs)

        decomp : List.map d→r (List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , cs ])) (pdU[ d , c ]))
          ≡ List.map d→r (parseAll[ d , c ∷ cs ])
        decomp = cong (List.map d→r) decomp-lemma

        left-side≡goal : left-side ≡ left-goal
        left-side≡goal = trans left-side≡left-side' (trans g∘comp-f≡map-cong (trans factor-out decomp))

  -- Key lemma: concatMap buildU (pdUMany-aux w pdis)
  --   = concatMap (λ pdi* → map (pdi*-inj pdi*) (parseAll[src pdi*, w])) pdis
  -- Purpose: Key lemma: concatMap buildU over pdUMany-aux equals concatMap of parseAll at sources
-- Used by: parseAll-pdU-decomp
-- Proof idea: Induction on w, base case uses buildU-≡-map-inj-parseAll-[]
  concatMap-buildU-pdUMany-aux-lemma :
    ∀ {r : RE} {pref : List Char} (w : List Char) (pdis : List (PDInstance* r pref))
    → List.concatMap buildU (pdUMany-aux {r} {pref} w pdis)
      ≡ List.concatMap (λ pdi* → List.map (pdi*-inj pdi*) (parseAll[ pdi*-src pdi* , w ])) pdis
  concatMap-buildU-pdUMany-aux-lemma {r} {pref} [] pdis rewrite (++-identityʳ pref) = lemma-[] pdis
    where
      lemma-[] : (pdis : List (PDInstance* r pref))
        → List.concatMap buildU pdis
          ≡ List.concatMap (λ pdi* → List.map (pdi*-inj pdi*) (parseAll[ pdi*-src pdi* , [] ])) pdis
      lemma-[] [] = refl
      lemma-[] (pdi* ∷ pdis') = cong₂ _++_ (buildU-≡-map-inj-parseAll-[] pdi*) (lemma-[] pdis')
  concatMap-buildU-pdUMany-aux-lemma {r} {pref} (c ∷ cs) pdis =
    let pdis' = List.concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis
        ih = concatMap-buildU-pdUMany-aux-lemma {r} {pref ∷ʳ c} cs pdis'
    in
      begin
        List.concatMap buildU (pdUMany-aux {r} {pref ∷ʳ c} cs pdis')
      ≡⟨ ih ⟩
        List.concatMap (λ pdi*' → List.map (pdi*-inj pdi*') (parseAll[ pdi*-src pdi*' , cs ])) pdis'
      ≡⟨ concatMap-buildU-pdUMany-aux-lemma-step c cs pdis ⟩
        List.concatMap (λ pdi* → List.map (pdi*-inj pdi*) (parseAll[ pdi*-src pdi* , c ∷ cs ])) pdis
      ∎


  -- Purpose: Lift PDInstance* from l to l+r by wrapping with LeftU
-- Used by: concatMap-buildU-pdUMany-aux-+, map-compose-id-left, advance-lift-pdi*-left-eq
-- Proof idea: Construct new pdinstance* with LeftU ∘ inj
  lift-pdi*-left : ∀ {l r loc} {pref : List Char}
    → PDInstance* l pref
    → PDInstance* (l + r ` loc) pref
  lift-pdi*-left {l} {r} {loc} {pref} (pdinstance* {p} .{l} .{pref} inj s-ev) =
    pdinstance* {p} {l + r ` loc} {pref} (LeftU ∘ inj) s-ev

  -- Purpose: Lift PDInstance* from r to l+r by wrapping with RightU
-- Used by: concatMap-buildU-pdUMany-aux-+, map-compose-id-right, advance-lift-pdi*-right-eq
-- Proof idea: Construct new pdinstance* with RightU ∘ inj
  lift-pdi*-right : ∀ {l r loc} {pref : List Char}
    → PDInstance* r pref
    → PDInstance* (l + r ` loc) pref
  lift-pdi*-right {l} {r} {loc} {pref} (pdinstance* {p} .{r} .{pref} inj s-ev) =
    pdinstance* {p} {l + r ` loc} {pref} (RightU ∘ inj) s-ev



  -- Purpose: buildU commutes with lift-pdi*-left: buildU of lifted = map LeftU of buildU
-- Used by: concatMap-buildU-pdUMany-aux-+
-- Proof idea: Case on ε∈? p, map-∘-eq or refl
  buildU-lift-pdi*-left : ∀ {l r loc} {pref : List Char} (pdi* : PDInstance* l pref)
    → buildU (lift-pdi*-left {l} {r} {loc} {pref} pdi*) ≡ List.map LeftU (buildU pdi*)
  buildU-lift-pdi*-left (pdinstance* {p} .{_} .{_} inj s-ev) with ε∈? p
  ... | yes ε∈p = map-∘-eq inj LeftU (mkAllEmptyU ε∈p)
  ... | no ¬ε∈p = refl

  -- Purpose: buildU commutes with lift-pdi*-right: buildU of lifted = map RightU of buildU
-- Used by: concatMap-buildU-pdUMany-aux-+
-- Proof idea: Case on ε∈? p, map-∘-eq or refl
  buildU-lift-pdi*-right : ∀ {l r loc} {pref : List Char} (pdi* : PDInstance* r pref)
    → buildU (lift-pdi*-right {l} {r} {loc} {pref} pdi*) ≡ List.map RightU (buildU pdi*)
  buildU-lift-pdi*-right (pdinstance* {p} .{_} .{_} inj s-ev) with ε∈? p
  ... | yes ε∈p = map-∘-eq inj RightU (mkAllEmptyU ε∈p)
  ... | no ¬ε∈p = refl

  -- Purpose: buildU commutes with compose-pdi-with and LeftU wrapping
-- Used by: concatMap-buildU-advance-lift-pdi*-left
-- Proof idea: Case on ε∈? p, map-∘-eq or refl
  buildU-compose-left :
    ∀ {l r loc} {pref : List Char} {c : Char} {d : RE}
      (inj : U d → U l) (s-ev : ∀ u → proj₁ (flat {l} (inj u)) ≡ pref ++ proj₁ (flat {d} u))
      (pdi' : PDInstance d c)
    → buildU (compose-pdi-with {l + r ` loc} {d} {pref} {c} (LeftU ∘ inj) s-ev pdi')
      ≡ List.map LeftU (buildU (compose-pdi-with {l} {d} {pref} {c} inj s-ev pdi'))
  buildU-compose-left {l} {r} {loc} {pref} {c} {d} inj s-ev (pdinstance {p} {d} {c} p→d s-ev-p→d) with ε∈? p
  ... | yes ε∈p = ev
      where
        ev : List.map (λ x → (LeftU {l} {r} {loc} (inj (p→d x)))) (mkAllEmptyU ε∈p) ≡
             List.map LeftU (List.map (λ x → inj (p→d x)) (mkAllEmptyU ε∈p))
        ev =  map-∘-eq  (λ x → inj (p→d x)) LeftU (mkAllEmptyU ε∈p) 
  ... | no ¬ε∈p = refl

  -- Purpose: buildU commutes with compose-pdi-with and RightU wrapping
-- Used by: concatMap-buildU-advance-lift-pdi*-right
-- Proof idea: Case on ε∈? p, map-∘-eq or refl
  buildU-compose-right :
    ∀ {l r loc} {pref : List Char} {c : Char} {d : RE}
      (inj : U d → U r) (s-ev : ∀ u → proj₁ (flat {r} (inj u)) ≡ pref ++ proj₁ (flat {d} u))
      (pdi' : PDInstance d c)
    → buildU (compose-pdi-with {l + r ` loc} {d} {pref} {c} (RightU ∘ inj) s-ev pdi')
      ≡ List.map RightU (buildU (compose-pdi-with {r} {d} {pref} {c} inj s-ev pdi'))
  buildU-compose-right {l} {r} {loc} {pref} {c} {d} inj s-ev (pdinstance {p} {d} {c} p→d s-ev-p→d) with ε∈? p
  ... | yes ε∈p = ev
      where
        ev : List.map (λ x → (RightU {l} {r} {loc} (inj (p→d x)))) (mkAllEmptyU ε∈p) ≡
             List.map RightU (List.map (λ x → inj (p→d x)) (mkAllEmptyU ε∈p))
        ev =  map-∘-eq  (λ x → inj (p→d x)) RightU (mkAllEmptyU ε∈p)   
  ... | no ¬ε∈p = refl

  -- Purpose: concatMap buildU over advance of lifted pdi* equals LeftU-wrapped result
-- Used by: concatMap-advance-lift-pdi*-left-eq
-- Proof idea: Rewrite advance as map compose, use buildU-compose-left, commute
  concatMap-buildU-advance-lift-pdi*-left :
    ∀ {l r loc} {pref : List Char} {c : Char}
    → (pdi* : PDInstance* l pref)
    → List.concatMap buildU (advance-pdi*-with-c {l + r ` loc} {pref} {c} (lift-pdi*-left {l} {r} {loc} {pref} pdi*))
      ≡ List.map LeftU (List.concatMap buildU (advance-pdi*-with-c {l} {pref} {c} pdi*))
  concatMap-buildU-advance-lift-pdi*-left {l} {r} {loc} {pref} {c} (pdinstance* {d} {l} {pref} inj s-ev) = 
    begin
      List.concatMap buildU
        (List.map (compose-pdi-with {l + r ` loc} {d} {pref} {c} (LeftU ∘ inj) s-ev) pdU[ d , c ])
    ≡⟨ sym (concatMap-∘-eq (compose-pdi-with (λ x → LeftU {l} {r} {loc} (inj x)) s-ev) buildU pdU[ d , c ])  ⟩ 
      List.concatMap (λ pdi' → buildU (compose-pdi-with {l + r ` loc} {d} {pref} {c} (LeftU ∘ inj) s-ev pdi')) pdU[ d , c ]
    ≡⟨ cong List.concat (map-cong {xs = pdU[ d , c ]} (λ pdi' → buildU-compose-left inj s-ev pdi')) ⟩
      List.concatMap (λ pdi' → List.map LeftU (buildU (compose-pdi-with {l} {d} {pref} {c} inj s-ev pdi'))) pdU[ d , c ]
    ≡⟨ concatMap-map-commute LeftU (λ pdi' → buildU (compose-pdi-with {l} {d} {pref} {c} inj s-ev pdi')) pdU[ d , c ] ⟩
      List.map LeftU (List.concatMap (λ pdi' → buildU (compose-pdi-with {l} {d} {pref} {c} inj s-ev pdi')) pdU[ d , c ])
    ≡⟨ cong (List.map LeftU) (concatMap-∘-eq (compose-pdi-with inj s-ev) buildU pdU[ d , c ]) ⟩
      List.map LeftU (List.concatMap buildU (advance-pdi*-with-c {l} {pref} {c} (pdinstance* inj s-ev)))
    ∎  

  -- Purpose: concatMap buildU over advance of lifted pdi* equals RightU-wrapped result
-- Used by: concatMap-advance-lift-pdi*-right-eq
-- Proof idea: Rewrite advance as map compose, use buildU-compose-right, commute
  concatMap-buildU-advance-lift-pdi*-right :
    ∀ {l r loc} {pref : List Char} {c : Char}
    → (pdi* : PDInstance* r pref)
    → List.concatMap buildU (advance-pdi*-with-c {l + r ` loc} {pref} {c} (lift-pdi*-right {l} {r} {loc} {pref} pdi*))
      ≡ List.map RightU (List.concatMap buildU (advance-pdi*-with-c {r} {pref} {c} pdi*))
  concatMap-buildU-advance-lift-pdi*-right {l} {r} {loc} {pref} {c} (pdinstance* {d} {r} {pref} inj s-ev) =
    begin
      List.concatMap buildU
        (List.map (compose-pdi-with {l + r ` loc} {d} {pref} {c} (RightU ∘ inj) s-ev) pdU[ d , c ])
    ≡⟨ sym (concatMap-∘-eq (compose-pdi-with (λ x → RightU {l} {r} {loc} (inj x)) s-ev) buildU pdU[ d , c ]) ⟩
      List.concatMap (λ pdi' → buildU (compose-pdi-with {l + r ` loc} {d} {pref} {c} (RightU ∘ inj) s-ev pdi')) pdU[ d , c ]
    ≡⟨ cong List.concat (map-cong {xs = pdU[ d , c ]} (λ pdi' → buildU-compose-right inj s-ev pdi')) ⟩
      List.concatMap (λ pdi' → List.map RightU (buildU (compose-pdi-with {r} {d} {pref} {c} inj s-ev pdi'))) pdU[ d , c ]
    ≡⟨ concatMap-map-commute RightU (λ pdi' → buildU (compose-pdi-with {r} {d} {pref} {c} inj s-ev pdi')) pdU[ d , c ] ⟩
      List.map RightU (List.concatMap (λ pdi' → buildU (compose-pdi-with {r} {d} {pref} {c} inj s-ev pdi')) pdU[ d , c ])
    ≡⟨ cong (List.map RightU) (concatMap-∘-eq (compose-pdi-with inj s-ev) buildU pdU[ d , c ]) ⟩
      List.map RightU (List.concatMap buildU (advance-pdi*-with-c {r} {pref} {c} (pdinstance* inj s-ev)))
    ∎ 
  -- Purpose: compose-pdi-with with LeftU equals lift of compose-pdi-with
-- Used by: advance-lift-pdi*-left-eq, map-compose-id-left
-- Proof idea: Reflexivity after pattern matching on pdinstance
  compose-pdi-with-lift-pdi*-left-eq : ∀ {l r loc} {pref : List Char} {c : Char} {d : RE}
    (inj : U d → U l) (s-ev : ∀ u → proj₁ (flat {l} (inj u)) ≡ pref ++ proj₁ (flat {d} u))
    (pdi : PDInstance d c)
    → compose-pdi-with {l + r ` loc} {d} {pref} {c} (LeftU ∘ inj) s-ev pdi
      ≡ lift-pdi*-left {l} {r} {loc} {pref ∷ʳ c} (compose-pdi-with {l} {d} {pref} {c} inj s-ev pdi)
  compose-pdi-with-lift-pdi*-left-eq inj s-ev (pdinstance f s-ev-p) = refl

  -- Purpose: compose-pdi-with with RightU equals lift of compose-pdi-with
-- Used by: advance-lift-pdi*-right-eq, map-compose-id-right
-- Proof idea: Reflexivity after pattern matching on pdinstance
  compose-pdi-with-lift-pdi*-right-eq : ∀ {l r loc} {pref : List Char} {c : Char} {d : RE}
    (inj : U d → U r) (s-ev : ∀ u → proj₁ (flat {r} (inj u)) ≡ pref ++ proj₁ (flat {d} u))
    (pdi : PDInstance d c)
    → compose-pdi-with {l + r ` loc} {d} {pref} {c} (RightU ∘ inj) s-ev pdi
      ≡ lift-pdi*-right {l} {r} {loc} {pref ∷ʳ c} (compose-pdi-with {r} {d} {pref} {c} inj s-ev pdi)
  compose-pdi-with-lift-pdi*-right-eq inj s-ev (pdinstance f s-ev-p) = refl

  -- Purpose: advance commutes with lift-pdi*-left: advance then lift = lift then advance
-- Used by: concatMap-advance-lift-pdi*-left-eq
-- Proof idea: Rewrite advance as map compose, use compose-pdi-with-lift-pdi*-left-eq
  advance-lift-pdi*-left-eq : ∀ {l r loc} {pref : List Char} (c : Char)
    (pdi* : PDInstance* l pref)
    → advance-pdi*-with-c {l + r ` loc} {pref} {c} (lift-pdi*-left {l} {r} {loc} {pref} pdi*)
      ≡ List.map (lift-pdi*-left {l} {r} {loc} {pref ∷ʳ c}) (advance-pdi*-with-c {l} {pref} {c} pdi*)
  advance-lift-pdi*-left-eq {l} {r} {loc} {pref} c (pdinstance* {d} inj s-ev) =
    begin
      advance-pdi*-with-c {l + r ` loc} {pref} {c} (lift-pdi*-left {l} {r} {loc} {pref} (pdinstance* inj s-ev))
    ≡⟨ refl ⟩
      List.map (compose-pdi-with {l + r ` loc} {d} {pref} {c} (λ x → LeftU {l} {r} {loc} (inj x)) s-ev) pdU[ d , c ]
    ≡⟨ map-cong {xs = pdU[ d , c ]} (λ pdi → compose-pdi-with-lift-pdi*-left-eq inj s-ev pdi) ⟩
      List.map (lift-pdi*-left {l} {r} {loc} {pref ∷ʳ c} ∘ compose-pdi-with {l} {d} {pref} {c} inj s-ev) pdU[ d , c ]
    ≡⟨ map-∘-eq (compose-pdi-with {l} {d} {pref} {c} inj s-ev) (lift-pdi*-left {l} {r} {loc} {pref ∷ʳ c}) pdU[ d , c ] ⟩
      List.map (lift-pdi*-left {l} {r} {loc} {pref ∷ʳ c}) (advance-pdi*-with-c {l} {pref} {c} (pdinstance* inj s-ev))
    ∎

  -- Purpose: advance commutes with lift-pdi*-right
-- Used by: concatMap-advance-lift-pdi*-right-eq
-- Proof idea: Rewrite advance as map compose, use compose-pdi-with-lift-pdi*-right-eq
  advance-lift-pdi*-right-eq : ∀ {l r loc} {pref : List Char} (c : Char)
    (pdi* : PDInstance* r pref)
    → advance-pdi*-with-c {l + r ` loc} {pref} {c} (lift-pdi*-right {l} {r} {loc} {pref} pdi*)
      ≡ List.map (lift-pdi*-right {l} {r} {loc} {pref ∷ʳ c}) (advance-pdi*-with-c {r} {pref} {c} pdi*)
  advance-lift-pdi*-right-eq {l} {r} {loc} {pref} c (pdinstance* {d} inj s-ev) =
    begin
      advance-pdi*-with-c {l + r ` loc} {pref} {c} (lift-pdi*-right {l} {r} {loc} {pref} (pdinstance* inj s-ev))
    ≡⟨ refl ⟩
      List.map (compose-pdi-with {l + r ` loc} {d} {pref} {c} (λ x → RightU {l} {r} {loc} (inj x)) s-ev) pdU[ d , c ]
    ≡⟨ map-cong {xs = pdU[ d , c ]} (λ pdi → compose-pdi-with-lift-pdi*-right-eq inj s-ev pdi) ⟩
      List.map (lift-pdi*-right {l} {r} {loc} {pref ∷ʳ c} ∘ compose-pdi-with {r} {d} {pref} {c} inj s-ev) pdU[ d , c ]
    ≡⟨ map-∘-eq (compose-pdi-with {r} {d} {pref} {c} inj s-ev) (lift-pdi*-right {l} {r} {loc} {pref ∷ʳ c}) pdU[ d , c ] ⟩
      List.map (lift-pdi*-right {l} {r} {loc} {pref ∷ʳ c}) (advance-pdi*-with-c {r} {pref} {c} (pdinstance* inj s-ev))
    ∎

  -- Purpose: concatMap of advance over lifted list equals lift of concatMap of advance
-- Used by: concatMap-buildU-pdUMany-aux-+
-- Proof idea: Induction on pdis-l, using advance-lift-pdi*-left-eq and map-++-distrib
  concatMap-advance-lift-pdi*-left-eq : ∀ {l r loc} {pref : List Char} (c : Char)
    (pdis-l : List (PDInstance* l pref))
    → List.concatMap (advance-pdi*-with-c {l + r ` loc} {pref} {c}) (List.map lift-pdi*-left pdis-l)
      ≡ List.map lift-pdi*-left (List.concatMap (advance-pdi*-with-c {l} {pref} {c}) pdis-l)
  concatMap-advance-lift-pdi*-left-eq c [] = refl
  concatMap-advance-lift-pdi*-left-eq {l} {r} {loc} {pref} c (pdi* ∷ pdis-l) =
    trans
      (cong₂ _++_ (advance-lift-pdi*-left-eq c pdi*) (concatMap-advance-lift-pdi*-left-eq c pdis-l))
      (sym (map-++-distrib lift-pdi*-left
             (advance-pdi*-with-c {l} {pref} {c} pdi*)
             (List.concatMap (advance-pdi*-with-c {l} {pref} {c}) pdis-l)))

  -- Purpose: concatMap of advance over lifted list equals lift of concatMap of advance (right)
-- Used by: concatMap-buildU-pdUMany-aux-+
-- Proof idea: Induction on pdis-r, using advance-lift-pdi*-right-eq and map-++-distrib
  concatMap-advance-lift-pdi*-right-eq : ∀ {l r loc} {pref : List Char} (c : Char)
    (pdis-r : List (PDInstance* r pref))
    → List.concatMap (advance-pdi*-with-c {l + r ` loc} {pref} {c}) (List.map lift-pdi*-right pdis-r)
      ≡ List.map lift-pdi*-right (List.concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis-r)
  concatMap-advance-lift-pdi*-right-eq c [] = refl
  concatMap-advance-lift-pdi*-right-eq {l} {r} {loc} {pref} c (pdi* ∷ pdis-r) =
    trans
      (cong₂ _++_ (advance-lift-pdi*-right-eq c pdi*) (concatMap-advance-lift-pdi*-right-eq c pdis-r))
      (sym (map-++-distrib lift-pdi*-right
             (advance-pdi*-with-c {r} {pref} {c} pdi*)
             (List.concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis-r)))

  -- Purpose: compose with identity on pdinstance-left equals lift of compose
-- Used by: map-compose-id-left
-- Proof idea: Reflexivity after pattern matching
  compose-id-pdinstance-left-eq : ∀ {l r : RE} {loc : ℕ} {c : Char} (pdi : PDInstance l c)
    → compose-pdi-with {l + r ` loc} {_} {[]} {c} (λ u → u) (λ u → refl) (pdinstance-left {l} {r} {loc} {c} pdi)
      ≡ lift-pdi*-left {l} {r} {loc} {_}
          (compose-pdi-with {l} {_} {[]} {c} (λ u → u) (λ u → refl) pdi)
  compose-id-pdinstance-left-eq (pdinstance f s-ev) = refl

  -- Purpose: compose with identity on pdinstance-right equals lift of compose
-- Used by: map-compose-id-right
-- Proof idea: Reflexivity after pattern matching
  compose-id-pdinstance-right-eq : ∀ {l r : RE} {loc : ℕ} {c : Char} (pdi : PDInstance r c)
    → compose-pdi-with {l + r ` loc} {_} {[]} {c} (λ u → u) (λ u → refl) (pdinstance-right {l} {r} {loc} {c} pdi)
      ≡ lift-pdi*-right {l} {r} {loc} {_}
          (compose-pdi-with {r} {_} {[]} {c} (λ u → u) (λ u → refl) pdi)
  compose-id-pdinstance-right-eq (pdinstance f s-ev) = refl

  -- Purpose: map of compose on left-mapped pdU equals lift of map of compose
-- Used by: concatMap-buildU-pdUMany-+
-- Proof idea: map-∘-eq, map-cong with compose-id-pdinstance-left-eq
  map-compose-id-left : ∀ {l r : RE} {loc : ℕ} {c : Char}
    → List.map (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl))
        (List.map (pdinstance-left {l} {r} {loc} {c}) pdU[ l , c ])
      ≡ List.map (lift-pdi*-left {l} {r} {loc} {_})
          (List.map (compose-pdi-with {l} {l} {[]} {c} (λ u → u) (λ u → refl)) pdU[ l , c ])
  map-compose-id-left {l} {r} {loc} {c} =
    begin
      List.map (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl))
        (List.map (pdinstance-left {l} {r} {loc} {c}) pdU[ l , c ])
    ≡⟨ sym (map-∘-eq (pdinstance-left {l} {r} {loc} {c}) (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl)) pdU[ l , c ]) ⟩
      List.map (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl) ∘ pdinstance-left {l} {r} {loc} {c}) pdU[ l , c ]
    ≡⟨ map-cong {xs = pdU[ l , c ]} (λ pdi → compose-id-pdinstance-left-eq {l} {r} {loc} {c} pdi) ⟩
      List.map (lift-pdi*-left {l} {r} {loc} {_} ∘ compose-pdi-with {l} {l} {[]} {c} (λ u → u) (λ u → refl)) pdU[ l , c ]
    ≡⟨ map-∘-eq (compose-pdi-with {l} {l} {[]} {c} (λ u → u) (λ u → refl)) (lift-pdi*-left {l} {r} {loc} {_}) pdU[ l , c ] ⟩
      List.map (lift-pdi*-left {l} {r} {loc} {_})
        (List.map (compose-pdi-with {l} {l} {[]} {c} (λ u → u) (λ u → refl)) pdU[ l , c ])
    ∎

  -- Purpose: map of compose on right-mapped pdU equals lift of map of compose
-- Used by: concatMap-buildU-pdUMany-+
-- Proof idea: map-∘-eq, map-cong with compose-id-pdinstance-right-eq
  map-compose-id-right : ∀ {l r : RE} {loc : ℕ} {c : Char}
    → List.map (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl))
        (List.map (pdinstance-right {l} {r} {loc} {c}) pdU[ r , c ])
      ≡ List.map (lift-pdi*-right {l} {r} {loc} {_})
          (List.map (compose-pdi-with {r} {r} {[]} {c} (λ u → u) (λ u → refl)) pdU[ r , c ])
  map-compose-id-right {l} {r} {loc} {c} =
    begin
      List.map (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl))
        (List.map (pdinstance-right {l} {r} {loc} {c}) pdU[ r , c ])
    ≡⟨ sym (map-∘-eq (pdinstance-right {l} {r} {loc} {c}) (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl)) pdU[ r , c ]) ⟩
      List.map (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl) ∘ pdinstance-right {l} {r} {loc} {c}) pdU[ r , c ]
    ≡⟨ map-cong {xs = pdU[ r , c ]} (λ pdi → compose-id-pdinstance-right-eq {l} {r} {loc} {c} pdi) ⟩
      List.map (lift-pdi*-right {l} {r} {loc} {_} ∘ compose-pdi-with {r} {r} {[]} {c} (λ u → u) (λ u → refl)) pdU[ r , c ]
    ≡⟨ map-∘-eq (compose-pdi-with {r} {r} {[]} {c} (λ u → u) (λ u → refl)) (lift-pdi*-right {l} {r} {loc} {_}) pdU[ r , c ] ⟩
      List.map (lift-pdi*-right {l} {r} {loc} {_})
        (List.map (compose-pdi-with {r} {r} {[]} {c} (λ u → u) (λ u → refl)) pdU[ r , c ])
    ∎

  -- Purpose: concatMap buildU over + pdis decomposes into LeftU and RightU parts
-- Used by: concatMap-buildU-pdUMany-+
-- Proof idea: Induction on cs, using buildU-lift-pdi*-left/right and concatMap-map-commute
  concatMap-buildU-pdUMany-aux-+ : ∀ (l r : RE) (loc : ℕ) (pref : List Char) (cs : List Char)
    (pdis-l : List (PDInstance* l pref)) (pdis-r : List (PDInstance* r pref))
    (pdis+ : List (PDInstance* (l + r ` loc) pref))
    → pdis+ ≡ List.map lift-pdi*-left pdis-l ++ List.map lift-pdi*-right pdis-r
    → List.concatMap buildU (pdUMany-aux {l + r ` loc} {pref} cs pdis+)
      ≡ List.map LeftU (List.concatMap buildU (pdUMany-aux {l} {pref} cs pdis-l))
        ++ List.map RightU (List.concatMap buildU (pdUMany-aux {r} {pref} cs pdis-r))
  concatMap-buildU-pdUMany-aux-+ l r loc pref [] pdis-l pdis-r pdis+ eq
    rewrite ++-identityʳ pref =
    begin
      List.concatMap buildU pdis+
    ≡⟨ cong (List.concatMap buildU) eq ⟩
      List.concatMap buildU (List.map lift-pdi*-left pdis-l ++ List.map lift-pdi*-right pdis-r)
    ≡⟨ concatMap-++-distrib buildU (List.map lift-pdi*-left pdis-l) (List.map lift-pdi*-right pdis-r) ⟩
      List.concatMap buildU (List.map lift-pdi*-left pdis-l) ++ List.concatMap buildU (List.map lift-pdi*-right pdis-r)
    ≡⟨ cong₂ _++_
         (trans (sym (concatMap-∘-eq lift-pdi*-left buildU pdis-l))
                (trans (concatMap-cong {xs = pdis-l} (buildU-lift-pdi*-left))
                       (concatMap-map-commute LeftU buildU pdis-l)))
         (trans (sym (concatMap-∘-eq lift-pdi*-right buildU pdis-r))
                (trans (concatMap-cong {xs = pdis-r} (buildU-lift-pdi*-right))
                       (concatMap-map-commute RightU buildU pdis-r))) ⟩
      List.map LeftU (List.concatMap buildU pdis-l) ++ List.map RightU (List.concatMap buildU pdis-r)
    ∎
  concatMap-buildU-pdUMany-aux-+ l r loc pref (c ∷ cs) pdis-l pdis-r pdis+ eq =
    let adv+ = List.concatMap (advance-pdi*-with-c {l + r ` loc} {pref} {c}) pdis+
        adv-l = List.concatMap (advance-pdi*-with-c {l} {pref} {c}) pdis-l
        adv-r = List.concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis-r
        adv-eq : adv+ ≡ List.map lift-pdi*-left adv-l ++ List.map lift-pdi*-right adv-r
        adv-eq =
          begin
            adv+
          ≡⟨ cong (List.concatMap (advance-pdi*-with-c {l + r ` loc} {pref} {c})) eq ⟩
            List.concatMap (advance-pdi*-with-c {l + r ` loc} {pref} {c})
              (List.map lift-pdi*-left pdis-l ++ List.map lift-pdi*-right pdis-r)
          ≡⟨ concatMap-++-distrib (advance-pdi*-with-c {l + r ` loc} {pref} {c})
               (List.map lift-pdi*-left pdis-l) (List.map lift-pdi*-right pdis-r) ⟩
            List.concatMap (advance-pdi*-with-c {l + r ` loc} {pref} {c}) (List.map lift-pdi*-left pdis-l)
            ++ List.concatMap (advance-pdi*-with-c {l + r ` loc} {pref} {c}) (List.map lift-pdi*-right pdis-r)
          ≡⟨ cong₂ _++_ (concatMap-advance-lift-pdi*-left-eq c pdis-l)
                        (concatMap-advance-lift-pdi*-right-eq c pdis-r) ⟩
            List.map lift-pdi*-left adv-l ++ List.map lift-pdi*-right adv-r
          ∎
    in concatMap-buildU-pdUMany-aux-+ l r loc (pref ∷ʳ c) cs adv-l adv-r adv+ adv-eq

  -- Purpose: pdUMany for + regex decomposes into LeftU and RightU parts
-- Used by: (internal lemma for parseAll + case)
-- Proof idea: Build root pdis, advance, reduce, apply concatMap-buildU-pdUMany-aux-+
  concatMap-buildU-pdUMany-+ : ∀ (l r : RE) (loc : ℕ) (c : Char) (w : List Char)
    → List.concatMap buildU pdUMany[ l + r ` loc , c ∷ w ]
    ≡ List.map LeftU (List.concatMap buildU pdUMany[ l , c ∷ w ])
      ++ List.map RightU (List.concatMap buildU pdUMany[ r , c ∷ w ])
  ++[]-distr : ∀ {A : Set} (xs ys : List A) → (xs ++ ys) ++ [] ≡ (xs ++ []) ++ (ys ++ [])
  ++[]-distr xs ys =
    begin
      (xs ++ ys) ++ []
    ≡⟨ ++-identityʳ (xs ++ ys) ⟩
      xs ++ ys
    ≡⟨ sym (cong (xs ++_) (++-identityʳ ys)) ⟩
      xs ++ (ys ++ [])
    ≡⟨ sym (++-assoc xs [] (ys ++ [])) ⟩
      (xs ++ []) ++ (ys ++ [])
    ∎

  map-++[] : ∀ {A B : Set} (f : A → B) (xs : List A) → List.map f (xs ++ []) ≡ List.map f xs ++ []
  map-++[] f xs = map-++-distrib f xs []

  concatMap-buildU-pdUMany-+ l r loc c w =
    let root-l = pdinstance* {l} {l} {[]} (λ u → u) (λ u → refl)
        root-r = pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl)
        root+  = pdinstance* {l + r ` loc} {l + r ` loc} {[]} (λ u → u) (λ u → refl)
        adv-l = List.concatMap (advance-pdi*-with-c {l} {[]} {c}) [ root-l ]
        adv-r = List.concatMap (advance-pdi*-with-c {r} {[]} {c}) [ root-r ]
        adv+  = List.concatMap (advance-pdi*-with-c {l + r ` loc} {[]} {c}) [ root+ ]
        adv-l-reduced = List.map (compose-pdi-with {l} {l} {[]} {c} (λ u → u) (λ u → refl)) pdU[ l , c ]
        adv-r-reduced = List.map (compose-pdi-with {r} {r} {[]} {c} (λ u → u) (λ u → refl)) pdU[ r , c ]
        adv+-reduced = List.map (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl))
                       (List.map (pdinstance-left {l} {r} {loc} {c}) pdU[ l , c ] ++
                        List.map (pdinstance-right {l} {r} {loc} {c}) pdU[ r , c ])
        adv-reduced-eq : adv+-reduced ≡ List.map lift-pdi*-left adv-l-reduced ++ List.map lift-pdi*-right adv-r-reduced
        adv-reduced-eq =
          begin
            adv+-reduced
          ≡⟨ map-++-distrib (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl))
               (List.map (pdinstance-left {l} {r} {loc} {c}) pdU[ l , c ])
               (List.map (pdinstance-right {l} {r} {loc} {c}) pdU[ r , c ]) ⟩
            List.map (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl)) (List.map (pdinstance-left {l} {r} {loc} {c}) pdU[ l , c ])
            ++ List.map (compose-pdi-with {l + r ` loc} {l + r ` loc} {[]} {c} (λ u → u) (λ u → refl)) (List.map (pdinstance-right {l} {r} {loc} {c}) pdU[ r , c ])
          ≡⟨ cong₂ _++_ map-compose-id-left map-compose-id-right ⟩
            List.map lift-pdi*-left adv-l-reduced ++ List.map lift-pdi*-right adv-r-reduced
          ∎
        adv-eq : adv+ ≡ List.map lift-pdi*-left adv-l ++ List.map lift-pdi*-right adv-r
        adv-eq =
          begin
            adv+
          ≡⟨ refl ⟩
            adv+-reduced ++ []
          ≡⟨ cong (_++ []) adv-reduced-eq ⟩
            (List.map lift-pdi*-left adv-l-reduced ++ List.map lift-pdi*-right adv-r-reduced) ++ []
          ≡⟨ ++[]-distr (List.map lift-pdi*-left adv-l-reduced) (List.map lift-pdi*-right adv-r-reduced) ⟩
            (List.map lift-pdi*-left adv-l-reduced ++ []) ++ (List.map lift-pdi*-right adv-r-reduced ++ [])
          ≡⟨ sym (cong₂ _++_ (map-++[] lift-pdi*-left adv-l-reduced) (map-++[] lift-pdi*-right adv-r-reduced)) ⟩
            List.map lift-pdi*-left adv-l ++ List.map lift-pdi*-right adv-r
          ∎
    in concatMap-buildU-pdUMany-aux-+ l r loc ([] ∷ʳ c) w adv-l adv-r adv+ adv-eq

  head-map-LeftU-++-map-RightU : ∀ (l r : RE) (loc : ℕ) (left : List (U l)) (right : List (U r)) (u : U (l + r ` loc))
    → head (List.map LeftU left ++ List.map RightU right) ≡ just u
    → Σ (U l) (λ uₗ → Σ (¬ left ≡ []) (λ _ → (u ≡ LeftU uₗ) × (head left ≡ just uₗ)))
       ⊎ Σ (U r) (λ uᵣ → Σ (left ≡ []) (λ _ → Σ (¬ right ≡ []) (λ _ → (u ≡ RightU uᵣ) × (head right ≡ just uᵣ))))
  head-map-LeftU-++-map-RightU l r loc [] [] u eq = ⊥-elim (¬nothing≡just eq)
  head-map-LeftU-++-map-RightU l r loc [] (y ∷ ys) u eq =
    inj₂ (y , refl , (λ ()) , sym (just-injective eq) , refl)
  head-map-LeftU-++-map-RightU l r loc (x ∷ xs) right u eq =
    inj₁ (x , (λ ()) , sym (just-injective eq) , refl)

  head-just-∈ : ∀ {A : Set} {xs : List A} {x : A} → head xs ≡ just x → x ∈ xs
  head-just-∈ {xs = []} ()
  head-just-∈ {xs = x ∷ xs} refl = here refl

  ∈[]-impossible : ∀ {A : Set} {x : A} → x ∈ [] → ⊥
  ∈[]-impossible ()

  decompose-+ : ∀ {l r : RE} {loc : ℕ} → U (l + r ` loc) → U l ⊎ U r
  decompose-+ (LeftU u) = inj₁ u
  decompose-+ (RightU v) = inj₂ v

  +-elim-U : ∀ {l r : RE} {loc : ℕ} {P : U (l + r ` loc) → Set}
    (f : (u : U l) → P (LeftU u))
    (g : (v : U r) → P (RightU v))
    (v : U (l + r ` loc))
    → P v
  +-elim-U f g (LeftU u) = f u
  +-elim-U f g (RightU v) = g v

  flat-LeftU-proj : ∀ {l r : RE} {loc : ℕ} (u : U l)
    → proj₁ (flat (LeftU {l} {r} {loc} u)) ≡ proj₁ (flat u)
  flat-LeftU-proj u = refl

  flat-RightU-proj : ∀ {l r : RE} {loc : ℕ} (u : U r)
    → proj₁ (flat (RightU {l} {r} {loc} u)) ≡ proj₁ (flat u)
  flat-RightU-proj u = refl

  flat-LeftU-word : ∀ {l r : RE} {loc : ℕ} (v : U l) {w : List Char}
    → proj₁ (flat (LeftU {l} {r} {loc} v)) ≡ w
    → proj₁ (flat v) ≡ w
  flat-LeftU-word v refl = refl

  flat-RightU-word : ∀ {l r : RE} {loc : ℕ} (v : U r) {w : List Char}
    → proj₁ (flat (RightU {l} {r} {loc} v)) ≡ w
    → proj₁ (flat v) ≡ w
  flat-RightU-word v refl = refl

  length>0-nonempty : ∀ {r : RE} (u : U r) {w : List Char}
    → proj₁ (flat u) ≡ w
    → w ≢ []
    → length (proj₁ (flat u)) Nat.> 0
  length>0-nonempty u flat-u≡w w≢[] =
    ¬≡[]→length>0 (λ eq → w≢[] (trans (sym flat-u≡w) eq))

  leftU>rightU : ∀ {l r : RE} {loc : ℕ} {u : U l} {v : U r}
    → length (proj₁ (flat u)) Nat.> 0
    → length (proj₁ (flat v)) Nat.> 0
    → l + r ` loc ⊢ LeftU u > RightU v
  leftU>rightU len>u len>v = bne len>u len>v choice-lr


  -- Projection from ≥-Max-PDInstance
  ≥-Max-PDInstance-u : ∀ {r c w} {pdi : PDInstance r c} → ≥-Max-PDInstance {r} {c} w pdi → U (pdi-src pdi)
  ≥-Max-PDInstance-u (≥-max-pdi u _ _ _) = u

  -- Extract ≥-Max (c ∷ w) from ≥-Max-PDInstance
  ≥-Max-PDInstance→≥-Max-c∷w : ∀ {r c w pdi} → (max-pdi : ≥-Max-PDInstance {r} {c} w pdi)
    → (u : U r) → u ≡ pdi-inj pdi (≥-Max-PDInstance-u max-pdi) → ≥-Max (c ∷ w) u
  ≥-Max-PDInstance→≥-Max-c∷w {w = w} {pdi = pdi} (≥-max-pdi u .w _ μ-c∷w) .(pdi-inj pdi u) refl = μ-c∷w

  -- ≥-Max uniqueness
  ≥-Max-unique : ∀ {p : RE} {w : List Char} (u₁ u₂ : U p)
    → ≥-Max w u₁ → ≥-Max w u₂ → u₁ ≡ u₂
  ≥-Max-unique {p} {w} u₁ u₂ (≥-max _ .u₁ flat-u₁≡w μ₁) (≥-max _ .u₂ flat-u₂≡w μ₂)
    with μ₁ u₂ flat-u₂≡w
  ... | inj₂ u₁≡u₂ = u₁≡u₂
  ... | inj₁ u₁>u₂ with μ₂ u₁ flat-u₁≡w
  ... | inj₂ u₂≡u₁ = ⊥-elim (>→¬≡ u₁>u₂ (sym u₂≡u₁))
  ... | inj₁ u₂>u₁ = ⊥-elim (>-asym u₁>u₂ u₂>u₁)

  -- map f xs is nonempty when xs is nonempty
  map-nonempty : ∀ {A B : Set} (f : A → B) {xs : List A} → xs ≢ [] → List.map f xs ≢ []
  map-nonempty f {x ∷ xs} _ = λ ()
  map-nonempty f {[]} neq = ⊥-elim (neq refl)

  -- head of (xs ++ ys) ≡ head xs when xs nonempty
  head-nonempty-++ : ∀ {A : Set} {xs ys : List A} → xs ≢ [] → head (xs ++ ys) ≡ head xs
  head-nonempty-++ {A} {x ∷ xs} {ys} _ = refl
  head-nonempty-++ {A} {[]} {ys} neq = ⊥-elim (neq refl)

  -- parseAll empty when w ∉⟦ p ⟧
  parseAll-no→[] : ∀ {p : RE} {w : List Char}
    → ¬ (w ∈⟦ p ⟧)
    → parseAll[ p , w ] ≡ []
  parseAll-no→[] {p = p} {w = w} ¬w∈p
    with ∈?-parseAll w p
  parseAll-no→[] {p = p} {w = w} ¬w∈p | yes w∈p = ⊥-elim (¬w∈p w∈p)
  parseAll-no→[] {p = p} {w = w} ¬w∈p | no _
    with parseAll[ p , w ] in eq-pa
  ... | [] = refl
  ... | u ∷ us = ⊥-elim (¬w∈p (subst (λ x → x ∈⟦ p ⟧) (parseAll-sound u (subst (λ x → u ∈ x) (sym eq-pa) (here refl))) (proj₂ (flat u))))

  -- Extract the source head behind an injected head
  head-map-just : ∀ {A B : Set} (f : A → B) {xs : List A} {y : B}
    → head (List.map f xs) ≡ just y
    → ∃[ x ] (head xs ≡ just x × y ≡ f x)
  head-map-just f {[]} eq = ⊥-elim (nothing≢just eq)
  head-map-just f {x ∷ xs} {y} eq =
    x , (refl , sym (just-injective eq))

  head-map-inj→head-src : ∀ {r c w} {pdi : PDInstance r c} {u : U r}
    → head (List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , w ])) ≡ just u
    → ∃[ u₀ ] (u ≡ pdi-inj pdi u₀ × head parseAll[ pdi-src pdi , w ] ≡ just u₀)
  head-map-inj→head-src {r} {c} {w} {pdi} {u} eq
    with head-map-just (pdi-inj pdi) {parseAll[ pdi-src pdi , w ]} {u} eq
  ... | (u₀ , head-pa≡just-u₀ , u≡inj-u₀) = u₀ , u≡inj-u₀ , head-pa≡just-u₀
  -- NOTE: previous proof via head-concatMap-h-aux relied on parseAll being >-sorted,
  -- which is NOT true in general (*>-Inc doesn't hold for arbitrary parse trees,
  -- only for maximal ones). This version only requires the head to be maximal,
  -- which follows from the induction hypothesis on the source RE.
  head-pdUparseAll→first-inhabit : ∀ {r : RE} {c : Char} {w : List Char}
    → (pdis : List (PDInstance r c)) (u : U r)
    → head (List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , w ])) pdis) ≡ just u
    → ∃[ pdi ] (first-inhabit r c w pdis ≡ just pdi
      × ∃[ u₀ ] (u ≡ pdi-inj pdi u₀ × head parseAll[ pdi-src pdi , w ] ≡ just u₀))
  head-pdUparseAll→first-inhabit [] _ ()
  head-pdUparseAll→first-inhabit {r} {c} {w} (pdi₀@(pdinstance {p} .{r} .{c} inj s-ev) ∷ pdis) u eq =
    let d = w ∈?⟦ p ⟧ in
    case d of λ where
      (yes w∈p) →
        let pa≢[] : parseAll[ p , w ] ≢ []
            pa≢[] = parseAll-nonempty {p} {w} w∈p
            map-pa≢[] : List.map (pdi-inj pdi₀) (parseAll[ p , w ]) ≢ []
            map-pa≢[] = map-nonempty (pdi-inj pdi₀) pa≢[]
            head-concat≡head-map :
              head (List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , w ])) (pdi₀ ∷ pdis))
              ≡ head (List.map (pdi-inj pdi₀) (parseAll[ p , w ]))
            head-concat≡head-map = head-nonempty-++ map-pa≢[]
            head-map≡just-u : head (List.map (pdi-inj pdi₀) (parseAll[ p , w ])) ≡ just u
            head-map≡just-u = trans (sym head-concat≡head-map) eq
            (u₀ , u≡inj-u₀ , head-pa≡just-u₀) = head-map-inj→head-src {r} {c} {w} {pdi = pdi₀} head-map≡just-u
            fi≡just = first-inhabit-yes-eq-full pdi₀ pdis w∈p
        in pdi₀ , fi≡just , u₀ , u≡inj-u₀ , head-pa≡just-u₀
      (no ¬w∈p) →
        let pa≡[] : parseAll[ p , w ] ≡ []
            pa≡[] = parseAll-no→[] ¬w∈p
            map-pa≡[] : List.map (pdi-inj pdi₀) (parseAll[ p , w ]) ≡ []
            map-pa≡[] = cong (List.map (pdi-inj pdi₀)) pa≡[]
            concat≡tail :
              List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , w ])) (pdi₀ ∷ pdis)
              ≡ List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , w ])) pdis
            concat≡tail =
              trans (cong (_++ List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , w ])) pdis) map-pa≡[])
                    (++-identityˡ (List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , w ])) pdis))
            eq' : head (List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , w ])) pdis) ≡ just u
            eq' = subst (λ zs → head zs ≡ just u) concat≡tail eq
            (pdi , fi≡just , u₀ , u≡inj-u₀ , head-pa≡just-u₀) = head-pdUparseAll→first-inhabit pdis u eq'
            fi≡just-ext : first-inhabit r c w (pdi₀ ∷ pdis) ≡ just pdi
            fi≡just-ext = trans (first-inhabit-no-eq pdi₀ pdis ¬w∈p) fi≡just
        in pdi , fi≡just-ext , u₀ , u≡inj-u₀ , head-pa≡just-u₀

  -- maximum of parseAll is ≥-Max (does NOT require parseAll to be sorted)
  max-parseAll-≥-Max : ∀ {p : RE} {w : List Char} (w∈p : w ∈⟦ p ⟧)
    → ≥-Max w (maximum (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈p))
  max-parseAll-≥-Max {p} {w} w∈p =
    ≥-max w max-u flat-max≡w μ
    where
      max-u : U p
      max-u = maximum (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈p)

      flat-max≡w : proj₁ (flat max-u) ≡ w
      flat-max≡w = maximum-flat (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈p) (parseAll-all-sound {p} {w})

      μ : ∀ (v : U p) → proj₁ (flat v) ≡ w → p ⊢ max-u ≥ v
      μ v flat-v≡w = maximum-≥-all (parseAll[ p , w ]) (parseAll-nonempty {p} {w} w∈p) v (parseAll-complete {p} {w} v flat-v≡w)

  ≥-Max-PDInstance→≥-Max-w : ∀ {r c w pdi} → (max-pdi : ≥-Max-PDInstance {r} {c} w pdi) → ≥-Max w (≥-Max-PDInstance-u max-pdi)
  ≥-Max-PDInstance→≥-Max-w {w = w} (≥-max-pdi u .w u-max _) = u-max

  parseAll-[]-yes : ∀ {p : RE} (ε∈p : ε∈ p) → parseAll[ p , [] ] ≡ mkAllEmptyU ε∈p
  parseAll-[]-yes {p} ε∈p =
    trans (parseAll-[]≡buildU-root {p}) (buildU-root-≡ (yes ε∈p))
    where
      root : PDInstance* p []
      root = pdinstance* {p} {p} {[]} (λ u → u) (λ u → refl)

      buildU-root-out : Dec (ε∈ p) → List (U p)
      buildU-root-out (yes prf) = mkAllEmptyU prf
      buildU-root-out (no _) = []

      buildU-root-≡ : (d : Dec (ε∈ p)) → buildU root ≡ buildU-root-out d
      buildU-root-≡ d
        with ε∈? p
      ... | yes prf' with d
      ... |   yes prf =
        trans
          (cong (List.map (λ u → u)) (mkAllEmptyU-irrelevant prf' prf))
          (map-id (mkAllEmptyU prf))
      ... |   no ¬prf = ⊥-elim (¬prf prf')
      buildU-root-≡ d | no ¬prf' with d
      ... |   yes prf = ⊥-elim (¬prf' prf)
      ... |   no ¬prf = refl

  -- The head of parseAll is ≥-Max.  Proof by induction on the length of the word:
  -- for [] we use sortedness of mkAllEmptyU; for c ∷ cs we use parseAll-pdU-decomp,
  -- the IH on the suffix cs, and first-pdU-accept-w-isMax.
  parseAll-head-isMax : ∀ (p : RE) (w : List Char) (w∈p : w ∈⟦ p ⟧) (u : U p)
    → head parseAll[ p , w ] ≡ just u
    → ≥-Max w u
  parseAll-head-isMax p [] w∈p u eq =
    let ε∈p : ε∈ p
        ε∈p = []∈⟦r⟧→ε∈r w∈p
        pa≡mk : parseAll[ p , [] ] ≡ mkAllEmptyU ε∈p
        pa≡mk = parseAll-[]-yes ε∈p
        (e , es , mk≡e∷es) = head-tail (mkAllEmptyU≢[] ε∈p)
        eq' : just e ≡ just u
        eq' = subst (λ xs → head xs ≡ just u) (trans pa≡mk mk≡e∷es) eq
        e≡u : e ≡ u
        e≡u = just-injective eq'
        sound : All (Flat-[] p) (e ∷ es)
        sound = subst (All (Flat-[] p)) mk≡e∷es (mkAllEmptyU-sound ε∈p)
        e-flat : proj₁ (flat e) ≡ []
        e-flat = flat-[]-proj (All.head sound)
        sorted : >-sorted {p} (e ∷ es)
        sorted = subst (>-sorted {p}) mk≡e∷es (mkAllEmptyU-sorted ε∈p)
        max-e : ≥-Max [] e
        max-e = mkAllEmptyU-first-≥-Max ε∈p e-flat mk≡e∷es sorted
    in subst (λ x → ≥-Max [] x) e≡u max-e
  parseAll-head-isMax p (c ∷ cs) w∈p u eq =
    let decomp = parseAll-pdU-decomp {p} c cs
        eq' : head (List.concatMap (λ pdi → List.map (pdi-inj pdi) (parseAll[ pdi-src pdi , cs ])) (pdU[ p , c ])) ≡ just u
        eq' = subst (λ xs → head xs ≡ just u) decomp eq
        (pdi , fi-eq , u₀ , u≡inj-u₀ , head-src≡) = head-pdUparseAll→first-inhabit (pdU[ p , c ]) u eq'
        u₀∈pa : u₀ ∈ parseAll[ pdi-src pdi , cs ]
        u₀∈pa = head-just-∈ head-src≡
        flat-u₀≡cs : proj₁ (flat u₀) ≡ cs
        flat-u₀≡cs = lookup (parseAll-all-sound {pdi-src pdi} {cs}) u₀∈pa
        cs∈src : cs ∈⟦ pdi-src pdi ⟧
        cs∈src = subst (λ x → x ∈⟦ pdi-src pdi ⟧) flat-u₀≡cs (proj₂ (flat u₀))
        ih : ≥-Max cs u₀
        ih = parseAll-head-isMax (pdi-src pdi) cs cs∈src u₀ head-src≡
        max-pdi = first-pdU-accept-w-isMax {p} {c} cs w∈p pdi fi-eq
        max-u = ≥-Max-PDInstance-u max-pdi
        max-u-max = ≥-Max-PDInstance→≥-Max-w max-pdi
        u₀≡max-u : u₀ ≡ max-u
        u₀≡max-u = ≥-Max-unique u₀ max-u ih max-u-max
    in ≥-Max-PDInstance→≥-Max-c∷w max-pdi u (trans u≡inj-u₀ (cong (pdi-inj pdi) u₀≡max-u))


  first-concatMap-buildU-pdUMany-isMax : ∀ ( r : RE )
    → ( w : List Char )
    → ( w ∈⟦ r ⟧  )
    → ( u : U r )
    → head (List.concatMap buildU pdUMany[ r , w ]) ≡ just u
    →  ≥-Max w u
  first-concatMap-buildU-pdUMany-isMax r w w∈r u eq = parseAll-head-isMax r w w∈r u eq
```



```agda
-- first-concatMap-buildU-pdUMany-isMax is defined in the mutual block above   



-- Purpose: The head of parseAll is the ≥-Max parse tree
-- Used by: (top-level theorem, entry point for max-word proof)
-- Proof idea: Alias of first-concatMap-buildU-pdUMany-isMax
first-parseAll-isMax  : ∀ ( r : RE )
  → ( w : List Char )
  → w ∈⟦ r ⟧
  → ( u : U r )
  → head parseAll[ r , w ] ≡ just u
  → ≥-Max w u 
first-parseAll-isMax = first-concatMap-buildU-pdUMany-isMax
```
