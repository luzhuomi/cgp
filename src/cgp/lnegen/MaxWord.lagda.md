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
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )


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
{-
data ≥-Max-Preserve : ∀ { r : RE } { c : Char } → PDInstance r c → Set where
  ≥-max-pres : ∀ { p r : RE } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ( w : List Char )
      → ≥-Max w u
      → ≥-Max (c ∷ w) (inj u) )
    → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)



data ≥-Max-Preserve-Bd : ∀ { r : RE } { c : Char } → PDInstance r c → Set where
  ≥-max-pres-bd : ∀ { p r : RE } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ( w : List Char )
      → ≥-Max w u
      → ≥-Max (c ∷ w) (inj u) ) -- → direction 
    → ( ( u : U p ) 
      → ( w : List Char )
      → ≥-Max (c ∷ w) (inj u)
      → ≥-Max w u ) -- ← direction 
    → ≥-Max-Preserve-Bd {r} {c} (pdinstance inj sound-ev)
-} 



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

{-
≥-max-pres-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-left pdi)
≥-max-pres-left {l} {r} {loc} {c} (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres u→w→max-u→max-inju) =
  ≥-max-pres (λ u w max-u → ≥-max-pres-left-helper p l r loc c inj u w (u→w→max-u→max-inju u w max-u))


≥-max-pres-left-bd : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve-Bd {l} {c} pdi
  → ≥-Max-Preserve-Bd {l + r ` loc} {c} (pdinstance-left pdi)
≥-max-pres-left-bd {l} {r} {loc} {c} (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres-bd u→w→max-u→max-inju u→w→max-inju→max-u) = ≥-max-pres-bd prf₁ prf₂
    where
      prf₁ : (u : U p) (w : List Char)
           → ≥-Max w u
           → ≥-Max (c ∷ w) (LeftU (inj u)) 
      prf₁ u w max-u   = ≥-max-pres-left-helper p l r loc c inj u w (u→w→max-u→max-inju u w max-u)
      prf₂ : (u : U p) (w : List Char)
           → ≥-Max (c ∷ w) (LeftU {l} {r} {loc} (inj u))
           → ≥-Max w u
      prf₂ u w max-left-inju@(≥-max (.c ∷ .w) (LeftU inju) |left-inju|≡c∷w μ' ) = u→w→max-inju→max-u u w (≥-max-pres-left-helper-inv p l r loc c inj u w max-left-inju ) 
        where
          max-inj-u : ≥-Max (c ∷ w) (inj u)
          max-inj-u =  ≥-max (c ∷ w) (inj u) |left-inju|≡c∷w prf₃
            where
              prf₃ : (v : U l) -- TODO: prf₃ is identical to prf of ≥-max-pres-left-helper-inv, can we simplify these two proofs.
                → proj₁ (flat v) ≡ c ∷ w
                → l ⊢ inj u ≥ v
              prf₃ v |v|≡c∷w with μ' (LeftU {l} {r} {loc} v) |v|≡c∷w
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
              
          max-left-inj-u : ≥-Max (c ∷ w) (LeftU {l} {r} {loc} (inj u))
          max-left-inj-u = ≥-max-pres-left-helper p l r loc c inj u w max-inj-u 
-}          




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

{-
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

≥-max-pres-right-direct : ∀ { l r : RE } { loc : ℕ } { c : Char }
  { pdi : PDInstance r c }
  → ≥-Max-Preserve {r} {c} pdi
  → (∀ (w : List Char) → ¬ ((c ∷ w) ∈⟦ l ⟧))
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-right pdi)
≥-max-pres-right-direct {l} {r} {loc} {c} {pdinstance inj s-ev} (≥-max-pres preserve) ¬c∷w∈l =
  ≥-max-pres (λ u w maxu → ≥-max-pres-right (≥-max-pres {sound-ev = s-ev} preserve) u w maxu (¬c∷w∈l w))
-} 
  



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

mkAllEmptyU-first-≥-Max : ∀ {l} {ε∈l : ε∈ l} {e₁ : U l} {es₁ : List (U l)}
  → proj₁ (flat {l} e₁) ≡ []
  → mkAllEmptyU ε∈l ≡ e₁ ∷ es₁
  → >-sorted (e₁ ∷ es₁)
  → ≥-Max {l} [] e₁
mkAllEmptyU-first-≥-Max {l} {ε∈l} {e₁} {es₁} flat-e₁≡[] mkAllEmptyU≡ sorted =
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



      
¬nothing≡just : ∀ {A : Set} {x : A} → ¬ nothing ≡ just x
¬nothing≡just ()

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

head-x∷xs≡just-x : ∀ { A : Set} {x : A } { xs : List A } → head ( x ∷ xs ) ≡ just x
head-x∷xs≡just-x {A} {x} {xs} = refl 

{-
-- can be imported from  Data.List.Relation.Unary.Any.Properties
¬Any[] : ∀ {A : Set} {P : A → Set} → ¬ Any P []
¬Any[] ()
-}

pdU≡[]→¬c∷w∈l : ∀ {l c} {w : List Char} → pdU[ l , c ] ≡ [] → ¬ ((c ∷ w) ∈⟦ l ⟧)
pdU≡[]→¬c∷w∈l {l} {c} {w} pdU≡[] c∷w∈l =
  let u = unflat c∷w∈l
      eq : proj₁ (flat {l} u) ≡ c ∷ w
      eq = cong proj₁ (flat∘unflat c∷w∈l)
      any-recons : Any (Recons {l} {c} u) pdU[ l , c ]
      any-recons = pdU-complete {l} {c} {w} u eq
  in ⊥-elim (¬Any[] (subst (λ x → Any (Recons {l} {c} u) x) pdU≡[] any-recons))

pdU[$c]≡[] : ∀ {c' c : Char} {loc : ℕ} → c ≢ c' → pdU[ $ c' ` loc , c ] ≡ []
pdU[$c]≡[] {c'} {c} ¬c≡c' with c' Char.≟ c
... | yes c'≡c = ⊥-elim (¬c≡c' (sym c'≡c))
... | no  _    = refl

pdU[$c]≡∷ : ∀ {c' : Char} {loc : ℕ} → pdU[ $ c' ` loc , c' ] ≡ [ pdinstance mkinjLetter mkinjLetterSound ]
pdU[$c]≡∷ {c'} {loc} with c' Char.≟ c'
... | yes refl = refl
... | no ¬c≡c = ⊥-elim (¬c≡c refl)

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
{-
head-pdU-+-right-eq : ∀ {l r : RE} {loc : ℕ} {c : Char} {pdi_r : PDInstance r c} {pdis_r : List (PDInstance r c)}
  → head (List.map pdinstance-left [] ++ List.map pdinstance-right (pdi_r ∷ pdis_r)) ≡ just (pdinstance-right pdi_r)
head-pdU-+-right-eq = refl
-}

-- head-pdU-+-right: If the left list is empty and right is non-empty, the head is the right-wrapped head.
head-pdU-+-right : ∀ {l r : RE} {loc : ℕ} {c : Char} {pdi_r : PDInstance r c} {pdis_r : List (PDInstance r c)} {pdi : PDInstance (l + r ` loc) c}
  → head (List.map pdinstance-left [] ++ List.map pdinstance-right (pdi_r ∷ pdis_r)) ≡ just pdi
  → pdi ≡ pdinstance-right pdi_r
head-pdU-+-right eq = just-inj (sym eq)

-- head-concatmap-empty: The head of concatMap of pdinstance-snd over empty pdis is nothing.
-- Needed for the l ● r case when pdU[r,c] is empty. really? not in used now. 
head-concatmap-empty : ∀ {l r : RE} {loc : ℕ} {c : Char}
  → (xs : List (∃[ e ] (Flat-[] l e)))
  → head (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x []) xs) ≡ nothing
head-concatmap-empty [] = refl
head-concatmap-empty (x ∷ xs) = head-concatmap-empty xs

-- compiled but not in used
{-
extract-mkAllEmptyU : ∀ {l} {ε∈l : ε∈ l}
  → ∃[ e₁ ] ∃[ es₁ ] ∃[ flat-e₁≡[] ] ∃[ flat-[]-es₁ ] ∃[ sorted ] (⊥ → ⊥)
extract-mkAllEmptyU {l} {ε∈l}
  with mkAllEmptyU {l} ε∈l in eq-mkAllEmptyU | mkAllEmptyU-sound {l} ε∈l | mkAllEmptyU-sorted {l} ε∈l
... | [] | [] | w = ⊥-elim (mkAllEmptyU≢[] ε∈l eq-mkAllEmptyU)
... | e₁ ∷ es₁ | flat-[] e₁ flat-e₁≡[] ∷ flat-[]-es₁ | sorted =
  e₁ , es₁ , flat-e₁≡[] , flat-[]-es₁ , sorted , λ ()
-}

-- compiled but not in used
{-
concatmap-pdinstance-snd-≡ : ∀ {l r : RE} {ε∈l : ε∈ l} {loc : ℕ} {c : Char}
  (pdis : List (PDInstance r c))
  → concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis
    ≡ concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x pdis)
      (zip-es-flat-[]-es {l} {ε∈l} (mkAllEmptyU {l} ε∈l) (mkAllEmptyU-sound {l} ε∈l))
concatmap-pdinstance-snd-≡ pdis = refl
-}

-- first-char-lemma: Extract c∷cs form from non-empty list with known first char.
-- compiled but not in used
{-
first-char-lemma : ∀ {c} (xs : List Char) → xs ≢ [] → (∀ {c₁ cs₁} → xs ≡ c₁ ∷ cs₁ → c₁ ≡ c) → ∃[ cs ] xs ≡ c ∷ cs
first-char-lemma [] ¬[] _ = ⊥-elim (¬[] refl)
first-char-lemma (c₁ ∷ cs₁) _ first-char = cs₁ , cong (λ x → x ∷ cs₁) (first-char refl)
-}

-- find-recons: Extract Recons proof from Any. -- not in use?
-- compiled but not in used
{-
find-recons : ∀ {A : Set} {P : A → Set} {x} {xs} → Any P xs → P x → P x
find-recons {P = P} {x} any px = px
-}

-- dom-lemma: If inj u₁ is the first reconstruction of the first pdi in pdU[l,c],
-- and v₁ has a c-word different from c∷flat u₁, then l ⊢ inj u₁ > v₁.
-- extract-Recons: Extract the pdi and membership proof from Any (Recons v₁) pdis.
-- compiled but not in used
{-
extract-Recons : ∀ {r c v₁} {pdis : List (PDInstance r c)}
  → Any (Recons {r} {c} v₁) pdis
  → ∃ λ pdi → pdi ∈ pdis × Recons v₁ pdi
extract-Recons (here recons-v₁) = _ , here refl , recons-v₁
extract-Recons (there v₁∈pdis) with extract-Recons v₁∈pdis
... | pdi , pdi∈ , recons-v₁ = pdi , there pdi∈ , recons-v₁
-} 


-- ------ >-wellfounded lemma ----------------------

-- extract-any turns an Any proof into the witnessing element, the proof it satisfies P,
-- and the membership evidence. Used to extract a reconstructing PDInstance* from
-- pdUMany-complete.
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
pick : ∀ {r : RE} → U r → U r → U r
pick v best
  with >-trichotomy best v
... | inj₁ best>v   = best
... | inj₂ (inj₁ v>best) = v
... | inj₂ (inj₂ best≡v) = best

-- pick preserves the flattened word: if both candidates flatten to w, so does the pick.
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
maximum : ∀ {r : RE} (us : List (U r)) → us ≢ [] → U r
maximum [] neq = ⊥-elim (neq refl)
maximum (u ∷ us) neq = foldr pick u us

-- parseAll-all-sound: every element of parseAll[ r , w ] flattens to w.
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

{-
head-parseAll-is-max : ∀ { r : RE } { w : List Char }
  → ( u : U r )
  → just u ≡ head parseAll[ r , w ]
  → ≥-Max w u
head-parseAll-is-max = {!!}   
-}


-- ∈?-parseAll: decide word membership via the derivative-based parser.
-- w ∈⟦ r ⟧ iff parseAll[ r , w ] is non-empty (parseAll-nonempty / parseAll-sound).
∈?-parseAll : ( w : List Char ) → ( r : RE ) → Dec ( w ∈⟦ r ⟧ )
∈?-parseAll w r with parseAll[ r , w ] in eq
... | [] = no (λ w∈r → parseAll-nonempty w∈r eq)
... | (u ∷ us) = yes (subst (λ x → x ∈⟦ r ⟧) (parseAll-sound u (subst (λ x → u ∈ x) (sym eq) (here refl))) (proj₂ (flat u)))

_∈?⟦_⟧ : ( w : List Char ) → ( r : RE ) → Dec ( w ∈⟦ r ⟧ )
_∈?⟦_⟧ =  ∈?-parseAll

{-
max-is-head-parseAll : ∀ { r : RE } { w : List Char }
  → ( u : U r )
  → ≥-Max w u
  → just u ≡ head parseAll[ r , w ] 
max-is-head-parseAll = {!!}
-}

data ≥-Max-Preserve-Local : ∀ { r : RE } { c : Char } → PDInstance r c → Set where
  ≥-max-pres-local : ∀ { p r : RE } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ≥-Max {p} (proj₁ (flat u)) u
      → ( v : U p ) 
      → p ⊢ u ≥ v
      → r ⊢ inj u ≥ inj v ) 
    → ≥-Max-Preserve-Local {r} {c} (pdinstance inj sound-ev)




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

≥-Max-Preserve-Local-concatmap-pdinstance-snd-sub :  ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( e-flat-[]-es  : List ( ∃[ e ] Flat-[] l e ) )
  → ( pdis : List (PDInstance r c ) )
  → All (Bijective {r} {c}) pdis  
  → All (≥-Max-Preserve-Local {r} {c}) pdis 
  -----------------------------------------------------------------------------------------------------
  → All (≥-Max-Preserve-Local { l ● r ` loc } {c}) (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) e-flat-[]-es)
≥-Max-Preserve-Local-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} [] _ _ _  = []  
≥-Max-Preserve-Local-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} ( e-flat-[]-e ∷ e-flat-[]-es ) pdis all-bijective-pdis all-max-pres-pdis =   all-concat  (≥-Max-Preserve-Local-concatmap-pdinstance-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  e-flat-[]-e pdis all-bijective-pdis all-max-pres-pdis ) (≥-Max-Preserve-Local-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} e-flat-[]-es pdis all-bijective-pdis all-max-pres-pdis )  
  


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

pdi-src : ∀ { r : RE } { c : Char } → PDInstance r c → RE
pdi-src (pdinstance {p} {r} {c} inj sound-ev) = p

pdi-inj : ∀ { r : RE } { c : Char } → ( g : PDInstance r c ) → U (pdi-src g) → U r
pdi-inj (pdinstance {p} {r} {c} inj sound-ev) = inj


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
first-inhabit-no-eq : ∀ { r : RE } { c : Char } { w : List Char }
  → ( pdi' : PDInstance r c ) ( pdis : List (PDInstance r c) )
  → ¬ ( w ∈⟦ pdi-src pdi' ⟧ )
  → first-inhabit r c w (pdi' ∷ pdis) ≡ first-inhabit r c w pdis
first-inhabit-no-eq {r} {c} {w} (pdinstance {p} .{r} .{c} inj sev) pdis ¬w∈src
  with w ∈?⟦ p ⟧
... | yes w∈src = ⊥-elim (¬w∈src w∈src)
... | no _ = refl


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


-- a chain of pdU injections (head link applied last)
data Chain : ( p₀ p : RE ) → Set where
  [] : ∀ { p : RE } → Chain p p
  cons : ∀ { p₀ p d : RE } { c : Char }
      → ( g : PDInstance d c )
      → ( prf : g ∈ pdU[ d , c ] )
      → ( rest : Chain p₀ (pdi-src g) )
      → Chain p₀ d

chain-inj : ∀ { p₀ p : RE } → Chain p₀ p → U p₀ → U p
chain-inj [] u = u
chain-inj (cons g prf rest) u = pdi-inj g (chain-inj rest u)


-- extract the ≥-Max-Preserve-Local evidence of a pdi from its membership in pdU[ r , c ]
∈→pres-local : ∀ { r : RE } { c : Char } ( g : PDInstance r c ) → g ∈ pdU[ r , c ] → ≥-Max-Preserve-Local g
∈→pres-local {r} {c} g g∈ = go pdU[ r , c ] (pdU-preseve-local {r} {c}) g∈
  where
    go : ( pdis : List (PDInstance r c) ) → All ≥-Max-Preserve-Local pdis → g ∈ pdis → ≥-Max-Preserve-Local g
    go [] [] ()
    go (pdi ∷ pdis) (pres ∷ all-pres) (here refl) = pres
    go (pdi ∷ pdis) (pres ∷ all-pres) (there g∈') = go pdis all-pres g∈'


-- chains into r preserve ≥, given a ≥-Max source tree.
--
-- Proof plan (chain-structure argument):
--   []           : trivial (u₀ ≥ v₀).
--   cons g prf [] : p₀ = pdi-src g, chain-inj [] u₀ = u₀ is maximal, so the
--                   ≥-Max-Preserve-Local of g (via ∈→pres-local) applies directly.
--   cons g prf (cons g' prf' rest'') : the inner pdi g' has a successor g, so
--                   g' is a fst-pdi or snd-pdi (letter/star/left/right pdi targets
--                   are $c / s* / unions — never chain sources).  Hence the pair
--                   x' = pdi-inj g' x'', y' = pdi-inj g' y'' has either
--                   nonempty-flat first components (g' = fst-pdi) or EQUAL first
--                   components (g' = snd-pdi, same all-empty e).  In both cases the
--                   lne/be sub-cases of g's preservation proof that would need
--                   maximality of x' cannot arise, and the seq₁ recursion descends
--                   on the tree structure.
-- The cons-of-cons case needs the chain-structure argument described below.
-- The easy cases are defined here; only the hard case is postulated.
postulate
  chain-inj-pres-≥-cons-cons :
    ∀ { p₀ d : RE } { c c' : Char }
    → ( g : PDInstance d c ) ( prf : g ∈ pdU[ d , c ] )
    → ( g' : PDInstance (pdi-src g) c' ) ( prf' : g' ∈ pdU[ pdi-src g , c' ] )
    → ( rest'' : Chain p₀ (pdi-src g') )
    → ( u₀ : U p₀ ) → ≥-Max {p₀} (proj₁ (flat u₀)) u₀
    → ( v₀ : U p₀ ) → p₀ ⊢ u₀ ≥ v₀
    → d ⊢ pdi-inj g (pdi-inj g' (chain-inj rest'' u₀))
            ≥ pdi-inj g (pdi-inj g' (chain-inj rest'' v₀))

chain-inj-pres-≥ : ∀ { r p₀ : RE } ( chain : Chain p₀ r ) ( u₀ : U p₀ )
  → ≥-Max {p₀} (proj₁ (flat u₀)) u₀
  → ( v₀ : U p₀ )
  → p₀ ⊢ u₀ ≥ v₀
  → r ⊢ chain-inj chain u₀ ≥ chain-inj chain v₀
chain-inj-pres-≥ [] _ _ _ u₀≥v₀ = u₀≥v₀
chain-inj-pres-≥ (cons g prf []) u₀ max-u₀ v₀ u₀≥v₀
  with ∈→pres-local g prf
... | ≥-max-pres-local ev = ev u₀ max-u₀ v₀ u₀≥v₀
chain-inj-pres-≥ (cons g prf (cons g' prf' rest'')) u₀ max-u₀ v₀ u₀≥v₀ =
  chain-inj-pres-≥-cons-cons g prf g' prf' rest'' u₀ max-u₀ v₀ u₀≥v₀

-- NOTE (chain-structure proof plan below is incomplete):
--
-- The plan assumes chain intermediates (pdi-src values) are only ε or left-nested
-- ●-over-ε, so the inner pdi g' is always fst/snd.  However, pdi-src can also be a
-- union, obtained via a snd-pdi whose right component is a union.  Example:
--
--   d  = ε ● ($a + $b)
--   g  = mk-snd-pdi (EmptyU, …) (left-pdi for $a)
--   g' = left-pdi from ε to ($a + $b)
--
-- Here pdi-src g = ($a + $b), so g' is left/right, not necessarily fst/snd.
-- Hence the sketch does not cover all cases.  We switch to the alternative route
-- via first-pdU-accept-w-isMax and pdU-completeness + pdU-sorted.

{-
PROOF PLAN for chain-inj-pres-≥-cons-cons (the cons-of-cons case):

Goal: r ⊢ pdi-inj g (chain-inj rest u₀) ≥ pdi-inj g (chain-inj rest v₀)
where rest = cons g' prf' rest'', x' = chain-inj rest u₀, y' = chain-inj rest v₀.

The natural step (apply g's ≥-Max-Preserve-Local via ∈→pres-local) needs
≥-Max x' at pdi-src g, which is FALSE in general (see the compiling
counterexample Chain-does-not-preserve-≥-Max above).  The correct argument is a
well-founded induction mirroring pdU-preseve-local, keyed on the CHAIN STRUCTURE:

Chain intermediates (pdi-src values) are ε or left-nested ●-over-ε — never unions.
Hence in a cons-of-cons, the inner pdi g' (which has a successor g) is a fst-pdi
or a snd-pdi (letter/star/left/right pdi targets are $c / s* / unions — never
chain sources).  Therefore the pair (x', y') = (pdi-inj g' x'', pdi-inj g' y'')
has, at every first-component spine level, either
  * nonempty-flat first components (g' = fst-pdi, or deeper fst-pdis), or
  * EQUAL first components (g' = snd-pdi, same all-empty tree e), or
  * a maximal first component (rest'' = [], via iterated ≥-max-pair-fst-prefix→>3).
Consequently the lne/be sub-cases of g's preservation proof whose premise would
need ≥-Max of x' (empty-flat first components with y₁ > x₁) CANNOT arise:
  * rest'' = []          → x₁ is maximal, pres-local applies directly;
  * g' = fst-pdi         → x₁ nonempty-flat, contradiction with the empty premise;
  * g' = snd-pdi         → x₁ ≡ y₁, close by cong / seq₂.
The seq₁ / choice-ll / choice-rr / star-head cases recurse into the inner pdi of
g on the first-component pair — a strict sub-proof / smaller tree, so the
induction is well-founded on (chain length, tree structure).

The one genuinely fiddly ingredient is the "empty first component" sub-lemma,
needed for the lne/be cases at arbitrary first-component depth:

  empty-fst-≥ : ∀ { l } ( rest : Chain p₀ (l ● s ` loc) ) ( sp : FstSpine )
    → ( u₀ : U p₀ ) → ≥-Max u₀ → ( v₀ : U p₀ )
    → flat (applySpine sp (chain-inj rest u₀)) ≡ []
    → flat (applySpine sp (chain-inj rest v₀)) ≡ []
    → l ⊢ applySpine sp (chain-inj rest u₀) ≥ applySpine sp (chain-inj rest v₀)

where FstSpine tracks a sequence of first-component projections.  It is proved by
induction on rest:
  * rest = [] : applySpine sp u₀ is maximal (iterate ≥-max-pair-fst over the spine),
    so it dominates the empty-flat applySpine sp v₀.
  * rest = cons g' (fst-pdi) : the spine projection lands on a nonempty-flat
    component, contradicting the emptiness premise.
  * rest = cons g' (snd-pdi) : both sides reduce to applySpine sp' e (the SAME
    all-empty e), closed by refl.
The formulation challenge is that at deeper spine levels the projections
interleave with the inner injections (applySpine sp' (inj-g₀' (proj₁U x''))), so
FstSpine must be a combined projection+injection telescope.  This is a
multi-hour careful formalization.
-}


-- ●-decomp : every pd from a ●-target is a fst-pdi or a snd-pdi
-- Strategy: use subst *before* any with-pattern, then delegate to helpers
-- that pattern-match on the substituted list membership.
-- Key insight: compute subst (λ xs → g' ∈ xs) (sym pdU●-no/yes) g'∈
-- in the main clause, then pass result to helpers.

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

●-decomp-no : ∀ {l r : RE} {loc : ℕ} {c : Char}
  → (g' : PDInstance (l ● r ` loc) c)
  → g' ∈ List.map pdinstance-fst pdU[ l , c ]
  → (∃[ gₕ' ] (g' ≡ pdinstance-fst {l} {r} {loc} {c} gₕ'))
    ⊎ (∃[ e ] ∃[ fl ] ∃[ gₕ' ] (g' ≡ mk-snd-pdi {l} {r} {loc} {c} (e , fl) gₕ'))
●-decomp-no g' g'∈ = inj₁
  (proj₁ (∈-map⁻ pdinstance-fst g'∈)
  , proj₂ (proj₂ (∈-map⁻ pdinstance-fst g'∈)))

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

●-decomp : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( g' : PDInstance (l ● r ` loc) c )
    → g' ∈ pdU[ l ● r ` loc , c ]
    → ( ∃[ gₕ' ] ( g' ≡ pdinstance-fst {l} {r} {loc} {c} gₕ' ) )
    ⊎ ( ∃[ e ] ∃[ fl ] ∃[ gₕ' ] ( g' ≡ mk-snd-pdi {l} {r} {loc} {c} (e , fl) gₕ' ) )
●-decomp {l} {r} {loc} {c} g' g'∈ with ε∈? l
... | no ¬ε∈l = ●-decomp-no g' g'∈
... | yes ε∈l = ●-decomp-yes g' g'∈

{-
CHAIN HELPERS (attempted ●-decomp approach — DOES NOT COMPILE):

The core problem: ●-decomp requires explicit l, r, loc :
  ●-decomp : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( g' : PDInstance (l ● r ` loc) c )
    → g' ∈ pdU[ l ● r ` loc , c ]
    → fst ⊎ snd

But in our helpers, the target type is (pdi-src g) : RE — an opaque regex.
Agda cannot "open up" d to see that it equals l ● r ` loc without an
equality proof, and we don't have one (the type of g is just PDInstance d c).

Even if we used ε∈? (pdi-src g), the branches give us ε∈ d or ¬ε∈ d,
but not the decomposition d ≡ l ● r ` loc needed for ●-decomp.
-}

{-  (OBSOLETE: the broken fst/snd dispatcher approach cannot be used here;
    see the postulate chain-inj-pres-≥-cons-cons above.)
-- Helper for fst-pdi case: x' and y' are at type U (pdi-src g).
-- The fst/snd distinction is about the PROOF STRATEGY, not the type.
-- NOTE: the conclusion is d ⊢ pdi-inj g x' ≥ pdi-inj g y'
-- since pdi-inj g : U (pdi-src g) → U d.
chain-inj-pres-≥-fst : ∀ { p₀ d : RE } { c c' : Char }
  → ( g : PDInstance d c )
  → ( x' y' : U (pdi-src g) )
  → pdi-src g ⊢ x' > y'
  → d ⊢ pdi-inj g x' ≥ pdi-inj g y'
chain-inj-pres-≥-fst g x' y' x'>y' = {!!}
-- Helper for snd-pdi case: x' = pdi-inj g (mk-snd-pdi e fl gₕ' x'' )
-- first components of x' and y' are equal (both e), so the proof reduces
-- to comparing second components via seq₂, which recurses on the inner r.
chain-inj-pres-≥-snd : ∀ { p₀ d : RE } { c c' : Char } { l r : RE } { loc : ℕ }
  → ( g : PDInstance d c )
  → ( e : U l ) ( fl : proj₁ (flat e) ≡ [] )
  → ( gₕ' : PDInstance r c' )
  → ( x' y' : U (l ● r ` loc) )
  → l ● r ` loc ⊢ x' > y'
  → d ⊢ pdi-inj g (mk-snd-pdi {l} {r} {loc} {c'} (e , fl) gₕ' x')
           ≥ pdi-inj g (mk-snd-pdi {l} {r} {loc} {c'} (e , fl) gₕ' y')
chain-inj-pres-≥-snd g e fl gₕ' x' y' x'>y' = {!!}

-- Same as fst but for the "y' > x'" (swap) case.
chain-inj-pres-≥-fst-swap : ∀ { p₀ d : RE } { c c' : Char } { l r : RE } { loc : ℕ }
  → ( g : PDInstance d c )
  → ( gₕ' : PDInstance l c' )
  → ( x' y' : U (l ● r ` loc) )
  → l ● r ` loc ⊢ y' > x'
  → d ⊢ pdi-inj g (pdinstance-fst {l} {r} {loc} {c'} gₕ' x')
           ≥ pdi-inj g (pdinstance-fst {l} {r} {loc} {c'} gₕ' y')
chain-inj-pres-≥-fst-swap g gₕ' x' y' y'>x' = {!!}

chain-inj-pres-≥-snd-swap : ∀ { p₀ d : RE } { c c' : Char } { l r : RE } { loc : ℕ }
  → ( g : PDInstance d c )
  → ( e : U l ) ( fl : proj₁ (flat e) ≡ [] )
  → ( gₕ' : PDInstance r c' )
  → ( x' y' : U (l ● r ` loc) )
  → l ● r ` loc ⊢ y' > x'
  → d ⊢ pdi-inj g (mk-snd-pdi {l} {r} {loc} {c'} (e , fl) gₕ' x')
           ≥ pdi-inj g (mk-snd-pdi {l} {r} {loc} {c'} (e , fl) gₕ' y')
chain-inj-pres-≥-snd-swap g e fl gₕ' x' y' y'>x' = {!!}

-- Dispatch on ●-decomp when ε∉ (pdi-src g).
chain-inj-pres-≥-cons-cons-●-no : ∀ { p₀ d : RE } { c c' : Char }
  → ( g : PDInstance d c ) ( prf : g ∈ pdU[ d , c ] )
  → ( g' : PDInstance (pdi-src g) c' ) ( prf' : g' ∈ pdU[ pdi-src g , c' ] )
  → ( x' y' : U (pdi-src g) )
  → pdi-src g ⊢ x' > y'
  → d ⊢ pdi-inj g x' ≥ pdi-inj g y'
chain-inj-pres-≥-cons-cons-●-no {p₀} {d} {c} {c'} g prf g' prf' x' y' x'>y'
  with ●-decomp g' prf'
... | inj₁ (gₕ' , g'≡fst) rewrite g'≡fst = chain-inj-pres-≥-fst g gₕ' x' y' x'>y'
... | inj₂ (e , fl , gₕ' , g'≡snd) rewrite g'≡snd = chain-inj-pres-≥-snd g e fl gₕ' x' y' x'>y'

-- Dispatch on ●-decomp when ε∈ (pdi-src g).
chain-inj-pres-≥-cons-cons-●-yes : ∀ { p₀ d : RE } { c c' : Char }
  → ( g : PDInstance d c ) ( prf : g ∈ pdU[ d , c ] )
  → ( g' : PDInstance (pdi-src g) c' ) ( prf' : g' ∈ pdU[ pdi-src g , c' ] )
  → ( x' y' : U (pdi-src g) )
  → pdi-src g ⊢ x' > y'
  → ε∈ (pdi-src g)
  → d ⊢ pdi-inj g x' ≥ pdi-inj g y'
chain-inj-pres-≥-cons-cons-●-yes {p₀} {d} {c} {c'} g prf g' prf' x' y' x'>y' ε∈src
  with ●-decomp g' prf'
... | inj₁ (gₕ' , g'≡fst) rewrite g'≡fst = chain-inj-pres-≥-fst g gₕ' x' y' x'>y'
... | inj₂ (e , fl , gₕ' , g'≡snd) rewrite g'≡snd = chain-inj-pres-≥-snd g e fl gₕ' x' y' x'>y'

-- When ε∈ (pdi-src g), dispatch on ε or ●.
chain-inj-pres-≥-cons-cons-ε : ∀ { p₀ d : RE } { c c' : Char }
  → ( g : PDInstance d c ) ( prf : g ∈ pdU[ d , c ] )
  → ( g' : PDInstance (pdi-src g) c' ) ( prf' : g' ∈ pdU[ pdi-src g , c' ] )
  → ( x' y' : U (pdi-src g) )
  → pdi-src g ⊢ x' > y'
  → d ⊢ pdi-inj g x' ≥ pdi-inj g y'
chain-inj-pres-≥-cons-cons-ε {p₀} {d} {c} {c'} g prf g' prf' x' y' x'>y'
  with ε∈? (pdi-src g)
... | no ¬ε∈src = chain-inj-pres-≥-cons-cons-●-no {p₀} {d} {c} {c'} g prf g' prf' x' y' x'>y'
... | yes ε∈src = chain-inj-pres-≥-cons-cons-●-yes {p₀} {d} {c} {c'} g prf g' prf' x' y' x'>y' ε∈src

-- Core helper using ev (≥-Max-Preserve-Local evidence).
chain-inj-pres-≥-cons-cons-●-ev : ∀ { d : RE } { c c' : Char }
  → ( g : PDInstance d c )
  → ( ev : ( u : U (pdi-src g) ) → ≥-Max {pdi-src g} (proj₁ (flat u)) u
       → ( v : U (pdi-src g) ) → pdi-src g ⊢ u ≥ v
       → d ⊢ pdi-inj g u ≥ pdi-inj g v )
  → ( g' : PDInstance (pdi-src g) c' ) ( prf' : g' ∈ pdU[ pdi-src g , c' ] )
  → ( x' y' : U (pdi-src g) )
  → pdi-src g ⊢ x' > y'
  → d ⊢ pdi-inj g x' ≥ pdi-inj g y'
chain-inj-pres-≥-cons-cons-●-ev g ev g' prf' x' y' x'>y'
  with ●-decomp g' prf'
... | inj₁ (gₕ' , g'≡fst) rewrite g'≡fst = chain-inj-pres-≥-fst g gₕ' x' y' x'>y'
... | inj₂ (e , fl , gₕ' , g'≡snd) rewrite g'≡snd = chain-inj-pres-≥-snd g e fl gₕ' x' y' x'>y'

-- Bridge from ∈→pres-local to ●-ev.
chain-inj-pres-≥-cons-cons-● : ∀ { d : RE } { c c' : Char }
  → ( g : PDInstance d c ) ( prf : g ∈ pdU[ d , c ] )
  → ( g' : PDInstance (pdi-src g) c' ) ( prf' : g' ∈ pdU[ pdi-src g , c' ] )
  → ( x' y' : U (pdi-src g) )
  → pdi-src g ⊢ x' > y'
  → d ⊢ pdi-inj g x' ≥ pdi-inj g y'
chain-inj-pres-≥-cons-cons-● g prf g' prf' x' y' x'>y'
  with ∈→pres-local g prf
... | ≥-max-pres-local ev = chain-inj-pres-≥-cons-cons-●-ev g ev g' prf' x' y' x'>y'

-- Swap case: y' > x'.
chain-inj-pres-≥-cons-cons-swap : ∀ { p₀ d : RE } { c c' : Char }
  → ( g : PDInstance d c ) ( prf : g ∈ pdU[ d , c ] )
  → ( g' : PDInstance (pdi-src g) c' ) ( prf' : g' ∈ pdU[ pdi-src g , c' ] )
  → ( x' y' : U (pdi-src g) )
  → pdi-src g ⊢ y' > x'
  → d ⊢ pdi-inj g x' ≥ pdi-inj g y'
chain-inj-pres-≥-cons-cons-swap {p₀} {d} {c} {c'} g prf g' prf' x' y' y'>x'
  with ●-decomp g' prf'
... | inj₁ (gₕ' , g'≡fst) rewrite g'≡fst = chain-inj-pres-≥-fst-swap g gₕ' x' y' y'>x'
... | inj₂ (e , fl , gₕ' , g'≡snd) rewrite g'≡snd = chain-inj-pres-≥-snd-swap g e fl gₕ' x' y' y'>x'

-- Main dispatcher: ε∉src → ●, ε∈src → ε/●.
chain-inj-pres-≥-cons-cons : ∀ { p₀ d : RE } { c c' : Char }
  → ( g : PDInstance d c ) ( prf : g ∈ pdU[ d , c ] )
  → ( g' : PDInstance (pdi-src g) c' ) ( prf' : g' ∈ pdU[ pdi-src g , c' ] )
  → ( x' y' : U (pdi-src g) )
  → pdi-src g ⊢ x' > y'
  → d ⊢ pdi-inj g x' ≥ pdi-inj g y'
chain-inj-pres-≥-cons-cons {p₀} {d} {c} {c'} g prf g' prf' x' y' x'>y'
  with ε∈? (pdi-src g)
... | no ¬ε∈src = chain-inj-pres-≥-cons-cons-● {d} {c} {c'} g prf g' prf' x' y' x'>y'
... | yes ε∈src = chain-inj-pres-≥-cons-cons-ε {p₀} {d} {c} {c'} g prf g' prf' x' y' x'>y'
-}

{-
postulate
  ●-decomp : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( g' : PDInstance (l ● r ` loc) c )
    → g' ∈ pdU[ l ● r ` loc , c ]
    → ( ∃[ gₕ' ] ( g' ≡ pdinstance-fst {l} {r} {loc} {c} gₕ' ) )
    ⊎ ( ∃[ e ] ∃[ fl ] ∃[ gₕ' ] ( g' ≡ mk-snd-pdi {l} {r} {loc} {c} (e , fl) gₕ' ) )
-}



data ≥-Max-Preserve-Local* : ∀ { r : RE } { pref : List Char } → PDInstance* r pref → Set where
  ≥-max-pres-local* : ∀ { p r : RE } { pref : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ pref ++ ( proj₁ (flat {p} x) )) }
    → ( ∀ { p₀ : RE } ( chain : Chain p₀ p ) ( u₀ : U p₀ )
      → ≥-Max {p₀} (proj₁ (flat u₀)) u₀
      → ( v₀ : U p₀ ) 
      → p₀ ⊢ u₀ ≥ v₀
      → r ⊢ inj (chain-inj chain u₀) ≥ inj (chain-inj chain v₀) ) 
    → ≥-Max-Preserve-Local* {r} {pref} (pdinstance* inj sound-ev)



-- pdUMany-preseve-local: all pdinstance*'s in pdUMany[r, w] preserve ≥-Max locally
--
-- Key insight for the inductive step: NO preservation lemmas are needed.
-- chain-inj (cons g g∈ chain) ≡ pdi-inj g ∘ chain-inj chain holds definitionally,
-- so given ≥-Max-Preserve-Local* for pdi* = pdinstance* d→r s-ev (evidence d-pres),
-- each composed pdinstance* in advance-pdi*-with-c pdi satisfies it by simply
-- EXTENDING the chain: d-pres (cons g g∈ chain) has exactly the required type.
--
-- The only remaining obligation is the base case (identity injection):
--   id-pres : chains into r preserve ≥  (hole below)
-- Its natural induction on the chain applies, at each step, the
-- ≥-Max-Preserve-Local of the head pdi (from pdU-preseve-local), whose premise
-- requires ≥-Max of the inner chain image (chain-inj rest u₀) at the intermediate
-- regex.  That is "chains preserve ≥-Max", which is FALSE in general —
-- see the compiling counterexample below.  Note the counterexample's bad
-- intermediate regex ($a + $a) is a union, which can never be a chain source
-- (sources are ε or left-nested ● over ε), so id-pres may still hold;
-- but proving it needs a different invariant or cross-pdi comparison machinery
-- (pdU-completeness + pdU-sorted, cf. first-pdU-accept-w-isMax).

-- COUNTEREXAMPLE: chains do NOT preserve ≥-Max.
-- r-ce = $a + $a (distinct locations); the right-pdi g-ce ∈ pdU[ r-ce , a ]
-- maps EmptyU (trivially ≥-Max at ε) to RightU (LetterU a), which is NOT
-- ≥-Max at [ a ]: LeftU (LetterU a) also flattens to [ a ] and beats it via
-- choice-lr, while RightU ≱ LeftU (no constructor gives RightU >ⁱ LeftU).
module Chain-does-not-preserve-≥-Max where
  a : Char
  a = 'a'

  r-ce : RE
  r-ce = ($ a ` 0) + ($ a ` 1) ` 0

  g-ce : PDInstance r-ce a
  g-ce = pdinstance-right (pdinstance mkinjLetter mkinjLetterSound)

  g-ce∈ : g-ce ∈ pdU[ r-ce , a ]
  g-ce∈ = there (here refl)

  chain-ce : Chain ε r-ce
  chain-ce = cons {ε} {ε} {r-ce} {a} g-ce g-ce∈ []

  -- chain-inj chain-ce EmptyU ≡ RightU (LetterU a)  (definitionally)

  max-empty : ≥-Max {ε} [] EmptyU
  max-empty = ≥-max [] EmptyU refl (λ { EmptyU refl → inj₂ refl })

  counterexample
    : ( ∀ { r p₀ : RE } ( chain : Chain p₀ r ) ( u₀ : U p₀ )
      → ≥-Max {p₀} (proj₁ (flat u₀)) u₀
      → ≥-Max {r} (proj₁ (flat (chain-inj chain u₀))) (chain-inj chain u₀) )
    → ⊥
  counterexample pres = right≱left right≥left
    where
      right≱left : ¬ ( r-ce ⊢ RightU (LetterU a) ≥ LeftU (LetterU a) )
      right≱left (inj₁ (be _ _ ()))
      right≱left (inj₁ (bne _ _ ()))
      right≱left (inj₁ (lne _ ()))
      right≱left (inj₂ ())

      right≥left : r-ce ⊢ RightU (LetterU a) ≥ LeftU (LetterU a)
      right≥left with pres chain-ce EmptyU max-empty
      ... | ≥-max w .(RightU (LetterU a)) _ beat = beat (LeftU (LetterU a)) refl

all-map-∈ : ∀ { A B : Set } { P : B → Set } ( f : A → B ) ( xs : List A )
  → ( ∀ ( x : A ) → x ∈ xs → P ( f x ) )
  → All P ( List.map f xs )
all-map-∈ f [] h = []
all-map-∈ f (x ∷ xs) h = h x (here refl) ∷ all-map-∈ f xs (λ x' x'∈xs → h x' (there x'∈xs))

compose-pdi-with-preseve-local : ∀ { r d : RE } { pref : List Char } { c : Char }
  → ( d→r : U d → U r )
  → ( s-ev-d→r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → ( d-pres : ∀ { p₀ : RE } ( chain : Chain p₀ d ) ( u₀ : U p₀ )
      → ≥-Max {p₀} (proj₁ (flat u₀)) u₀
      → ( v₀ : U p₀ )
      → p₀ ⊢ u₀ ≥ v₀
      → r ⊢ d→r (chain-inj chain u₀) ≥ d→r (chain-inj chain v₀) )
  → ( g : PDInstance d c )
  → g ∈ pdU[ d , c ]
  → ≥-Max-Preserve-Local* {r} {pref ∷ʳ c} (compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d→r g)
compose-pdi-with-preseve-local {r} {d} {pref} {c} d→r s-ev-d→r d-pres (pdinstance {p} {d} {c} p→d s-ev-p→d) g∈ =
  ≥-max-pres-local* ev
  where
    ev : ∀ { p₀ : RE } ( chain : Chain p₀ p ) ( u₀ : U p₀ )
      → ≥-Max {p₀} (proj₁ (flat u₀)) u₀
      → ( v₀ : U p₀ )
      → p₀ ⊢ u₀ ≥ v₀
      → r ⊢ d→r (p→d (chain-inj chain u₀)) ≥ d→r (p→d (chain-inj chain v₀))
    ev {p₀} chain u₀ max-u₀ v₀ u₀≥v₀ = d-pres chain' u₀ max-u₀ v₀ u₀≥v₀
      where
        chain' : Chain p₀ d
        chain' = cons {p₀} {p} {d} {c} (pdinstance p→d s-ev-p→d) g∈ chain

advance-pdi*-with-c-preseve-local : ∀ { r : RE } { pref : List Char } { c : Char }
  → ( pdi : PDInstance* r pref )
  → ≥-Max-Preserve-Local* pdi
  → All (≥-Max-Preserve-Local* {r} {pref ∷ʳ c}) (advance-pdi*-with-c {r} {pref} {c} pdi)
advance-pdi*-with-c-preseve-local {r} {pref} {c} (pdinstance* {d} {r} {pref} d→r s-ev-d→r) (≥-max-pres-local* d-pres) =
  all-map-∈ (compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d→r) pdU[ d , c ]
    (λ g g∈ → compose-pdi-with-preseve-local d→r s-ev-d→r d-pres g g∈)

concatmap-advance-pdi*-with-c-preseve-local : ∀ { r : RE } { pref : List Char } { c : Char }
  → ( pdis : List (PDInstance* r pref) )
  → All (≥-Max-Preserve-Local* {r} {pref}) pdis
  → All (≥-Max-Preserve-Local* {r} {pref ∷ʳ c}) (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
concatmap-advance-pdi*-with-c-preseve-local {r} {pref} {c} [] [] = []
concatmap-advance-pdi*-with-c-preseve-local {r} {pref} {c} (pdi ∷ pdis) (pres-pdi ∷ all-pres-pdis) =
  all-concat (advance-pdi*-with-c-preseve-local pdi pres-pdi) (concatmap-advance-pdi*-with-c-preseve-local pdis all-pres-pdis)

pdUMany-aux-preseve-local : ∀ { r : RE } { pref : List Char }
  → ( suff : List Char )
  → ( pdis : List (PDInstance* r pref) )
  → All (≥-Max-Preserve-Local* {r} {pref}) pdis
  → All (≥-Max-Preserve-Local* {r} {pref ++ suff}) (pdUMany-aux suff pdis)
pdUMany-aux-preseve-local {r} {pref} [] pdis all-pres rewrite (++-identityʳ pref) = all-pres
pdUMany-aux-preseve-local {r} {pref} (c ∷ cs) pdis all-pres =
  pdUMany-aux-preseve-local {r} {pref ∷ʳ c} cs (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis) concatmap-pres
  where
    concatmap-pres : All (≥-Max-Preserve-Local* {r} {pref ∷ʳ c}) (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    concatmap-pres = concatmap-advance-pdi*-with-c-preseve-local pdis all-pres

-- this lemma is not yet proven. we just leave it aside for now 
-- TODO: chain-inj-pres-≥-cons-cons is postulated.
pdUMany-preseve-local : ∀ { r : RE } { w : List Char }
  → All (≥-Max-Preserve-Local* {r} {w}) pdUMany[ r , w ]
pdUMany-preseve-local {r} {w} = pdUMany-aux-preseve-local {r} {[]} w initial initial-all
  where
    initial : List (PDInstance* r [])
    initial = pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ∷ []

    initial-all : All (≥-Max-Preserve-Local* {r} {[]}) initial
    initial-all = ≥-max-pres-local* id-pres ∷ []
      where
        id-pres : ∀ { p₀ : RE } ( chain : Chain p₀ r ) ( u₀ : U p₀ )
          → ≥-Max {p₀} (proj₁ (flat u₀)) u₀
          → ( v₀ : U p₀ )
          → p₀ ⊢ u₀ ≥ v₀
          → r ⊢ chain-inj chain u₀ ≥ chain-inj chain v₀
        id-pres = chain-inj-pres-≥   -- TODO: chain-inj-pres-≥-cons-cons is postulated.
```


does the following definition make sense and is helpful?

A pdinstance is suffix w maximal iff given the max parse tree of w w.r.t to some p, say u,  inject u gives us the maximal parse tree of r.
```agda

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


pdU●-no : ∀ { l r : RE } { loc : ℕ } { c : Char } → (¬ε∈l : ¬ ε∈ l) → pdU● {l} {r} {loc} {c} (no ¬ε∈l) ≡ List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ]
pdU●-no ¬ε∈l = refl

pdU●-yes : ∀ { l r : RE } { loc : ℕ } { c : Char } → (ε∈l : ε∈ l) → pdU● {l} {r} {loc} {c} (yes ε∈l) ≡ List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ] ++ concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ]
pdU●-yes ε∈l = refl

first-inhabit-nil-nothing : ∀ { r : RE } { c : Char } { w : List Char }
  → first-inhabit r c w [] ≡ nothing
first-inhabit-nil-nothing = refl

first-inhabit-++-just : ∀ { r : RE } { c : Char } { w : List Char }
  → ( xs ys : List (PDInstance r c) ) ( pdil : PDInstance r c )
  → first-inhabit r c w xs ≡ just pdil
  → first-inhabit r c w (xs ++ ys) ≡ just pdil
first-inhabit-++-just [] ys pdil ()
first-inhabit-++-just {w = w} (x ∷ xs) ys pdil eq with w ∈?⟦ pdi-src x ⟧
... | yes w∈src-x rewrite first-inhabit-yes-eq-full x xs w∈src-x rewrite sym eq = refl
... | no ¬w∈src-x rewrite first-inhabit-no-eq x (xs ++ ys) ¬w∈src-x
  rewrite first-inhabit-++-just xs ys pdil eq = refl

-- TODO: first-inhabit-++-just-left-pdi is postulated due to Agda 2.7 with-abstraction issue.
-- The lemma states: if first-inhabit on pdU[l+r, c] finds pdi, and (c∷w) ∈⟦ l ⟧,
-- then pdi ≡ pdinstance-left pdil for some pdil with first-inhabit l c w (pdU[l,c]) ≡ just pdil.
{-
postulate
  first-inhabit-++-just-left-pdi-old : ∀ { l r : RE } { loc : ℕ } { c : Char } { w : List Char }
    → ( pdi : PDInstance (l + r ` loc) c )
    → first-inhabit (l + r ` loc) c w (pdU[ l + r ` loc , c ]) ≡ just pdi
    -- → Σ (PDInstance l c) λ pdil → first-inhabit l c w (pdU[ l , c ]) ≡ just pdil × pdi ≡ pdinstance-left pdil
    → ∃[ pdil ] first-inhabit l c w (pdU[ l , c ]) ≡ just pdil × pdi ≡ pdinstance-left pdil
-}


pdi-src-pres-left : ∀ {l r : RE} {loc : ℕ} {c : Char} (x : PDInstance l c)
  → pdi-src (pdinstance-left {l} {r} {loc}  x) ≡ pdi-src x
pdi-src-pres-left (pdinstance {p} inj s-ev) = refl


-- Core: first-inhabit on (map left xs ++ map right ys) preserves result from xs.
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


-- is this being used? 
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
    
-- FIXED by Kenny
-- is this being used?
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

-- FIXED by Kenny
-- is this being used? 
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


-- FIXED by Kenny
-- we prove first-inhabit-++-just-left-pdi using the following sub lemma
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

-- FIXED by Kenny  
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
    

≥-max-pres-left-pdi : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdil : PDInstance l c ) (w : List Char)
  → (c∷w∈l : (c ∷ w) ∈⟦ l ⟧)
  → ≥-Max-PDInstance {l} {c} w pdil
  → ≥-Max-PDInstance {l + r ` loc} {c} w (pdinstance-left pdil)
≥-max-pres-left-pdi {l} {r} {loc} {c} (pdinstance inj s-ev) w c∷w∈l (≥-max-pdi u w μ-w μ-c∷w) =
  ≥-max-pdi u w μ-w (≥-max-pres-left-helper (pdi-src (pdinstance inj s-ev)) l r loc c inj u w μ-c∷w)

-- When left is nothing, combined result falls through to right.
mutual
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
  ≥-max-pres-right-pdi : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( pdir : PDInstance r c ) (w : List Char)
    → (c∷w∈r : (c ∷ w) ∈⟦ r ⟧)
    → ¬ ((c ∷ w) ∈⟦ l ⟧)
    → ≥-Max-PDInstance {r} {c} w pdir
    → ≥-Max-PDInstance {l + r ` loc} {c} w (pdinstance-right pdir)
  ≥-max-pres-right-pdi {l} {r} {loc} {c} (pdinstance inj s-ev) w c∷w∈r ¬c∷w∈l (≥-max-pdi u w μ-w μ-c∷w) =
    ≥-max-pdi u w μ-w (≥-max-pres-right-helper _ l r loc c inj u w ¬c∷w∈l μ-c∷w)
  
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
  first-pdU-accept-w-isMax-+ : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ l + r ` loc ⟧)
    → ( pdi : PDInstance (l + r ` loc) c)
    → (first-inhabit (l + r ` loc) c w  pdU[ l + r ` loc , c ]) ≡ just pdi
    → ≥-Max-PDInstance {l + r ` loc} {c} w pdi
  first-pdU-accept-w-isMax-+ {l} {r} {loc} {c} w c∷w∈+ pdi eq with +-elim c∷w∈+
  ... | inj₁ cw∈l = first-pdU-accept-w-isMax-+-left w cw∈l pdi eq
  ... | inj₂ cw∈r = first-pdU-accept-w-isMax-+-right w cw∈r pdi eq

  +-elim : ∀ {l r : RE} {loc : ℕ} {w : List Char} → w ∈⟦ l + r ` loc ⟧ → w ∈⟦ l ⟧ ⊎ w ∈⟦ r ⟧
  +-elim {l} {r} (_+L_ {l} {xs = w} {loc} .r w∈l) = inj₁ w∈l
  +-elim {l} {r} (_+R_ {r} {xs = w} {loc} .l w∈r) = inj₂ w∈r

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

  -- Helper for ● case, ¬ε∈l
  first-pdU-accept-w-isMax-●-no : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( ¬ε∈l : ¬ ε∈ l )
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ l ● r ` loc ⟧)
    → ( pdi : PDInstance (l ● r ` loc) c)
    → (first-inhabit (l ● r ` loc) c w  (List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ])) ≡ just pdi
    → ≥-Max-PDInstance {l ● r ` loc} {c} w pdi
  first-pdU-accept-w-isMax-●-no ¬ε∈l w c∷w∈● pdi eq = {!!}
    -- TODO: Show pdi ≡ pdinstance-fst pdil for some pdil : PDInstance l c
    -- Then use first-pdU-accept-w-isMax {l} {c} (w' ∷ _) ... pdil eq-l
    -- where w' ∷ _ is the split of c∷w across l and r.

  -- Helper for ● case, ε∈l
  first-pdU-accept-w-isMax-●-yes : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( ε∈l : ε∈ l )
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ l ● r ` loc ⟧)
    → ( pdi : PDInstance (l ● r ` loc) c)
    → (first-inhabit (l ● r ` loc) c w  (List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ] ++ concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ])) ≡ just pdi
    → ≥-Max-PDInstance {l ● r ` loc} {c} w pdi
  first-pdU-accept-w-isMax-●-yes ε∈l w c∷w∈● pdi eq = {!!}
    -- TODO: Similar to ●-no but also handle the concatmap-pdinstance-snd part.

  -- Helper for * case
  first-pdU-accept-w-isMax-* : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ } { c : Char }
    → ( w : List Char )
    → ((c ∷ w) ∈⟦ r * nε ` loc ⟧)
    → ( pdi : PDInstance (r * nε ` loc) c)
    → (first-inhabit (r * nε ` loc) c w  pdU[ r * nε ` loc , c ]) ≡ just pdi
    → ≥-Max-PDInstance {r * nε ` loc} {c} w pdi
  first-pdU-accept-w-isMax-* nε c∷w∈* pdi eq = {!!}
    -- TODO: Show pdi ≡ pdinstance-star pdir for some pdir : PDInstance r c
    -- Then use first-pdU-accept-w-isMax {r} {c} ... pdir eq-r

  first-concatMap-buildU-pdUMany-isMax : ∀ ( r : RE )
    → ( w : List Char )
    → ( w ∈⟦ r ⟧  )
    → ( u : U r )
    → head (List.concatMap buildU pdUMany[ r , w ]) ≡ just u
    →  ≥-Max w u
  first-concatMap-buildU-pdUMany-isMax r w w∈r u eq = {!!}
    -- TODO: Mutually recursive with first-pdU-accept-w-isMax.
    -- For ε: direct proof using flat-Uε≡[]
    -- For $ c: use first-pdU-accept-w-isMax for $ c
    -- For +, ●, *: decompose w and use IH
```


Extended Order 

```agda
data _,_,_⊢*_≥_ : ∀ ( r : RE ) → ( pref : List Char ) → ( suf : List Char ) → PDInstance* r pref → PDInstance* r pref  → Set where
  *≥-pdi : ∀ { p₁ p₂ r : RE } { pref : List Char }
    { inj₁ : U p₁ → U r }
    { sound-ev₁ : ∀ ( x : U p₁ ) → ( proj₁ (flat {r} (inj₁ x ) ) ≡ pref ++ ( proj₁ (flat {p₁} x) )) }
    { inj₂ : U p₂ → U r }
    { sound-ev₂ : ∀ ( x : U p₂ ) → ( proj₁ (flat {r} (inj₂ x ) ) ≡ pref ++ ( proj₁ (flat {p₂} x) )) }
    → ( suf : List Char )
    → ( ( u₁ : U p₁ )
      → ( u₂ : U p₂ )
      → ( ≥-Max {p₁} suf u₁ )
      → ( ≥-Max {p₂} suf u₂ )
      → r ⊢ inj₁ u₁ ≥ inj₂ u₂ )
    → r , pref , suf  ⊢* pdinstance* inj₁ sound-ev₁ ≥ pdinstance* inj₂ sound-ev₂

```


A pdinstance* is suffix w maximal iff given the max parse tree of w w.r.t to some p, say u,  inject u gives us the maximal parse tree of r.
```agda

data ≥-Max-PDInstance* : ∀ {r : RE } { pref : List Char } → ( List Char ) → PDInstance* r pref → Set where
  ≥-max-pdi* : ∀ { p r : RE } { pref : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ (flat {r} (inj x ) ) ≡ pref ++ ( proj₁ (flat {p} x) )) }
    → ( u : U p )
    → ( suff : List Char )
    → ≥-Max suff u
    → ≥-Max (pref ++ suff) (inj u)
    → ≥-Max-PDInstance* {r} {pref} suff (pdinstance* inj sound-ev) 

```



```agda
-- first-concatMap-buildU-pdUMany-isMax is defined in the mutual block above   




first-parseAll-isMax  : ∀ ( r : RE )
  → ( w : List Char )
  → w ∈⟦ r ⟧
  → ( u : U r )
  → head parseAll[ r , w ] ≡ just u
  → ≥-Max w u 
first-parseAll-isMax = first-concatMap-buildU-pdUMany-isMax
```
```agda
