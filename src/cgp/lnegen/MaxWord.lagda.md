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
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; mkAllEmptyU≢[] ; Flat-[] ; flat-[] ; proj₁flat-v≡[]→ε∈r )

import cgp.Recons as Recons
open Recons using ( Recons ; recons )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ; 
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ; mkinjFstSoundEv ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ;
  concatmap-pdinstance-snd ; concatmap-pdinstance-snd-[]≡[] ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with 
  ) 


import cgp.lnegen.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ;  pdU-complete ; 
  advance-pdi*-with-c ; 
  pdUMany[_,_]; pdUMany-aux ;
  mkinjLetter ; mkinjLetterSound ;
  parseAll[_,_] ; buildU ;
  pdUMany-complete ; buildU-complete ; buildU-sound

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
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _+_ ; _∸_ ; _≤_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; _≟_ ; m+n≤o⇒m≤o∸n ; m≤o∸n⇒m+n≤o ; m+n≤o⇒n≤o ; +-identityʳ ; +-identityˡ ; m≤m+n ; m≤n+m ; +-comm ; m+n≡0⇒m≡0 ; m+n≡0⇒n≡0 )



import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length ; foldr )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ; length-++ ; ++-assoc ; ∷-injective )

open import Data.List.Relation.Unary.Any using (Any; here; there ; map)

import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)

import Data.List.Membership.Propositional.Properties as MembershipProperties
open MembershipProperties using (∈-concat⁺′ ; ∈-concat⁻′ ; ∈-map⁺ ; ∈-map⁻)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst)
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
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

open import Function using (_∘_ ; flip ; case_of_)

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


-- we need this to get ≥-Max u from ≥-Max (PairU u v) 
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

≥-max-pres-right-direct : ∀ { l r : RE } { loc : ℕ } { c : Char }
  { pdi : PDInstance r c }
  → ≥-Max-Preserve {r} {c} pdi
  → (∀ (w : List Char) → ¬ ((c ∷ w) ∈⟦ l ⟧))
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-right pdi)
≥-max-pres-right-direct {l} {r} {loc} {c} {pdinstance inj s-ev} (≥-max-pres preserve) ¬c∷w∈l =
  ≥-max-pres (λ u w maxu → ≥-max-pres-right (≥-max-pres preserve) u w maxu (¬c∷w∈l w))

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

-- too weak, we have a stronger version below.

{-
≥-max-pres-fst : ∀ { p l r : RE } { loc : ℕ } { c : Char }
  { inj : U p → U l }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {l} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max-Preserve {l} {c} (pdinstance inj sound-ev)
  → ( u₁ : U p ) ( u₂ : U r )
  → ( w : List Char )
  → ≥-Max {p ● r ` loc} w (PairU u₁ u₂)
  → ≥-Max {r} (proj₁ (flat u₂)) u₂
  → ( ∀ ( v₁ : U l ) -- is this dom premise too strong (unnecessarily?)
      → proj₁ (flat {l} v₁) ≢ c ∷ proj₁ (flat {p} u₁)
      → proj₁ (flat {l} v₁) ≢ []
      → (∀ {c₁ cs₁} → proj₁ (flat {l} v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c) -- shall we weaken it by restricting ∃[ v₂ ] |Pair v₁ v₂| ≡ c ∷ w?
      → l ⊢ inj u₁ > v₁ ) 
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
    helper : ( v : U (l ● r ` loc) )
           → proj₁ (flat {l ● r ` loc} v) ≡ c ∷ w
           → l ● r ` loc ⊢ PairU (inj u₁) u₂ ≥ v
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
          first-char : ∀ {c₁ cs₁} → proj₁ (flat {l} v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c
          first-char {c₁} {cs₁} eq₁ =
            proj₁ (Utils.∷-inj (trans (sym (cong (λ x → x ++ proj₁ (flat {r} v₂)) eq₁)) flat-v≡c∷w))
      in inj₁ (bne {l ● r ` loc} {PairU (inj u₁) u₂} {PairU v₁ v₂}
           len>0-pair-inj (len>0-pair-v (PairU {l} {r} {loc} v₁ v₂) flat-v≡c∷w)
           (seq₁ {l} {r} {loc} {inj u₁} {v₁} {u₂} {v₂} (dom v₁ ¬eq ¬[] first-char)))
  
-} 
  
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
  → ( ∀ ( v : U r ) → proj₁ (flat {r} v) ≢ c ∷ proj₁ (flat {p} u) → proj₁ (flat {r} v) ≢ [] → (∀ {c₁ cs₁} → proj₁ (flat {r} v) ≡ c₁ ∷ cs₁ → c₁ ≡ c) → r ⊢ inj u > v )
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
      let ¬[] : proj₁ (flat {r} w₁) ≢ []
          ¬[] eq = ¬len-w₁≡0 (cong length eq)
          first-char : ∀ {c₁ cs₁} → proj₁ (flat {r} w₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c
          first-char {c₁} {cs₁} eq₁ =
            proj₁ (Utils.∷-inj (trans (sym (cong (λ x → x ++ proj₁ (flat {r * ε∉r ` loc} (ListU {r} {ε∉r} {loc} ws'))) eq₁)) flat-v≡c∷w))
      in inj₁ (bne {r * ε∉r ` loc} {mkinjList inj (PairU u (ListU vs))} {ListU {r} {ε∉r} {loc} (w₁ ∷ ws')}
        len>0-list-inj (len>0-list-v (ListU {r} {ε∉r} {loc} (w₁ ∷ ws')) flat-v≡c∷w)
        (star-head {r} {loc} {ε∉r} {inj u} {w₁} {vs} {ws'} (dom w₁ ¬eq ¬[] first-char)))


-- a stronger variant of ≥-max-pres-fst
≥-max-pres-fst-strong : ∀ { p l r : RE } { loc : ℕ } { c : Char }
  { inj : U p → U l }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {l} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max-Preserve {l} {c} (pdinstance inj sound-ev)
  → ( u₁ : U p ) ( u₂ : U r )
  → ( w : List Char )
  → ≥-Max {p ● r ` loc} w (PairU u₁ u₂)
  → ≥-Max {r} (proj₁ (flat u₂)) u₂
  → ( ∀ ( v₁ : U l ) -- weaken compared to  ≥-max-pres-fst
      → proj₁ (flat {l} v₁) ≢ c ∷ proj₁ (flat {p} u₁)
      → proj₁ (flat {l} v₁) ≢ []
      → (∀ {c₁ cs₁} → proj₁ (flat {l} v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c) 
      → ∃[ v₂ ] (proj₁ (flat {l ● r ` loc} (PairU v₁ v₂))) ≡ c ∷ w 
      → l ⊢ inj u₁ ≥ v₁ ) 
  → ≥-Max {l ● r ` loc} (c ∷ w) (PairU (inj u₁) u₂)
≥-max-pres-fst-strong {p} {l} {r} {loc} {c} {inj} {sound-ev} (≥-max-pres preserve) u₁ u₂ w max-pair max-u₂ dom =
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
    u₁-max : ≥-Max {p} (proj₁ (flat {p} u₁)) u₁ -- TODO: this can be obtained from ≥-max-pair-fst-prefix→>3  
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
    helper : ( v : U (l ● r ` loc) )
           → proj₁ (flat {l ● r ` loc} v) ≡ c ∷ w
           → l ● r ` loc ⊢ PairU (inj u₁) u₂ ≥ v
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
    ...   | no ¬eq = prf
      where
        ¬[] : proj₁ (flat {l} v₁) ≢ []
        ¬[] eq = ¬len-v₁≡0 (cong length eq)
        first-char : ∀ {c₁ cs₁} → proj₁ (flat {l} v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c
        first-char {c₁} {cs₁} eq₁ =
          proj₁ (Utils.∷-inj (trans (sym (cong (λ x → x ++ proj₁ (flat {r} v₂)) eq₁)) flat-v≡c∷w))
        prf :  (l ● r ` loc) ⊢ PairU (inj u₁) u₂ ≥ PairU v₁ v₂ 
        prf with (dom v₁ ¬eq ¬[] first-char (v₂ , flat-v≡c∷w) )
        ... | inj₁ inj-u₁>v₁ = inj₁ (bne {l ● r ` loc} {PairU (inj u₁) u₂} {PairU v₁ v₂} len>0-pair-inj (len>0-pair-v (PairU {l} {r} {loc} v₁ v₂) flat-v≡c∷w) (seq₁ {l} {r} {loc} {inj u₁} {v₁} {u₂} {v₂} inj-u₁>v₁  ))
        ... | inj₂ inj-u₁≡v₁ = inj₂  {!!} -- we need u₂ ≥ v₂ 


-- len-flat-pair (top-level): length of flat(PairU a b) decomposes as sum of component lengths.
-- Needed by extract-≥-snd.
len-flat-pair : ∀ {l' r' : RE} {loc' : ℕ} {a : U l'} {b : U r'}
  → length (proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} a b))) ≡ length (proj₁ (flat {l'} a)) + length (proj₁ (flat {r'} b))
len-flat-pair {l'} {r'} {loc'} {a = a} {b = b} =
  begin
    length (proj₁ (flat {l' ● r' ` loc'} (PairU {l'} {r'} {loc'} a b)))
  ≡⟨ cong length refl ⟩
    length (proj₁ (flat {l'} a) ++ proj₁ (flat {r'} b))
  ≡⟨ length-++ (proj₁ (flat {l'} a)) {proj₁ (flat {r'} b)} ⟩
    length (proj₁ (flat {l'} a)) + length (proj₁ (flat {r'} b))
  ∎

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


-- ≥-max-pres-fst-preserve: Lift ≥-Max-Preserve through pdinstance-fst.
-- Given ≥-Max-Preserve for the left factor pdi and a dom premise,
-- returns ≥-Max-Preserve for the pair pdi on the first component.
-- too weak, we have a stronger version below
{-
≥-max-pres-fst-preserve : ∀ { p l r : RE } { loc : ℕ } { c : Char }
  { inj : U p → U l }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {l} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max-Preserve {l} {c} (pdinstance inj sound-ev)
  → ( dom : ∀ ( u₁ : U p ) ( u₂ : U r ) ( w : List Char )
        → ≥-Max {p ● r ` loc} w (PairU u₁ u₂)
        → ( v₁ : U l )
        → proj₁ (flat {l} v₁) ≢ c ∷ proj₁ (flat {p} u₁)
        → proj₁ (flat {l} v₁) ≢ []
        → (∀ {c₁ cs₁} → proj₁ (flat {l} v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c) -- can we restrict ∃[ v₂ ] | Pair v₁ v₂ | ≡ c ∷ w ? 
        → l ⊢ inj u₁ > v₁ )
  → ≥-Max-Preserve {l ● r ` loc} {c} (pdinstance-fst (pdinstance inj sound-ev))
≥-max-pres-fst-preserve {p} {l} {r} {loc} {c} {inj} {sound-ev} ind-hyp-l dom =
  ≥-max-pres (λ { (PairU u₁ u₂) w max-pair →
    ≥-max-pres-fst ind-hyp-l u₁ u₂ w max-pair (max-pair→max-snd max-pair) (dom u₁ u₂ w max-pair)
  })
-} 

-- we need this for dom-weaker? 
≥-max-pres-fst-preserve-strong : ∀ { p l r : RE } { loc : ℕ } { c : Char }
  { inj : U p → U l }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {l} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max-Preserve {l} {c} (pdinstance inj sound-ev)
  → ( dom-weak : ∀ ( u₁ : U p ) ( u₂ : U r ) ( w : List Char )
        → ≥-Max {p ● r ` loc} w (PairU u₁ u₂)
        → ( v₁ : U l )
        → proj₁ (flat {l} v₁) ≢ c ∷ proj₁ (flat {p} u₁)
        → proj₁ (flat {l} v₁) ≢ []
        → (∀ {c₁ cs₁} → proj₁ (flat {l} v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c) 
        → ∃[ v₂ ] (proj₁ (flat {l ● r ` loc} (PairU v₁ v₂))) ≡ c ∷ w 
        → l ⊢ inj u₁ ≥ v₁ )
  → ≥-Max-Preserve {l ● r ` loc} {c} (pdinstance-fst (pdinstance inj sound-ev))
≥-max-pres-fst-preserve-strong {p} {l} {r} {loc} {c} {inj} {sound-ev} ind-hyp-l dom =
  ≥-max-pres (λ { (PairU u₁ u₂) w max-pair →
    ≥-max-pres-fst-strong ind-hyp-l u₁ u₂ w max-pair (max-pair→max-snd max-pair) (dom u₁ u₂ w max-pair)  
  }) -- we need a different version of ≥-max-pres-fst that requires  ∃[ v₂ ] (proj₁ (flat {l ● r ` loc} (PairU v₁ v₂))) ≡ c ∷ w  

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

-- ≥-max-pres-snd-preserve: Lift ≥-Max-Preserve through mk-snd-pdi.
-- Given ≥-Max-Preserve for the right factor pdi and evidence that pdU[l,c] is empty,
-- returns ≥-Max-Preserve for the snd pair pdi.
≥-max-pres-snd-preserve : ∀ { p l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  { e₁ : U l }
  { flat-e₁≡[] : proj₁ (flat {l} e₁) ≡ [] }
  { inj : U p → U r }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {r} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max {l} [] e₁
  → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
  → ( ¬c∷w∈l : ∀ (w : List Char) → ¬ ((c ∷ w) ∈⟦ l ⟧) )
  → ≥-Max-Preserve {l ● r ` loc} {c} (mk-snd-pdi {l} {r} {loc} {c} (e₁ , flat-[] e₁ flat-e₁≡[]) (pdinstance inj sound-ev))
≥-max-pres-snd-preserve {p} {l} {r} {ε∈l} {loc} {c} {e₁} {flat-e₁≡[]} {inj} {sound-ev} max-e₁ ind-hyp-r ¬c∷w∈l =
  ≥-max-pres (λ { u₂ w max-u₂ →
    let ¬split = λ (w₁ , (w₂ , (¬w₁≡[] , (eq , (w₁∈⟦l⟧ , w₂∈⟦r⟧))))) →
          let w₁≡c∷w₁' : ∃[ w₁' ] w₁ ≡ c ∷ w₁'
              w₁≡c∷w₁' = first-char-non-empty w w₁ w₂ ¬w₁≡[] eq
              w₁' = proj₁ w₁≡c∷w₁'
              w₁≡c∷w₁'-eq = proj₂ w₁≡c∷w₁'
              c∷w₁'∈l = subst (λ x → x ∈⟦ l ⟧) w₁≡c∷w₁'-eq w₁∈⟦l⟧
          in ¬c∷w∈l w₁' c∷w₁'∈l
    in ≥-max-pres-snd ind-hyp-r e₁ u₂ w max-e₁ max-u₂ ¬split
  })
  where
    -- first-char-non-empty: If w₁ is non-empty and w₁ ++ w₂ ≡ c ∷ w, then w₁ starts with c.
    first-char-non-empty : (w : List Char) (w₁ w₂ : List Char) → ¬ w₁ ≡ [] → w₁ ++ w₂ ≡ c ∷ w → ∃[ w₁' ] w₁ ≡ c ∷ w₁'
    first-char-non-empty w [] w₂ ¬[] eq = ⊥-elim (¬[] refl)
    first-char-non-empty w (c₁ ∷ w₁') w₂ ¬[] refl = w₁' , refl


-- ≥-max-pres-star-preserve: Lift ≥-Max-Preserve through pdinstance-star.
-- Given ≥-Max-Preserve for the inner pdi and a dom premise,
-- returns ≥-Max-Preserve for the star pdi.
≥-max-pres-star-preserve : ∀ { p r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  { inj : U p → U r }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {r} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
  → ( dom : ∀ ( u : U p ) ( us : U (r * ε∉r ` loc) ) ( w : List Char )
        → ≥-Max {p ● (r * ε∉r ` loc) ` loc} w (PairU u us)
        → ( v : U r ) → proj₁ (flat {r} v) ≢ c ∷ proj₁ (flat {p} u)
        → proj₁ (flat {r} v) ≢ []
        → (∀ {c₁ cs₁} → proj₁ (flat {r} v) ≡ c₁ ∷ cs₁ → c₁ ≡ c)
        → r ⊢ inj u > v )
  → ≥-Max-Preserve {r * ε∉r ` loc} {c} (pdinstance-star (pdinstance inj sound-ev))
≥-max-pres-star-preserve {p} {r} {ε∉r} {loc} {c} {inj} {sound-ev} ind-hyp-r dom =
  ≥-max-pres (λ { (PairU u us) w max-pair →
    ≥-max-pres-star ind-hyp-r u us w max-pair (max-pair→max-snd max-pair) (dom u us w max-pair)
  })


data ≥-Max-Preserve-List : ∀ { r : RE } { c : Char } → List (PDInstance r c) → Set where
  ≥-max-pres-nil : ∀ {r : RE } { c : Char} → ≥-Max-Preserve-List {r} {c} []
  ≥-max-pres-cons : ∀ { r : RE } { c : Char }
      → (pdi : PDInstance r c)
      → (pdis : List (PDInstance r c))
      → ≥-Max-Preserve {r} {c} pdi
      → ≥-Max-Preserve-List {r} {c} (pdi ∷ pdis)
      
¬nothing≡just : ∀ {A : Set} {x : A} → ¬ nothing ≡ just x
¬nothing≡just ()

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

head-x∷xs≡just-x : ∀ { A : Set} {x : A } { xs : List A } → head ( x ∷ xs ) ≡ just x
head-x∷xs≡just-x {A} {x} {xs} = refl 

¬Any[] : ∀ {A : Set} {P : A → Set} → ¬ Any P []
¬Any[] ()

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
head-pdU-+-right-eq : ∀ {l r : RE} {loc : ℕ} {c : Char} {pdi_r : PDInstance r c} {pdis_r : List (PDInstance r c)}
  → head (List.map pdinstance-left [] ++ List.map pdinstance-right (pdi_r ∷ pdis_r)) ≡ just (pdinstance-right pdi_r)
head-pdU-+-right-eq = refl

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

-- Ex>-sorted-first>all: First pdi of an Ex>-sorted list is > all subsequent pdis.
Ex>-sorted-first>all : ∀ {r : RE} {c : Char} {pdi : PDInstance r c} {pdis : List (PDInstance r c)}
  → Ex>-sorted (pdi ∷ pdis)
  → (pdi' : PDInstance r c) → pdi' ∈ pdis
  → r , c ⊢ pdi > pdi'
Ex>-sorted-first>all (ex>-cons _ (ex>-just pdi>pdi₂)) pdi' (here refl) = pdi>pdi₂
Ex>-sorted-first>all {r} {c} (ex>-cons sorted (ex>-just pdi>pdi₂)) pdi' (there pdi'∈pdis')
  with Ex>-sorted-first>all sorted pdi' pdi'∈pdis'
... | pdi₂>pdi' = >-pdi-trans pdi>pdi₂ pdi₂>pdi'
Ex>-sorted-first>all (ex>-cons ex>-nil ex>-nothing) pdi' ()

-- not in use
extract-mkAllEmptyU : ∀ {l} {ε∈l : ε∈ l}
  → ∃[ e₁ ] ∃[ es₁ ] ∃[ flat-e₁≡[] ] ∃[ flat-[]-es₁ ] ∃[ sorted ] (⊥ → ⊥)
extract-mkAllEmptyU {l} {ε∈l}
  with mkAllEmptyU {l} ε∈l in eq-mkAllEmptyU | mkAllEmptyU-sound {l} ε∈l | mkAllEmptyU-sorted {l} ε∈l
... | [] | [] | w = ⊥-elim (mkAllEmptyU≢[] ε∈l eq-mkAllEmptyU)
... | e₁ ∷ es₁ | flat-[] e₁ flat-e₁≡[] ∷ flat-[]-es₁ | sorted =
  e₁ , es₁ , flat-e₁≡[] , flat-[]-es₁ , sorted , λ ()

concatmap-pdinstance-snd-≡ : ∀ {l r : RE} {ε∈l : ε∈ l} {loc : ℕ} {c : Char} (pdis : List (PDInstance r c))
  → concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis
    ≡ concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x pdis)
      (zip-es-flat-[]-es {l} {ε∈l} (mkAllEmptyU {l} ε∈l) (mkAllEmptyU-sound {l} ε∈l))
concatmap-pdinstance-snd-≡ pdis = refl

-- first-char-lemma: Extract c∷cs form from non-empty list with known first char.
first-char-lemma : ∀ {c} (xs : List Char) → xs ≢ [] → (∀ {c₁ cs₁} → xs ≡ c₁ ∷ cs₁ → c₁ ≡ c) → ∃[ cs ] xs ≡ c ∷ cs
first-char-lemma [] ¬[] _ = ⊥-elim (¬[] refl)
first-char-lemma (c₁ ∷ cs₁) _ first-char = cs₁ , cong (λ x → x ∷ cs₁) (first-char refl)

-- find-recons: Extract Recons proof from Any. -- not in use?
find-recons : ∀ {A : Set} {P : A → Set} {x} {xs} → Any P xs → P x → P x
find-recons {P = P} {x} any px = px

-- dom-lemma: If inj u₁ is the first reconstruction of the first pdi in pdU[l,c],
-- and v₁ has a c-word different from c∷flat u₁, then l ⊢ inj u₁ > v₁.
-- extract-Recons: Extract the pdi and membership proof from Any (Recons v₁) pdis.
extract-Recons : ∀ {r c v₁} {pdis : List (PDInstance r c)}
  → Any (Recons {r} {c} v₁) pdis → ∃ λ pdi → pdi ∈ pdis × Recons v₁ pdi
extract-Recons (here recons-v₁) = _ , here refl , recons-v₁
extract-Recons (there v₁∈pdis) with extract-Recons v₁∈pdis
... | pdi , pdi∈ , recons-v₁ = pdi , there pdi∈ , recons-v₁

{-
-- too strong, we have a weaken version below 
-- the dom-lemma is bogus, is u₂ : U r used any where? 
dom-lemma : ∀ {p l r loc c} {inj : U p → U l} {sound-ev}
  → (pdis : List (PDInstance l c))
  → pdU[ l , c ] ≡ pdinstance inj sound-ev ∷ pdis
  → Ex>-sorted (pdinstance inj sound-ev ∷ pdis)
  → (u₁ : U p) (u₂ : U r) (w : List Char)
  → ≥-Max {p ● r ` loc} w (PairU u₁ u₂)
  → (v₁ : U l)
  → proj₁ (flat v₁) ≢ c ∷ proj₁ (flat u₁) -- ¬ |v₁| ≡ c ∷ | u₁| 
  → proj₁ (flat v₁) ≢ []                  -- ¬ |v₁| ≡ [] 
  → (∀ {c₁ cs₁} → proj₁ (flat v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c) -- head |v₁| ≡ c
  -- can we weaken dom-lemma by restricting ∃[ v₂ ] | PairU v₁ v₂ | ≡ c ∷ w ?
  --
  -- This restriction seems to help. we can make use of ≥-max-pair-fst-prefix→>: 
  --  Given ∃[ v₂ ] | PairU v₁ v₂ | ≡ c ∷ w
  --      note that v₁ is recons from inj, by pdU soundness
  --  which means (inj v₁') ≡ v₁ by soundness evidence we have
  --    |pair v₁ v₂ | ≡ c ∷ w and |pair v₁' v₂| ≡ w 
  --  Since ≥-Max {p ● r ` loc} w (PairU u₁ u₂), 
  --    by ≥-max-pair-fst-prefix→> we have p ⊢ u₁ > v₁'
  --  Since inj is ≥-Max-preserve,
  --     l ⊢ inj u₁ > inj v₁'
  → l ⊢ inj u₁ > v₁ -- not provable, what if |v₁| is a word starting with c and longer than c ∷ |u₁|,  |Pair v₁ u₂| ≢  w. Pair v₁ u₂ is not constrained by ≥-Max w (PairU (inj u₁) u₂)
dom-lemma {inj = inj} {sound-ev} [] pdU≡ sorted u₁ u₂ w max v₁ ¬eq ¬[] first-char-lemma-outer
  with first-char-lemma (proj₁ (flat v₁)) ¬[] first-char-lemma-outer
... | cs₁ , eq  with pdU-complete v₁ eq
...               | v₁∈pdU rewrite pdU≡
...                                      |  here (recons .v₁ ( w₁∈⟦p⟧ , inj∘unflatw₁∈⟦p⟧≡v₁ )) = {!!} -- no need to prove, we abandon this lemma? 
...                                      |  there v₁∈pdis  = ⊥-elim (¬Any[] v₁∈pdis)
-- since (pdi inj) is max preserve, l ⊢ max (inj u) <=> p ⊢ max u
-- we need some lemma ≥-Max (Pair u v) what properties should u and v have.


dom-lemma {inj = inj} {sound-ev} (pdi' ∷ pdis') pdU≡ sorted u₁ u₂ w max v₁ ¬eq ¬[] first-char-lemma-outer
  with first-char-lemma (proj₁ (flat v₁)) ¬[] first-char-lemma-outer
... | cs₁ , eq
  with pdU-complete v₁ eq | pdU-complete (inj u₁) (sound-ev u₁)
... | v₁∈pdU | v₁∈pdU-inj
  rewrite pdU≡
  = case v₁∈pdU of λ {
    (here recons-v₁) → {!!} ; -- no need to prove, we abandon this lemma?
    (there v₁∈pdis) →
      case v₁∈pdU-inj of λ {
        (here recons-inj-u₁) →
          case extract-Recons v₁∈pdis of λ {
            (pdi'' , pdi''∈ , recons-v₁) →
              case Ex>-sorted-first>all sorted pdi'' pdi''∈ of λ {
                (>-pdi _ _ ev'') →
                  ev'' (inj u₁) v₁ recons-inj-u₁ recons-v₁
              }
          } ;
        (there v₁∈pdis-inj) → {!!} -- no need to prove, we abandon this lemma? 
      }
  }
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


-- counter example
-- r = a + a ● b
-- c = 'a'
-- w = '"b"
-- pdU[ r , 'a' ] = [ left-pdi , right-pdi ] 
-- left pdi can only reconstruct Left 'a'
-- then 
pdU-complete-max : ∀ { r : RE  } { c : Char } { w : List Char }
  → ( u : U r )
  → ( proj₁ (flat {r} u) ≡ c ∷ w )
  → ≥-Max {r} (c ∷ w) u
  → ∃[ pdi ] ∃[ pdis ] ( pdU[ r , c ] ≡ pdi ∷ pdis ) × (Recons {r} {c} u pdi)
pdU-complete-max = {!!}



recons-cong : ∀ { r : RE } { c : Char }
   { p : PDInstance r c } { q : PDInstance r c }
   → p ≡ q
   → ( u : U r )
   → Recons {r} u p 
   → Recons {r} u q
recons-cong = {!!}    


-- dom-lemma-weak and pdU-≥-max-left-most-pres are mutually recursive .
dom-lemma-weak : ∀ {p l r loc c} {inj : U p → U l} {sound-ev}
  → (pdis : List (PDInstance l c))
  → pdU[ l , c ] ≡ pdinstance inj sound-ev ∷ pdis
  → Ex>-sorted (pdinstance inj sound-ev ∷ pdis)
  → (u₁ : U p) (u₂ : U r) (w : List Char)
  → ≥-Max {p ● r ` loc} w (PairU u₁ u₂)
  → (v₁ : U l)
  → proj₁ (flat v₁) ≢ c ∷ proj₁ (flat u₁) -- ¬ |v₁| ≡ c ∷ | u₁| 
  → proj₁ (flat v₁) ≢ []                  -- ¬ |v₁| ≡ [] 
  → (∀ {c₁ cs₁} → proj₁ (flat v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c) -- head |v₁| ≡ c
  → ∃[ v₂ ] (proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)) ≡ c ∷ w )
  → l ⊢ inj u₁ ≥ v₁
  --  Given ∃[ v₂ ] | PairU v₁ v₂ | ≡ c ∷ w
  --      note that v₁ is recons from inj, by pdU soundness
  --  which means (inj v₁') ≡ v₁ by soundness evidence we have
  --    |pair v₁ v₂ | ≡ c ∷ w and |pair v₁' v₂| ≡ w 
  --  Since ≥-Max {p ● r ` loc} w (PairU u₁ u₂), 
  --    by ≥-max-pair-fst-prefix→>2 we have p ⊢ u₁ ≥ v₁' (**)
  --  Since inj is ≥-Max-preserve, -- we need to pass this in. (***) this is not trivia. we need bidirection preserve
  --     l ⊢ inj u₁ ≥ inj v₁' i.e. l ⊢ inj u₁ ≥ v
  --  we use trichotomy of >, inj u₁ > v₁, done, inj u₁ ≡ v₁ done
  --  v₁ > inj u, i.e. inj v₁' > inj u from the ← direction of ≥-Max-preserve inj,
  --       we have v₁' is max, by ≥-max-pair-fst-prefix→>2 we have v₁' > u which leads to a contradiction 

-- this is too weak.. we have the same issue with the counter example to pdU-complete-max
-- shouldn't this be all? not really, provided we eliminate the overlapping w.
pdU-≥-max-left-most-pres : ∀ { r : RE } { c : Char }
  → {pdi : PDInstance r c}
  → head pdU[ r , c ] ≡ just pdi
  → ≥-Max-Preserve-Bd pdi


dom-lemma-weak {p} {l} {r} {loc} {c}  {inj} {sound-ev} []             pdU-lc≡pdi-inj∷[]         sorted u₁ u₂ w
  max@(≥-max .(w) (PairU .u₁ .u₂) |u₁u₂|≡w v→|v|≡w→pair-u₁u₂≥v) v₁ ¬eq ¬[] first-char-lemma-outer ( v₂ , |v₁v₂|≡c∷w )
  with first-char-lemma (proj₁ (flat v₁)) ¬[] first-char-lemma-outer
... | cs₁ , eq  with pdU-complete v₁ eq
...   | v₁∈pdU rewrite pdU-lc≡pdi-inj∷[] with v₁∈pdU
...     | there v₁∈pdis  = ⊥-elim (¬Any[] v₁∈pdis)
...     | here (recons .v₁ ( w₁∈⟦p⟧ , inj∘unflatw₁∈⟦p⟧≡v₁ )) = inju₁≥v₁
           -- unflat w₁∈⟦p⟧ is v₁'
           where
             pdi-inj-sev-max-pres :  ≥-Max-Preserve-Bd (pdinstance inj sound-ev)
             pdi-inj-sev-max-pres rewrite pdU-lc≡pdi-inj∷[] = pdU-≥-max-left-most-pres {!!} -- this hole should be easy  

             c∷|pair-unflatw₁∈⟦p⟧-v₂|≡|pairv₁v₂| : ( c ∷ (proj₁ (flat (PairU {p} {r} {loc} (unflat w₁∈⟦p⟧) v₂))))  ≡ (proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)))
             c∷|pair-unflatw₁∈⟦p⟧-v₂|≡|pairv₁v₂| =
                begin
                  c ∷ (proj₁ (flat (PairU {p} {r} {loc} (unflat w₁∈⟦p⟧) v₂)))
                ≡⟨⟩ 
                  c ∷ ((proj₁ (flat (unflat w₁∈⟦p⟧))) ++ (proj₁ (flat v₂)))
                ≡⟨⟩ 
                  (c ∷ (proj₁ (flat (unflat w₁∈⟦p⟧)))) ++ (proj₁ (flat v₂))
                ≡⟨ cong (λ x → x ++ (proj₁ (flat v₂))) (sym ( sound-ev (unflat w₁∈⟦p⟧) ) ) ⟩
                  (proj₁ (flat (inj (unflat w₁∈⟦p⟧) ))) ++ (proj₁ (flat v₂))
                ≡⟨ cong (λ x → (proj₁ (flat x)) ++ (proj₁ (flat v₂))) inj∘unflatw₁∈⟦p⟧≡v₁ ⟩ 
                  (proj₁ (flat v₁)) ++ (proj₁ (flat v₂))                                                  
                ≡⟨⟩ 
                  proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)) 
                ∎
             |pairv₁v₂|≡c∷|pair-unflatw₁∈⟦p⟧-v₂| :  proj₁ (flat (PairU {l} {r} {loc} v₁ v₂)) ≡ c ∷ (proj₁ (flat (PairU {p} {r} {loc} (unflat w₁∈⟦p⟧) v₂)))
             |pairv₁v₂|≡c∷|pair-unflatw₁∈⟦p⟧-v₂| = sym c∷|pair-unflatw₁∈⟦p⟧-v₂|≡|pairv₁v₂|

             |pair-unflatw₁∈⟦p⟧-v₂|≡w : proj₁ (flat (PairU {p} {r} {loc} (unflat w₁∈⟦p⟧) v₂)) ≡ w 
             |pair-unflatw₁∈⟦p⟧-v₂|≡w = proj₂ (Utils.∷-inj (trans (sym |pairv₁v₂|≡c∷|pair-unflatw₁∈⟦p⟧-v₂|) |v₁v₂|≡c∷w)) 

             u₁≥unflatw₁∈⟦p⟧ : p ⊢ u₁ ≥ (unflat w₁∈⟦p⟧)
             u₁≥unflatw₁∈⟦p⟧ = ≥-max-pair-fst-prefix→>2 {p} {r} {loc} u₁ u₂ (≥-max (proj₁ (flat (PairU {p} {r} {loc} u₁ u₂))) (PairU u₁ u₂) refl prf₁)  (unflat w₁∈⟦p⟧) v₂ prf₂ 
               where
                 prf₁ : ∀ (v : U (p ● r ` loc))
                      → proj₁ (flat v) ≡ proj₁ (flat (PairU {p} {r} {loc} u₁ u₂))
                      → (p ● r ` loc) ⊢ PairU u₁ u₂ ≥ v
                 prf₁ rewrite  |u₁u₂|≡w = v→|v|≡w→pair-u₁u₂≥v
                 prf₂ : proj₁ (flat (PairU {p} {r} {loc} (unflat w₁∈⟦p⟧) v₂)) ≡ proj₁ (flat (PairU {p} {r} {loc} u₁ u₂)) 
                 prf₂ rewrite  |u₁u₂|≡w  =  |pair-unflatw₁∈⟦p⟧-v₂|≡w
                 max-u₁ :  ≥-Max {p} (proj₁ (flat u₁)) u₁ 
                 max-u₁ = ≥-max-pair-fst-prefix→>3 {p} {r} {loc} u₁ u₂ max-pair-u₁u₂ 
                   where
                     v→|v|≡|u₁u₂|→pair-u₁u₂≥v : (v : U (p ● r ` loc))
                                              → proj₁ (flat v) ≡ proj₁ (flat (PairU  {p} {r} {loc} u₁ u₂))
                                              → (p ● r ` loc) ⊢ PairU u₁ u₂ ≥ v
                     v→|v|≡|u₁u₂|→pair-u₁u₂≥v  rewrite |u₁u₂|≡w =  v→|v|≡w→pair-u₁u₂≥v 
                     max-pair-u₁u₂ : ≥-Max (proj₁ (flat (PairU {p} {r} {loc} u₁ u₂))) (PairU u₁ u₂) 
                     max-pair-u₁u₂  = ≥-max (proj₁ (flat (PairU {p} {r} {loc} u₁ u₂))) (PairU u₁ u₂) refl v→|v|≡|u₁u₂|→pair-u₁u₂≥v 

             inju₁≥v₁ : l ⊢ inj u₁ ≥ v₁
             inju₁≥v₁ with pdi-inj-sev-max-pres
             ... | ≥-max-pres-bd u→w→maxwu→max-c∷w-inj-u u→w→max-c∷w-inj-u→maxwu  with >-trichotomy (inj u₁) v₁
             ...      | inj₁ inj-u₁>v₁        = inj₁ inj-u₁>v₁
             ...      | inj₂ (inj₂ inj-u₁≡v₁) = inj₂ inj-u₁≡v₁
             ...      | inj₂ (inj₁ v₁>inj-u₁) rewrite (sym inj∘unflatw₁∈⟦p⟧≡v₁) = prf -- we need a contradiction
                        -- the idea: find t₁, where |v₁|≡|t₁| and max t₁ (we need a wellfoundedness lemma of >) then  we have t₁≥v₁>inj-u₁
                        -- how do we know t₁ is recons from the same inj? we don't have to ??  (not sure #1)
                        -- by completeness of pdU[ r , c ], there exist inj' and t₁' such that t₁ ≡ inj' t₁'
                        -- is inj' leftmost? let's assume so (not sure #2)
                        -- by  u→w→max-c∷w-inj-u→maxwu  max-t₁ we have max-t₁' (here)
                        -- by defn of ≥-Max, we have max |t₁'v₂| (pair t₁' v₂)
                        -- by ≥-max-pair-fst-prefix→>2  max (pair t₁' v₂), we have p ⊢ t₁' > u₁
                        -- by ≥-max-pair-fst-prefix→>2  max (pair u₁ u₂), we have p ⊢ u₁ > t₁'
                        -- question: is inj' same as inj? if so, the above will be easier.


                        -- new idea:   (pdinstance {p} {l} {c} inj sev) ∈ pdU[ l , c] , p is an Efn,
                        --                  ≥-Max (u : p , u' : r), we have u > v for any |v, v'|≡|u, u'|,
                        --                  we have inj u > inj v,
                        --                  for all v : U p, when u is Max, is that true for all Efn? because Efn is of shape ε ● r, or ε, inj 
                        where
                          t₁-max-|v₁|-t₁ : ∃[ t₁ ] ≥-Max {l} (proj₁ (flat v₁)) t₁                  -- found t₁ which is amx 
                          t₁-max-|v₁|-t₁ = >-wellfounded {l} {proj₁ (flat v₁)} (proj₂ (flat v₁) )

                                                            
                          prf :  l ⊢ inj u₁ > inj (unflat w₁∈⟦p⟧) ⊎ inj u₁ ≡ inj (unflat w₁∈⟦p⟧)   -- inj (unflat w₁∈⟦p⟧ ≡ v₁
                          prf with t₁-max-|v₁|-t₁
                          ... | t₁ , max-|v₁|-t₁@(≥-max |v₁| .t₁ |t₁|≡|v₁| t₂→|t₂|≡|v₁|→t₁≥t₂) =  inner -- how do I know |v₁|≡c∷w₁' ? because inj∘unflatw₁∈⟦p⟧≡v₁
                              -- we need to find out that t₁ is reconstructible from inj
                              where
                                
                                |t₁|≡c∷w₁ : proj₁ (flat t₁) ≡ c ∷ (proj₁ (flat (unflat w₁∈⟦p⟧)))
                                |t₁|≡c∷w₁ =
                                  begin
                                    proj₁ (flat t₁)
                                  ≡⟨  |t₁|≡|v₁| ⟩
                                    proj₁ (flat v₁)
                                  ≡⟨ cong (λ x → (proj₁ (flat x))) (sym inj∘unflatw₁∈⟦p⟧≡v₁) ⟩ 
                                    proj₁ (flat (inj (unflat w₁∈⟦p⟧)))
                                  ≡⟨ sound-ev (unflat w₁∈⟦p⟧) ⟩ 
                                    c ∷ (proj₁ (flat (unflat w₁∈⟦p⟧)))
                                  ∎
                                max-c∷w₁-t₁ : ≥-Max (c ∷ Product.proj₁ (flat (unflat w₁∈⟦p⟧))) t₁
                                max-c∷w₁-t₁ rewrite  sym inj∘unflatw₁∈⟦p⟧≡v₁ |  sound-ev (unflat w₁∈⟦p⟧) = ≥-max (c ∷ Product.proj₁ (flat (unflat w₁∈⟦p⟧))) t₁ |t₁|≡|v₁|
                                                                                                                        t₂→|t₂|≡|v₁|→t₁≥t₂ 
                                ∃qdi∃qdispdU-l-c≡qdi∷qdis×recons-l-t₁-qdi : ∃[ qdi ] ∃[ qdis ] ( pdU[ l , c ] ≡ qdi ∷ qdis ) × (Recons {l} {c} t₁ qdi)
                                ∃qdi∃qdispdU-l-c≡qdi∷qdis×recons-l-t₁-qdi  = pdU-complete-max t₁  |t₁|≡c∷w₁ max-c∷w₁-t₁ --  pdU-complete-max is not provable.

                                inner : l ⊢ inj u₁ > inj (unflat w₁∈⟦p⟧) ⊎ inj u₁ ≡ inj (unflat w₁∈⟦p⟧)
                                inner with ∃qdi∃qdispdU-l-c≡qdi∷qdis×recons-l-t₁-qdi
                                ... | qdi@(pdinstance {p'} .{l} .{c} inj' sound-ev') , qdis , pdu-l-c≡qdi∷qdis , recons-t₁-qdi  with recons-cong (sym (proj₁ ( ∷-injective (trans ( sym pdU-lc≡pdi-inj∷[] ) pdu-l-c≡qdi∷qdis) ) ) ) t₁ recons-t₁-qdi   -- we use pdu-l-c≡qdi∷qdis to derive qdi ≡ pdi

                                ...      | recons .t₁ ( w₂∈⟦p⟧ , inj∘unflatw₂∈⟦p⟧≡t₁ )   = {!!}
                                  where
                                    -- unflat w₂∈⟦p⟧ = t₁'
                                    -- so that we have max t₁'
                                    |t₁|≡c∷|unflat-w₂∈⟦p⟧| : proj₁ (flat t₁) ≡ c ∷ proj₁ (flat (unflat w₂∈⟦p⟧))
                                    |t₁|≡c∷|unflat-w₂∈⟦p⟧| rewrite sym (sound-ev (unflat w₂∈⟦p⟧)) |  inj∘unflatw₂∈⟦p⟧≡t₁  = refl

                                    v→|v|≡c∷|t₁'|→t₁≥v : (v : U l)
                                       → proj₁ (flat v) ≡ c ∷ proj₁ (flat (unflat w₂∈⟦p⟧))
                                       → l ⊢ t₁ ≥ v
                                    v→|v|≡c∷|t₁'|→t₁≥v v |v|≡c∷|unflat-w₂∈⟦p⟧| = t₂→|t₂|≡|v₁|→t₁≥t₂ v (trans |v|≡c∷|unflat-w₂∈⟦p⟧| (trans (sym  |t₁|≡c∷|unflat-w₂∈⟦p⟧| ) |t₁|≡|v₁|  )  )  
                                    
                                    max-c∷w₂-inj-unflat-w₂∈⟦p⟧ : ≥-Max (c ∷ proj₁ (flat (unflat w₂∈⟦p⟧))) (inj (unflat w₂∈⟦p⟧)) 
                                    max-c∷w₂-inj-unflat-w₂∈⟦p⟧ rewrite  inj∘unflatw₂∈⟦p⟧≡t₁  = ≥-max (c ∷ proj₁ (flat (unflat w₂∈⟦p⟧))) t₁  |t₁|≡c∷|unflat-w₂∈⟦p⟧| v→|v|≡c∷|t₁'|→t₁≥v
                                                 

                                    max-unflat-w₂∈⟦p⟧ : ≥-Max {p} (proj₁ (flat (unflat w₂∈⟦p⟧))) (unflat w₂∈⟦p⟧)
                                    max-unflat-w₂∈⟦p⟧ = u→w→max-c∷w-inj-u→maxwu  (unflat w₂∈⟦p⟧)  (proj₁ (flat (unflat w₂∈⟦p⟧)))  max-c∷w₂-inj-unflat-w₂∈⟦p⟧

                                    ev : (v : U (p ● r ` loc))
                                       → proj₁ (flat v) ≡ (proj₁ (flat (unflat w₂∈⟦p⟧))) ++ (proj₁ (flat v₂)) 
                                       → (p ● r ` loc) ⊢ PairU (unflat w₂∈⟦p⟧) v₂ ≥ v
                                    ev (PairU {p} {r} {loc} v₃ v₄)  |v₃v₄|≡|t₁'|++|v₂| = {!!}  -- only when (unflat w₂∈⟦p⟧) is not null

                                    max-|t₁'v₂|-pair-t₁'-v₂ : ≥-Max {p ● r ` loc } (proj₁ (flat (PairU {p} {r} {loc} ( unflat w₂∈⟦p⟧ ) v₂))) (PairU ( unflat w₂∈⟦p⟧ ) v₂)
                                    max-|t₁'v₂|-pair-t₁'-v₂ = ≥-max (flat (unflat w₂∈⟦p⟧) .Product.proj₁ ++ flat v₂ .Product.proj₁) (PairU (unflat w₂∈⟦p⟧) v₂) refl ev 
                                                                


                                    -- ... | ≥-max-pres-bd u→w→maxwu→max-c∷w-inj-u u→w→max-c∷w-inj-u→maxwu  with u→w→maxwu→max-c∷w-inj-u u₁ (proj₁ (flat u₁)) max-u₁ 
                                    -- ...      | ≥-max c∷|u₁| inju₁ _ v→|v|≡c∷|u₁|→inju₁≥v =  v→|v|≡c∷|u₁|→inju₁≥v v₁ {!!}   -- |v₁|≡ c∷|u₁| how do get this? we only have |v₁v₂|≡c∷w≡c∷|u₁u₂|, can we derive another property


dom-lemma-weak {p} {l} {r} {loc} {c} {inj} {sound-ev}  (pdi' ∷ pdis') pdU-lc≡pdi-inj∷pdi'∷pdis' sorted u₁ u₂ w max v₁ ¬eq ¬[] first-char-lemma-outer ( v₂ , |v₁v₂|≡c∷w ) =  {!!} 



pdU-≥-max-left-most-pres {ε} {c} {pdi} eq = ⊥-elim (¬nothing≡just eq)
{-
pdU-≥-max-left-most-pres {$ c' ` loc} {c} {pdinstance inj sound-ev} eq with c' Char.≟ c
... | no ¬c'≡c
  rewrite pdU[$c]≡[] ¬c'≡c
  = ⊥-elim (¬nothing≡just eq)
... | yes refl
  with just-injective eq
... | refl = ≥-max-pres (λ { EmptyU w (≥-max _ _ flat-empty≡w μ) →
    ≥-max (c ∷ w) (mkinjLetter {c'} {loc} EmptyU)
      (trans (mkinjLetterSound {c'} {loc} EmptyU) (cong (c ∷_) flat-empty≡w))
      (λ { (LetterU .c') flat-letter≡c∷w → inj₂ refl })
  })

pdU-≥-max-left-most-pres {l + r ` loc} {c} {pdi} eq =
  helper pdU[ l , c ] pdU[ r , c ] refl refl eq
  where
    helper : (pdU-l : List (PDInstance l c)) → (pdU-r : List (PDInstance r c))
      → pdU[ l , c ] ≡ pdU-l
      → pdU[ r , c ] ≡ pdU-r
      → head (List.map pdinstance-left pdU-l ++ List.map pdinstance-right pdU-r) ≡ just pdi
      → ≥-Max-Preserve pdi
    helper (pdi_l ∷ pdis_l) pdU-r pdU-l≡ pdU-r≡ eq =
      subst (λ x → ≥-Max-Preserve x) (just-injective eq)
        (≥-max-pres-left pdi_l (pdU-≥-max-left-most-pres {l} {c} (cong head pdU-l≡)) )
    helper [] [] pdU-l≡ pdU-r≡ eq =
      ⊥-elim (¬nothing≡just eq)
    helper [] (pdi_r ∷ pdis_r) pdU-l≡ pdU-r≡ eq =
      subst (λ x → ≥-Max-Preserve x) (sym (head-pdU-+-right eq))
      (≥-max-pres-right-direct (pdU-≥-max-left-most-pres {r} {c} (cong head pdU-r≡)) (λ w → pdU≡[]→¬c∷w∈l {l} {c} {w} pdU-l≡))

pdU-≥-max-left-most-pres {l ● r ` loc} {c} {pdi} eq with ε∈? l in ε∈?l-eq
... | no ¬ε∈l =
  helper-no ¬ε∈l pdU[ l , c ] refl eq
  where
    helper-no : (¬ε∈l : ¬ ε∈ l) → (pdU-l : List (PDInstance l c))
      → pdU[ l , c ] ≡ pdU-l
      → head (List.map pdinstance-fst pdU-l) ≡ just pdi
      → ≥-Max-Preserve pdi
    helper-no ¬ε∈l [] _ eq = ⊥-elim (¬nothing≡just eq)
    helper-no ¬ε∈l (pdinstance {p} inj sound-ev ∷ pdis_l) pdU-l≡ eq =
      subst (λ x → ≥-Max-Preserve x) (just-injective eq)
        (≥-max-pres-fst-preserve-strong
          (pdU-≥-max-left-most-pres {l} {c} {pdinstance {p} inj sound-ev} (cong head pdU-l≡))
          (dom-lemma-weak pdis_l pdU-l≡ (subst (λ x → Ex>-sorted x) pdU-l≡  (pdU-sorted {l} {c})))
          )      
        {- (≥-max-pres-fst-preserve-strong
          (pdU-≥-max-left-most-pres {l} {c} {pdinstance {p} inj sound-ev} (cong head pdU-l≡))
          (dom-lemma-weak pdis_l pdU-l≡ (subst (λ x → Ex>-sorted x) pdU-l≡  (pdU-sorted {l} {c})))
          ) -}
... | yes ε∈l = 
  helper-yes {- ε∈l -}  pdU[ l , c ] pdU[ r , c ] refl refl eq
  where
    helper-yes : {- (ε∈l' : ε∈ l) → -}
        (pdU-l : List (PDInstance l c))
      → (pdU-r : List (PDInstance r c))
      → pdU[ l , c ] ≡ pdU-l
      → pdU[ r , c ] ≡ pdU-r
      → head (List.map pdinstance-fst pdU-l ++ concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU-r) ≡ just pdi
      → ≥-Max-Preserve pdi

    helper-yes {- ε∈l' -} (pdinstance inj sound-ev ∷ pdis_l) pdU-r pdU-l≡ pdU-r≡ eq =
      subst (λ x → ≥-Max-Preserve x) (just-injective eq)
        (≥-max-pres-fst-preserve-strong
          (pdU-≥-max-left-most-pres {l} {c} {pdinstance inj sound-ev} (cong head pdU-l≡))
          (λ u₁ u₂ w max-pair v₁ ¬eq ¬[] first-char → {!!}))

    helper-yes {- ε∈l' -} [] [] pdU-l≡ pdU-r≡ eq =
      ⊥-elim (¬nothing≡just (trans (sym (cong head (concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c}))) eq))

    helper-yes {- ε∈l' -}  [] (pdinstance inj sound-ev ∷ pdis_r) pdU-l≡ pdU-r≡ eq
      rewrite concatmap-pdinstance-snd-≡ {l} {r} {ε∈l} {loc} {c} (pdinstance inj sound-ev ∷ pdis_r)
      with mkAllEmptyU {l}  ε∈l in eq-mkAllEmptyU | mkAllEmptyU-sound  {l} ε∈l | mkAllEmptyU-sorted {l}  ε∈l
    ... | e₁ ∷ es₁ |  flat-[] e₁ flat-e₁≡[] ∷ flat-[]-es₁ | sorted  =
        subst (λ x → ≥-Max-Preserve x) (just-injective eq)
          (≥-max-pres-snd-preserve
            (≥-max [] e₁ flat-e₁≡[]
              (λ v flat-v≡[] →
                >-sorted-first≥all sorted v
                (subst (λ xs → v ∈ xs) eq-mkAllEmptyU
                (mkAllEmptyU-complete ε∈l v (flat-[] v flat-v≡[])))))
            (pdU-≥-max-left-most-pres {r} {c} {pdinstance inj sound-ev} (cong head pdU-r≡))
            (λ w → pdU≡[]→¬c∷w∈l {l} {c} {w} pdU-l≡)) 


pdU-≥-max-left-most-pres {r * ε∉r ` loc} {c} {pdi} eq
  with pdU[ r , c ]
... | [] = ⊥-elim (¬nothing≡just eq)
... | pdi_r ∷ pdis_r = {!!}

-} 
{-
  with pdU-≥-max-left-most-pres {r} {c} refl
... | ind-hyp-r =
  subst (λ x → ≥-Max-Preserve x) (sym (just-injective eq))
    (≥-max-pres-star-preserve ind-hyp-r (λ u us w max-pair v ¬eq ¬[] first-char → {!!}))
-}    
```

Let me give a correct counterexample.

We need two trees u and v both flattening to c ∷ w,
reconstructed by pdis where the one for u is to the right of the one for v.

Consider r = ($'a' ● $'b') + ($'a' ● $'b'), c = 'a', w = "b".

Then there are two pdis in pdU[ r , 'a' ],
both reconstructing the same (or isomorphic) PairU trees.

Let u be the tree from the right pdi and v from the left pdi.
u is maximal (only tree for "ab"), but pdi (right) is after qdi (left).

So no suffix pdis with (pdi ∷ pdis) ∈ tails pdU can contain qdi.



```agda

head-parseAll-is-max : ∀ { r : RE } { w : List Char }
  → ( u : U r )
  → just u ≡ head parseAll[ r , w ]
  → ≥-Max w u
head-parseAll-is-max = {!!}   


_∈?⟦_⟧ : ( w : List Char ) → ( r : RE ) → Dec ( w ∈⟦ r ⟧ )
_∈?⟦_⟧ [] ε = yes ε
_∈?⟦_⟧ [] (r * ε∉r ` loc) = yes (((r ● r * ε∉r ` loc ` loc) +L ε) *)
_∈?⟦_⟧ [] ($ _ ` _) = no λ ()
_∈?⟦_⟧ [] (l ● r ` loc ) with [] ∈?⟦ l ⟧ | [] ∈?⟦ r ⟧ 
... | yes []∈⟦l⟧ | yes []∈⟦r⟧ = yes ([]∈⟦l⟧ ● []∈⟦r⟧ ⧺ refl)
... | no ¬[]∈⟦l⟧ | _          = no ¬[]∈⟦l●r⟧ 
  where
    ¬[]∈⟦l●r⟧ : ¬ ([] ∈⟦ l ● r ` loc ⟧)
    ¬[]∈⟦l●r⟧ (_●_⧺_ {xs} {ys} {[]} xs∈⟦l⟧ ys∈⟦r⟧ xs++ys≡[] ) rewrite (++-conicalˡ xs ys xs++ys≡[])  = ¬[]∈⟦l⟧ xs∈⟦l⟧ 
... | _          |  no ¬[]∈⟦r⟧ = no ¬[]∈⟦l●r⟧
  where
    ¬[]∈⟦l●r⟧ : ¬ ([] ∈⟦ l ● r ` loc ⟧)
    ¬[]∈⟦l●r⟧ (_●_⧺_ {xs} {ys} {[]} xs∈⟦l⟧ ys∈⟦r⟧ xs++ys≡[] ) rewrite (++-conicalʳ xs ys xs++ys≡[])  = ¬[]∈⟦r⟧ ys∈⟦r⟧
_∈?⟦_⟧ (c ∷ w) ε  = no λ () 
    
_∈?⟦_⟧ (c ∷ []) ($ c' ` loc) with c Char.≟ c'
... | yes c≡c' rewrite c≡c' = yes ($ c')
... | no ¬c≡c' = no ¬c∷[]∈⟦c'⟧
  where
    ¬c∷[]∈⟦c'⟧ : ¬ ( (c ∷ []) ∈⟦ $ c' ` loc ⟧ )
    ¬c∷[]∈⟦c'⟧ ($ .(c')) = ¬c≡c' refl 
_∈?⟦_⟧ (c ∷ d ∷ _ ) ($ c' ` loc)  = no λ () 

_∈?⟦_⟧ w (l + r ` loc ) with w ∈?⟦ l ⟧
... | yes w∈⟦l⟧ = yes (r +L w∈⟦l⟧)
... | no ¬w∈⟦l⟧ with w ∈?⟦ r ⟧
...              | yes w∈⟦r⟧ = yes (l +R w∈⟦r⟧)
...              | no  ¬w∈⟦r⟧ = no ¬w∈⟦l+r⟧
  where
    ¬w∈⟦l+r⟧ : ¬ (w ∈⟦ l + r ` loc ⟧)
    ¬w∈⟦l+r⟧ (r +L w∈⟦l⟧ ) = ¬w∈⟦l⟧ w∈⟦l⟧
    ¬w∈⟦l+r⟧ (l +R w∈⟦r⟧ ) = ¬w∈⟦r⟧ w∈⟦r⟧


_∈?⟦_⟧ (c ∷ w) (l ● r ` loc ) with ε∈? l
... | yes ε∈l = {!!}
... | no ¬ε∈l = {!!} 

max-is-head-parseAll : ∀ { r : RE } { w : List Char }
  → ( u : U r )
  → ≥-Max w u
  → just u ≡ head parseAll[ r , w ] 
max-is-head-parseAll = {!!}


first-inhabit : ∀ { r : RE } { c : Char } { w : List Char } → List (PDInstance r c) → Maybe (PDInstance r c)
first-inhabit {r} {c} {w} [] = nothing
first-inhabit {r} {c} {w} ((pdinstance {p} .{r} .{c} inj sev) ∷ pdis )
  with w ∈?⟦ p ⟧
... | no ¬w∈⟦p⟧ = first-inhabit {r} {c} {w} pdis
... | yes w∈⟦p⟧ = just (pdinstance {p} {r} {c} inj sev)


{-
first-inhahib-pdU-max-pres : ∀ { p r : RE } { c : Char } { inj : U p → U r }
   { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
   → just (pdinstance {p} {r} {c} inj sev)  pdU[ r , c ] 
-}



data ≥-Max-Preserve-Local : ∀ { r : RE } { c : Char } → PDInstance r c → Set where
  ≥-max-pres-local : ∀ { p r : RE } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ≥-Max {p} (proj₁ (flat u)) u
      → ( v : U p ) 
      → proj₁ (flat u) ≡ proj₁ (flat v)
      → r ⊢ inj u ≥ inj v ) 
    → ≥-Max-Preserve-Local {r} {c} (pdinstance inj sound-ev)



≥-Max-Preserve-Local-map-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdis : List (PDInstance l c ))
  → All (≥-Max-Preserve-Local {l} {c}) pdis
  → All (≥-Max-Preserve-Local {l + r ` loc} {c}) (List.map pdinstance-left pdis)
≥-Max-Preserve-Local-map-left {l} {r} {loc} {c} [] [] = []
≥-Max-Preserve-Local-map-left {l} {r} {loc} {c} ((pdinstance {p} .{l} .{c} inj sound-ev) ∷ pdis ) ((≥-max-pres-local u→max-u→v→|u|≡|v|→inju≥injv) ∷ pxs ) = ≥-max-pres-local ev ∷  ≥-Max-Preserve-Local-map-left pdis pxs  
  where    
    ev : (u : U p)
       → ≥-Max (proj₁ (flat u)) u
       → (v : U p)
       → proj₁ (flat u) ≡ proj₁ (flat v)
       → (l + r ` loc) ⊢ LeftU (inj u) ≥ LeftU (inj v)
    ev u max-u@(≥-max .{p} w .(u) |u|≡w v→|v|≡w→u≥v)  v |u|≡|v| with u→max-u→v→|u|≡|v|→inju≥injv u max-u v |u|≡|v|
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
≥-Max-Preserve-Local-map-right {l} {r} {loc} {c} ((pdinstance {p} .{r} .{c} inj sound-ev) ∷ pdis ) ((≥-max-pres-local u→max-u→v→|u|≡|v|→inju≥injv) ∷ pxs ) = ≥-max-pres-local ev ∷  ≥-Max-Preserve-Local-map-right pdis pxs  
  where    
    ev : (u : U p)
       → ≥-Max (proj₁ (flat u)) u
       → (v : U p)
       → proj₁ (flat u) ≡ proj₁ (flat v)
       → (l + r ` loc) ⊢ RightU (inj u) ≥ RightU (inj v)
    ev u max-u@(≥-max .{p} w .(u) |u|≡w v→|v|≡w→u≥v)  v |u|≡|v| with u→max-u→v→|u|≡|v|→inju≥injv u max-u v |u|≡|v|
    ... | inj₂ inju≡injv = inj₂ (cong RightU inju≡injv)
    ... | inj₁ inju>injv = inj₁ (bne (len>0-inj u) (len>0-inj v) (choice-rr inju>injv) )
      where
        len>0-inj : ∀ (x : U p ) → length (proj₁ (flat {r} (inj x))) Nat.> 0
        len>0-inj x rewrite sound-ev x = Nat.s≤s Nat.z≤n


≥-Max-Preserve-Local-inc-map-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdis : List (PDInstance l c ) )
  → All (≥-Max-Preserve-Local {l} {c}) pdis
  → All (≥-Max-Preserve-Local {l ● r ` loc} {c}) (List.map (pdinstance-fst {l} {r} {loc} {c}) pdis)
≥-Max-Preserve-Local-inc-map-fst [] [] = []
≥-Max-Preserve-Local-inc-map-fst {l} {r} {loc} {c} ((pdinstance {p} .{l} .{c}  inj sound-ev) ∷ pdis) ((≥-max-pres-local u→max-u→v→|u|≡|v|→inju≥injv) ∷ pxs ) =  ≥-max-pres-local ev ∷ ≥-Max-Preserve-Local-inc-map-fst pdis pxs
  where
    injFst : U (p ● r ` loc)   → U (l ● r ` loc )
    injFst = mkinjFst inj
  
    ev : (u : U (p ● r ` loc))
      → ≥-Max (Product.proj₁ (flat u)) u
      → (v : U (p ● r ` loc))
      → Product.proj₁ (flat u) ≡ Product.proj₁ (flat v)
      →  (l ● r ` loc) ⊢ injFst u ≥ injFst v
    ev (PairU u₁ u₂) max-pair-u₁u₂@(≥-max {.p ● .r ` loc} w (PairU .u₁ .u₂) |u₁u₂|≡w v₁v₂→|v₁v₂|≡w→u₁u₂≥v₁v₂) (PairU v₁ v₂) |u₁u₂|≡|v₁v₂| with v₁v₂→|v₁v₂|≡w→u₁u₂≥v₁v₂  (PairU v₁ v₂) (trans (sym |u₁u₂|≡|v₁v₂|)  |u₁u₂|≡w)
    ... | inj₂ u₁u₂≡v₁v₂  = inj₂ pair-inj-u₁-u₂≡pair-inj-v₁-v₂
      where
        pair-inj-u₁-u₂≡pair-inj-v₁-v₂ : PairU {l} {r} {loc} (inj u₁) u₂ ≡ PairU (inj v₁) v₂
        pair-inj-u₁-u₂≡pair-inj-v₁-v₂ =
          begin
             PairU (inj u₁) u₂
          ≡⟨ cong (λ x → (PairU (inj x) u₂ )) (proj₁ (inv-pairU u₁ u₂ v₁ v₂ u₁u₂≡v₁v₂)) ⟩
             PairU (inj v₁) u₂
          ≡⟨ cong (λ x → (PairU (inj v₁) x )) (proj₂ (inv-pairU u₁ u₂ v₁ v₂ u₁u₂≡v₁v₂)) ⟩
             PairU (inj v₁) v₂
          ∎
    ... | inj₁ u₁u₂>v₁v₂@(bne len|u₁u₂|>0 len|v₁v₂|>0 (seq₁ u₁>v₁)) = inj₁ (bne {!!} {!!} {!!} )
        -- what we can apply ?
        -- Goal: (l ● r ` loc₁) ⊢ PairU (inj u₁) u₂ >ⁱ PairU (inj v₁) v₂
    ... | inj₁ u₁u₂>v₁v₂@(be len|u₁u₂|≡0 len|v₁v₂|≡0 (seq₁ u₁>v₁)) = inj₁ (bne {!!} {!!} {!!} ) -- |u₁|≡|v₁|≡[] , we can apply  u→max-u→v→|u|≡|v|→inju≥injv
      -- either way it must be bne here.
      -- if |u₁|≡|v₁|, we can apply ? ?
    ... | inj₁ u₁u₂>v₁v₂@(lne len|u₁u₂|>0 len|v₁v₂|≡0) = {!!} -- what here? 
    

pdU-preseve-local : ∀ { r : RE } { c : Char }
  → All ≥-Max-Preserve-Local pdU[ r , c ] 
pdU-preseve-local {$ c ` loc} {c'} with c Char.≟ c'
... | no ¬c≡c' = [] 
... | yes c≡c' rewrite c≡c'  = (≥-max-pres-local ev ) ∷ []
  where
    ev : (u : U ε)
       → ≥-Max (proj₁ (flat u)) u
       → (v : U ε)
       → proj₁ (flat u) ≡ proj₁ (flat v)
       → ($ c' ` loc) ⊢ mkinjLetter u ≥ mkinjLetter v
    ev EmptyU max-empty EmptyU refl = inj₂ refl        
pdU-preseve-local {l + r  ` loc} {c} = all-concat (≥-Max-Preserve-Local-map-left pdU[ l , c ] ind-hyp-l ) (≥-Max-Preserve-Local-map-right pdU[ r , c ] ind-hyp-r ) 
  where
    ind-hyp-l : All ≥-Max-Preserve-Local pdU[ l , c ]
    ind-hyp-l = pdU-preseve-local {l} {c}
    ind-hyp-r : All ≥-Max-Preserve-Local pdU[ r , c ]
    ind-hyp-r = pdU-preseve-local {r} {c}
pdU-preseve-local {l ● r  ` loc} {c} with ε∈? l 
... | no ¬ε∈l =  ≥-Max-Preserve-Local-inc-map-fst pdU[ l , c ] ind-hyp-l 
  where
    ind-hyp-l : All ≥-Max-Preserve-Local pdU[ l , c ]
    ind-hyp-l = pdU-preseve-local {l} {c}
    


```
