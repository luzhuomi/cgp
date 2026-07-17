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
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ; mkinjSndSoundEv ; 
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
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ; length-++ ; ++-assoc ; ∷-injective ; ≡-dec )


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

```



```agda

{-
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
pdU-preseve-local {r * ε∉r ` loc} {c} = {!!} 
```
