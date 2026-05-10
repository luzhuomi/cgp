```agda
{-# OPTIONS --rewriting  #-}
-- {-# OPTIONS --rewriting --allow-unsolved-metas #-}
module cgp.lnegen.MaxLen where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ¬≡[]→length>0 ; ¬≡0→>0 ; length≡0→[] ; n≡0→¬n>0 
 )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; unListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ) 

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
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ; length-++ )


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
data ≥-Max : ∀ { r : RE } → ℕ → U r  → Set where 
  ≥-max : ∀ { r : RE }
        → ( n : ℕ )
        → ( u : U r )
        → length (proj₁ (flat u)) Nat.≤ n
        → ( ( v : U r )
          → length ( proj₁ (flat v)) Nat.≤ n  
          → r ⊢ u ≥ v )
        → ≥-Max {r} n u

-- each partial derivative p is unique
-- inj is ≥-Max-Preserve is given an u which is max, and another v,
-- we must have inj u ≥ inj v 
data ≥-Max-Preserve : ∀ { r : RE } { n : ℕ } { c : Char } → PDInstance r c → Set where
  ≥-max-pres : ∀ { p r : RE } { n : ℕ }  { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ≥-Max n u 
      → ( v : U p )
      → ( length ( proj₁ (flat v)) Nat.≤ n )
      → r ⊢ inj u ≥ inj v ) -- local max w.r.t to the inj
    → ≥-Max-Preserve {r} {suc n} {c} (pdinstance inj sound-ev)

-- inj is ≥-Max-pdi if we fix a particular parse tree u,
-- inj u ≥ inj' u for any other injection inj'

-- looks like ex≥  ?

data _,_⊢_>_ : ∀ { r : RE } { c : Char } → PDInstance r c → PDInstance r c → Set where
  >-pdi : 

data ≥-Max-PDInstance : ∀ {r : RE } { n : ℕ } { c : Char } → PDInstance r c → Set where
  ≥-max-pdi : ∀ { p r : RE } { n ∶ ℕ } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ≥-Max n u
      → ( v : U p )
      → ( length ( proj₁ (flat v)) Nat.≤ n ) 


≥-max-pair-inv : ∀ { l r : RE } { loc : ℕ } { n : ℕ } { c : Char }
  → ( u : U l )
  → ( v : U r )
  → ≥-Max n (PairU {l} {r} {loc} u v)
  → ≥-Max (n ∸ length (proj₁ (flat v))) u × ≥-Max (n ∸ length (proj₁ (flat u))) v
≥-max-pair-inv {l} {r} {loc} {n} {c} u v (≥-max .n (PairU .u .v) len|pair-u-v|≤n pair-u'-v'→|u'v'|≤n→uv≥u'v') =
  ≥-max (n ∸ length (proj₁ (flat v))) u len-u≤n∸len-v ev₁ ,
  ≥-max (n ∸ length (proj₁ (flat u))) v len-v≤n∸len-u ev₂
  where
    flat-pairU-proj₁ : (u' : U l) (v' : U r) → proj₁ (flat (PairU {l} {r} {loc} u' v')) ≡ proj₁ (flat u') ++ proj₁ (flat v')
    flat-pairU-proj₁ u' v' with flat u' | flat v'
    ... | xs , _ | ys , _ = refl

    len|uv|≡|u|+|v| : length (proj₁ (flat (PairU {l} {r} {loc} u v))) ≡ (length (proj₁ (flat u)) + length (proj₁ (flat v)))
    len|uv|≡|u|+|v| = trans (cong length (flat-pairU-proj₁ u v)) (length-++ (proj₁ (flat u)) {proj₁ (flat v)})

    len|pair-u-v|≡n : length (proj₁ (flat u)) + length (proj₁ (flat v)) ≤ n
    len|pair-u-v|≡n = subst (λ k → k ≤ n) len|uv|≡|u|+|v| len|pair-u-v|≤n

    len-v≤n : length (proj₁ (flat v)) ≤ n
    len-v≤n = ≤-trans (m≤n+m (length (proj₁ (flat v))) (length (proj₁ (flat u)))) len|pair-u-v|≡n

    len-u≤n : length (proj₁ (flat u)) ≤ n
    len-u≤n = ≤-trans (m≤m+n (length (proj₁ (flat u))) (length (proj₁ (flat v)))) len|pair-u-v|≡n

    len-u≤n∸len-v : length (proj₁ (flat u)) ≤ n ∸ length (proj₁ (flat v))
    len-u≤n∸len-v = m+n≤o⇒m≤o∸n (length (proj₁ (flat u))) len|pair-u-v|≡n

    len-v≤n∸len-u : length (proj₁ (flat v)) ≤ n ∸ length (proj₁ (flat u))
    len-v≤n∸len-u = m+n≤o⇒m≤o∸n (length (proj₁ (flat v))) (subst (λ k → k ≤ n) (+-comm (length (proj₁ (flat u))) (length (proj₁ (flat v)))) len|pair-u-v|≡n)

    extract-≥-fst : ∀ {u₁ u₂ : U l} {v₁ : U r}
      → proj₁ (flat u₁) ≡ proj₁ (flat u₂)
      → (l ● r ` loc) ⊢ PairU u₁ v₁ ≥ PairU u₂ v₁
      → l ⊢ u₁ ≥ u₂
    extract-≥-fst _ (inj₁ (be _ _ (seq₁ u₁>u₂))) = inj₁ u₁>u₂
    extract-≥-fst _ (inj₁ (be _ _ (seq₂ refl v₁>v₁))) = ⊥-elim (>→¬≡ v₁>v₁ refl)
    extract-≥-fst _ (inj₁ (bne _ _ (seq₁ u₁>u₂))) = inj₁ u₁>u₂
    extract-≥-fst _ (inj₁ (bne _ _ (seq₂ refl v₁>v₁))) = ⊥-elim (>→¬≡ v₁>v₁ refl)
    extract-≥-fst {u₁} {u₂} {v₁} flat-u₁≡flat-u₂ (inj₁ (lne len>0 len≡0)) =
      ⊥-elim (n≡0→¬n>0 len-u₁v₁≡0 len>0)
      where
        len-u₁v₁≡len-u₂v₁ : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ length (proj₁ (flat (PairU {l} {r} {loc} u₂ v₁)))
        len-u₁v₁≡len-u₂v₁ = cong length (cong (λ w → w List.++ proj₁ (flat v₁)) flat-u₁≡flat-u₂)
        len-u₁v₁≡0 : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ 0
        len-u₁v₁≡0 = trans len-u₁v₁≡len-u₂v₁ len≡0
    extract-≥-fst _ (inj₂ refl) = inj₂ refl

    pair≥→fst≥ : ∀ {u₁ u₂ : U l} {v₁ : U r}
      → (l ● r ` loc) ⊢ PairU u₁ v₁ ≥ PairU u₂ v₁
      → l ⊢ u₁ ≥ u₂
    pair≥→fst≥ (inj₁ (be len≡ len0 (seq₁ u₁>u₂))) = inj₁ u₁>u₂
    pair≥→fst≥ (inj₁ (be len≡ len0 (seq₂ refl v₁>v₁))) = ⊥-elim (>→¬≡ v₁>v₁ refl)
    pair≥→fst≥ (inj₁ (bne _ _ (seq₁ u₁>u₂))) = inj₁ u₁>u₂
    pair≥→fst≥ (inj₁ (bne _ _ (seq₂ refl v₁>v₁))) = ⊥-elim (>→¬≡ v₁>v₁ refl)
    pair≥→fst≥ {u₁} {u₂} {v₁} (inj₁ (lne len>0 len0)) =
      let len|u₂v₁|≡|u₂|+|v₁| : length (proj₁ (flat (PairU {l} {r} {loc} u₂ v₁))) ≡ (length (proj₁ (flat u₂)) + length (proj₁ (flat v₁)))
          len|u₂v₁|≡|u₂|+|v₁| = trans (cong length (flat-pairU-proj₁ u₂ v₁)) (length-++ (proj₁ (flat u₂)) {proj₁ (flat v₁)})
          len-v₁≡0 : length (proj₁ (flat v₁)) ≡ 0
          len-v₁≡0 = m+n≡0⇒n≡0 (length (proj₁ (flat u₂))) (trans (sym len|u₂v₁|≡|u₂|+|v₁|) len0)
          len|u₁v₁|≡|u₁|+|v₁| : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ (length (proj₁ (flat u₁)) + length (proj₁ (flat v₁)))
          len|u₁v₁|≡|u₁|+|v₁| = trans (cong length (flat-pairU-proj₁ u₁ v₁)) (length-++ (proj₁ (flat u₁)) {proj₁ (flat v₁)})
          len|u₁v₁|≡|u₁| : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ length (proj₁ (flat u₁))
          len|u₁v₁|≡|u₁| = trans len|u₁v₁|≡|u₁|+|v₁| (trans (cong (λ k → length (proj₁ (flat u₁)) + k) len-v₁≡0) (+-identityʳ (length (proj₁ (flat u₁)))))
          len-u₁>0 : length (proj₁ (flat u₁)) Nat.> 0
          len-u₁>0 = subst (λ k → k Nat.> 0) len|u₁v₁|≡|u₁| len>0
          len-u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
          len-u₂≡0 = m+n≡0⇒m≡0 (length (proj₁ (flat u₂))) (trans (sym len|u₂v₁|≡|u₂|+|v₁|) len0)
      in inj₁ (lne len-u₁>0 len-u₂≡0)
    pair≥→fst≥ (inj₂ refl) = inj₂ refl

    ev₁ : (u' : U l) → length (proj₁ (flat u')) ≤ n ∸ length (proj₁ (flat v)) → l ⊢ u ≥ u'
    ev₁ u' len-u'≤n∸len-v =
      let len|u'v|≡|u'|+|v| : length (proj₁ (flat (PairU {l} {r} {loc} u' v))) ≡ (length (proj₁ (flat u')) + length (proj₁ (flat v)))
          len|u'v|≡|u'|+|v| = trans (cong length (flat-pairU-proj₁ u' v)) (length-++ (proj₁ (flat u')) {proj₁ (flat v)})
          len-u'v≤n : length (proj₁ (flat (PairU {l} {r} {loc} u' v))) ≤ n
          len-u'v≤n = subst (λ k → k ≤ n) (sym len|u'v|≡|u'|+|v|) (m≤o∸n⇒m+n≤o (length (proj₁ (flat u'))) len-v≤n len-u'≤n∸len-v)
      in pair≥→fst≥ (pair-u'-v'→|u'v'|≤n→uv≥u'v' (PairU u' v) len-u'v≤n)

    extract-≥-snd : ∀ {u₁ : U l} {v₁ v₂ : U r}
      → proj₁ (flat v₁) ≡ proj₁ (flat v₂)
      → (l ● r ` loc) ⊢ PairU u₁ v₁ ≥ PairU u₁ v₂
      → r ⊢ v₁ ≥ v₂
    extract-≥-snd _ (inj₁ (be _ _ (seq₂ refl v₁>v₂))) = inj₁ v₁>v₂
    extract-≥-snd _ (inj₁ (be _ _ (seq₁ u₁>u₁))) = ⊥-elim (>→¬≡ u₁>u₁ refl)
    extract-≥-snd _ (inj₁ (bne _ _ (seq₂ refl v₁>v₂))) = inj₁ v₁>v₂
    extract-≥-snd _ (inj₁ (bne _ _ (seq₁ u₁>u₁))) = ⊥-elim (>→¬≡ u₁>u₁ refl)
    extract-≥-snd {u₁} {v₁} {v₂} flat-v₁≡flat-v₂ (inj₁ (lne len>0 len≡0)) =
       ⊥-elim (n≡0→¬n>0 len-u₁v₁≡0 len>0)
       where
         len-u₁v₁≡len-u₁v₂ : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₂)))
         len-u₁v₁≡len-u₁v₂ = cong length (cong (proj₁ (flat u₁) List.++_) flat-v₁≡flat-v₂)
         len-u₁v₁≡0 : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ 0
         len-u₁v₁≡0 = trans len-u₁v₁≡len-u₁v₂ len≡0
    extract-≥-snd _ (inj₂ refl) = inj₂ refl

    pair≥→snd≥ : ∀ {u₁ : U l} {v₁ v₂ : U r}
      → (l ● r ` loc) ⊢ PairU u₁ v₁ ≥ PairU u₁ v₂
      → r ⊢ v₁ ≥ v₂
    pair≥→snd≥ (inj₁ (be len≡ len0 (seq₂ refl v₁>v₂))) = inj₁ v₁>v₂
    pair≥→snd≥ (inj₁ (be len≡ len0 (seq₁ u₁>u₁))) = ⊥-elim (>→¬≡ u₁>u₁ refl)
    pair≥→snd≥ (inj₁ (bne _ _ (seq₂ refl v₁>v₂))) = inj₁ v₁>v₂
    pair≥→snd≥ (inj₁ (bne _ _ (seq₁ u₁>u₁))) = ⊥-elim (>→¬≡ u₁>u₁ refl)
    pair≥→snd≥ {u₁} {v₁} {v₂} (inj₁ (lne len>0 len0)) =
      let len|u₁v₂|≡|u₁|+|v₂| : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₂))) ≡ (length (proj₁ (flat u₁)) + length (proj₁ (flat v₂)))
          len|u₁v₂|≡|u₁|+|v₂| = trans (cong length (flat-pairU-proj₁ u₁ v₂)) (length-++ (proj₁ (flat u₁)) {proj₁ (flat v₂)})
          len-u₁≡0 : length (proj₁ (flat u₁)) ≡ 0
          len-u₁≡0 = m+n≡0⇒m≡0 (length (proj₁ (flat u₁))) (trans (sym len|u₁v₂|≡|u₁|+|v₂|) len0)
          len|u₁v₁|≡|u₁|+|v₁| : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ (length (proj₁ (flat u₁)) + length (proj₁ (flat v₁)))
          len|u₁v₁|≡|u₁|+|v₁| = trans (cong length (flat-pairU-proj₁ u₁ v₁)) (length-++ (proj₁ (flat u₁)) {proj₁ (flat v₁)})
          len|u₁v₁|≡|v₁| : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ length (proj₁ (flat v₁))
          len|u₁v₁|≡|v₁| = trans len|u₁v₁|≡|u₁|+|v₁| (trans (cong (λ k → k + length (proj₁ (flat v₁))) len-u₁≡0) (+-identityˡ (length (proj₁ (flat v₁)))))
          len-v₁>0 : length (proj₁ (flat v₁)) Nat.> 0
          len-v₁>0 = subst (λ k → k Nat.> 0) len|u₁v₁|≡|v₁| len>0
          len-v₂≡0 : length (proj₁ (flat v₂)) ≡ 0
          len-v₂≡0 = m+n≡0⇒n≡0 (length (proj₁ (flat u₁))) (trans (sym len|u₁v₂|≡|u₁|+|v₂|) len0)
      in inj₁ (lne len-v₁>0 len-v₂≡0)
    pair≥→snd≥ (inj₂ refl) = inj₂ refl

    ev₂ : (v' : U r) → length (proj₁ (flat v')) ≤ n ∸ length (proj₁ (flat u)) → r ⊢ v ≥ v'
    ev₂ v' len-v'≤n∸len-u =
      let len|uv'|≡|u|+|v'| : length (proj₁ (flat (PairU {l} {r} {loc} u v'))) ≡ (length (proj₁ (flat u)) + length (proj₁ (flat v')))
          len|uv'|≡|u|+|v'| = trans (cong length (flat-pairU-proj₁ u v')) (length-++ (proj₁ (flat u)))
          len-uv'≤n : length (proj₁ (flat (PairU {l} {r} {loc} u v'))) ≤ n
          len-uv'≤n = subst (λ k → k ≤ n) (trans (+-comm (length (proj₁ (flat v'))) (length (proj₁ (flat u)))) (sym len|uv'|≡|u|+|v'|)) (m≤o∸n⇒m+n≤o (length (proj₁ (flat v'))) len-u≤n len-v'≤n∸len-u)
      in pair≥→snd≥ (pair-u'-v'→|u'v'|≤n→uv≥u'v' (PairU u v') len-uv'≤n)



-- do we have some thing like ≥-Max-Preserve but for the first of a pair parse tree?

≥-max-pres-left : ∀ { l r : RE } { loc : ℕ } { n : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {suc n} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {suc n} {c} (pdinstance-left pdi)
≥-max-pres-left {l} {r} {loc} {n} {c} (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres u→maxu→v→len|v|≤n→inj-u≥inj-v) =
  ≥-max-pres (λ u maxu v len|v|≤n  → left-mono-≥ (u→maxu→v→len|v|≤n→inj-u≥inj-v u maxu v len|v|≤n))


≥-max-pres-right : ∀ { l r : RE } { loc : ℕ } { n : ℕ } { c : Char }
  → ( pdi : PDInstance r c )
  → ≥-Max-Preserve {r} {suc n} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {suc n} {c} (pdinstance-right pdi)
≥-max-pres-right {l} {r} {loc} {n} {c} (pdinstance {p} .{r} .{c} inj s-ev) (≥-max-pres u→maxu→v→len|v|≤n→inj-u≥inj-v) =
  ≥-max-pres (λ u maxu v len|v|≤n → right-mono-≥ (u→maxu→v→len|v|≤n→inj-u≥inj-v u maxu v len|v|≤n))        

{-
≥-max-pres-●-fst :  ∀ { p l r : RE } { loc : ℕ }  { c : Char }  { inj : U p →  U l }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {l} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ≥-Max-Preserve {l} {c} (pdinstance inj sound-ev)
    → ( u : U p )
    → ≥-Max u
    → ( v : U r )
    → ≥-Max v
    → ( y : U p )
    →  proj₁ (flat u ) ≡ proj₁ (flat y) 
    → ( l ● r ` loc ) ⊢ mkinjFst inj (PairU u v) ≥ mkinjFst inj (PairU y v )
≥-max-pres-●-fst {p} {l} {r} {loc} {c} {inj} {s-ev} (≥-max-pres u→maxu→v→|u|≡|v|→u≥v)
  u (≥-max .(u) v→|u|≡|v|→u≥v) v ≥-max-v y |u|≡|y|
  with u→maxu→v→|u|≡|v|→u≥v u (≥-max u v→|u|≡|v|→u≥v) y |u|≡|y|
... | inj₁ inj-u>inj-y = inj₁ (bne len>0 len>0 (seq₁ inj-u>inj-y))
  where
    len>0 : ∀ {w} → length (proj₁ (flat (PairU {l} {r} {loc} (inj w) v))) Nat.> 0
    len>0 {w} rewrite s-ev w = Nat.s≤s Nat.z≤n
... | inj₂ inj-u≡inj-y rewrite inj-u≡inj-y = inj₂ refl

-}

{-
-- the following is a "monomorphized" version of the ≥-Max-Preserve 
data ≥-Max-Fst : ∀ { l r : RE } { loc : ℕ } { c : Char } → ( PDInstance ( l ● r ` loc ) c ) → Set where
  ≥-max-fst : ∀ { p l r : RE } { loc : ℕ } { c : Char } { inj : U p → U l }
    { sound-ev : ∀ ( x : U p ) → (proj₁ (flat {l} (inj x))) ≡ c ∷ ( proj₁ (flat {p} x )) }
    → ( ( u : U p )
      → ( v : U r )
      → ≥-Max (PairU {p} {r} {loc} u v)
      → ( u' : U p )
      → ( v' : U r ) 
      → ( proj₁ (flat (PairU {p} {r} {loc} u v)) ≡ proj₁ (flat (PairU {p} {r} {loc} u' v')) )
      → l ● r ` loc ⊢ mkinjFst inj (PairU u v) ≥ mkinjFst inj (PairU u' v') )
    → ≥-Max-Fst {l} {r} {loc} {c} (pdinstance-fst (pdinstance inj sound-ev))

-- this data type looks similar to ≥-max-pres-●-fst except that v ≡ v'.
-- if ≥-max-pres-●-fst is provable why ≥-pres0-fst is not?

-- probably a very useful lemma
-}
{-
len-max> : ∀ { r : RE } { u v : U r }
  → ≥-Max u
  → ≥-Max v
  → length (proj₁ (flat u))  >  
-} 

{-
Take the example from the commented code (lines 431–435):
- p = ε ● ($ a + ε)
- l = $ c ● p (so inj maps w to PairU (LetterU c) w)
- r = $ a + ε
Let:
- u₁ = PairU EmptyU (LeftU (LetterU 'a'))  — flat length 1
- u₂ = RightU EmptyU                        — flat length 0
- v₁ = PairU EmptyU (RightU EmptyU)         — flat length 0
- v₂ = LeftU (LetterU 'a')                  — flat length 1
With n = 1:
- PairU u₁ u₂ has flat length 1 and is ≥-Max 1 (it beats all trees of length ≤ 1)
- PairU v₁ v₂ has flat length 1, so length (flat v) ≤ 1 holds
After pdinstance-fst:
- mkinjFst inj (PairU u₁ u₂) = PairU (inj u₁) u₂ has flat length 2
- mkinjFst inj (PairU v₁ v₂) = PairU (inj v₁) v₂ has flat length 2
To show (l ● r) ⊢ PairU (inj u₁) u₂ ≥ PairU (inj v₁) v₂ we need bne + >ⁱ:
- seq₁: requires l ⊢ inj u₁ > inj v₁. This is true, but it only yields  
  PairU (inj u₁) u₂ >ⁱ PairU (inj v₁) u₂ — not PairU (inj v₁) v₂.
- seq₂: requires inj u₁ ≡ inj v₁ (false, lengths differ) and r ⊢ u₂ > v₂.  
  But u₂ = RightU EmptyU and v₂ = LeftU (LetterU 'a'), so actually r ⊢ v₂ > u₂ — the opposite!
So neither seq₁ nor seq₂ works, and the goal is unprovable.
What to do instead
The file already contains a provable variant that keeps the second component fixed — ≥-max-pres-●-fst (commented out at lines 271–291). That lemma type-checks and is usable:
≥-max-pres-●-fst :
  → ≥-Max-Preserve {l} {c} (pdinstance inj sound-ev)
  → (u : U p) → ≥-Max u → (v : U r) → ≥-Max v
  → (y : U p) → proj₁ (flat u) ≡ proj₁ (flat y)
  → (l ● r ` loc) ⊢ mkinjFst inj (PairU u v) ≥ mkinjFst inj (PairU y v)
If your use case genuinely needs ≥-max-pres-fst, the definition of ≥-Max-Preserve or ≥-Max would need to be strengthened (e.g. by requiring a component-wise maximality condition for PairU). As written, the lemma cannot be completed.

-}

≥-max-pres-fst : ∀ { l r : RE } { loc : ℕ } { n : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {suc n} {c} pdi
  → ≥-Max-Preserve {l ● r ` loc} {suc n} {c} (pdinstance-fst pdi)
≥-max-pres-fst {l} {r} {loc} {n} {c}  (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres u→maxu→v→len|v|≤n→inju≥injv) =
  ≥-max-pres prf
  where
    prf :  (u : U (p ● r ` loc))
        →  ≥-Max n u
        →  (v : U (p ● r ` loc))
        →  length (proj₁ (flat v)) ≤ n
        → (l ● r ` loc) ⊢ mkinjFst inj u ≥ mkinjFst inj v
    prf = {!!} 
  

  


{-
≥-max-pres-●-snd : ∀ { p l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( u : U p )
    → ≥-Max u
    → ( e : U l )
    → Flat-[] l e
    → ≥-Max e
    → ( y : U p )
    → proj₁ (flat u) ≡ proj₁ (flat y)
    → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
    → ( l ● r ` loc ) ⊢ mkinjSnd inj e u ≥  mkinjSnd inj e y
≥-max-pres-●-snd {p} {l} {r} {ε∈l} {loc} {c} {inj} {s-ev} u max-u e (flat-[] .e flat-e≡[]) max-e y flat-u≡flat-y (≥-max-pres f) =
  aux (f u max-u y flat-u≡flat-y)
  where
    len>0-inj : (w : U p) → length (proj₁ (flat (inj w))) Nat.> 0
    len>0-inj w rewrite s-ev w = Nat.s≤s Nat.z≤n

    len>0-pair : (w : U p) → length (proj₁ (flat (PairU {l} {r} {loc} e (inj w)))) Nat.> 0
    len>0-pair w rewrite flat-e≡[] | s-ev w = Nat.s≤s Nat.z≤n

    aux : r ⊢ inj u ≥ inj y → (l ● r ` loc) ⊢ mkinjSnd inj e u ≥ mkinjSnd inj e y
    aux (inj₁ (be _ len0 _)) = ⊥-elim (n≡0→¬n>0 len0 (len>0-inj y))
    aux (inj₁ (bne _ _ inj-u>ⁱinj-y)) =
      inj₁ (bne {l ● r ` loc} {PairU {l} {r} {loc} e (inj u)} {PairU {l} {r} {loc} e (inj y)}
        (len>0-pair u) (len>0-pair y)
        (seq₂ {l} {r} {loc} {e} {e} {inj u} {inj y} refl
          (bne {r} {inj u} {inj y} (len>0-inj u) (len>0-inj y) inj-u>ⁱinj-y)))
    aux (inj₁ (lne _ len0)) = ⊥-elim (n≡0→¬n>0 len0 (len>0-inj y))
    aux (inj₂ eq) = inj₂ (cong (PairU {l} {r} {loc} e) eq) 





≥-max-pres-* : ∀ { p r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( u : U p )
    → ≥-Max u
    → ( vs : U (r * ε∉r ` loc )  )
    → ≥-Max vs
    → ( y : U p )
    → ( proj₁ (flat u ) ≡ proj₁ (flat y) )
    → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
    → ( r * ε∉r ` loc ) ⊢ mkinjList inj (PairU u vs) ≥ mkinjList inj (PairU y vs )
≥-max-pres-*  {p} {r} {ε∉r} {loc} {c} {inj} {s-ev} u (≥-max .(u) v→|u|≡|v|→u≥v) (ListU vs) ≥-max-list-vs y |u|≡|y|
  (≥-max-pres u→maxu→v→|u|≡|v|→u≥v)
  with  u→maxu→v→|u|≡|v|→u≥v u (≥-max u v→|u|≡|v|→u≥v) y |u|≡|y|
... | inj₁ inj-u>inj-y = inj₁ (bne len>0 len>0 (star-head inj-u>inj-y))
  where
    len>0 : ∀ {w} → length (proj₁ (flat (ListU {r} {ε∉r}  {loc} ((inj w) ∷ vs )))) Nat.> 0
    len>0 {w} rewrite s-ev w = Nat.s≤s Nat.z≤n
... | inj₂ inj-u≡inj-y rewrite inj-u≡inj-y = inj₂ refl 

-} 


-- pdU-≥-max-pres : ∀ {r : RE } { c : Char }
--   → 
  
{-

-- fst
-- not provable 
≥-max-pres-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {c} pdi
  → ≥-Max-Preserve {l ● r ` loc} {c} (pdinstance-fst pdi)
≥-max-pres-fst {l} {r} {loc} {c}  (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres f) =
  ≥-max-pres (λ { (PairU u₁ u₂) max-u'@(≥-max .(PairU u₁ u₂) h) (PairU v₁ v₂) flat-eq →
    let max₁ = max-u₁ max-u'
        max₂ = max-u₂ max-u'
    in case h (PairU v₁ v₂) flat-eq of λ {
      (inj₁ (be len≡ len0 seq)) →
        case seq of λ {
          (seq₁ u₁>v₁) →
            let flat-u₁≡[] = ++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat u₂)) (length≡0→[] (trans len≡ len0))
                flat-v₁≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) (length≡0→[] len0)
            in case-flat-eq max₁ max₂ flat-eq (trans flat-u₁≡[] (sym flat-v₁≡[]))
        ; (seq₂ u₁≡v₁ _) →
            case-flat-eq max₁ max₂ flat-eq (cong proj₁ (cong flat u₁≡v₁))
        }
    ; (inj₁ (bne len>0 len>0' (seq₂ u₁≡v₁ u₂>v₂))) →
        case-flat-eq max₁ max₂ flat-eq (cong proj₁ (cong flat u₁≡v₁))
    ; (inj₁ (bne len>0 len>0' (seq₁ u₁>v₁))) →
        case u₁>v₁ of λ {
          (be len≡' len0' _) →
            let flat-u₁≡[] = length≡0→[] (trans len≡' len0')
                flat-v₁≡[] = length≡0→[] len0'
            in case-flat-eq max₁ max₂ flat-eq (trans flat-u₁≡[] (sym flat-v₁≡[]))
        ; (bne lenu₁>0 lenv₁>0 u₁>ⁱv₁) →
            {!!}
            -- COUNTEREXAMPLE: when p = ε ● ($ a + ε), r = $ a + ε,
            -- u₁ = PairU EmptyU (LeftU (LetterU 'a')), u₂ = RightU EmptyU,
            -- v₁ = PairU EmptyU (RightU EmptyU), v₂ = LeftU (LetterU 'a'),
            -- the goal is unprovable because l ⊢ inj u₁ > inj v₁ is impossible
            -- (lengths differ: 2 vs 1) and inj u₁ ≢ inj v₁.
        ; (lne lenu₁>0 lenv₁≡0) →
            {!!}
            -- Similarly unprovable: flat v₁ ≡ [] but flat u₁ is non-empty,
            -- so l ⊢ inj u₁ > inj v₁ is impossible (no applicable > constructor).
        }
    ; (inj₁ (lne len>0 len0)) →
        let flat-v₁v₂≡[] = length≡0→[] len0
            flat-v₁≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) flat-v₁v₂≡[]
            flat-v₂≡[] = ++-conicalʳ (proj₁ (flat v₁)) (proj₁ (flat v₂)) flat-v₁v₂≡[]
            flat-u₁u₂≡[] = trans flat-eq (cong₂ _++_ flat-v₁≡[] flat-v₂≡[])
            len-pair≡0 = cong length flat-u₁u₂≡[]
        in ⊥-elim (n≡0→¬n>0 len-pair≡0 len>0)
    ; (inj₂ u≡v) →
        let u₁≡v₁ = proj₁ (ParseTree.inv-pairU u₁ u₂ v₁ v₂ u≡v)
            u₂≡v₂ = proj₂ (ParseTree.inv-pairU u₁ u₂ v₁ v₂ u≡v)
        in inj₂ (cong₂ (PairU {l} {r} {loc}) (cong inj u₁≡v₁) u₂≡v₂)
    }
  })
  where
    len>0 : ∀ {u v} → length (proj₁ (flat (PairU {l} {r} {loc} (inj u) v))) Nat.> 0
    len>0 {u} rewrite s-ev u = Nat.s≤s Nat.z≤n

    extract-≥-fst : ∀ {x₁ w₁ : U p} {x₂ : U r}
      → proj₁ (flat x₁) ≡ proj₁ (flat w₁)
      → (p ● r ` loc) ⊢ PairU x₁ x₂ ≥ PairU w₁ x₂
      → p ⊢ x₁ ≥ w₁
    extract-≥-fst _ (inj₁ (be _ _ (seq₁ x₁>w₁))) = inj₁ x₁>w₁
    extract-≥-fst _ (inj₁ (be _ _ (seq₂ refl x₂>x₂))) = ⊥-elim (>→¬≡ x₂>x₂ refl)
    extract-≥-fst _ (inj₁ (bne _ _ (seq₁ x₁>w₁))) = inj₁ x₁>w₁
    extract-≥-fst _ (inj₁ (bne _ _ (seq₂ refl x₂>x₂))) = ⊥-elim (>→¬≡ x₂>x₂ refl)
    extract-≥-fst {x₁} {w₁} {x₂} flat-x₁≡flat-w₁ (inj₁ (lne len-x₁x₂>0 len-w₁x₂≡0)) =
      ⊥-elim (n≡0→¬n>0 len-x₁x₂≡0 len-x₁x₂>0)
      where
        flat-w₁x₂≡[] = length≡0→[] len-w₁x₂≡0
        flat-w₁≡[] = ++-conicalˡ (proj₁ (flat w₁)) (proj₁ (flat x₂)) flat-w₁x₂≡[]
        flat-x₂≡[] = ++-conicalʳ (proj₁ (flat w₁)) (proj₁ (flat x₂)) flat-w₁x₂≡[]
        flat-x₁≡[] = trans flat-x₁≡flat-w₁ flat-w₁≡[]
        flat-x₁x₂≡[] : proj₁ (flat (PairU {p} {r} {loc} x₁ x₂)) ≡ []
        flat-x₁x₂≡[] = subst (λ w → w List.++ proj₁ (flat x₂) ≡ []) (sym flat-x₁≡[]) (trans (++-identityˡ (proj₁ (flat x₂))) flat-x₂≡[])
        len-x₁x₂≡0 = cong length flat-x₁x₂≡[]
    extract-≥-fst _ (inj₂ refl) = inj₂ refl

    max-u₁ : ∀ {x₁ x₂} → ≥-Max {p ● r ` loc} (PairU x₁ x₂) → ≥-Max {p} x₁
    max-u₁ (≥-max (PairU x₁ x₂) h) = ≥-max x₁ (λ w₁ flat-x₁≡flat-w₁ →
      extract-≥-fst flat-x₁≡flat-w₁ (h (PairU w₁ x₂) (cong (_++ proj₁ (flat x₂)) flat-x₁≡flat-w₁)))

    extract-≥-snd : ∀ {x₁ : U p} {x₂ w₂ : U r}
      → proj₁ (flat x₂) ≡ proj₁ (flat w₂)
      → (p ● r ` loc) ⊢ PairU x₁ x₂ ≥ PairU x₁ w₂
      → r ⊢ x₂ ≥ w₂
    extract-≥-snd _ (inj₁ (be _ _ (seq₂ refl x₂>w₂))) = inj₁ x₂>w₂
    extract-≥-snd _ (inj₁ (be _ _ (seq₁ x₁>x₁))) = ⊥-elim (>→¬≡ x₁>x₁ refl)
    extract-≥-snd _ (inj₁ (bne _ _ (seq₂ refl x₂>w₂))) = inj₁ x₂>w₂
    extract-≥-snd _ (inj₁ (bne _ _ (seq₁ x₁>x₁))) = ⊥-elim (>→¬≡ x₁>x₁ refl)
    extract-≥-snd {x₁} flat-x₂≡flat-w₂ (inj₁ (lne len-x₁x₂>0 len-x₁w₂≡0)) =
      ⊥-elim (n≡0→¬n>0 (trans (cong length flat-x₁x₂≡flat-x₁w₂) len-x₁w₂≡0) len-x₁x₂>0)
      where
        flat-x₁x₂≡flat-x₁w₂ = cong (proj₁ (flat x₁) ++_) flat-x₂≡flat-w₂
    extract-≥-snd _ (inj₂ refl) = inj₂ refl

    max-u₂ : ∀ {x₁ x₂} → ≥-Max {p ● r ` loc} (PairU x₁ x₂) → ≥-Max {r} x₂
    max-u₂ (≥-max (PairU x₁ x₂) h) = ≥-max x₂ (λ w₂ flat-x₂≡flat-w₂ →
      extract-≥-snd flat-x₂≡flat-w₂ (h (PairU x₁ w₂) (cong (proj₁ (flat x₁) ++_) flat-x₂≡flat-w₂)))

    case-flat-eq : ∀ {u₁ v₁ : U p} {u₂ v₂ : U r}
      → ≥-Max {p} u₁
      → ≥-Max {r} u₂
      → proj₁ (flat (PairU {p} {r} {loc} u₁ u₂)) ≡ proj₁ (flat (PairU {p} {r} {loc} v₁ v₂))
      → proj₁ (flat u₁) ≡ proj₁ (flat v₁)
      → (l ● r ` loc) ⊢ mkinjFst inj (PairU {p} {r} {loc} u₁ u₂) ≥ mkinjFst inj (PairU {p} {r} {loc} v₁ v₂)
    case-flat-eq {u₁} {v₁} {u₂} {v₂} max₁ (≥-max .u₂ max₂f) flat-eq flat-u₁≡flat-v₁ =
      let flat-u₂≡flat-v₂ : proj₁ (flat u₂) ≡ proj₁ (flat v₂)
          flat-u₂≡flat-v₂ = ++-cancelˡ (proj₁ (flat u₁)) (proj₁ (flat u₂)) (proj₁ (flat v₂))
                              (trans flat-eq (cong (λ w → w List.++ proj₁ (flat v₂)) (sym flat-u₁≡flat-v₁)))
          pair≥ : (l ● r ` loc) ⊢ mkinjFst inj (PairU {p} {r} {loc} u₁ u₂) ≥ mkinjFst inj (PairU {p} {r} {loc} v₁ u₂)
          pair≥ = ≥-max-pres-● {p} {l} {r} {loc} {c} {inj} {s-ev} u₁ max₁ u₂ (≥-max u₂ max₂f) v₁ flat-u₁≡flat-v₁ (≥-max-pres f)
      in combine pair≥ (max₂f v₂ flat-u₂≡flat-v₂)
      where
        combine : (l ● r ` loc) ⊢ mkinjFst inj (PairU u₁ u₂) ≥ mkinjFst inj (PairU v₁ u₂) → r ⊢ u₂ ≥ v₂ → (l ● r ` loc) ⊢ mkinjFst inj (PairU u₁ u₂) ≥ mkinjFst inj (PairU v₁ v₂)
        combine (inj₁ (be _ len0 _)) _ = ⊥-elim (n≡0→¬n>0 len0 len>0)
        combine (inj₁ (lne _ len0)) _ = ⊥-elim (n≡0→¬n>0 len0 len>0)
        combine (inj₁ (bne _ _ (seq₁ inj-u>inj-v))) _ = inj₁ (bne len>0 len>0 (seq₁ inj-u>inj-v))
        combine (inj₁ (bne _ _ (seq₂ _ u₂>u₂))) _ = ⊥-elim (>→¬≡ u₂>u₂ refl)
        combine (inj₂ eq) (inj₁ u₂>v₂) =
          let inj-u₁≡inj-v₁ = proj₁ (ParseTree.inv-pairU (inj u₁) u₂ (inj v₁) u₂ eq)
          in inj₁ (bne len>0 len>0 (seq₂ inj-u₁≡inj-v₁ u₂>v₂))
        combine (inj₂ eq) (inj₂ u₂≡v₂) =
          let inj-u₁≡inj-v₁ = proj₁ (ParseTree.inv-pairU (inj u₁) u₂ (inj v₁) u₂ eq)
          in inj₂ (trans eq (cong (PairU (inj v₁)) u₂≡v₂)) 
-} 
```
