```agda
{-# OPTIONS --rewriting  #-}
module cgp.lnegen.MaxPre where

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
open Data.List.Properties using ( ++-assoc ; ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ; length-++ )


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

open import Data.List.Relation.Unary.Any using (Any; here; there ; map)

import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )


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
data ≥-Max : ∀ { r : RE } → U r  → Set where 
  ≥-max : ∀ { r : RE }
        → ( u : U r )
        → ( ( v : U r )
          → ∃[ w ] proj₁ (flat u) ≡ ( proj₁ (flat v )) ++ w  -- |v| is a prefix of |u| ;  too weak, this only says, the > proof is an lne one. when w ≢ [], choice-lr when  w≡[]
          → r ⊢ u ≥ v )
        → ( ( v : U r )
          → ¬ ( ∃[ c ] ∃[ w ] proj₁ (flat v) ≡ ( proj₁ (flat u)) ++ ( c ∷ w ) ) -- |u| is not a proper prefix of |v|
          → r ⊢ u ≥ v )
        → ≥-Max {r} u

-- each partial derivative p is unique
-- inj is ≥-Max-Preserve is given an u which is max, and another v,
-- we must have inj u ≥ inj v 
data ≥-Max-Preserve : ∀ { r : RE } { c : Char } → PDInstance r c → Set where
  ≥-max-pres : ∀ { p r : RE } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ≥-Max u 
      → ( v : U p )
      → ∃[ w ] proj₁ (flat u) ≡ ( proj₁ (flat v )) ++ w  
      → r ⊢ inj u ≥ inj v ) -- local max w.r.t to the inj
    → ( ( u : U p )
      → ≥-Max u
      → ( v : U p )
      → ¬ ( ∃[ c ] ∃[ w ] proj₁ (flat v) ≡ ( proj₁ (flat u)) ++ ( c ∷ w ) )
      → r ⊢ inj u ≥ inj v )      
    → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)


++-≡-[] : {A : Set} {xs ys : List A}
        → xs ++ ys ≡ []
        → xs ≡ [] × ys ≡ []
++-≡-[] {xs = []}     {ys = []}     refl = refl , refl
++-≡-[] {xs = []}     {ys = _ ∷ _} ()
++-≡-[] {xs = _ ∷ _}              ()

≥-max-pair-inv3 : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( u : U l )
  → ( v : U r )
  → ≥-Max (PairU {l} {r} {loc} u v)
  → ( u' : U l )
  → ( v' : U r )
  → ∃[ w ] proj₁ (flat u) ++ proj₁ (flat v) ≡ (proj₁ (flat u') ++ proj₁ (flat v')) ++ w
  → l ⊢ u ≥ u'
≥-max-pair-inv3 {l} {r} {loc} {c} u v  (≥-max (PairU .u .v) pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' _ ) u' v' ( w , |uv|≡|u'v'|++w )
  with pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' (PairU u' v') ( w , |uv|≡|u'v'|++w ) 
... | inj₂ pair-u-v≡pair-u'-v'  = inj₂ (proj₁ (inv-pairU u v u' v' pair-u-v≡pair-u'-v' ))
... | inj₁ (be len|uv|≡|u'v'| len|u'v'|≡0 (seq₂ u≡u' _)) = inj₂ u≡u'
... | inj₁ (be len|uv|≡|u'v'| len|u'v'|≡0 (seq₁ u>u')) = inj₁ u>u'
... | inj₁ (bne len|uv|>0 len|u'v'|>0 (seq₂ u≡u' _)) = inj₂ u≡u'
... | inj₁ (bne len|uv|>0 len|u'v'|>0 (seq₁ u>u')) = inj₁ u>u'
... | inj₁ (lne len|uv|>0 len|u'v'|≡0) with length (proj₁ (flat u)) ≟ 0
...                                    | no ¬len|u|≡0 = inj₁ (lne (¬≡0→>0  ¬len|u|≡0 ) len|u'|≡0 ) -- case 1 len|u|>0 
  where
    |u'v'|≡[] : (proj₁ (flat (PairU {l} {r} {loc} u' v'))) ≡ []
    |u'v'|≡[]  = Utils.length≡0→[]  len|u'v'|≡0
    |u'|≡[] : (proj₁ (flat u')) ≡ []
    |u'|≡[] = proj₁ (++-≡-[] |u'v'|≡[] ) 
    
    len|u'|≡0 : length (proj₁ (flat u')) ≡ 0
    len|u'|≡0 = Utils.[]→length≡0 |u'|≡[]
... | yes len|u|≡0 = ev
  where
    |u'v'|≡[] : (proj₁ (flat (PairU {l} {r} {loc} u' v'))) ≡ []
    |u'v'|≡[]  = Utils.length≡0→[]  len|u'v'|≡0
    |u'|≡[] : (proj₁ (flat u')) ≡ []
    |u'|≡[] = proj₁ (++-≡-[] |u'v'|≡[] ) 
    |u|≡[] : (proj₁ (flat u)) ≡ []
    |u|≡[] = Utils.length≡0→[] len|u|≡0
    |u|≡|u'| : (proj₁ (flat u)) ≡ (proj₁ (flat u'))
    |u|≡|u'| rewrite |u'|≡[] = |u|≡[] 
    len|u'|≡0 : length (proj₁ (flat u')) ≡ 0
    len|u'|≡0 = Utils.[]→length≡0 |u'|≡[] 
  
    ev :  l ⊢ u > u' ⊎ u ≡ u'
    ev  with >-trichotomy u u'
    ... | inj₂ (inj₂ u≡u') = inj₂ u≡u'
    ... | inj₁ u>u' = inj₁ u>u'
    ... | inj₂ (inj₁ u'>u) = Nullary.contradiction  uv≥u'v   (<→¬≥  u'v>uv)   -- we need a contradiction
      where
        |uv|≡|u'v| : proj₁ (flat (PairU {l} {r} {loc} u v)) ≡ proj₁ (flat (PairU {l} {r} {loc} u' v))
        |uv|≡|u'v| rewrite  |u|≡[]  |  |u'|≡[] = refl
        |uv|≡|u'v|++[] : proj₁ (flat (PairU {l} {r} {loc} u v)) ≡ proj₁ (flat (PairU {l} {r} {loc} u' v)) ++ []
        |uv|≡|u'v|++[] rewrite |uv|≡|u'v| |  ++-identityʳ (proj₁ (flat (PairU {l} {r} {loc} u' v))) = refl
        len|u'v|>0 :  length (proj₁ (flat (PairU {l} {r} {loc} u' v))) Nat.> 0
        len|u'v|>0 rewrite sym |uv|≡|u'v| =  len|uv|>0 
        u'v>uv : l ● r ` loc ⊢ PairU u' v > PairU u v
        u'v>uv = bne  len|u'v|>0  len|uv|>0 (seq₁ u'>u)
        uv≥u'v : l ● r ` loc ⊢ PairU u v ≥ PairU u' v
        uv≥u'v  =  pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' (PairU u' v) ([] , |uv|≡|u'v|++[])



≥-max-pair-inv4 : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( u : U l )
  → ( v : U r )
  → ≥-Max (PairU {l} {r} {loc} u v)
  → ( u' : U l )
  → ( v' : U r )
  → ¬ ( ∃[ c ] ∃[ w ] proj₁ (flat u') ++ proj₁ (flat v') ≡ (proj₁ (flat u) ++ proj₁ (flat v)) ++ (c ∷ w) )
  → l ⊢ u > u' ⊎ (proj₁ (flat u) ≡ proj₁ (flat u'))

≥-max-pair-inv4 {l} {r} {loc} {c} u v (≥-max (PairU .u .v) _ f₂) u' v' ¬|u'v'|extends|uv|  with f₂ (PairU u' v') ¬|u'v'|extends|uv|
... | inj₂ pair-uv≡u'v' = inj₂ (cong (λ x → proj₁ (flat x)) (proj₁ (inv-pairU u v u' v' pair-uv≡u'v')))
... | inj₁ (be len|uv|≡len|u'v| len|u'v'|≡0 (seq₁ u>u')) = inj₁ u>u'
... | inj₁ (be len|uv|≡len|u'v| len|u'v'|≡0 (seq₂ u≡u' v>v')) = inj₂ (cong (λ x → proj₁ (flat x)) u≡u') 
... | inj₁ (bne len|uv|>0 len|u'v'|>0 (seq₁ u>u')) = inj₁ u>u'
... | inj₁ (bne len|uv|>0 len|u'v'|>0 (seq₂ u≡u' v>v')) = inj₂ (cong (λ x → proj₁ (flat x)) u≡u') 
... | inj₁ (lne len|uv|>0 len|u'v'|≡0) with proj₁ (flat u) in |u|-eq 
...        | []     = inj₂ (sym  |u'|≡[])
  where
    |u'v'|≡[] : (proj₁ (flat (PairU {l} {r} {loc} u' v'))) ≡ []
    |u'v'|≡[]  = Utils.length≡0→[]  len|u'v'|≡0
    |u'|≡[] : (proj₁ (flat u')) ≡ []
    |u'|≡[] = proj₁ (++-≡-[] |u'v'|≡[] ) 
...        | c₁ ∷ cs = inj₁ (lne ( |u|>0 ) ( Utils.[]→length≡0 |u'|≡[]))
  where
    |u'v'|≡[] : (proj₁ (flat (PairU {l} {r} {loc} u' v'))) ≡ []
    |u'v'|≡[]  = Utils.length≡0→[]  len|u'v'|≡0
    |u'|≡[] : (proj₁ (flat u')) ≡ []
    |u'|≡[] = proj₁ (++-≡-[] |u'v'|≡[] )
    |u|>0 : length (proj₁ (flat u)) Nat.> 0
    |u|>0 rewrite |u|-eq  = Nat.s≤s Nat.z≤n 

-- Extract ≥ from first component of pair
extract-≥-fst : ∀ { l r : RE } (loc : ℕ) { x₁ w₁ : U l } { x₂ : U r }
              → l ● r ` loc ⊢ PairU x₁ x₂ ≥ PairU w₁ x₂
              → l ⊢ x₁ ≥ w₁
extract-≥-fst loc (inj₁ (be _ _ (seq₁ x>w))) = inj₁ x>w
extract-≥-fst loc (inj₁ (be _ _ (seq₂ refl x>x))) = ⊥-elim (>→¬≡ x>x refl)
extract-≥-fst loc (inj₁ (bne _ _ (seq₁ x>w))) = inj₁ x>w
extract-≥-fst loc (inj₁ (bne _ _ (seq₂ refl x>x))) = ⊥-elim (>→¬≡ x>x refl)
extract-≥-fst {l} {r} loc {x₁} {w₁} {x₂} (inj₁ (lne len>0 len0)) =
    inj₁ (lne len-x₁>0 len-w₁≡0)
  where
    flat-w₁x₂≡[] : proj₁ (flat (PairU {l} {r} {loc} w₁ x₂)) ≡ []
    flat-w₁x₂≡[] = Utils.length≡0→[] len0
    flat-x₂≡[] : proj₁ (flat x₂) ≡ []
    flat-x₂≡[] = proj₂ (++-≡-[] flat-w₁x₂≡[])
    flat-w₁≡[] : proj₁ (flat w₁) ≡ []
    flat-w₁≡[] = proj₁ (++-≡-[] flat-w₁x₂≡[])
    len-w₁≡0 : length (proj₁ (flat w₁)) ≡ 0
    len-w₁≡0 = Utils.[]→length≡0 flat-w₁≡[]
    ¬len-x₁≡0 : ¬ length (proj₁ (flat x₁)) ≡ 0
    ¬len-x₁≡0 len-x₁≡0 = Utils.n≡0→¬n>0 len-pair≡0 len>0
      where
        flat-x₁≡[] : proj₁ (flat x₁) ≡ []
        flat-x₁≡[] = Utils.length≡0→[] len-x₁≡0
        flat-pair≡[] : proj₁ (flat (PairU {l} {r} {loc} x₁ x₂)) ≡ []
        flat-pair≡[] rewrite flat-x₁≡[] | flat-x₂≡[] = refl
        len-pair≡0 : length (proj₁ (flat (PairU {l} {r} {loc} x₁ x₂))) ≡ 0
        len-pair≡0 = Utils.[]→length≡0 flat-pair≡[]
    len-x₁>0 : length (proj₁ (flat x₁)) Nat.> 0
    len-x₁>0 = Utils.¬≡0→>0 ¬len-x₁≡0
extract-≥-fst loc (inj₂ refl) = inj₂ refl

-- Length of injected pair is > 0
inj-pair-len>0 : ∀ {p l r : RE} (loc : ℕ) {c : Char}
               → (inj : U p → U l)
               → (s-ev : ∀ (u : U p) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u))
               → (v₁ : U p) → (v₂ : U r)
               → length (proj₁ (flat (PairU {l} {r} {loc} (inj v₁) v₂))) Nat.> 0
inj-pair-len>0 loc inj s-ev v₁ _ rewrite s-ev v₁ = Nat.s≤s Nat.z≤n

-- Extract ≥-Max of first component from ≥-Max of pair
max-v₁-from-pair : ∀ { l r : RE } (loc : ℕ)
                  → (u₁ : U l) → (u₂ : U r)
                  → ≥-Max (PairU {l} {r} {loc} u₁ u₂)
                  → ≥-Max u₁
max-v₁-from-pair loc u₁ u₂ max-pair = {!!}
  -- NOTE: extracting ≥-Max u₁ from ≥-Max (PairU u₁ u₂) is not straightforward
  -- because the suffix w in the pair's ≥ proof doesn't decompose.

-- do we have some thing like ≥-Max-Preserve but for the first of a pair parse tree?

≥-max-pres-left : ∀ { l r : RE } {loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-left pdi)
≥-max-pres-left {l} {r} {loc} {c} (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u≥inj-v) =
  ≥-max-pres (λ u maxu v ∃w|u|≡|v|++w → left-mono-≥ (u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u maxu v ∃w|u|≡|v|++w))
             (λ u maxu v ¬∃cw|v|≡|u|++cw → left-mono (u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u≥inj-v u maxu v ¬∃cw|v|≡|u|++cw))


≥-max-pres-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance r c )
  → ≥-Max-Preserve {r} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-right pdi)
≥-max-pres-right {l} {r} {loc} {c} (pdinstance {p} .{r} .{c} inj s-ev) (≥-max-pres  u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u≥inj-v) =
  ≥-max-pres (λ u maxu v ∃w|u|≡|v|++w  → right-mono-≥ (u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u maxu v ∃w|u|≡|v|++w))        
             (λ u maxu v ¬∃cw|v|≡|u|++cw → right-mono (u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u≥inj-v u maxu v ¬∃cw|v|≡|u|++cw))

≥-max-pres-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
   → ( pdi : PDInstance l c )
   → ≥-Max-Preserve {l} {c} pdi
   → ≥-Max-Preserve {l ● r ` loc} {c} (pdinstance-fst pdi)
≥-max-pres-fst {l} {r} {loc} {c}  (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u≥inj-v) =
  ≥-max-pres prf snd-prf
     where
       prf : (u : U (p ● r ` loc))
            → ≥-Max u
            → (v : U (p ● r ` loc))
            → ∃[ w ] proj₁ (flat u) ≡ (proj₁ (flat v)) ++ w
            → (l ● r ` loc) ⊢ mkinjFst inj u ≥ mkinjFst inj v
       prf (PairU v₁ v₂)
           max-pair@(≥-max (PairU .v₁ .v₂) f₁ f₂)
           (PairU v₁' v₂')
           ( w , |v₁v₂|≡|v₁'v₂'|++w )
         with f₁ (PairU v₁' v₂') ( w , |v₁v₂|≡|v₁'v₂'|++w )
       prf (PairU v₁ v₂)
           max-pair@(≥-max (PairU .v₁ .v₂) f₁ f₂)
           (PairU v₁' v₂')
           ( _ , _ )
         | inj₁ (be len≡ len0 (seq₁ _)) =
             let max-v₁ = max-v₁-from-pair loc v₁ v₂ max-pair
                 iv1gtv1p = u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u>inj-v v₁ max-v₁ v₁' {!!}
             in inj₁ (bne (inj-pair-len>0 loc inj s-ev v₁ v₂) (inj-pair-len>0 loc inj s-ev v₁' v₂') (seq₁ iv1gtv1p))
       prf (PairU v₁ v₂)
           max-pair@(≥-max (PairU .v₁ .v₂) f₁ f₂)
           (PairU v₁' v₂')
           ( _ , _ )
         | inj₁ (be len≡ len0 (seq₂ v₁≡v₁' v₂>v₂')) =
             let max-v₁ = max-v₁-from-pair loc v₁ v₂ max-pair
                 iv1gtv1p = u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u>inj-v v₁ max-v₁ v₁' {!!}
             in inj₁ (bne (inj-pair-len>0 loc inj s-ev v₁ v₂) (inj-pair-len>0 loc inj s-ev v₁' v₂') (seq₂ (cong inj v₁≡v₁') v₂>v₂'))
       prf (PairU v₁ v₂)
           max-pair@(≥-max (PairU .v₁ .v₂) f₁ f₂)
           (PairU v₁' v₂')
           ( _ , _ )
         | inj₁ (lne len>0 len0) =
             let max-v₁ = max-v₁-from-pair loc v₁ v₂ max-pair
                 iv1gtv1p = u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u>inj-v v₁ max-v₁ v₁' {!!}
             in inj₁ (bne (inj-pair-len>0 loc inj s-ev v₁ v₂) (inj-pair-len>0 loc inj s-ev v₁' v₂') (seq₁ iv1gtv1p))
       prf (PairU v₁ v₂)
           max-pair@(≥-max (PairU .v₁ .v₂) f₁ f₂)
           (PairU v₁' v₂')
           ( _ , _ )
         | inj₁ (bne len>0 len>0' _) =
             let max-v₁ = max-v₁-from-pair loc v₁ v₂ max-pair
                 iv1gtv1p = u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u>inj-v v₁ max-v₁ v₁' {!!}
             in inj₁ (bne (inj-pair-len>0 loc inj s-ev v₁ v₂) (inj-pair-len>0 loc inj s-ev v₁' v₂') (seq₁ iv1gtv1p))
       prf (PairU v₁ v₂)
           max-pair@(≥-max (PairU .v₁ .v₂) f₁ f₂)
           (PairU v₁' v₂')
           ( _ , _ )
         | inj₂ pairv₁v₂≡pairv₁'v₂' =
             let v₁≡v₁' , v₂≡v₂' = inv-pairU v₁ v₂ v₁' v₂' pairv₁v₂≡pairv₁'v₂'
             in inj₂ (cong₂ PairU (cong inj v₁≡v₁') v₂≡v₂')

       snd-prf : (u : U (p ● r ` loc))
                → ≥-Max u
                → (v : U (p ● r ` loc))
                → ¬ (∃[ c ] ∃[ w ] proj₁ (flat v) ≡ proj₁ (flat u) ++ c ∷ w)
                → (l ● r ` loc) ⊢ mkinjFst inj u > mkinjFst inj v
       snd-prf (PairU v₁ v₂) snd-max-pair@(≥-max (PairU .v₁ .v₂) f₁' f₂') (PairU v₁' v₂') ¬∃ =
             bne (inj-pair-len>0 loc inj s-ev v₁ v₂) (inj-pair-len>0 loc inj s-ev v₁' v₂') (seq₁ snd-v₁>ⁱv₁')
           where
             snd-max-v₁ : ≥-Max v₁
             snd-max-v₁ = max-v₁-from-pair loc v₁ v₂ snd-max-pair

             snd-¬∃-v₁ : ¬ (∃[ c ] ∃[ w ] proj₁ (flat v₁') ≡ proj₁ (flat v₁) ++ c ∷ w)
             snd-¬∃-v₁ (c₁ , (w₁ , p)) = {!!}

             snd-v₁>ⁱv₁' : l ⊢ inj v₁ > inj v₁'
             snd-v₁>ⁱv₁' = u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u>inj-v v₁ snd-max-v₁ v₁' snd-¬∃-v₁
  

  


```
