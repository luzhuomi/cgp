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
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; mkAllEmptyU≢[] ; Flat-[] ; flat-[] ; proj₁flat-v≡[]→ε∈r )


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
open PartialDerivative using ( pdU[_,_] ;
  advance-pdi*-with-c ;
  pdUMany[_,_]; pdUMany-aux ;
  mkinjLetter ; mkinjLetterSound ;
  pdU-complete
  )

import cgp.Recons as Recons
open Recons using ( Recons ; recons ; inv-recons-fst ; inv-recons-left ; inv-recons-right ; inv-recons-star ; inv-recons-snd )

import cgp.lnegen.ExtendedOrder as ExtendedOrder
open ExtendedOrder using (
  pdU-sorted ;
  Ex>-sorted ; ex>-nil ; ex>-cons ;
  Ex>-maybe ; ex>-nothing ; ex>-just ;
  >-pdi-trans ;
  _,_⊢_>_ ; >-pdi
  )

import cgp.lnegen.PrefEq as PrefEq
open PrefEq using (
  >-Inc-≅ ; >-inc ;
  >-inc-fst ;
  _⊢_≅_ ;
  pdU->-inc
  )

import cgp.lnegen.PrefEq as PrefEq
open PrefEq using (
  >-Inc-≅ ; >-inc ;
  >-inc-fst ;
  _⊢_≅_ ; ≅→||≡||
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

import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)


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
             (λ u maxu v ¬∃cw|v|≡|u|++cw → left-mono-≥ (u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u≥inj-v u maxu v ¬∃cw|v|≡|u|++cw))


≥-max-pres-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance r c )
  → ≥-Max-Preserve {r} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-right pdi)
≥-max-pres-right {l} {r} {loc} {c} (pdinstance {p} .{r} .{c} inj s-ev) (≥-max-pres  u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u≥inj-v) =
  ≥-max-pres (λ u maxu v ∃w|u|≡|v|++w  → right-mono-≥ (u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u maxu v ∃w|u|≡|v|++w))        
             (λ u maxu v ¬∃cw|v|≡|u|++cw → right-mono-≥ (u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u≥inj-v u maxu v ¬∃cw|v|≡|u|++cw))

list-≟ : (xs ys : List Char) → Dec (xs ≡ ys)
list-≟ [] [] = yes refl
list-≟ [] (_ ∷ _) = no (λ ())
list-≟ (_ ∷ _) [] = no (λ ())
list-≟ (x ∷ xs) (y ∷ ys) with x Char.≟ y | list-≟ xs ys
... | yes x≡y | yes xs≡ys = yes (cong₂ _∷_ x≡y xs≡ys)
... | no ¬x≡y | _         = no (λ eq → ¬x≡y (proj₁ (Utils.∷-inj eq)))
... | yes _   | no ¬xs≡ys = no (λ eq → ¬xs≡ys (proj₂ (Utils.∷-inj eq)))

-- extract-≅-fst: Try to extract structural equivalence of first components
-- from component equality. This is provable for +/* but may be a hole for ●.
extract-≅-fst : ∀ {p : RE} (u₁ v₁' : U p)
  → proj₁ (flat u₁) ≡ proj₁ (flat v₁')
  → p ⊢ u₁ > v₁'
  → p ⊢ u₁ ≅ v₁'
extract-≅-fst u₁ v₁' eq u₁>v₁' = {!!}

≥-max-pres-fst : ∀ { p l r : RE } { loc : ℕ } { c : Char }
   → ( inj : U p → U l )
   → ( sound-ev : ∀ ( x : U p ) → proj₁ (flat {l} (inj x)) ≡ c ∷ proj₁ (flat {p} x) )
   → ≥-Max-Preserve {l} {c} (pdinstance inj sound-ev)
   → >-Inc-≅ (pdinstance inj sound-ev)
   → ( ( u₁ : U p ) ( u₂ : U r )
       → ≥-Max (PairU u₁ u₂)
       → ( v₁ : U l )
       → proj₁ (flat v₁) ≢ []
       → (∀ {c₁ cs₁} → proj₁ (flat v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c)
       → l ⊢ inj u₁ > v₁ )
   → ≥-Max-Preserve {l ● r ` loc} {c} (pdinstance-fst (pdinstance inj sound-ev))
≥-max-pres-fst {p} {l} {r} {loc} {c} inj sound-ev (≥-max-pres u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u≥inj-v) (>-inc lift) dom =
  ≥-max-pres prf snd-prf
      where
        helper-prf : ∀ (u₁ : U p) (u₂ : U r) (max-pair : ≥-Max (PairU u₁ u₂)) (v₁' : U p) (v₂' : U r)
                   → (p ● r ` loc) ⊢ PairU u₁ u₂ ≥ PairU v₁' v₂'
                   → (l ● r ` loc) ⊢ mkinjFst inj (PairU u₁ u₂) ≥ mkinjFst inj (PairU v₁' v₂')
        helper-prf u₁ u₂ max-pair v₁' v₂' (inj₂ refl) = inj₂ (cong (mkinjFst inj) refl)
        helper-prf u₁ u₂ max-pair v₁' v₂' (inj₁ (be len≡ len0 (seq₂ u₁≡v₁' u₂>v₂'))) =
          inj₁ (bne (inj-pair-len>0 loc inj sound-ev u₁ u₂)
                    (inj-pair-len>0 loc inj sound-ev v₁' v₂')
                    (seq₂ (cong inj u₁≡v₁') u₂>v₂'))
        helper-prf u₁ u₂ max-pair v₁' v₂' (inj₁ (be len≡ len0 (seq₁ u₁>v₁'))) =
          let ¬[] : proj₁ (flat (inj v₁')) ≢ []
              ¬[] = λ eq → case trans (sym eq) (sound-ev v₁') of λ { () }
              first-char : ∀ {c₁ cs₁} → proj₁ (flat (inj v₁')) ≡ c₁ ∷ cs₁ → c₁ ≡ c
              first-char = λ eq₁ →
                sym (proj₁ (Utils.∷-inj (trans (sym (sound-ev v₁')) eq₁)))
          in inj₁ (bne (inj-pair-len>0 loc inj sound-ev u₁ u₂)
                       (inj-pair-len>0 loc inj sound-ev v₁' v₂')
                       (seq₁ (dom u₁ u₂ max-pair (inj v₁') ¬[] first-char)))
        helper-prf u₁ u₂ max-pair v₁' v₂' (inj₁ (lne len>0 len0)) =
          let ¬[] : proj₁ (flat (inj v₁')) ≢ []
              ¬[] = λ eq → case trans (sym eq) (sound-ev v₁') of λ { () }
              first-char : ∀ {c₁ cs₁} → proj₁ (flat (inj v₁')) ≡ c₁ ∷ cs₁ → c₁ ≡ c
              first-char = λ eq₁ →
                sym (proj₁ (Utils.∷-inj (trans (sym (sound-ev v₁')) eq₁)))
          in inj₁ (bne (inj-pair-len>0 loc inj sound-ev u₁ u₂)
                       (inj-pair-len>0 loc inj sound-ev v₁' v₂')
                       (seq₁ (dom u₁ u₂ max-pair (inj v₁') ¬[] first-char)))
        helper-prf u₁ u₂ max-pair v₁' v₂' (inj₁ (bne len>0 len>0' (seq₁ u₁>v₁'))) =
          let ¬[] : proj₁ (flat (inj v₁')) ≢ []
              ¬[] = λ eq → case trans (sym eq) (sound-ev v₁') of λ { () }
              first-char : ∀ {c₁ cs₁} → proj₁ (flat (inj v₁')) ≡ c₁ ∷ cs₁ → c₁ ≡ c
              first-char = λ eq₁ →
                sym (proj₁ (Utils.∷-inj (trans (sym (sound-ev v₁')) eq₁)))
          in inj₁ (bne (inj-pair-len>0 loc inj sound-ev u₁ u₂)
                       (inj-pair-len>0 loc inj sound-ev v₁' v₂')
                       (seq₁ (dom u₁ u₂ max-pair (inj v₁') ¬[] first-char)))
        helper-prf u₁ u₂ max-pair v₁' v₂' (inj₁ (bne len>0 len>0' (seq₂ u₁≡v₁' u₂>v₂'))) =
          inj₁ (bne (inj-pair-len>0 loc inj sound-ev u₁ u₂)
                    (inj-pair-len>0 loc inj sound-ev v₁' v₂')
                    (seq₂ (cong inj u₁≡v₁') u₂>v₂'))

        prf : (u : U (p ● r ` loc))
             → ≥-Max u
             → (v : U (p ● r ` loc))
             → ∃[ w ] proj₁ (flat u) ≡ (proj₁ (flat v)) ++ w
              → (l ● r ` loc) ⊢ mkinjFst inj u ≥ mkinjFst inj v
        prf (PairU u₁ u₂) (≥-max (PairU .u₁ .u₂) f₁ f₂) (PairU v₁' v₂') (w , flat-u≡flat-v++w)
          = helper-prf u₁ u₂ (≥-max (PairU u₁ u₂) f₁ f₂) v₁' v₂' (f₁ (PairU v₁' v₂') (w , flat-u≡flat-v++w))

        snd-prf : (u : U (p ● r ` loc))
               → ≥-Max u
               → (v : U (p ● r ` loc))
               → ¬ (∃[ c ] ∃[ w ] proj₁ (flat v) ≡ proj₁ (flat u) ++ c ∷ w)
                → (l ● r ` loc) ⊢ mkinjFst inj u ≥ mkinjFst inj v
        snd-prf (PairU u₁ u₂) max-pair (PairU v₁' v₂') ¬∃
          = helper-snd u₁ u₂ max-pair v₁' v₂' ¬∃
            (length (proj₁ (flat v₁')) Nat.≟ 0)
          where
            helper-snd : (u₁ : U p) (u₂ : U r) (max-pair : ≥-Max (PairU u₁ u₂)) (v₁' : U p) (v₂' : U r) (¬∃ : ¬ (∃[ c' ] ∃[ w ] proj₁ (flat (PairU v₁' v₂')) ≡ proj₁ (flat (PairU u₁ u₂)) ++ c' ∷ w))
                       → Dec (length (proj₁ (flat v₁')) ≡ 0)
                       → (l ● r ` loc) ⊢ mkinjFst inj (PairU u₁ u₂) ≥ mkinjFst inj (PairU v₁' v₂')
            helper-snd u₁ u₂ max-pair v₁' v₂' ¬∃ (yes len-v₁'≡0) =
              let ¬[] : proj₁ (flat (inj v₁')) ≢ []
                  ¬[] = λ eq → case trans (sym eq) (sound-ev v₁') of λ { () }
                  first-char : ∀ {c₁ cs₁} → proj₁ (flat (inj v₁')) ≡ c₁ ∷ cs₁ → c₁ ≡ c
                  first-char = λ eq₁ →
                    sym (proj₁ (Utils.∷-inj (trans (sym (sound-ev v₁')) eq₁)))
              in inj₁ (bne (inj-pair-len>0 loc inj sound-ev u₁ u₂)
                           (inj-pair-len>0 loc inj sound-ev v₁' v₂')
                           (seq₁ (dom u₁ u₂ max-pair (inj v₁') ¬[] first-char)))
            helper-snd u₁ u₂ max-pair v₁' v₂' ¬∃ (no ¬len-v₁'≡0)
              = helper-snd' u₁ u₂ max-pair v₁' v₂' ¬∃ ¬len-v₁'≡0
                (list-≟ (proj₁ (flat (inj v₁'))) (c ∷ proj₁ (flat u₁)))
              where
                helper-snd' : (u₁ : U p) (u₂ : U r) (max-pair : ≥-Max (PairU u₁ u₂)) (v₁' : U p) (v₂' : U r) (¬∃ : ¬ (∃[ c' ] ∃[ w ] proj₁ (flat (PairU v₁' v₂')) ≡ proj₁ (flat (PairU u₁ u₂)) ++ c' ∷ w)) (¬len-v₁'≡0 : ¬ (length (proj₁ (flat v₁')) ≡ 0))
                            → Dec (proj₁ (flat (inj v₁')) ≡ c ∷ proj₁ (flat u₁))
                            → (l ● r ` loc) ⊢ mkinjFst inj (PairU u₁ u₂) ≥ mkinjFst inj (PairU v₁' v₂')
                helper-snd' u₁ u₂ max-pair v₁' v₂' ¬∃ ¬len-v₁'≡0 (yes eq) =
                  let ¬[] : proj₁ (flat (inj v₁')) ≢ []
                      ¬[] = λ eq → case trans (sym eq) (sound-ev v₁') of λ { () }
                      first-char : ∀ {c₁ cs₁} → proj₁ (flat (inj v₁')) ≡ c₁ ∷ cs₁ → c₁ ≡ c
                      first-char = λ eq₁ →
                        sym (proj₁ (Utils.∷-inj (trans (sym (sound-ev v₁')) eq₁)))
                  in inj₁ (bne (inj-pair-len>0 loc inj sound-ev u₁ u₂)
                               (inj-pair-len>0 loc inj sound-ev v₁' v₂')
                               (seq₁ (dom u₁ u₂ max-pair (inj v₁') ¬[] first-char)))
                helper-snd' u₁ u₂ max-pair v₁' v₂' ¬∃ ¬len-v₁'≡0 (no ¬eq) =
                  let ¬[] : proj₁ (flat (inj v₁')) ≢ []
                      ¬[] = λ eq → case trans (sym eq) (sound-ev v₁') of λ { () }
                      first-char : ∀ {c₁ cs₁} → proj₁ (flat (inj v₁')) ≡ c₁ ∷ cs₁ → c₁ ≡ c
                      first-char = λ eq₁ →
                        sym (proj₁ (Utils.∷-inj (trans (sym (sound-ev v₁')) eq₁)))
                   in inj₁ (bne (inj-pair-len>0 loc inj sound-ev u₁ u₂)
                                (inj-pair-len>0 loc inj sound-ev v₁' v₂')
                                (seq₁ (dom u₁ u₂ max-pair (inj v₁') ¬[] first-char)))

-- Helper lemmas for pdU-≥-max-left-most-pres

just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

¬nothing≡just : ∀ {A : Set} {x : A} → ¬ nothing ≡ just x
¬nothing≡just ()

pdU[$c]≡[] : ∀ {c' c : Char} {loc : ℕ} → c ≢ c' → pdU[ $ c' ` loc , c ] ≡ []
pdU[$c]≡[] {c'} {c} ¬c≡c' with c' Char.≟ c
... | yes c'≡c = ⊥-elim (¬c≡c' (sym c'≡c))
... | no _ = refl

head-pdU-+-right : ∀ {l r : RE} {loc : ℕ} {c : Char} {pdi_r : PDInstance r c} {pdis_r : List (PDInstance r c)} {pdi : PDInstance (l + r ` loc) c}
  → head (List.map pdinstance-left [] ++ List.map pdinstance-right (pdi_r ∷ pdis_r)) ≡ just pdi
  → pdi ≡ pdinstance-right pdi_r
head-pdU-+-right eq = just-injective (sym eq)

pdU≡[]→¬c∷w∈l : ∀ {l c} {w : List Char} → pdU[ l , c ] ≡ [] → ¬ ((c ∷ w) ∈⟦ l ⟧)
pdU≡[]→¬c∷w∈l {l} {c} {w} pdU≡[] c∷w∈l =
  let u = unflat c∷w∈l
      eq : proj₁ (flat {l} u) ≡ c ∷ w
      eq = cong proj₁ (flat∘unflat c∷w∈l)
      any-recons : Any (Recons {l} {c} u) pdU[ l , c ]
      any-recons = pdU-complete {l} {c} {w} u eq
  in ⊥-elim (¬Any[] (subst (λ x → Any (Recons {l} {c} u) x) pdU≡[] any-recons))

¬∃→[] : ∀ {l : RE} {v : U l}
  → ¬ (∃[ c' ] ∃[ w ] proj₁ (flat v) ≡ c' ∷ w)
  → proj₁ (flat v) ≡ []
¬∃→[] {l} {v} ¬∃ with proj₁ (flat v)
... | [] = refl
... | c' ∷ w = ⊥-elim (¬∃ (c' , (w , refl)))

concatmap-pdinstance-snd-≡ : ∀ {l r : RE} {ε∈l : ε∈ l} {loc : ℕ} {c : Char} (pdis : List (PDInstance r c))
  → concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis
    ≡ concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x pdis)
      (zip-es-flat-[]-es {l} {ε∈l} (mkAllEmptyU {l} ε∈l) (mkAllEmptyU-sound {l} ε∈l))
concatmap-pdinstance-snd-≡ pdis = refl

-- first-char-lemma: Extract c∷cs form from non-empty list with known first char.
first-char-lemma : ∀ {c} (xs : List Char) → xs ≢ [] → (∀ {c₁ cs₁} → xs ≡ c₁ ∷ cs₁ → c₁ ≡ c) → ∃[ cs ] xs ≡ c ∷ cs
first-char-lemma [] ¬[] _ = ⊥-elim (¬[] refl)
first-char-lemma (c₁ ∷ cs₁) _ first-char = cs₁ , cong (λ x → x ∷ cs₁) (first-char refl)

-- extract-Recons: Extract the pdi and membership proof from Any (Recons v₁) pdis.
extract-Recons : ∀ {r c v₁} {pdis : List (PDInstance r c)}
  → Any (Recons {r} {c} v₁) pdis → ∃ λ pdi → (pdi ∈ pdis) × Recons v₁ pdi
extract-Recons (here recons-v₁) = _ , here refl , recons-v₁
extract-Recons (there v₁∈pdis) with extract-Recons v₁∈pdis
... | pdi , pdi∈ , recons-v₁ = pdi , there pdi∈ , recons-v₁

-- >-pdi-apply: Apply >-pdi evidence to specific reconstructions
>-pdi-apply : ∀ {r c pdi₁ pdi₂} → r , c ⊢ pdi₁ > pdi₂
  → ∀ (u₁ u₂ : U r) → Recons u₁ pdi₁ → Recons u₂ pdi₂ → r ⊢ u₁ > u₂
>-pdi-apply (>-pdi _ _ ev) = ev

-- >-sorted-first>all: First element of a >-sorted list is greater than all elements in the tail.
>-sorted-first>all : ∀ {r : RE} {u : U r} {us : List (U r)}
  → >-sorted (u ∷ us)
  → (v : U r) → v ∈ us
  → r ⊢ u > v
>-sorted-first>all (>-cons _ (>-just u>v)) _ (here refl) = u>v
>-sorted-first>all (>-cons s (>-just u>head)) _ (there v∈tail) =
  >-trans u>head (>-sorted-first>all s _ v∈tail)
>-sorted-first>all (>-cons >-nil >-nothing) _ ()

-- >-sorted-first≥all: First element of a >-sorted list is ≥ all elements in the list.
>-sorted-first≥all : ∀ {r : RE} {u : U r} {us : List (U r)}
  → >-sorted (u ∷ us)
  → (v : U r) → v ∈ (u ∷ us)
  → r ⊢ u ≥ v
>-sorted-first≥all _ v (here refl) = inj₂ refl
>-sorted-first≥all sorted v (there v∈us) = inj₁ (>-sorted-first>all sorted v v∈us)

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

-- ≥-max-pres-snd: Lifting maximality through pdinstance on the second component.
-- (Stub: full proof deferred to match MaxPre style)
≥-max-pres-snd : ∀ { p l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  { inj : U p → U r }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {r} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
  → ( e₁ : U l) ( u₂ : U p )
  → ≥-Max e₁
  → ≥-Max u₂
  → ( ∀ (w : List Char) → ¬ ((c ∷ proj₁ (flat u₂)) ∈⟦ l ⟧))
  → ≥-Max (mkinjSnd {l} {r} {p} {loc} inj e₁ u₂)
≥-max-pres-snd preserve e₁ u₂ max-e₁ max-u₂ ¬c∷w∈l = {!!}

-- ≥-max-pres-snd-preserve: Wrapper for ≥-max-pres-snd
≥-max-pres-snd-preserve : ∀ { p l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  { e₁ : U l }
  { flat-e₁≡[] : proj₁ (flat e₁) ≡ [] }
  { inj : U p → U r }
  { sound-ev : ∀ ( x : U p ) → proj₁ (flat {r} (inj x)) ≡ c ∷ proj₁ (flat {p} x) }
  → ≥-Max e₁
  → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
  → ( ∀ (w : List Char) → ¬ ((c ∷ w) ∈⟦ l ⟧))
  → ≥-Max-Preserve { l ● r ` loc } {c} (mk-snd-pdi {l} {r} {loc} {c} ( e₁ , flat-[] e₁ flat-e₁≡[] ) (pdinstance inj sound-ev))
≥-max-pres-snd-preserve {p} {l} {r} {ε∈l} {loc} {c} {e₁} {flat-e₁≡[]} {inj} {sound-ev} max-e₁ (≥-max-pres f₁ f₂) ¬c∷w∈l =
  ≥-max-pres
    (λ u maxu v ∃w → pair-≥-from-snd u v (f₁ u maxu v ∃w))
    (λ u maxu v ¬∃ → pair-≥-from-snd u v (f₂ u maxu v ¬∃))
  where
    len>0-pair-inj : ∀ (u : U p) → length (proj₁ (flat (PairU {l} {r} {loc} e₁ (inj u)))) Nat.> 0
    len>0-pair-inj u =
      let eq : proj₁ (flat (PairU e₁ (inj u))) ≡ c ∷ proj₁ (flat u)
          eq =
            begin
              proj₁ (flat (PairU e₁ (inj u)))
            ≡⟨ refl ⟩
              proj₁ (flat e₁) ++ proj₁ (flat (inj u))
            ≡⟨ cong (_++ proj₁ (flat (inj u))) flat-e₁≡[] ⟩
              [] ++ proj₁ (flat (inj u))
            ≡⟨ ++-identityˡ (proj₁ (flat (inj u))) ⟩
              proj₁ (flat (inj u))
            ≡⟨ sound-ev u ⟩
              c ∷ proj₁ (flat u)
            ∎
      in subst (λ xs → length xs Nat.> 0) (sym eq) (Nat.s≤s Nat.z≤n)

    pair-≥-from-snd : ∀ (u v : U p) → r ⊢ inj u ≥ inj v → (l ● r ` loc) ⊢ PairU e₁ (inj u) ≥ PairU e₁ (inj v)
    pair-≥-from-snd u v (inj₁ inj-u>inj-v) =
      inj₁ (bne (len>0-pair-inj u) (len>0-pair-inj v) (seq₂ refl inj-u>inj-v))
    pair-≥-from-snd u v (inj₂ eq) = inj₂ (cong (PairU e₁) eq)

pdU-≥-max-left-most-pres : ∀ { r : RE } { c : Char } { pdi : PDInstance r c }
  → head pdU[ r , c ] ≡ just pdi
  → ≥-Max-Preserve pdi

pdU-≥-max-left-most-pres {ε} {c} {pdi} eq = ⊥-elim (¬nothing≡just eq)

pdU-≥-max-left-most-pres {$ c' ` loc} {c} {pdinstance inj sound-ev} eq with c' Char.≟ c
... | no ¬c'≡c
  rewrite pdU[$c]≡[] ¬c'≡c
  = ⊥-elim (¬nothing≡just eq)
... | yes refl
  with just-injective eq
... | refl = ≥-max-pres (λ { EmptyU _ EmptyU _ → inj₂ refl }) (λ { EmptyU _ EmptyU _ → inj₂ refl })

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
        (≥-max-pres-left pdi_l (pdU-≥-max-left-most-pres {l} {c} (cong head pdU-l≡)))
    helper [] [] pdU-l≡ pdU-r≡ eq =
      ⊥-elim (¬nothing≡just eq)
    helper [] (pdi_r ∷ pdis_r) pdU-l≡ pdU-r≡ eq =
      subst (λ x → ≥-Max-Preserve x) (sym (head-pdU-+-right eq))
        (≥-max-pres-right pdi_r (pdU-≥-max-left-most-pres {r} {c} (cong head pdU-r≡)))

pdU-≥-max-left-most-pres {l ● r ` loc} {c} {pdi} eq with ε∈? l
... | no ¬ε∈l =
  helper-no ¬ε∈l pdU[ l , c ] refl eq
  where
    helper-no : (¬ε∈l : ¬ ε∈ l) → (pdU-l : List (PDInstance l c))
      → pdU[ l , c ] ≡ pdU-l
      → head (List.map pdinstance-fst pdU-l) ≡ just pdi
      → ≥-Max-Preserve pdi
    helper-no ¬ε∈l [] _ eq = ⊥-elim (¬nothing≡just eq)
    helper-no ¬ε∈l (pdinstance {p} inj sound-ev ∷ pdis_l) pdU-l≡ eq =
      let >-inc-all : All >-Inc-≅ (pdinstance inj sound-ev ∷ pdis_l)
          >-inc-all = subst (λ xs → All >-Inc-≅ xs) pdU-l≡ (pdU->-inc {l} {c})
          >-inc-ev = All.head >-inc-all
      in subst (λ x → ≥-Max-Preserve x) (just-injective eq)
        (≥-max-pres-fst inj sound-ev
          (pdU-≥-max-left-most-pres {l} {c} {pdinstance {p} inj sound-ev} (cong head pdU-l≡))
          >-inc-ev
          (λ u₁ u₂ max-pair v₁ ¬[] first-char →
            dom-lemma u₁ v₁ ¬[] first-char))
      where
        dom-lemma : (u₁ : U p) (v₁ : U l)
          → proj₁ (flat v₁) ≢ []
          → (∀ {c₁ cs₁} → proj₁ (flat v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c)
          → l ⊢ inj u₁ > v₁
        dom-lemma u₁ v₁ ¬[] first-char
          with first-char-lemma (proj₁ (flat v₁)) ¬[] first-char
        ... | cs₁ , flat-v₁≡c∷cs₁
          with pdU-complete v₁ flat-v₁≡c∷cs₁
            | pdU-complete (inj u₁) (sound-ev u₁)
        ... | v₁∈pdU | inj-u₁∈pdU
          rewrite pdU-l≡
          = case v₁∈pdU of λ {
              (here recons-v₁) →
                -- Hard structural lifting hole: v₁ is in the image of the first pdi,
                -- so v₁ ≡ inj v₁'. Need l ⊢ inj u₁ > inj v₁'. Requires either
                -- showing u₁ ≅ v₁' (to apply >-Inc-≅) or a stronger max-pair lemma.
                {!!} ;
              (there v₁∈pdis) →
                case inj-u₁∈pdU of λ {
                  (here recons-inj-u₁) →
                    case extract-Recons v₁∈pdis of λ {
                      (pdi'' , pdi''∈ , recons-v₁) →
                        let sorted = subst (λ x → Ex>-sorted x) pdU-l≡ (pdU-sorted {l} {c})
                        in >-pdi-apply
                             (Ex>-sorted-first>all sorted pdi'' pdi''∈)
                             (inj u₁) v₁ recons-inj-u₁ recons-v₁
                    } ;
                  (there inj-u₁∈pdis') →
                    -- Hard hole: both inj u₁ and v₁ are reconstructed by later pdis.
                    -- Need to compare their respective pdis in the sorted list, but
                    -- the relative order is unknown. May require showing inj u₁ is
                    -- always reconstructed by the first pdi (i.e. pdU-complete returns here).
                    {!!}
                }
            }
... | yes ε∈l =
  helper-yes pdU[ l , c ] pdU[ r , c ] refl refl eq
  where
    helper-yes : (pdU-l : List (PDInstance l c)) → (pdU-r : List (PDInstance r c))
      → pdU[ l , c ] ≡ pdU-l
      → pdU[ r , c ] ≡ pdU-r
      → head (List.map pdinstance-fst pdU-l ++ concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU-r) ≡ just pdi
      → ≥-Max-Preserve pdi
    helper-yes (pdinstance {p} inj sound-ev ∷ pdis_l) pdU-r pdU-l≡ pdU-r≡ eq =
      let >-inc-all : All >-Inc-≅ (pdinstance inj sound-ev ∷ pdis_l)
          >-inc-all = subst (λ xs → All >-Inc-≅ xs) pdU-l≡ (pdU->-inc {l} {c})
          >-inc-ev = All.head >-inc-all
      in subst (λ x → ≥-Max-Preserve x) (just-injective eq)
        (≥-max-pres-fst inj sound-ev
          (pdU-≥-max-left-most-pres {l} {c} {pdinstance {p} inj sound-ev} (cong head pdU-l≡))
          >-inc-ev
          (λ u₁ u₂ max-pair v₁ ¬[] first-char →
            dom-lemma-yes u₁ v₁ ¬[] first-char))
      where
        dom-lemma-yes : (u₁ : U p) (v₁ : U l)
          → proj₁ (flat v₁) ≢ []
          → (∀ {c₁ cs₁} → proj₁ (flat v₁) ≡ c₁ ∷ cs₁ → c₁ ≡ c)
          → l ⊢ inj u₁ > v₁
        dom-lemma-yes u₁ v₁ ¬[] first-char
          with first-char-lemma (proj₁ (flat v₁)) ¬[] first-char
        ... | cs₁ , flat-v₁≡c∷cs₁
          with pdU-complete v₁ flat-v₁≡c∷cs₁
            | pdU-complete (inj u₁) (sound-ev u₁)
        ... | v₁∈pdU | inj-u₁∈pdU
          rewrite pdU-l≡
          = case v₁∈pdU of λ {
              (here recons-v₁) →
                -- Same hard structural lifting hole as in dom-lemma:
                -- v₁ ≡ inj v₁', need l ⊢ inj u₁ > inj v₁'.
                {!!} ;
              (there v₁∈pdis) →
                case inj-u₁∈pdU of λ {
                  (here recons-inj-u₁) →
                    case extract-Recons v₁∈pdis of λ {
                      (pdi'' , pdi''∈ , recons-v₁) →
                        let sorted = subst (λ x → Ex>-sorted x) pdU-l≡ (pdU-sorted {l} {c})
                        in >-pdi-apply
                             (Ex>-sorted-first>all sorted pdi'' pdi''∈)
                             (inj u₁) v₁ recons-inj-u₁ recons-v₁
                    } ;
                  (there inj-u₁∈pdis') →
                    -- Same hard hole as in dom-lemma: relative ordering of
                    -- pdis reconstructing inj u₁ and v₁ is unknown.
                    {!!}
                }
            }
    helper-yes [] [] pdU-l≡ pdU-r≡ eq =
      ⊥-elim (¬nothing≡just
        (trans (sym (cong head (concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c}))) eq))
    helper-yes [] (pdinstance {p} inj sound-ev ∷ pdis_r) pdU-l≡ pdU-r≡ eq
      rewrite concatmap-pdinstance-snd-≡ {l} {r} {ε∈l} {loc} {c} (pdinstance inj sound-ev ∷ pdis_r)
      with mkAllEmptyU {l} ε∈l in eq-mkAllEmptyU | mkAllEmptyU-sound {l} ε∈l | mkAllEmptyU-sorted {l} ε∈l
    ... | e₁ ∷ es₁ | flat-[] e₁ flat-e₁≡[] ∷ flat-[]-es₁ | sorted =
        subst (λ x → ≥-Max-Preserve x) (just-injective eq)
          (≥-max-pres-snd-preserve {e₁ = e₁} {flat-e₁≡[] = flat-e₁≡[]}
            (≥-max e₁
              (λ v (w , flat-e₁≡flat-v++w) →
                let flat-v≡[] : proj₁ (flat v) ≡ []
                    flat-v≡[] = proj₁ (++-≡-[] (trans (sym flat-e₁≡flat-v++w) flat-e₁≡[]))
                in >-sorted-first≥all sorted v
                     (subst (λ xs → v ∈ xs) eq-mkAllEmptyU
                       (mkAllEmptyU-complete ε∈l v (flat-[] v flat-v≡[]))))
               (λ v ¬∃ →
                  let ¬∃' : ¬ (∃[ c' ] ∃[ w ] proj₁ (flat v) ≡ c' ∷ w)
                      ¬∃' = subst (λ xs → ¬ (∃[ c' ] ∃[ w ] proj₁ (flat v) ≡ xs ++ c' ∷ w)) flat-e₁≡[] ¬∃
                      flat-v≡[] : proj₁ (flat v) ≡ []
                      flat-v≡[] = ¬∃→[] {l} {v} ¬∃'
                 in >-sorted-first≥all sorted v
                      (subst (λ xs → v ∈ xs) eq-mkAllEmptyU
                        (mkAllEmptyU-complete ε∈l v (flat-[] v flat-v≡[])))))
            (pdU-≥-max-left-most-pres {r} {c} {pdinstance {p} inj sound-ev} (cong head pdU-r≡))
            (λ w → pdU≡[]→¬c∷w∈l {l} {c} {w} pdU-l≡))

pdU-≥-max-left-most-pres {r * ε∉r ` loc} {c} {pdi} eq
  with pdU[ r , c ]
... | [] = ⊥-elim (¬nothing≡just eq)
... | pdi_r ∷ pdis_r = {!!}
```
