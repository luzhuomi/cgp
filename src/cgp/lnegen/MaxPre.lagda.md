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
          → r ⊢ u > v )
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
      → r ⊢ inj u > inj v )      
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
  → l ⊢ u > u'
≥-max-pair-inv4 = {!!}   

{-
-- this is not provable. See the counter example
≥-max-pair-inv5 : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( u : U l )
  → ( v : U r )
  → ≥-Max (PairU {l} {r} {loc} u v)
  → ( u' : U l )
  → ( v' : U r )
  → ∃[ w ] proj₁ (flat u) ++ proj₁ (flat v) ≡ (proj₁ (flat u') ++ proj₁ (flat v')) ++ w
  → ∃[ w' ] proj₁ (flat u) ≡ (proj₁ (flat u')) ++ w'
≥-max-pair-inv5  {l} {r} {loc} {c} u v (≥-max (PairU .u .v) pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' a ) u' v' ( w , |uv|≡|u'v'|++w )  with pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' (PairU u' v') ( w , |uv|≡|u'v'|++w ) 
≥-max-pair-inv5  {l} {r} {loc} {c} u v (≥-max (PairU .u .v) pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' a ) u' v' ( w , |uv|≡|u'v'|++w )  | inj₂ pair-u-v≡pair-u'-v' with inv-pairU u v u' v' pair-u-v≡pair-u'-v'
...                            | u≡u' , v≡v' rewrite u≡u' = []  , sym (++-identityʳ (proj₁ (flat u')))
≥-max-pair-inv5  {l} {r} {loc} {c} u v (≥-max (PairU .u .v) pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' a ) u' v' ( w , |uv|≡|u'v'|++w )  | inj₁ (be len|uv|≡|u'v'| len|u'v'|≡0 (seq₂ u≡u' _)) rewrite u≡u' =  []  , sym (++-identityʳ (proj₁ (flat u')))
≥-max-pair-inv5  {l} {r} {loc} {c} u v (≥-max (PairU .u .v) pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' a ) u' v' ( w , |uv|≡|u'v'|++w )  | inj₁ (be len|uv|≡|u'v'| len|u'v'|≡0 (seq₁ u>u')) = ev 
  where 
    |u'v'|≡[] : (proj₁ (flat (PairU {l} {r} {loc} u' v'))) ≡ []
    |u'v'|≡[]  = Utils.length≡0→[]  len|u'v'|≡0
    |u'|≡[] : (proj₁ (flat u')) ≡ []
    |u'|≡[] = proj₁ (++-≡-[] |u'v'|≡[] )
    ev : ∃[ w ] proj₁ (flat u) ≡ proj₁ (flat u') ++ w
    ev rewrite |u'|≡[] = ( proj₁ (flat u) , ++-identityˡ (  proj₁ (flat u) ) )
≥-max-pair-inv5  {l} {r} {loc} {c} u v (≥-max (PairU .u .v) pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' a ) u' v' ( w , |uv|≡|u'v'|++w )  | inj₁ (bne len|uv|>0 len|u'v'|>0 (seq₂ u≡u' _)) rewrite u≡u' =  []  , sym (++-identityʳ (proj₁ (flat u'))) 
≥-max-pair-inv5  {l} {r} {loc} {c} u v (≥-max (PairU .u .v) pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' pair-u'-v'→¬∃w→¬w≡[]×|u'v'|≡|uv|++w→uv>u'v' ) u' v' ( w , |uv|≡|u'v'|++w )  | inj₁ (bne len|uv|>0 len|u'v'|>0 (seq₁ u>u')) = {!!}
  

  where    -- a counter example
    l₁ r₁ : RE
    l₁ = ($ 'a' ` 1 ) ● ( ( $ 'b' ` 2 ) + ( ($ 'b' ` 3) ● ($ 'b' ` 4 ) ` 5) ` 6) ` 7 
    r₁ = (($ 'b' ` 8) ● ($ 'c' ` 9) ` 10 ) + ($ 'c' ` 11) ` 12
    x x' : U l₁
    y y' : U r₁
    x =  PairU (LetterU 'a') (LeftU (LetterU 'b'))
    y = LeftU (PairU (LetterU 'b') (LetterU 'c'))
    x' = PairU (LetterU 'a') (RightU (PairU (LetterU 'b') (LetterU 'b')))
    y' = RightU (LetterU 'c')
    xy>x'y' : l₁ ● r₁ ` 13 ⊢ (PairU x y) > (PairU x' y')
    xy>x'y' = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁
                            (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                             (seq₂ refl (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) choice-lr))))
    -- PairU x y is the maximal
    -- but |x'| is not a prefix of |x|
    max-|xy| :  ≥-Max (PairU {l₁} {r₁} {13} x y)
    max-|xy| = ≥-max {l₁ ● r₁ ` 13} (PairU x y) max-ev {!!} 
      where
        max-ev : (v₁ : U (l₁ ● r₁ ` 13) )
          → ∃[ w' ] proj₁ (flat (PairU {l₁} {r₁} {13} x y)) ≡ proj₁ (flat v₁) ++ w'
          → (l₁ ● r₁ ` 13) ⊢ PairU x y ≥ v₁
        max-ev (PairU (PairU (LetterU 'a') (LeftU (LetterU 'b'))) (LeftU (PairU (LetterU 'b') (LetterU 'c')))) ( [] , |xy|≡|x₁y₁|++[] ) =  inj₂ refl
        max-ev (PairU (PairU (LetterU 'a') (RightU (PairU (LetterU 'b') (LetterU 'b')))) ( RightU (LetterU 'c') )) ( [] , |xy|≡|x₁y₁|++[] ) = inj₁ xy>x'y'
        max-ev (PairU (PairU (LetterU 'a') (LeftU (LetterU 'b')))  ( RightU (LetterU 'c') )) ()
        max-ev (PairU (PairU (LetterU 'a') (RightU (PairU (LetterU 'b') (LetterU 'b')))) (LeftU (PairU (LetterU 'b') (LetterU 'c')))) () 
    -- |xy| ≡ a b b c
    -- what about the last case? a b b b c ? they are not prefix of one another.

≥-max-pair-inv5  {l} {r} {loc} {c} u v (≥-max (PairU .u .v) pair-u'-v'→∃w|uv|≡|u'v'|++w→uv≥u'v' a) u' v' ( w , |uv|≡|u'v'|++w )  | inj₁ (lne len|uv|>0 len|u'v'|≡0) = ev 
  where
    |u'v'|≡[] : (proj₁ (flat (PairU {l} {r} {loc} u' v'))) ≡ []
    |u'v'|≡[]  = Utils.length≡0→[]  len|u'v'|≡0
    |u'|≡[] : (proj₁ (flat u')) ≡ []
    |u'|≡[] = proj₁ (++-≡-[] |u'v'|≡[] )
    ev : ∃[ w ] proj₁ (flat u) ≡ proj₁ (flat u') ++ w
    ev rewrite |u'|≡[] = ( proj₁ (flat u) , ++-identityˡ (  proj₁ (flat u) ) )
-}

-- insights:
-- there are two kinds of leave nodes for the > proof, with either lne or choice-lr as the inner most leaf nodes
-- all inj should not change the inner most leaf nodes
-- inj does not change the inner most choice-lr to something else?; seems not true; mkinjFst changes that
-- inj does not change the inner most lne to something else? ; seemsnot true 
-- what about mkinjSnd ? should be the same?

data leaf-kind : Set where
  lne-kind : leaf-kind
  clr-kind : leaf-kind

mutual
  >-leaf-kind : ∀ { r : RE } { u v : U r } → r ⊢ u > v → leaf-kind
  >-leaf-kind (lne _ _) = lne-kind
  >-leaf-kind (be _ _ p) = >-ⁱ-leaf-kind p
  >-leaf-kind (bne _ _ p) = >-ⁱ-leaf-kind p

  >-ⁱ-leaf-kind : ∀ { r : RE } { u v : U r } → r ⊢ u >ⁱ v → leaf-kind
  >-ⁱ-leaf-kind (seq₁ p) = >-leaf-kind p
  >-ⁱ-leaf-kind (seq₂ _ p) = >-leaf-kind p
  >-ⁱ-leaf-kind choice-lr = clr-kind
  >-ⁱ-leaf-kind (choice-ll p) = >-leaf-kind p
  >-ⁱ-leaf-kind (choice-rr p) = >-leaf-kind p
  >-ⁱ-leaf-kind star-cons-nil = clr-kind
  >-ⁱ-leaf-kind (star-head p) = >-leaf-kind p
  >-ⁱ-leaf-kind (star-tail _ p) = >-leaf-kind p

data inj-leaf-pres : ∀ { p r : RE } { c : Char } → PDInstance r c → Set where
  inj-leaf-pres-con : ∀ { p r : RE } { c : Char }
                     { inj : U p → U r }
                     { sound-ev : ∀ ( u : U p ) → proj₁ (flat {r} (inj u)) ≡ c ∷ proj₁ (flat {p} u) }
                     → ( ( u v : U p )
                       → (prf₁ : p ⊢ u > v)
                       → ∃[ prf₂ ] (>-leaf-kind {p} {u} {v} prf₁) ≡ (>-leaf-kind {r} {inj u} {inj v} prf₂ ) )
                     → inj-leaf-pres {p} {r} {c} (pdinstance inj sound-ev) 


-- do we have some thing like ≥-Max-Preserve but for the first of a pair parse tree?

≥-max-pres-left : ∀ { l r : RE } {loc : ℕ } { c : Char } 
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-left pdi)
≥-max-pres-left {l} {r} {loc} {c} (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u>inj-v) =
  ≥-max-pres (λ u maxu v ∃w|u|≡|v|++w → left-mono-≥ (u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u maxu v ∃w|u|≡|v|++w))
             (λ u maxu v ¬∃cw|v|≡|u|++cw → left-mono (u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u>inj-v u maxu v ¬∃cw|v|≡|u|++cw))


≥-max-pres-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance r c )
  → ≥-Max-Preserve {r} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-right pdi)
≥-max-pres-right {l} {r} {loc} {c} (pdinstance {p} .{r} .{c} inj s-ev) (≥-max-pres  u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u>inj-v) =
  ≥-max-pres (λ u maxu v ∃w|u|≡|v|++w  → right-mono-≥ (u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u maxu v ∃w|u|≡|v|++w))        
             (λ u maxu v ¬∃cw|v|≡|u|++cw → right-mono (u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u>inj-v u maxu v ¬∃cw|v|≡|u|++cw))

≥-max-pres-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {c} pdi
  → ≥-Max-Preserve {l ● r ` loc} {c} (pdinstance-fst pdi)
≥-max-pres-fst {l} {r} {loc} {c}  (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres u→maxu→v→∃w|u|≡|v|++w→inj-u≥inj-v u→maxu→v→¬∃cw|v|≡|u|++cw→inj-u>inj-v) =
  ≥-max-pres prf {!!}  
  where
    prf :  (u : U (p ● r ` loc))
        →  ≥-Max u
        →  (v : U (p ● r ` loc))
        →  ∃[ w ] proj₁ (flat u) ≡ (proj₁ (flat v)) ++ w 
        → (l ● r ` loc) ⊢ mkinjFst inj u ≥ mkinjFst inj v
    prf (PairU v₁ v₂)
        ≥-max-v₁v₂@(≥-max (PairU .v₁ .v₂) pair-v₁'v₂'→∃w|v₁v₂|≡|v₁'v₂'|++w→pair-v₁v₂>pair-v₁'v₂' pair-v₁'v₂'→¬∃w→|v₁'v₂'|≡|v₁v₂|++w→pair-v₁v₂>pair-v₁'v₂' )
        (PairU v₁' v₂')
        ( w , |v₁v₂|≡|v₁'v₂'|++w )
        with pair-v₁'v₂'→∃w|v₁v₂|≡|v₁'v₂'|++w→pair-v₁v₂>pair-v₁'v₂' (PairU v₁' v₂') ( w , |v₁v₂|≡|v₁'v₂'|++w )
    ... | inj₁ (be len|v₁v₂|≡len|v₁'v₂'| len|v₁v₂|≡0 pairv₁v₂>ⁱpairv₁'v₂') = {!!}
      -- by calling ≥-max-pair-inv3 to establish IH
      -- we have inj v₁ ≥ inj v₁'
      -- then we can prove by bne _ _ (seq₁ _)
    ... | inj₁ (lne len|v₁v₂|>0 len|v₁'v₂'|≡0) = {!!}
      -- by calling ≥-max-pair-inv3 to establish IH
      -- we have inj v₁ ≥ inj v₁'
      -- then we can prove by bne _ _ (seq₁ _)
    ... | inj₁ (bne len|v₁v₂|>0 len|v₁'v₂'|>0 pairv₁v₂>ⁱpairv₁'v₂') = {!!}
      -- by calling ≥-max-pair-inv3 to establish IH
      -- we have inj v₁ ≥ inj v₁'
      -- then we can prove by bne _ _ (seq₁ _)
    ... | inj₂ pairv₁v₂≡pairv₁'v₂' = inj₂ {!!}  -- cong
  

  


```
