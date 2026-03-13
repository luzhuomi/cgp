```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.ExtendedOrder where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ;
  ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ; ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ;
  first ; ε∉r→¬first-r≡[] )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ∷-inj ; ¬∷≡[] ; inv-map-[] ; inv-concatMap-map-f-[] ) 


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )


import cgp.ParseTree as ParseTree
open ParseTree using (
  U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ;
  flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;
  flat-Uε≡[] ;
  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; unListU ; listU∘unListU ;
  u-of-r*-islist ; pair-≡ ; left-≡ ; right-≡ ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU)

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ; mkAllEmptyU≢[] ; all-flat-[]-left ; all-flat-[]-right ; proj₁flat-v≡[]→ε∈r)

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ; 
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ; mkinjListSoundEv ; 
  pdinstance-fst ; mkinjFst   ; mkinjFstSoundEv ; 
  pdinstance-snd ; mk-snd-pdi ; mkinjSnd ; mkinjSndSoundEv ; 
  concatmap-pdinstance-snd ; zip-es-flat-[]-es  ;
  pdinstance-assoc; inv-assoc ;
  compose-pdi-with   ; concatmap-pdinstance-snd-[]≡[]
  ) 


import cgp.Recons as Recons
open Recons using ( Recons ; recons ;
  Recons* ; recons* ;
  inv-recons-left ;   inv-recons-right ; inv-recons-fst ; inv-recons-snd ; inv-recons-star ; inv-recons-assoc ; 
  inv-recons*-compose-pdi-with ; 
  ¬recons-right-from-pdinstance-left ; ¬recons-left-from-pdinstance-right ; ¬recons-[]-from-pdinstance-star 
  )


import cgp.posix.PartialDerivative as PartialDerivative
open PartialDerivative using (
  pdU[_,_] ; -- pdUConcat ;
  pdinstance-oplus ; fuse ; mkfuseInj ; mkfuseInjSoundEv ; 
  pdUMany[_,_]; pdUMany-aux;
  advance-pdi*-with-c ; 
  parseAll[_,_] ; buildU ;
  pdi*-∃
  -- ;
  -- recons-v→¬proj₁flat-v≡[]
  )


import cgp.posix.Order as PosixOrder
open PosixOrder using ( _⊢_>_ ; len-≡ ; len-> ; 
  _⊢_>ⁱ_ ; seq₁ ; seq₂ ;
  choice-ll ; choice-rr ;
  choice-lr ;
  choice-rl ; star-head ; star-cons-nil ; star-tail ; 
  >-sorted ; >-nil ; >-cons ; concat-sorted ; 
  mkAllEmptyU-sorted ;
  >-maybe ; >-nothing ; >-just ; 
  >-trans ; *>-Inc ; *>-inc ;
  concatmap-advance-pdi*-with-c-*>inc ;
  pdUMany-*>-inc )   



import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _≥_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ )


import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length  )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalˡ ; ++-conicalʳ ;  ++-assoc )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)


import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map ; tabulate )

open import Data.List.Relation.Unary.Any using (Any; here; there ; map)

import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )


import Data.List.Membership.Propositional
open Data.List.Membership.Propositional using (_∈_)


import Relation.Nullary as Nullary 
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

open import Function using (_∘_ ; flip)

```


```agda
-- a relation shoow a partial derivative instance is "hiding" a partial derivative p
data Inhabit : ∀ { r : RE } { c : Char } → RE →  PDInstance r c → Set where
  hide : ∀ { p r : RE } { c : Char } 
    → ( inj : U p → U r ) -- ^ the injection function 
    → ( s-ev : ∀ ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) )  -- s^ soundnes evidence
    → Inhabit {r} {c} p (pdinstance {p} {r} {c} inj s-ev)

-- a list of pdinstance is homogenous iff all of them are hiding the same pd.
data Homogenous : ∀ { r : RE } { c : Char } → List (PDInstance r c) → Set where
  homogenous : ∀ { r : RE } { c : Char } (pdis : List (PDInstance r c ) )
    → ∃[ p ] (All (Inhabit p) pdis)
    → Homogenous {r} {c} pdis 
    


map-left-inhabit⁺ : ∀ { l r p : RE } { loc : ℕ } { c : Char } { pdi : PDInstance l c } { pdis : List (PDInstance l c) }
  → Inhabit {l} {c} p pdi
  → All (Inhabit {l} {c}  p) pdis
  -------------------------------------------
  → All (Inhabit {l + r ` loc} {c}  p) (List.map pdinstance-left (pdi ∷ pdis))
map-left-inhabit⁺ {l} {r} {p} {loc} {c} {pdi@(pdinstance .{p} .{l} .{c} inj s-ev)} {[]}
  (hide .{p} .{l} .{c} .(inj) .(s-ev)) [] = hide (λ u → LeftU (inj u)) s-ev ∷ []
map-left-inhabit⁺ {l} {r} {p} {loc} {c} {pdi@(pdinstance .{p} .{l} .{c} inj s-ev)} {pdi'@(pdinstance .{p} .{l} .{c} inj' s-ev') ∷ pdis} 
  (hide .{p} .{l} .{c} .(inj) .(s-ev)) ((hide .{p} .{l} .{c} .(inj') .(s-ev')) ∷ all-hide-p-pdis ) = hide (λ u → LeftU (inj u)) s-ev ∷ map-left-inhabit⁺ (hide inj' s-ev') all-hide-p-pdis 

map-left-Homogenous : ∀ { l r : RE } {loc : ℕ } { c : Char } { pdis : List (PDInstance l c) }
  → Homogenous pdis
  --------------------------------------------------
  → Homogenous (List.map (pdinstance-left {l} {r} {loc} {c}) pdis)
map-left-Homogenous {l} {r} {loc} {c} {[]} (homogenous [] ( p , [] ) ) =  homogenous (List.map pdinstance-left []) (p , [])
map-left-Homogenous {l} {r} {loc} {c} {pdi@(pdinstance {p} {l} {c} inj s-ev) ∷ pdis }  (homogenous  (.(pdi) ∷ .(pdis)) ( .(p) , hide-p-pdi@(hide .{p} {l} {c} .(inj) .(s-ev)) ∷ hide-p-pdis ))
  = homogenous (pdinstance {p} {l + r ` loc} {c} (λ u → LeftU (inj u)) s-ev ∷  List.map pdinstance-left pdis) (p , map-left-inhabit⁺ {l} {r} {p} {loc} {c} {pdi} {pdis}  hide-p-pdi  hide-p-pdis  ) 


map-right-inhabit⁺ : ∀ { l r p : RE } { loc : ℕ } { c : Char } { pdi : PDInstance r c } { pdis : List (PDInstance r c) }
  → Inhabit {r} {c} p pdi
  → All (Inhabit {r} {c} p) pdis
  -------------------------------------------
  → All (Inhabit {l + r ` loc} {c}  p) (List.map pdinstance-right (pdi ∷ pdis))
map-right-inhabit⁺ {l} {r} {p} {loc} {c} {pdi@(pdinstance .{p} .{r} .{c} inj s-ev)} {[]}
  (hide .{p} .{r} .{c} .(inj) .(s-ev)) [] = hide (λ u → RightU (inj u)) s-ev ∷ []
map-right-inhabit⁺ {l} {r} {p} {loc} {c} {pdi@(pdinstance .{p} .{r} .{c} inj s-ev)} {pdi'@(pdinstance .{p} .{r} .{c} inj' s-ev') ∷ pdis} 
  (hide .{p} .{r} .{c} .(inj) .(s-ev)) ((hide .{p} .{r} .{c} .(inj') .(s-ev')) ∷ all-hide-p-pdis ) = hide (λ u → RightU (inj u)) s-ev ∷
                                                                                                      map-right-inhabit⁺ (hide inj' s-ev') all-hide-p-pdis 

map-right-Homogenous : ∀ { l r : RE } {loc : ℕ } { c : Char } { pdis : List (PDInstance r c) }
  → Homogenous pdis
  --------------------------------------------------
  → Homogenous (List.map (pdinstance-right {l} {r} {loc} {c}) pdis)
map-right-Homogenous {l} {r} {loc} {c} {[]} (homogenous [] ( p , [] ) ) =  homogenous (List.map pdinstance-right []) (p , [])
map-right-Homogenous {l} {r} {loc} {c} {pdi@(pdinstance {p} {r} {c} inj s-ev) ∷ pdis }  (homogenous  (.(pdi) ∷ .(pdis)) ( .(p) , hide-p-pdi@(hide .{p} {r} {c} .(inj) .(s-ev)) ∷ hide-p-pdis ))
  = homogenous (pdinstance {p} {l + r ` loc} {c} (λ u → RightU (inj u)) s-ev ∷  List.map pdinstance-right pdis) (p , map-right-inhabit⁺ {l} {r} {p} {loc} {c} {pdi} {pdis}  hide-p-pdi  hide-p-pdis  )



map-fst-inhabit⁺ : ∀ { l r p : RE } { loc : ℕ } { c : Char } { pdi : PDInstance l c } { pdis : List (PDInstance l c) }
  → Inhabit {l} {c} p pdi
  → All (Inhabit {l} {c} p) pdis
  -------------------------------------------------
  → All (Inhabit {l ● r ` loc} {c} ( p ● r ` loc) ) (List.map pdinstance-fst (pdi ∷ pdis))
map-fst-inhabit⁺ {l} {r} {p} {loc} {c} {pdi@(pdinstance .{p} .{l} .{c} inj s-ev)} {[]}
  (hide .{p} .{l} .{c} .(inj) .(s-ev)) [] = hide (mkinjFst inj) (mkinjFstSoundEv inj s-ev)   ∷ []
map-fst-inhabit⁺ {l} {r} {p} {loc} {c} {pdi@(pdinstance .{p} .{l} .{c} inj s-ev)} {pdi'@(pdinstance .{p} .{l} .{c} inj' s-ev') ∷ pdis}
  (hide .{p} .{l} .{c} .(inj) .(s-ev)) ((hide .{p} .{l} .{c} .(inj') .(s-ev')) ∷ all-hide-p-pdis ) = hide (mkinjFst inj)
                                                                                                      (mkinjFstSoundEv inj s-ev)  
                                                                                                      ∷ map-fst-inhabit⁺ (hide inj' s-ev') all-hide-p-pdis 
      

map-fst-Homogenous : ∀ { l r : RE } { loc : ℕ } { c : Char } { pdis : List (PDInstance l c)  }
  → Homogenous pdis
  --------------------------------------------------
  → Homogenous (List.map (pdinstance-fst {l} {r} {loc} {c}) pdis)
map-fst-Homogenous {l} {r} {loc} {c} {[]} (homogenous [] ( p , [] )) = homogenous (List.map pdinstance-fst []) (l , [])
map-fst-Homogenous {l} {r} {loc} {c} {pdi@(pdinstance {p} {l} {c} inj s-ev) ∷ pdis }  (homogenous  (.(pdi) ∷ .(pdis)) ( .(p) , hide-p-pdi@(hide .{p} {l} {c} .(inj) .(s-ev)) ∷ hide-p-pdis ))
  = homogenous (List.map pdinstance-fst (pdinstance inj s-ev ∷ pdis)) ( (p ● r ` loc) , map-fst-inhabit⁺ (hide inj s-ev) hide-p-pdis ) 


cong-mk-snd-pdi-inhabit : ∀ { l r p : RE } { loc : ℕ } { c : Char }
  → ( e-flat-[]-e : ∃[ e ] Flat-[] l e )
  → ( pdi : PDInstance r c ) 
  → Inhabit {r} {c} p pdi
  → Inhabit {l ● r ` loc} {c} p (mk-snd-pdi {l} {r} {loc} {c} e-flat-[]-e pdi)
cong-mk-snd-pdi-inhabit {l} {r} {p} {loc} {c} ( e , (flat-[] .(e) proj₁∘flate≡[]) ) (pdinstance .{p} .{r} .{c} inj s-ev) (hide inj s-ev)
  = hide (mkinjSnd inj e) (mkinjSndSoundEv {p} {l} {r} {loc} {c} inj s-ev e (flat-[] e proj₁∘flate≡[]))
                          
concatmap-snd-inhabit⁺ :  ∀ { l r p : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char } { pdi : PDInstance r c } { pdis : List (PDInstance r c) }
  → Inhabit {r} {c} p pdi
  → All (Inhabit {r} {c} p) pdis
  --------------------------------------------
  → All (Inhabit {l ● r ` loc} {c} p) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} (pdi ∷ pdis))
  -- hm... p is the partial derivative here. not p ● r !!!
  -- so it is not weaksingleton or homomorphic..
  -- posix has a very unique extended ordering
  -- it is like staircase, a list of pdis with the same partial derivative,
  -- the until a concat case... change to another partial derivative which should be following > order.  let me think about how to write it down as data type in agda.
  -- update: it is ok, because (pˡ ● r) the fst'ed pd and pʳ the snd'ed pd, will be combined by oplus and become (pˡ ● r) + pʳ
concatmap-snd-inhabit⁺ {l} {r} {p} {ε∈l} {loc} {c} {pdi@(pdinstance .{p} .{r} .{c} inj s-ev)} {pdis}  
  (hide .{p} .{r} .{c} .(inj) .(s-ev)) all-hide-p-pdis = prf e-flat-es 
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l
    e-flat-es :  List ( ∃[ e ] (Flat-[] l e) )
    e-flat-es = zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es
    prf : (xs :  List ( ∃[ e ] (Flat-[] l e) )) → All (Inhabit p) (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x ((pdinstance {p} {r} {c} inj s-ev) ∷ pdis)) xs)
    prf [] = []
    prf ( x ∷ xs ) = all-concat (sub-prf x ((pdinstance inj s-ev) ∷ pdis) (hide inj s-ev ∷ all-hide-p-pdis))  (prf xs)
      where
        sub-prf :
          ( e-flat-[]-e  :  ( ∃[ e ] (Flat-[] l e) ) )
          → ( qdis : List (PDInstance r c) )
          → All (Inhabit p ) qdis 
          → All (Inhabit p ) (List.map (mk-snd-pdi {l} {r} {loc} {c} e-flat-[]-e ) qdis)
        sub-prf _ [] []  = []
        sub-prf (e , flat-[]-e) ( qdi@(pdinstance {- {p} {r} {c} -} inj s-ev) ∷ qdis ) ((hide .{p} .{r} .{c} .(inj) .(s-ev)) ∷ all-hide-p-qdis ) = 
          cong-mk-snd-pdi-inhabit {l} {r} {p} {loc} {c} (e , flat-[]-e) qdi (hide inj s-ev)
          ∷ sub-prf (e , flat-[]-e)   qdis all-hide-p-qdis 
            
concatmap-snd-Homogenous : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char } { pdis : List (PDInstance r c) }
  → Homogenous pdis
  ---------------------------------------------------------------
  → Homogenous (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis)
concatmap-snd-Homogenous {l} {r} {ε∈l} {loc} {c} {[]} (homogenous [] ( p , [] )) rewrite concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c} = homogenous [] (p , [])
concatmap-snd-Homogenous {l} {r} {ε∈l} {loc} {c} {pdi@(pdinstance {p} {r} {c} inj s-ev) ∷ pdis } (homogenous  (.(pdi) ∷ .(pdis)) ( .(p) , hide-p-pdi@(hide .{p} {r} {c} .(inj) .(s-ev)) ∷ hide-p-pdis ))
  = homogenous (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} (pdi ∷  pdis)) ( p , concatmap-snd-inhabit⁺ (hide inj s-ev) hide-p-pdis )



map-star-inhabit⁺ :  ∀ { r p  : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char } {pdi : PDInstance r c } { pdis : List (PDInstance r c) }
  → Inhabit {r} {c} p pdi
  → All (Inhabit {r} {c} p) pdis
  --------------------------------
  → All (Inhabit {r * ε∉r ` loc} {c} ( p ● (r * ε∉r ` loc) ` loc )) (List.map pdinstance-star ( pdi ∷ pdis ))
map-star-inhabit⁺ {r} {p} {ε∉r} {loc} {c} {pdi@(pdinstance .{p} .{r} .{c} inj s-ev)} {[]} -- TODO:  can we combine these two cases?
  (hide .{p} .{r} .{c} .(inj) .(s-ev)) [] = hide (mkinjList inj) (mkinjListSoundEv inj s-ev) ∷ []
map-star-inhabit⁺ {r} {p} {ε∉r} {loc} {c} {pdi@(pdinstance .{p} .{r} .{c} inj s-ev)} {pdi'@(pdinstance .{p} .{r} .{c} inj' s-ev') ∷ pdis}
   (hide .{p} .{r} .{c} .(inj) .(s-ev)) ((hide .{p} .{r} .{c} .(inj') .(s-ev')) ∷ all-hide-p-pdis )  =
     hide (mkinjList inj) (mkinjListSoundEv inj s-ev) ∷ map-star-inhabit⁺ (hide inj' s-ev') all-hide-p-pdis 

map-star-Homogenous : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char } { pdis : List (PDInstance r c) }
  → Homogenous pdis
  ----------------------------------------------------------------
  → Homogenous (List.map (pdinstance-star {r} {ε∉r} {loc}) pdis)
map-star-Homogenous {r} {ε∉r} {loc} {c} {[]} (homogenous [] ( p , [] ))  = homogenous (List.map pdinstance-star []) (r , [])
map-star-Homogenous {r} {ε∉r} {loc} {c} {pdi@(pdinstance {p} {r} {c} inj s-ev) ∷ pdis} (homogenous  (.(pdi) ∷ .(pdis)) ( .(p) , hide-p-pdi@(hide .{p} {r} {c} .(inj) .(s-ev)) ∷ hide-p-pdis ))
  = homogenous (List.map (pdinstance-star {r} {ε∉r} {loc}) (pdi ∷ pdis)) (  ( p ● (r * ε∉r ` loc) ` loc ) , map-star-inhabit⁺ hide-p-pdi hide-p-pdis  )

oplus-Homogenous : ∀ { r : RE } { loc : ℕ } { c : Char }
  → ( pdis₁ : List (PDInstance r c ) )
  → ( pdis₂ : List (PDInstance r c ) )
  → Homogenous pdis₁
  → Homogenous pdis₂
  --------------------------------------------------------------
  → Homogenous (pdinstance-oplus {r} {loc} {c} pdis₁ pdis₂)
oplus-Homogenous {r} {loc} {c} []             pdis₂ _  weaksingleton-pdis₂ = weaksingleton-pdis₂
oplus-Homogenous {r} {loc} {c} (pdi₁ ∷ pdis₁) []    weaksingleton-pdi₁pdis₁ _ = weaksingleton-pdi₁pdis₁
oplus-Homogenous {r} {loc} {c} (pdi₁ ∷ pdis₁) (pdi₂ ∷ pdis₂)
  (homogenous (.(pdi₁) ∷ .(pdis₁)) ( p₁ , hide-p₁-pdi₁ ∷ hide-p₁-pdis₁ ))
  (homogenous (.(pdi₂) ∷ .(pdis₂)) ( p₂ , hide-p₂-pdi₂ ∷ hide-p₂-pdis₂ ))  = homogenous (pdinstance-oplus (pdi₁ ∷ pdis₁) (pdi₂ ∷ pdis₂)) prf
    where
      prf : ∃[ p ] All (Inhabit {r} {c} p) (concatMap (λ pdiˡ₁ → 
                                                (fuse pdiˡ₁ pdi₂) ∷  (List.map (fuse pdiˡ₁) pdis₂) )
                                             (pdi₁ ∷ pdis₁))
      prf = (p₁ + p₂ ` loc) , sub-prf (pdi₁ ∷ pdis₁) ( hide-p₁-pdi₁ ∷ hide-p₁-pdis₁ )
        where
          sub-prf : ∀ ( pdis₁' : List (PDInstance r c ) )
            → All (Inhabit {r} {c} p₁) pdis₁'
            → All (Inhabit {r} {c} (p₁ + p₂ ` loc)) (concatMap (λ pdiˡ₁ → 
                                                (List.map (fuse {r} {loc} {c}  pdiˡ₁) (pdi₂ ∷ pdis₂) )) pdis₁')
          sub-prf [] []  = [] 
          sub-prf ( pdi₁' ∷ pdis₁') ( hide-p₁-pdi₁' ∷ hide-p₁-pdis₁' ) =  all-concat ( sub-sub-prf pdi₁' (pdi₂ ∷  pdis₂) hide-p₁-pdi₁' (hide-p₂-pdi₂ ∷ hide-p₂-pdis₂ ) )  (sub-prf pdis₁'  hide-p₁-pdis₁')  
            where
              sub-sub-prf : (pdi : PDInstance r c)
                → ( pdis₂' : List (PDInstance r c ) )
                → Inhabit {r} {c} p₁ pdi 
                → All (Inhabit {r} {c} p₂) pdis₂'
                → All (Inhabit {r} {c} (p₁ + p₂ ` loc)) (List.map (fuse  {r} {loc} {c} pdi) (pdis₂'))
              sub-sub-prf (pdinstance in₁ s-ev₁)  [] hide-p₁-pdi₁ [] = []
              sub-sub-prf pdi@(pdinstance in₁ s-ev₁) ((pdinstance in₂ s-ev₂) ∷ pdis₂')  hide-p₁-pdi@(hide .{p₁} {r} {c} .(in₁) .(s-ev₁)) (hide-p₂-pdi₂'@(hide .{p₂} {r} {c} .(in₂) .(s-ev₂)) ∷ hide-p₂-pdis₂') = (hide inj sound-ev) ∷ sub-sub-prf pdi pdis₂' hide-p₁-pdi hide-p₂-pdis₂' 
                where
                  inj : U (p₁ + p₂ ` loc ) → U r
                  inj = mkfuseInj in₁ in₂
                  sound-ev : (u : U (p₁ + p₂ ` loc)) → proj₁ (flat (inj u))  ≡ c ∷ proj₁ (flat u)
                  sound-ev = mkfuseInjSoundEv in₁ in₂ s-ev₁ s-ev₂


pdU-Homogenous : ∀ { r : RE } { c : Char }
  → Homogenous pdU[ r  , c ]
pdU-Homogenous {ε} {c} = homogenous pdU[ ε , c ] (ε , [])
pdU-Homogenous {$ c ` loc} {c₁} with c Char.≟ c₁
... | no ¬c≡c₁ = homogenous [] (ε , [])
... | yes c≡c₁ rewrite c≡c₁ = homogenous (( pdinstance {ε} {$ c₁ ` loc} {c₁} inj s-ev ) ∷ [] ) 
                               (ε , 
                                hide inj s-ev                                   
                                ∷ [])
                   where
                     inj : U ε → U ($ c₁ ` loc)
                     inj =  (λ u → LetterU c₁)
                     s-ev : ∀ ( u : U ε ) → ( proj₁ ( flat {$ c₁ ` loc} (inj u) ) ≡ c₁ ∷ ( proj₁ (flat {ε} u) ))  
                     s-ev = (λ EmptyU →                 -- ^ soundness ev
                               begin
                                 [ c₁ ]
                               ≡⟨⟩
                                 c₁ ∷ []
                               ≡⟨ cong ( λ x → ( c₁ ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                                 c₁ ∷ (proj₁ (flat EmptyU))
                               ∎)
pdU-Homogenous {l + r ` loc} {c} = oplus-Homogenous (List.map pdinstance-left pdU[ l , c ]) (List.map pdinstance-right pdU[ r , c ]) (map-left-Homogenous ind-hyp-l) (map-right-Homogenous ind-hyp-r)
  where
    ind-hyp-l : Homogenous pdU[ l , c ]
    ind-hyp-l = pdU-Homogenous {l} {c}
    ind-hyp-r : Homogenous pdU[ r , c ]
    ind-hyp-r = pdU-Homogenous {r} {c}
pdU-Homogenous {l ● r ` loc} {c} with ε∈? l
... | no ¬ε∈l = map-fst-Homogenous ind-hyp-l
  where
    ind-hyp-l : Homogenous pdU[ l , c ]
    ind-hyp-l = pdU-Homogenous {l} {c}
... | yes ε∈l = oplus-Homogenous (List.map pdinstance-fst pdU[ l , c ]) (concatmap-pdinstance-snd pdU[ r , c ]) ( map-fst-Homogenous ind-hyp-l) (concatmap-snd-Homogenous ind-hyp-r) 
  where 
    ind-hyp-l : Homogenous pdU[ l , c ]
    ind-hyp-l = pdU-Homogenous {l} {c}
    ind-hyp-r : Homogenous pdU[ r , c ]
    ind-hyp-r = pdU-Homogenous {r} {c}
pdU-Homogenous {r * ε∉r ` loc} {c} = map-star-Homogenous  ind-hyp-r 
  where                                        
    ind-hyp-r : Homogenous pdU[ r , c ]
    ind-hyp-r = pdU-Homogenous {r} {c}


```


### Definition 36 : (Extended) POSIX ordering among PDInstances 

Let r be a non problematic regular expression.

Let c be a letter.

Let pdi₁ and pdi₂ be two partial derivative instances of r w.r.t c.

We say pdi₁ is "posix" greater than pdi₂, r , c  ⊢ pdi₁ > pdi₂ iff
  for all parse trees u₁ u₂  of r, |u₁| ≥ |u₂|, u₁ is constructible from pdi₁ and u₂ is constructibled from pdi₂ 
    then r ⊢ u₁ > u₂ ?


.


```agda
{-
trying to define a > among Recons r c, but it 
 does not work
data Rec> : { r : RE } { c : Char } { u₁ u₂ : U r } { p₁ p₂ : PDInstance r c }
  → Recons u₁ p₁ → Recons u₂ p₂ → Set where
  rec> : ∀ { r p₁ p₂ : RE } { c : Char } { w₁ w₂ : List Char } { inj1 : U p₁ → U r }
    { inj2 : U p₂ → U r  }
    { s-ev₁ : ∀ ( x : U p₁ ) → ( proj₁ ( flat {r} (inj1 x) ) ≡ c ∷ ( proj₁ (flat {p₁} x) )) }
    { s-ev₂ : ∀ ( x : U p₂ ) → ( proj₁ ( flat {r} (inj2 x) ) ≡ c ∷ ( proj₁ (flat {p₂} x) )) }
    → ( u₁ u₂ : U r )
    → ( c-ev₁ : ∃[ w₁∈⟦p₁⟧ ] ( (inj1 (unflat {p₁} {w₁}  w₁∈⟦p₁⟧)) ≡ u₁ ) )
    → ( c-ev₂ : ∃[ w₂∈⟦p₂⟧ ] ( (inj2 (unflat {p₂} {w₂}  w₂∈⟦p₂⟧)) ≡ u₂ ) )
    -- but p₁ and p₂ are not the same! we can compare unflat w₁∈⟦p₁⟧ and unflat w₂∈⟦p₂⟧
    ------------------------------------
    → Rec> (Recons.recons {p₁} {r} {c} {w₁} {inj1} {s-ev₁} u₁ c-ev₁) (Recons.recons {p₂} {r} {c} {w₂} {inj2} {s-ev₂} u₂ c-ev₂)
-}    
  

-- what if in addition, we know that p from pdi₁ and pdi₂ are identitcal? weak-singleton

{-
data _,_⊢_>_ : ∀ ( r : RE ) → (c : Char ) → PDInstance r c → PDInstance r c → Set where
  >-pdi : ∀ { r : RE } { c : Char }
    → ( pdi₁ : PDInstance r c ) 
    → ( pdi₂ : PDInstance r c )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r )
      → length (proj₁ (flat u₁)) ≥ length (proj₁ (flat u₂))
        -- this premise is problematic? it weakens the >-pdi relation compared to the greedy and lne order 
        -- w/o this, we can't prove left-ex-sort and right-ex-sort refer to (**)
        -- can we still create a contradiction w/o this to prove (**)?
        -- even if we could do it for left-ex-sort and right-ex-sort, how about star-ex-sort? 

      → (Recons u₁ pdi₁ ) → (Recons u₂ pdi₂) → ( r ⊢ u₁ > u₂) )
    → r , c ⊢ pdi₁ > pdi₂
-}
-- does that means that they are actually the same injection?? no...
data _,_⊢_>_ : ∀ ( r : RE ) → (c : Char ) → PDInstance r c → PDInstance r c → Set where
  >-pdi : ∀ { r p : RE } { c : Char }
    → ( injection₁ : U p → U r )
    → ( s-ev₁ : ∀ ( u : U p ) → (proj₁ ( flat {r} (injection₁ u)) ≡ c ∷ (proj₁ (flat {p} u))) )
    → ( injection₂ : U p → U r )
    → ( s-ev₂ : ∀ ( u : U p ) → (proj₁ ( flat {r} (injection₂ u)) ≡ c ∷ (proj₁ (flat {p} u))) )
    → ( ∀ ( v₁ : U p )
        → ( v₂ : U p ) 
        → p ⊢ v₁ > v₂ -- or v₁ ≡ v₂ then via >-inc pdi₁ and >-trans we got the same 
        → r ⊢ injection₁ v₁ > injection₂ v₂ )
    → ( ∀ ( v : U p ) → ( r ⊢ injection₁ v > injection₂ v ) ⊎ (injection₁ v ≡ injection₂ v ) ) -- ? strict inc? 
   → r , c ⊢ (pdinstance {p} {r} {c} injection₁ s-ev₁) > (pdinstance {p} {r} {c} injection₂ s-ev₂)

```




### Definition 37 : (Extended) POSIX order sortedness

```agda

data Ex>-maybe : ∀ { r : RE } { c : Char } ( pdi : PDInstance r c ) → ( mpdi : Maybe (PDInstance r c) ) → Set where
  ex>-nothing : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c } 
    ---------------------------
    → Ex>-maybe {r} {c} pdi nothing
  ex>-just : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c }
    → { pdi' : PDInstance r c }
    → r , c ⊢ pdi > pdi' 
    ----------------------------------
    → Ex>-maybe {r} {c} pdi (just pdi')

data Ex>-sorted : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) ) → Set where
  ex>-nil  : ∀ { r : RE } { c : Char } → Ex>-sorted {r} {c} []
  ex>-cons : ∀ { r : RE } { c : Char } 
    → { pdi : PDInstance r c }
    → { pdis : List (PDInstance r c) } 
    → Ex>-sorted  {r} {c} pdis 
    → Ex>-maybe {r} {c} pdi (head pdis)
    --------------------------------------
    → Ex>-sorted {r} {c} ( pdi ∷ pdis )

{-

data Ex>-maybe : ∀ { r : RE } { c : Char } { w : List Char }  ( pdi : PDInstance r c ) → ( mpdi : Maybe (PDInstance r c) ) → Set where
  ex>-nothing : ∀ { r : RE } { c : Char } { w : List Char }
    → { pdi : PDInstance r c } 
    ---------------------------
    → Ex>-maybe {r} {c} {w} pdi nothing
  ex>-just : ∀ { r : RE } { c : Char } { w : List Char }
    → { pdi : PDInstance r c }
    → { pdi' : PDInstance r c }
    → r , c , w  ⊢ pdi > pdi' 
    ----------------------------------
    → Ex>-maybe {r} {c} {w} pdi (just pdi')


data Ex>-sorted : ∀ { r : RE } { c : Char } { w : List Char } ( pdis : List (PDInstance r c) ) → Set where
  ex>-nil  : ∀ { r : RE } { c : Char } { w : List Char } → Ex>-sorted {r} {c} {w} []
  ex>-cons : ∀ { r : RE } { c : Char } { w : List Char } 
    → { pdi : PDInstance r c }
    → { pdis : List (PDInstance r c) } 
    → Ex>-sorted  {r} {c} {w} pdis 
    → Ex>-maybe {r} {c} {w} pdi (head pdis)
    --------------------------------------
    → Ex>-sorted {r} {c} {w} ( pdi ∷ pdis )

-}
```




### Lemma 38: the list of pdinstances from pdU[ r , c] is extended POSIX-> sorted. 


Let r be a non problematic regular expression.

Let c be a letter.

Then pdU[r , c] is LNE sorted. 




#### Sub Lemma 38.1 - 38.22 : Ex>-sortedness is preserved inductively over pdinstance operations.

```agda

-------------------------------------------------------------
-- Sub Lemma 38.1 - 38.22 BEGIN
-------------------------------------------------------------

import Relation.Binary.Definitions
open  Relation.Binary.Definitions using (
  Tri ; tri< ; tri≈ ; tri> ) 


left-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁  : PDInstance l c )
  → (pdi₂ : PDInstance l c )
  → l , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (l + r ` loc) , c ⊢ pdinstance-left pdi₁ > pdinstance-left pdi₂
left-ex-sorted {l} {r} {loc} {c} (pdinstance {p} .{l} .{c} in₁ s-ev₁) (pdinstance .{p} .{l} .{c} in₂ s-ev₂)
  (>-pdi .{l} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v ) = >-pdi {l + r ` loc} {p} {c} inject₁ s-ev₁  inject₂ s-ev₂ prf₁ prf₂
  where
    inject₁ : U p → U ( l + r ` loc )
    inject₁ v = LeftU (in₁ v)
    inject₂ : U p → U ( l + r ` loc )    
    inject₂ v = LeftU (in₂ v)    

    len-|in₁-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
    len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

    len-|in₂-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
    len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 


    prf₁ : ∀ ( v₁ : U p)
          → ( v₂ : U p) 
          →  p ⊢ v₁ > v₂ 
          -------------------------
          →  (l + r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
    prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len-|left-in₁-v₁|>len-|left-in₂-v₂|
      where
        len-|left-in₁-v₁|>len-|left-in₂-v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.> length (proj₁ (flat (inject₂ v₂)))
                                               
        len-|left-in₁-v₁|>len-|left-in₂-v₂| rewrite len-|in₁-u|≡len-|u|+1 v₁ | len-|in₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
    prf₁ v₁ v₂ (len-≡ len|v₁|≡len|v₂| v₁>ⁱv₂) =  len-≡ len-|left-in₁-v₁|≡len-|left-in₂-v₂| (choice-ll (v₁>v₂→in₁v₁>in₂v₂ v₁ v₂ (len-≡ len|v₁|≡len|v₂| v₁>ⁱv₂)))
      where
        len-|left-in₁-v₁|≡len-|left-in₂-v₂| : length (proj₁ (flat (inject₁ v₁))) ≡ length (proj₁ (flat (inject₂ v₂)))
        len-|left-in₁-v₁|≡len-|left-in₂-v₂| rewrite len-|in₁-u|≡len-|u|+1 v₁ | len-|in₂-u|≡len-|u|+1 v₂ | len|v₁|≡len|v₂| = refl
        
    prf₂ : ∀ ( v : U p )
      → ( (l + r ` loc) ⊢ inject₁ v > inject₂ v ) ⊎ (inject₁ v ≡ inject₂ v)
    prf₂ v with v→in₁v≥in₂v v 
    ... | inj₁ in₁v>in₂v = inj₁ (len-≡ len-|left-in₁-v|≡len-|left-in₂-v| (choice-ll in₁v>in₂v) ) 
      where
        len-|left-in₁-v|≡len-|left-in₂-v| : length (proj₁ (flat (inject₁ v))) ≡ length (proj₁ (flat (inject₂ v)))
        len-|left-in₁-v|≡len-|left-in₂-v| rewrite len-|in₁-u|≡len-|u|+1 v | len-|in₂-u|≡len-|u|+1 v = refl

right-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁  : PDInstance r c )
  → (pdi₂ : PDInstance r c )
  → r , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (l + r ` loc) , c ⊢ pdinstance-right pdi₁ > pdinstance-right pdi₂
right-ex-sorted {l} {r} {loc} {c} (pdinstance {p} .{r} .{c} in₁ s-ev₁) (pdinstance .{p} .{r} .{c} in₂ s-ev₂)
  (>-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v ) = >-pdi {l + r ` loc} {p} {c} inject₁ s-ev₁  inject₂ s-ev₂ prf₁ prf₂
  where
    inject₁ : U p → U ( l + r ` loc )
    inject₁ v = RightU (in₁ v)
    inject₂ : U p → U ( l + r ` loc )    
    inject₂ v = RightU (in₂ v)    

    len-|in₁-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
    len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

    len-|in₂-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
    len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 


    prf₁ : ∀ ( v₁ : U p)
          → ( v₂ : U p) 
          →  p ⊢ v₁ > v₂ 
          -------------------------
          →  (l + r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
    prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len-|right-in₁-v₁|>len-|right-in₂-v₂|
      where
        len-|right-in₁-v₁|>len-|right-in₂-v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.>
                                              length (proj₁ (flat (inject₂ v₂)))
                                               
        len-|right-in₁-v₁|>len-|right-in₂-v₂| rewrite len-|in₁-u|≡len-|u|+1 v₁ | len-|in₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
    prf₁ v₁ v₂ (len-≡ len|v₁|≡len|v₂| v₁>ⁱv₂) =  len-≡ len-|right-in₁-v₁|≡len-|right-in₂-v₂| (choice-rr (v₁>v₂→in₁v₁>in₂v₂ v₁ v₂ (len-≡ len|v₁|≡len|v₂| v₁>ⁱv₂)))
      where
        len-|right-in₁-v₁|≡len-|right-in₂-v₂| : length (proj₁ (flat (inject₁ v₁))) ≡ 
                                               length (proj₁ (flat (inject₂ v₂)))
        len-|right-in₁-v₁|≡len-|right-in₂-v₂| rewrite len-|in₁-u|≡len-|u|+1 v₁ | len-|in₂-u|≡len-|u|+1 v₂ | len|v₁|≡len|v₂| = refl                                        

    prf₂ : ∀ ( v : U p )
      → ( (l + r ` loc) ⊢ inject₁ v > inject₂ v)  ⊎ (inject₁ v ≡ inject₂ v)
    prf₂ v with v→in₁v≥in₂v v
    ... | inj₁ in₁v>in₂v = inj₁ (len-≡ len-|right-in₁-v|≡len-|right-in₂-v| (choice-rr in₁v>in₂v ) )
      where
        len-|right-in₁-v|≡len-|right-in₂-v| : length (proj₁ (flat (inject₁ v))) ≡ length (proj₁ (flat (inject₂ v)))
        len-|right-in₁-v|≡len-|right-in₂-v| rewrite len-|in₁-u|≡len-|u|+1 v | len-|in₂-u|≡len-|u|+1 v = refl


map-left-ex-sorted : ∀ { l r : RE }  { loc : ℕ } { c : Char } 
  → ( pdis : List (PDInstance l c ) )
  → Ex>-sorted {l} pdis
  → Ex>-sorted {l + r ` loc } (List.map pdinstance-left pdis)
map-left-ex-sorted []            ex>-nil = ex>-nil
map-left-ex-sorted ( pdi ∷ [] ) (ex>-cons ex>-nil (ex>-nothing) )
  = ex>-cons  ex>-nil (ex>-nothing)
map-left-ex-sorted ( pdi ∷ (pdi' ∷ pdis) ) (ex>-cons  ex>-sorted-pdis (ex>-just pdi>pdi'))
  = ex>-cons 
           (map-left-ex-sorted (pdi' ∷ pdis) ex>-sorted-pdis)
           (ex>-just (left-ex-sorted pdi pdi'  pdi>pdi'))



map-right-ex-sorted : ∀ { l r : RE }  { loc : ℕ } { c : Char } 
  → ( pdis : List (PDInstance r c ) )
  → Ex>-sorted {r} pdis
  → Ex>-sorted {l + r ` loc } (List.map pdinstance-right pdis)
map-right-ex-sorted []            ex>-nil = ex>-nil
map-right-ex-sorted ( pdi ∷ [] ) (ex>-cons ex>-nil ex>-nothing)
  = ex>-cons  ex>-nil ex>-nothing
map-right-ex-sorted ( pdi ∷ (pdi' ∷ pdis) ) (ex>-cons ex>-sorted-pdis (ex>-just pdi>pdi'))
  = ex>-cons 
           (map-right-ex-sorted (pdi' ∷ pdis) ex>-sorted-pdis)
           (ex>-just (right-ex-sorted pdi pdi'  pdi>pdi'))

-- it seems that we dont need this lemma since all the left and right pdis are combined with oplus 
{- 

map-left-right-ex-sorted : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( pdis  : List (PDInstance l c) )
  → ( pdis' : List (PDInstance r c) )
  → Ex>-sorted {l} pdis
  → Ex>-sorted {r} pdis'
  → Ex>-sorted {l + r ` loc } ((List.map pdinstance-left pdis) ++ (List.map pdinstance-right pdis'))
map-left-right-ex-sorted               []              pdis'  ex>-sorted-l-[]   ex>-sorted-r-pdis' = map-right-ex-sorted pdis' ex>-sorted-r-pdis'
map-left-right-ex-sorted {l} {r} {loc} pdis            []     ex>-sorted-l-pdis ex>-sorted-r-[] rewrite (cong (λ x → Ex>-sorted x) (++-identityʳ (List.map (pdinstance-left {l} {r} {loc}) pdis)))
  = map-left-ex-sorted  pdis ex>-sorted-l-pdis
map-left-right-ex-sorted {l} {r} {loc} (pdi@(pdinstance {p} {l} {c} inj s-ev) ∷ [])     (pdi'@(pdinstance {p'} {r} .{c} inj' s-ev') ∷ pdis')   ex>-sorted-l-pdis  ex>-sorted-r-pdis'
  = ex>-cons (map-right-ex-sorted (pdi' ∷ pdis') ex>-sorted-r-pdis') (ex>-just {!!} )
  where
    prf : (l + r ` loc) , c ⊢ pdinstance-left pdi >  pdinstance-right pdi'
    prf = >-pdi {l + r ` loc} { p + p' ` loc } {c} ? ? ? ? ? --  requires both side share the same p .
-}     


star-ex-sorted : ∀ { r : RE }  { ε∉r : ε∉ r } {loc : ℕ} { c : Char } 
  → (pdi₁ : PDInstance r c )
  → (pdi₂ : PDInstance r c )
  → r , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (r * ε∉r ` loc) , c ⊢ pdinstance-star pdi₁ > pdinstance-star pdi₂
star-ex-sorted {r} {ε∉r} {loc} {c}  (pdinstance {p} .{r} .{c} in₁ s-ev₁) (pdinstance .{p} .{r} .{c} in₂ s-ev₂)
    (>-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v) = >-pdi {r * ε∉r ` loc} {p ● (r * ε∉r ` loc) ` loc } {c} (mkinjList in₁) (mkinjListSoundEv in₁ s-ev₁) (mkinjList in₂) (mkinjListSoundEv in₂ s-ev₂) prf₁ prf₂ 
    where
      inject₁ : U ( p ● (r * ε∉r ` loc) ` loc )  → U ( r * ε∉r ` loc )
      inject₁ = mkinjList {p} {r} {ε∉r} {loc} in₁ 
      inject₂ : U ( p ● (r * ε∉r ` loc) ` loc )  → U ( r * ε∉r ` loc )
      inject₂ = mkinjList {p} {r} {ε∉r} {loc} in₂  

      sound-ev₁ : ∀ ( u : U ( p ● (r * ε∉r ` loc) ` loc )) → proj₁ (flat (inject₁ u)) ≡ c ∷ proj₁ (flat u)
      sound-ev₁ = mkinjListSoundEv {p} {r} {ε∉r} {loc} {c} in₁ s-ev₁ 

      sound-ev₂ : ∀ ( u : U ( p ● (r * ε∉r ` loc) ` loc )) → proj₁ (flat (inject₂ u)) ≡ c ∷ proj₁ (flat u)
      sound-ev₂ = mkinjListSoundEv {p} {r} {ε∉r} {loc} {c} in₂ s-ev₂ 

      len-|inject₁-u|≡len-|u|+1 : (u : U ( p ● (r * ε∉r ` loc) ` loc ) ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
      len-|inject₁-u|≡len-|u|+1 u rewrite (sound-ev₁ u) = refl 
    
      len-|inject₂-u|≡len-|u|+1 : (u : U ( p ● (r * ε∉r ` loc) ` loc ) ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
      len-|inject₂-u|≡len-|u|+1 u rewrite (sound-ev₂ u) = refl 


      prf₁ : (v₁ v₂ : U (p ● r * ε∉r ` loc ` loc)) →
            (p ● r * ε∉r ` loc ` loc) ⊢ v₁ > v₂ →
            (r * ε∉r ` loc) ⊢ mkinjList in₁ v₁ > mkinjList in₂ v₂
      prf₁ (PairU v₁ v₂) (PairU u₁ u₂) (len-> len|pair-v₁v₂|>len|pair-u₁u₂|) = len-> len-|star-in₁-pair-v₁v₂|>len-|star-in₂-pair-u₁u₂|
        where
          len-|star-in₁-pair-v₁v₂|>len-|star-in₂-pair-u₁u₂| : length (proj₁ (flat (mkinjList in₁ (PairU v₁ v₂))))
                           Nat.> length (proj₁ (flat (mkinjList in₂ (PairU u₁ u₂))))
          len-|star-in₁-pair-v₁v₂|>len-|star-in₂-pair-u₁u₂| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v₁ v₂) | len-|inject₂-u|≡len-|u|+1 (PairU u₁ u₂) = Nat.s≤s len|pair-v₁v₂|>len|pair-u₁u₂|
          
      prf₁ (PairU v (ListU vs)) (PairU u (ListU us)) (len-≡ len|pair-vvs|≡len|pair-uus| (seq₁ v>u)) = len-≡ len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| (star-head (v₁>v₂→in₁v₁>in₂v₂ v u v>u)) 
        where
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| : length (proj₁ (flat (mkinjList in₁ (PairU {p} { r * ε∉r ` loc} {loc}  v (ListU vs))))) ≡ length (proj₁ (flat (mkinjList in₂ (PairU {p} { r * ε∉r ` loc} {loc}  u (ListU us)))))
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v (ListU vs)) | len-|inject₂-u|≡len-|u|+1 (PairU u (ListU us)) | len|pair-vvs|≡len|pair-uus| = refl
          

      prf₁ (PairU v (ListU vs)) (PairU u (ListU us)) (len-≡ len|pair-vvs|≡len|pair-uus| (seq₂ v≡u vs>us)) with  v→in₁v≥in₂v u
      ... | inj₁ in₁u>in₂u = len-≡ len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| (star-head in₁v>in₂u  ) 
        where
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| : length (proj₁ (flat (mkinjList in₁ (PairU {p} { r * ε∉r ` loc} {loc}  v (ListU vs))))) ≡ length (proj₁ (flat (mkinjList in₂ (PairU {p} { r * ε∉r ` loc} {loc}  u (ListU us)))))
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v (ListU vs)) | len-|inject₂-u|≡len-|u|+1 (PairU u (ListU us)) | len|pair-vvs|≡len|pair-uus| = refl
          in₁v>in₂u  : r ⊢ in₁ v > in₂ u
          in₁v>in₂u rewrite v≡u = in₁u>in₂u 

      prf₂ : (v : U (p ● r * ε∉r ` loc ` loc)) →
        ( (r * ε∉r ` loc) ⊢ mkinjList in₁ v > mkinjList in₂ v )  ⊎  ( mkinjList in₁ v ≡  mkinjList in₂ v  )
      prf₂ (PairU v (ListU vs)) with v→in₁v≥in₂v v
      ... | inj₁ in₁v>in₂v = inj₁ (len-≡ len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-vvs| (star-head in₁v>in₂v) )
        where
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-vvs| : length (proj₁ (flat (mkinjList in₁ (PairU {p} { r * ε∉r ` loc} {loc}  v (ListU vs))))) ≡ length (proj₁ (flat (mkinjList in₂ (PairU {p} { r * ε∉r ` loc} {loc}  v (ListU vs)))))
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-vvs| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v (ListU vs)) | len-|inject₂-u|≡len-|u|+1 (PairU v (ListU vs))  = refl
          

map-star-ex-sorted : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
                     → ( pdis : List (PDInstance r c) )
                     → Ex>-sorted {r} pdis
                     → Ex>-sorted {r * ε∉r ` loc } (List.map pdinstance-star pdis)
map-star-ex-sorted {r} {ε∉r} {loc} {c} [] ex>-nil = ex>-nil
map-star-ex-sorted {r} {ε∉r} {loc} {c} (pdi ∷ [])  (ex>-cons ex>-nil ex>-nothing) = ex>-cons ex>-nil ex>-nothing
map-star-ex-sorted {r} {ε∉r} {loc} {c} (pdi₁ ∷ pdi₂ ∷ pdis)  (ex>-cons ex>-sorted-pdi2pdis (ex>-just pdi1>pdi2))
  = ex>-cons (map-star-ex-sorted (pdi₂ ∷ pdis) ex>-sorted-pdi2pdis)
             (ex>-just (star-ex-sorted pdi₁ pdi₂ pdi1>pdi2))




fst-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁ : PDInstance l c )
  → (pdi₂ : PDInstance l c )
  → l , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (l ● r ` loc) , c ⊢ pdinstance-fst pdi₁ > pdinstance-fst pdi₂
fst-ex-sorted {l} {r} {loc} {c}  (pdinstance {p} .{l} .{c} in₁ s-ev₁) (pdinstance .{p} .{l} .{c} in₂ s-ev₂)
  (>-pdi .{l} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v) = >-pdi {l ● r ` loc } { p ● r ` loc } {c} inject₁ sound-ev₁ inject₂ sound-ev₂ prf₁ prf₂
  where 
    inject₁ : U (p ● r ` loc ) → U ( l ● r ` loc )
    inject₁ v = mkinjFst in₁ v
    inject₂ : U (p ● r ` loc ) → U ( l ● r ` loc )    
    inject₂ v = mkinjFst in₂ v

    sound-ev₁ : ∀ (u : U ( p ● r ` loc ) ) → proj₁ (flat (inject₁ u)) ≡ c ∷ proj₁ (flat u)
    sound-ev₁ = mkinjFstSoundEv in₁ s-ev₁

    sound-ev₂ : ∀ (u : U ( p ● r ` loc ) ) → proj₁ (flat (inject₂ u)) ≡ c ∷ proj₁ (flat u)
    sound-ev₂ = mkinjFstSoundEv in₂ s-ev₂

    len-|inject₁-u|≡len-|u|+1 : (u : U ( p ● r ` loc ) ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
    len-|inject₁-u|≡len-|u|+1 u rewrite (sound-ev₁ u) = refl 

    len-|inject₂-u|≡len-|u|+1 : (u : U ( p ● r ` loc ) ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
    len-|inject₂-u|≡len-|u|+1 u rewrite (sound-ev₂ u) = refl 

    
    prf₁ : (v₁ v₂ : U (p ● r ` loc))
         → (p ● r ` loc) ⊢ v₁ > v₂
         -----------------------------------------
         → (l ● r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
    prf₁ (PairU v₁ u₁) (PairU v₂ u₂) (len-> len|pair-v₁u₁|>len|pair-v₂u₂|) = len-> len-|pair-in₁-v₁-u₁|>len-|pair-in₂-v₂-u₂| 
      where
        len-|pair-in₁-v₁-u₁|>len-|pair-in₂-v₂-u₂| : length (proj₁ (flat (inject₁ (PairU {p} {r} {loc} v₁ u₁)))) Nat.> length (proj₁ (flat (inject₂ (PairU {p} {r} {loc} v₂ u₂))))
                                               
        len-|pair-in₁-v₁-u₁|>len-|pair-in₂-v₂-u₂| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v₁ u₁) | len-|inject₂-u|≡len-|u|+1 (PairU v₂ u₂)  = Nat.s≤s len|pair-v₁u₁|>len|pair-v₂u₂|
    prf₁ (PairU v₁ u₁) (PairU v₂ u₂) (len-≡ len|pair-v₁u₁|≡len|pair-v₂u₂| (seq₁ v₁>v₂)) = len-≡ len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| (seq₁ (v₁>v₂→in₁v₁>in₂v₂ v₁ v₂ v₁>v₂)) 
      where
        len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| : length (proj₁ (flat (inject₁ (PairU {p} {r} {loc} v₁ u₁)))) ≡ length (proj₁ (flat (inject₂ (PairU {p} {r} {loc} v₂ u₂))))
                                               
        len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v₁ u₁) | len-|inject₂-u|≡len-|u|+1 (PairU v₂ u₂) | len|pair-v₁u₁|≡len|pair-v₂u₂|  = refl 
    prf₁ (PairU v₁ u₁) (PairU v₂ u₂) (len-≡ len|pair-v₁u₁|≡len|pair-v₂u₂| (seq₂ v₁≡v₂ u₁>u₂)) with v→in₁v≥in₂v v₂
    ... | inj₁ in₁v₂>in₂v₂ =  len-≡ len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| (seq₁ in₁v>in₂u )
      where
        len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| : length (proj₁ (flat (inject₁ (PairU {p} {r} {loc} v₁ u₁)))) ≡ length (proj₁ (flat (inject₂ (PairU {p} {r} {loc} v₂ u₂))))
                                               
        len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v₁ u₁) | len-|inject₂-u|≡len-|u|+1 (PairU v₂ u₂) | len|pair-v₁u₁|≡len|pair-v₂u₂|  = refl 
        in₁v>in₂u  : l ⊢ in₁ v₁ > in₂ v₂
        in₁v>in₂u rewrite v₁≡v₂ =  in₁v₂>in₂v₂  

    prf₂ :  (v : U (p ● r ` loc)) 
      → ( (l ● r ` loc) ⊢ inject₁ v > inject₂ v ) ⊎ ( inject₁ v ≡ inject₂ v )
    prf₂ (PairU v u) with v→in₁v≥in₂v v
    ... | inj₁ in₁v>in₂v = inj₁ (len-≡ len-|pair-in₁-v-u|≡len-|pair-in₂-v-u| (seq₁ in₁v>in₂v ))
      where
        len-|pair-in₁-v-u|≡len-|pair-in₂-v-u| : length (proj₁ (flat (inject₁ (PairU {p} {r} {loc} v u)))) ≡ length (proj₁ (flat (inject₂ (PairU {p} {r} {loc} v u))))
                                               
        len-|pair-in₁-v-u|≡len-|pair-in₂-v-u| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v u) | len-|inject₂-u|≡len-|u|+1 (PairU v u)  = refl 
        


map-fst-ex-sorted : ∀ { l r : RE } { loc : ℕ } { c : Char }
                    → ( pdis : List (PDInstance l c) )
                    → Ex>-sorted {l} pdis
                    → Ex>-sorted {l ● r ` loc } (List.map pdinstance-fst pdis)
map-fst-ex-sorted {l} {r} {loc} {c} [] ex>-nil = ex>-nil
map-fst-ex-sorted {l} {r} {loc} {c} (pdi ∷ [])              (ex>-cons ex>-nil ex>-nothing ) =
  ex>-cons  ex>-nil ex>-nothing 
map-fst-ex-sorted {l} {r} {loc} {c} (pdi₁  ∷ pdi₂ ∷ pdis ) (ex>-cons pdi₂pdis-sorted@(ex>-cons pdis-sorted pdi₂>head-pdis)  (ex>-just pdi₁>pdi₂ )) =
  ex>-cons (map-fst-ex-sorted {l} {r} {loc} {c}  (pdi₂ ∷  pdis) pdi₂pdis-sorted) (ex>-just (fst-ex-sorted {l} {r} pdi₁ pdi₂ pdi₁>pdi₂ ))


--------------------------------------------------------------------------------------------
-- sub lemma snd-ex-sorted and its sub sub lemmas BEGIN 
--------------------------------------------------------------------------------------------


-- main sub lemma :
-- pdinstances generated by pdinstance-snd is ex>-sorted.

pdinstance-snd-ex>-sorted : ∀ { l r : RE } { loc : ℕ } { c : Char }
                → (e-flat-[]-e : ∃[ e ] Flat-[] l e ) 
                → (pdis : List (PDInstance r c) )
                → Ex>-sorted {r} pdis 
                → Ex>-sorted { l ● r ` loc } (List.map (mk-snd-pdi {l} {r} {loc} {c}  e-flat-[]-e) pdis)
pdinstance-snd-ex>-sorted {l} {r} {loc} {c} (e ,  flat-[]-e ) []            ex>-nil                                   = ex>-nil 
pdinstance-snd-ex>-sorted {l} {r} {loc} {c}  (e , flat-[]-e ) (pdi ∷ [] ) (ex>-cons ex>-nil ex>-nothing)              = ex>-cons ex>-nil ex>-nothing

pdinstance-snd-ex>-sorted {l} {r} {loc} {c}  (e , (flat-[] {l} .(e) proj₁flate≡[])) (pdi₁@(pdinstance {p} .{r} .{c} in₁ s-ev₁)  ∷ pdi₂@(pdinstance .{p} .{r} .{c} in₂ s-ev₂) ∷ pdis )
  (ex>-cons pdi₂pdis-ex>-sorted (ex>-just (>-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) u₁→u₂→u₁>u₂→in₁u₁>in₂u₂ u→in₁u≥in₂u)))  =
     ex>-cons (pdinstance-snd-ex>-sorted (e , (flat-[] {l} e proj₁flate≡[])) (pdi₂ ∷ pdis) pdi₂pdis-ex>-sorted)
               (ex>-just (>-pdi {l ● r ` loc} {p} {c} inject₁ sound-ev₁ inject₂ sound-ev₂ prf₁ prf₂   ))
     where
       inject₁ : U p → U (l ● r ` loc)
       inject₁ = mkinjSnd in₁ e 
       inject₂ : U p → U (l ● r ` loc)       
       inject₂ = mkinjSnd in₂ e 
       sound-ev₁ : (u : U p) → proj₁ (flat (inject₁ u)) ≡ c ∷ (proj₁ (flat u))
       sound-ev₁ = mkinjSndSoundEv {p} {l} {r} {loc} {c} in₁ s-ev₁ e (flat-[] {l} e proj₁flate≡[])
       sound-ev₂ : (u : U p) → proj₁ (flat (inject₂ u)) ≡ c ∷ (proj₁ (flat u))
       sound-ev₂ = mkinjSndSoundEv {p} {l} {r} {loc} {c} in₂ s-ev₂ e (flat-[] {l} e proj₁flate≡[])


       len-|in₁-u|≡len-|u|+1 : (u : U p ) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
       len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

       len-|in₂-u|≡len-|u|+1 : (u : U p ) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
       len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 

       len-|inject₁-u|≡len-|u|+1 : (u : U p ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
       len-|inject₁-u|≡len-|u|+1 u rewrite (sound-ev₁ u) = refl 

       len-|inject₂-u|≡len-|u|+1 : (u : U p ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
       len-|inject₂-u|≡len-|u|+1 u rewrite (sound-ev₂ u) = refl 

       prf₁ :  (v₁ v₂ : U p) →
         p ⊢ v₁ > v₂ → (l ● r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
       prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|pair-e-in₁v₁|>len|pair-e-in₂v₂|
         where
           len|pair-e-in₁v₁|>len|pair-e-in₂v₂| : length (proj₁ (flat (PairU {l} {r} {loc} e (in₁ v₁))))
                                                 Nat.> length (proj₁ (flat (PairU {l} {r} {loc} e (in₂ v₂))))
           len|pair-e-in₁v₁|>len|pair-e-in₂v₂| rewrite  proj₁flate≡[] |  len-|in₁-u|≡len-|u|+1 v₁ |  len-|in₂-u|≡len-|u|+1 v₂   = Nat.s≤s len|v₁|>len|v₂| 
         
       prf₁ v₁ v₂ (len-≡ len|v₁|≡len|v₂| v₁>ⁱv₂) = len-≡ len|pair-e-in₁v₁|≡len|pair-e-in₂v₂| (seq₂ refl
                                                               (u₁→u₂→u₁>u₂→in₁u₁>in₂u₂ v₁ v₂ (len-≡ len|v₁|≡len|v₂| v₁>ⁱv₂)))
         where
           len|pair-e-in₁v₁|≡len|pair-e-in₂v₂| : length (proj₁ (flat (PairU {l} {r} {loc} e (in₁ v₁))))
                                                 ≡ length (proj₁ (flat (PairU {l} {r} {loc} e (in₂ v₂))))
           len|pair-e-in₁v₁|≡len|pair-e-in₂v₂| rewrite  proj₁flate≡[] |  len-|in₁-u|≡len-|u|+1 v₁ |  len-|in₂-u|≡len-|u|+1 v₂ | len|v₁|≡len|v₂| = refl                                       
       prf₂ : (v : U p)
         →  ( (l ● r ` loc) ⊢ inject₁ v > inject₂ v ) ⊎ (inject₁ v ≡ inject₂ v) 
       prf₂ v with u→in₁u≥in₂u v
       ... | inj₁ in₁v>in₂v = inj₁ (len-≡ len|pair-e-in₁v|≡len|pair-e-in₂v| (seq₂ refl in₁v>in₂v))
         where 
           len|pair-e-in₁v|≡len|pair-e-in₂v| : length (proj₁ (flat (PairU {l} {r} {loc} e (in₁ v))))
                                                 ≡ length (proj₁ (flat (PairU {l} {r} {loc} e (in₂ v))))
           len|pair-e-in₁v|≡len|pair-e-in₂v| rewrite  proj₁flate≡[] |  len-|in₁-u|≡len-|u|+1 v |  len-|in₂-u|≡len-|u|+1 v  = refl                                       

--------------------------------------------------------------------------------------------
-- sub lemma: pdinstance-snd-ex>-sorted END
--------------------------------------------------------------------------------------------

-- concatenation of two ex sorted lists of pdis are sorted if all the pdis from the first list are ex-> than the head of the 2nd list. 
concat-ex-sorted : ∀ { r : RE } { c }
    → ( pdis₁ : List ( PDInstance r c ))
    → ( pdis₂ : List ( PDInstance r c ))
    → Ex>-sorted { r } pdis₁
    → Ex>-sorted { r } pdis₂
    → All (λ pdi₁ → Ex>-maybe  {r} pdi₁ (head pdis₂)) pdis₁
    -------------------------------------------------------
    → Ex>-sorted { r } (pdis₁ ++ pdis₂)
concat-ex-sorted []                       pdis₂          ex>-nil                                       pdis₂-sorted     []                              = pdis₂-sorted
concat-ex-sorted pdis₁                    []             pdis₁-sorted                                  ex>-nil           _  rewrite (++-identityʳ pdis₁) = pdis₁-sorted
concat-ex-sorted (pdi₁ ∷ [])             (pdi₂ ∷ pdis₂) pdis₁-sorted                                  pdi₂pdis₂-sorted (ex>-just pdi₁>pdi₂  ∷ [])      = ex>-cons pdi₂pdis₂-sorted (ex>-just pdi₁>pdi₂) 
concat-ex-sorted (pdi₁ ∷ pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) (ex>-cons pdi₁'pdis₁-sorted pdi₁>head-pdis₁)  pdi₂pdis₂-sorted (ex>-just pdi₁>pdi₂  ∷ pxs)     = ex>-cons ind-hyp pdi₁>head-pdis₁
  where
    ind-hyp = concat-ex-sorted (pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) pdi₁'pdis₁-sorted  pdi₂pdis₂-sorted  pxs 


---------------------------------------------------------------------------------------------------
-- concatmap-pdinstance-snd-ex>-sorted and its sub lemma
--------------------------------------------------------------------------------------------------

-- do we need this ? 

pdinstance-snd-fst-all->concatmap-pdinstance-snd : ∀ { l r : RE } {ε∈l : ε∈ l } { loc : ℕ } { c : Char }
    → ( e  : U l )
    → ( flat-[]-e : Flat-[] l e )
    → ( es : List (U l) )
    → ( flat-[]-es : All ( Flat-[] l ) es )
    → ( e>-head-es : >-maybe e (head es))
    → ( es->-sorted : >-sorted es ) 
    → ( pdis : List (PDInstance r c ) )
    → Homogenous pdis  -- we need this premise to ensure all pdis sharing the same p
    -----------------------------------------------------------------
    → All (λ pdi₁ → Ex>-maybe {l ● r ` loc } pdi₁ (head (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es))))
       (List.map (mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e)) pdis)
pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e (flat-[] e proj₁flat-e≡[]) [] [] >-nothing ex->-nil pdis _ = prf  (List.map (mk-snd-pdi (e , flat-[] e proj₁flat-e≡[])) pdis)
  where
    prf : (pdis : List (PDInstance (l ● r ` loc) c) )
          → All  (λ pdi₁ → Ex>-maybe pdi₁ nothing) pdis
    prf [] = []
    prf (pdi ∷ pdis) = ex>-nothing ∷ prf pdis
pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e₁ flat-[]-e₁                   (e₂ ∷ es) (flat-[]-e₂ ∷ flat-[]-es)                  (>-just e₁>e₂) e₂es->sorted [] _ = [] 
pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e₁ (flat-[] e₁ proj₁flate₁≡[])  (e₂ ∷ es) ((flat-[] e₂ proj₁flate₂≡[]) ∷ flat-[]-es) (>-just e₁>e₂) e₂es->sorted
  (pdi@(pdinstance {p} {r} {c} inj s-ev) ∷ pdis) (homogenous ( .(pdi) ∷ .(pdis) ) ( .(p) , ( hide .{p} .{r} .{c} .(inj) .(s-ev) ) ∷ hide-p-pdis))    =  sub (pdi ∷ pdis) (( hide {p} {r} {c} inj s-ev ) ∷ hide-p-pdis)
  where 
    sub : ( pdis' : List (PDInstance r c) )
          → All (Inhabit p) pdis' 
          →  All (λ pdi₁ → Ex>-maybe pdi₁
                    (head
                      (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x (pdi ∷ pdis))
                                 ((e₂ , (flat-[] e₂ proj₁flate₂≡[])) ∷ zip-es-flat-[]-es {l} {ε∈l}  es flat-[]-es))))
                    (List.map (mk-snd-pdi (e₁ , (flat-[] e₁ proj₁flate₁≡[]))) pdis')
    sub [] []  = []
    sub (pdi'@(pdinstance .{p} .{r} .{c} inj' s-ev') ∷ pdis' ) ((hide .{p} .{r} .{c} .(inj') .(s-ev')) ∷  hide-p-pdis')  = -- we can't enforce p' is p
      ex>-just (>-pdi inject₁ sound-ev₁ inject₂ sound-ev₂ prf₁ prf₂ )
        ∷ sub pdis'   hide-p-pdis'
      where
        inject₁ : U p → U (l ● r ` loc )
        inject₁ = mkinjSnd inj' e₁
        sound-ev₁ : ( u : U p ) → proj₁ (flat (inject₁ u)) ≡ c ∷ proj₁ (flat u )
        sound-ev₁ = mkinjSndSoundEv {p} {l} {r} {loc} {c}  inj' s-ev' e₁ (flat-[] e₁ proj₁flate₁≡[])
        inject₂ : U p → U (l ● r ` loc )
        inject₂ = mkinjSnd inj e₂ 
        sound-ev₂ : ( u : U p ) → proj₁ (flat (inject₂ u)) ≡ c ∷ proj₁ (flat u )
        sound-ev₂ = mkinjSndSoundEv {p} {l} {r} {loc} {c}  inj s-ev e₂ (flat-[] e₂ proj₁flate₂≡[])

        len-|inject₁-u|≡len-|u|+1 : (u : U  p ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject₁-u|≡len-|u|+1 u rewrite (sound-ev₁ u) = refl 
    
        len-|inject₂-u|≡len-|u|+1 : (u : U  p ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject₂-u|≡len-|u|+1 u rewrite (sound-ev₂ u) = refl 

        prf₁ : (v₁ v₂ : U p)
             → p ⊢ v₁ > v₂
             → (l ● r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
        prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|inject₁v₁|>len|inject₂v₂|
          where
            len|inject₁v₁|>len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.> length (proj₁ (flat (inject₂ v₂)))
            len|inject₁v₁|>len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
        prf₁ v₁ v₂ (len-≡ len|v₁|≡len|v₂| v₁>ⁱv₂) = len-≡ len|inject₁v₁|≡len|inject₂v₂| (seq₁ e₁>e₂)
          where
            len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) ≡ length (proj₁ (flat (inject₂ v₂)))
            len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ | len|v₁|≡len|v₂|  = refl 
            
        prf₂ : (v : U p) → ( (l ● r ` loc) ⊢  inject₁ v > inject₂ v) ⊎ (inject₁ v ≡ inject₂ v) 
        prf₂ v = inj₁ (len-≡ len|inject₁v|≡len|inject₂v| (seq₁ e₁>e₂))
          where
            len|inject₁v|≡len|inject₂v| : length (proj₁ (flat (inject₁ v))) ≡ length (proj₁ (flat (inject₂ v)))
            len|inject₁v|≡len|inject₂v| rewrite len-|inject₁-u|≡len-|u|+1 v |  len-|inject₂-u|≡len-|u|+1 v   = refl 


concatmap-pdinstance-snd-ex>-sorted-sub : ∀ { l r : RE } {ε∈l : ε∈ l } {loc : ℕ } { c : Char }
                                     → ( es : List (U l) )
                                     → ( flat-[]-es : All ( Flat-[] l ) es ) 
                                     → ( ex->-sorted : >-sorted es ) 
                                     → ( pdis : List (PDInstance r c ) )
                                     → Ex>-sorted {r} pdis
                                     → Homogenous pdis  -- we need this premise to ensure all pdis sharing the same p
                                     ----------------------------------------------------------------
                                     → Ex>-sorted {l ● r ` loc} (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es))
concatmap-pdinstance-snd-ex>-sorted-sub {l} {r} {ε∈l} {loc} {c} []       []                        >-nil                          _    _               _ = ex>-nil
concatmap-pdinstance-snd-ex>-sorted-sub {l} {r} {ε∈l} {loc} {c} (e ∷ es) (flat-[]-e ∷ flat-[]-es)  (>-cons es->-sorted e>head-es) pdis pdis-ex>-sorted pdis-homo =
  concat-ex-sorted
    (List.map (mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e)) pdis)                                          -- ^ curr batch
    (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es)) -- ^ next bacth
    curr-sorted
    next-sorted
    (pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  e flat-[]-e es flat-[]-es e>head-es es->-sorted pdis pdis-homo ) 
  where
    curr-sorted : Ex>-sorted {l ● r ` loc} (List.map (mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e)) pdis)
    curr-sorted = pdinstance-snd-ex>-sorted {l} {r} {loc} {c} (e , flat-[]-e) pdis pdis-ex>-sorted
    next-sorted : Ex>-sorted {l ● r ` loc} (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es))
    next-sorted = concatmap-pdinstance-snd-ex>-sorted-sub {l} {r} {ε∈l} {loc} {c} es flat-[]-es es->-sorted pdis pdis-ex>-sorted pdis-homo

-- pdinstances generated by concatmap-pdinstance-snd must be ex sorted. 
concatmap-pdinstance-snd-ex>-sorted : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
                                     → ( pdis : List (PDInstance r c ) )
                                     → Ex>-sorted {r} pdis
                                     → Homogenous pdis  -- we need this premise to ensure all pdis sharing the same p                                     
                                     → Ex>-sorted {l ● r ` loc } (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis)
concatmap-pdinstance-snd-ex>-sorted {l} {r} {ε∈l} {loc} {c} pdis ex>-sorted-pdis pdis-homo = concatmap-pdinstance-snd-ex>-sorted-sub {l} {r}  {ε∈l} {loc} {c}  es flat-[]-es es->-sorted pdis ex>-sorted-pdis pdis-homo 
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l
    es->-sorted : >-sorted es
    es->-sorted = mkAllEmptyU-sorted {l} ε∈l 
    
---------------------------------------------------------------------------------------------------
-- concatmap-pdinstance-snd-ex>-sorted and its sub lemma END 
--------------------------------------------------------------------------------------------------



map-fuse-sorted :  ∀ { r : RE } {loc : ℕ } { c : Char }
  → ( pdi₁ : PDInstance r c )
  → ( pdis₂ : List (PDInstance r c ))
  → Ex>-sorted { r } pdis₂
  → Homogenous pdis₂
  ------------------------------------------------------------
  → Ex>-sorted { r } (List.map (fuse {r} {loc} {c} pdi₁) pdis₂)
map-fuse-sorted {r} {loc} {c} pdi₁ [] ex>-nil _ = ex>-nil
map-fuse-sorted {r} {loc} {c} pdi₁@(pdinstance {p₁} {r} {c} in₁ s-ev₁) (pdi₂@(pdinstance {p₂} .{r} .{c} in₂ s-ev₂) ∷ pdis₂) (ex>-cons ex>-sorted-pdis₂ pdi₂>head-pdis₂) (homogenous (.(pdi₂) ∷ .(pdis₂)) ( .(p₂) , (hide .{p₂} {r} {c} in₂ s-ev₂ ) ∷ hide-p₂-pdis₂ )) =
  ex>-cons (map-fuse-sorted (pdinstance in₁ s-ev₁) pdis₂ ex>-sorted-pdis₂ (homogenous pdis₂ (p₂ , hide-p₂-pdis₂)) ) (sub pdi₂ pdis₂ pdi₂>head-pdis₂ (hide in₂ s-ev₂) hide-p₂-pdis₂ )
  where
    sub : (qdi : PDInstance r c )
       → (qdis : List (PDInstance r c))
       → Ex>-maybe qdi (head qdis)
       → Inhabit p₂ qdi
       → All (Inhabit p₂) qdis
       → Ex>-maybe (fuse {r} {loc} {c}  (pdinstance in₁ s-ev₁) qdi) (head (List.map (fuse {r} {loc} {c}  (pdinstance in₁ s-ev₁)) qdis)) 
    sub qdi@(pdinstance {p₂} .{r} .{c} inj s-ev) [] ex>-nothing _ _   = ex>-nothing
    sub qdi@(pdinstance .{p₂} .{r} .{c} inj s-ev) ((pdinstance .{p₂} .{r} .{c} inj' s-ev') ∷ qdis) (ex>-just (>-pdi .(inj) .(s-ev) .(inj') .(s-ev') v₁→v₂→v₁>v₂→injv₁>inj'v₂ v→injv≥inj'v   )) -- (ex>-just qdi>qdi' )
      -- qdi>qdi' : r , c ⊢ pdinstance inj s-ev > pdinstance inj' s-ev'
      (hide .{p₂} .{r} .{c}  .(inj) .(s-ev)) 
      ((hide .{p₂} .{r} .{c}  .(inj') .(s-ev')) ∷ hide-p₂-qids )= ex>-just (>-pdi inject₁ sound-ev₁ inject₂ sound-ev₂ prf₁ prf₂)
      where
        inject₁ : U (p₁ + p₂ ` loc) → U r 
        inject₁ = mkfuseInj in₁ inj
        inject₂ : U (p₁ + p₂ ` loc) → U r         
        inject₂ = mkfuseInj in₁ inj'
        sound-ev₁ : ( u :  U (p₁ + p₂ ` loc) )  → proj₁ (flat (inject₁ u)) ≡ c ∷ proj₁ (flat u )
        sound-ev₁ = mkfuseInjSoundEv {p₁} {p₂} {r} {loc} {c}  in₁ inj s-ev₁ s-ev 
        sound-ev₂ : ( u :  U (p₁ + p₂ ` loc) )  → proj₁ (flat (inject₂ u)) ≡ c ∷ proj₁ (flat u )
        sound-ev₂ = mkfuseInjSoundEv {p₁} {p₂} {r} {loc} {c}  in₁ inj' s-ev₁ s-ev'

        len-|inject₁-u|≡len-|u|+1 : (u : U (p₁ + p₂ ` loc) ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject₁-u|≡len-|u|+1 u rewrite (sound-ev₁ u) = refl 
    
        len-|inject₂-u|≡len-|u|+1 : (u : U (p₁ + p₂ ` loc) ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject₂-u|≡len-|u|+1 u rewrite (sound-ev₂ u) = refl 

        prf₁ : (v₁ v₂ : U (p₁ + p₂ ` loc))
          → (p₁ + p₂ ` loc) ⊢ v₁ > v₂
          →  r ⊢ inject₁ v₁ > inject₂ v₂ 
        prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|inject₁v₁|>len|inject₂v₂|
          where
            len|inject₁v₁|>len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.> length (proj₁ (flat (inject₂ v₂)))
            len|inject₁v₁|>len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
            
        prf₁ v₁@(LeftU u₁) v₂@(LeftU u₂) (len-≡ len|v₁|≡len|v₂| (choice-ll u₁>u₂)) = len-≡ len|inject₁v₁|≡len|inject₂v₂| inject₁leftu₁>inject₂leftu₂
          where 
            len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) ≡ length (proj₁ (flat (inject₂ v₂)))
            len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
            in₁u₁>in₁u₂ : r ⊢ in₁ u₁ > in₁ u₂
            in₁u₁>in₁u₂ = {!!}
            inject₁leftu₁≡
            inject₁leftu₁>inject₂leftu₂ : r ⊢ inject₁ (LeftU u₁) >ⁱ inject₂ (LeftU u₂)
            inject₁leftu₁>inject₂leftu₂ = {!!} 
        prf₂ : (v : U (p₁ + p₂ ` loc))
          → ( r ⊢ inject₁ v > inject₂ v ) ⊎ (inject₁ v ≡ inject₂ v )
        prf₂ v@(RightU u) = inj₁ (len-≡ len|inject₁v|≡len|inject₂v| (  {!!} ) )
          -- why choice-r here does not work? because it is not a r + s type in the end, it is r!
          -- we need >-pdi between  inject1 is in1 + inj, inject2 is in1 + inj'
          -- inject₁ (RightU u) --> inj u
          -- inject₂ (RightU u) --> inj' u  we need qdi > qdi' 
          where 
            len|inject₁v|≡len|inject₂v| : length (proj₁ (flat (inject₁ v))) ≡ length (proj₁ (flat (inject₂ v)))
            len|inject₁v|≡len|inject₂v| rewrite len-|inject₁-u|≡len-|u|+1 v |  len-|inject₂-u|≡len-|u|+1 v = refl 
        prf₂ v@(LeftU u) = inj₂ refl 
          -- why choice-ll here does not work? because it is not a r + s type in the end, it is r!
          -- we need >-pdi between  inject1 is in1 + inj, inject2 is in1 + inj'
          -- inject₁ (LeftU u) --> in₁ u
          -- inject₂ (LeftU u) --> in₁ u  should be ≡ !
          where 
            len|inject₁v|≡len|inject₂v| : length (proj₁ (flat (inject₁ v))) ≡ length (proj₁ (flat (inject₂ v)))
            len|inject₁v|≡len|inject₂v| rewrite len-|inject₁-u|≡len-|u|+1 v |  len-|inject₂-u|≡len-|u|+1 v = refl 


oplus-ex-sorted : ∀ { r : RE } {loc : ℕ } { c : Char }
    → ( pdis₁ : List ( PDInstance r c ))
    → ( pdis₂ : List ( PDInstance r c ))
    → Ex>-sorted { r } pdis₁
    → Ex>-sorted { r } pdis₂ 
    -------------------------------------------------------
    → Ex>-sorted { r } (pdinstance-oplus {r} {loc} {c}  pdis₁ pdis₂)
oplus-ex-sorted {r} {loc} {c} []             pdis₂          ex>-nil                                     ex>-sorted-pdis₂  = ex>-sorted-pdis₂
oplus-ex-sorted {r} {loc} {c} (pdi₁ ∷ pdis₁) []             ex>-sorted-pdi₁pdis₁                        ex>-nil           = ex>-sorted-pdi₁pdis₁
oplus-ex-sorted {r} {loc} {c} (pdi₁@(pdinstance {p₁} {r} {c} in₁ s-ev₁) ∷ pdis₁) (pdi₂@(pdinstance {p₂} .{r} .{c} in₂ s-ev₂) ∷ pdis₂) (ex>-cons ex>-sorted-pdis₁ pdi₁>head-pdis₁) (ex>-cons ex>-sorted-pdis₂ pdi₂>head-pdis₂) = oplus-ex-sorted-sub (pdi₁ ∷ pdis₁) (pdi₂ ∷ pdis₂) (ex>-cons ex>-sorted-pdis₁ pdi₁>head-pdis₁) (ex>-cons ex>-sorted-pdis₂ pdi₂>head-pdis₂)
  where
    oplus-ex-sorted-sub :
        ( pdisˡ : List ( PDInstance r c ))
      → ( pdisʳ : List ( PDInstance r c ))
      → Ex>-sorted { r } pdisˡ 
      → Ex>-sorted { r } pdisʳ
      → Ex>-sorted {r} ( concatMap (λ pdi → List.map (fuse {r} {loc} {c}  pdi)  pdisʳ) pdisˡ) 
    oplus-ex-sorted-sub []             pdisʳ ex>-nil ex>-sorted-pdisʳ = ex>-nil
    oplus-ex-sorted-sub (pdiˡ ∷ pdisˡ) []     ex>-sorted-pdiˡ∷pdisˡ ex>-nil rewrite Utils.concatmap-λx→[]-xs≡[] { PDInstance r c} { PDInstance r c}  (pdiˡ ∷ pdisˡ) = ex>-nil
    oplus-ex-sorted-sub (pdiˡ ∷ []) (pdiʳ ∷ pdisʳ) (ex>-cons ex>-nil ex>-nothing) (ex>-cons ex>-sorted-pdisʳ pdiʳ>head-pdisʳ)  rewrite ++-identityʳ (List.map (fuse {r} {loc} {c} pdiˡ) pdisʳ)  =
      map-fuse-sorted  pdiˡ (pdiʳ ∷ pdisʳ) (ex>-cons ex>-sorted-pdisʳ pdiʳ>head-pdisʳ) {!!} 
    oplus-ex-sorted-sub (pdiˡ ∷ pdisˡ) (pdiʳ ∷ pdisʳ) (ex>-cons ex>-sorted-pdisˡ pdiˡ>head-pdisˡ) (ex>-cons ex>-sorted-pdisʳ pdiˡ>head-pdisʳ) = ex>-cons {!!} {!!} -- hide-p₂-pdis₂ 
      


-- main lemma: 
pdU-sorted : ∀ { r : RE } { c : Char }
  → Ex>-sorted {r} {c} pdU[ r , c ]
pdU-sorted {ε} {c} = ex>-nil
pdU-sorted {$ c ` loc } {c'} with c Char.≟ c'
...                           | no _ = ex>-nil 
...                           | yes refl = ex>-cons ex>-nil ex>-nothing 
  where
    -- duplicated from PartialDerivativeParseTree
    pdi : PDInstance ($ c ` loc) c
    pdi = pdinstance {ε} {$ c ` loc} {c}
                     (λ u → LetterU {loc} c)
                          (λ EmptyU →                 -- ^ soudness ev
                             begin
                               [ c ]
                             ≡⟨⟩
                               c ∷ []
                             ≡⟨ cong ( λ x → ( c ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                               c ∷ (proj₁ (flat EmptyU))
                             ∎)
                             
pdU-sorted {l + r ` loc } {c} =  oplus-ex-sorted {l + r ` loc} {loc} {c} (List.map pdinstance-left pdU[ l , c ]) (List.map pdinstance-right pdU[ r , c ]) (map-left-ex-sorted pdU[ l , c ] ind-hyp-l) (map-right-ex-sorted pdU[ r , c ] ind-hyp-r) 
  where
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c}
    ind-hyp-r : Ex>-sorted pdU[ r , c ]
    ind-hyp-r = pdU-sorted {r} {c}
pdU-sorted {l * ε∉l ` loc } {c} =  map-star-ex-sorted pdU[ l , c ] ind-hyp-l
  where 
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c}

pdU-sorted {l ● r ` loc } {c} with ε∈? l
...  | no ¬ε∈l = map-fst-ex-sorted {l} {r} {loc} {c}  pdU[ l , c ] ind-hyp-l
  where
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c}
...  | yes ε∈l =  oplus-ex-sorted {l ● r ` loc} {loc} {c} (List.map pdinstance-fst pdU[ l , c ]) (concatmap-pdinstance-snd pdU[ r , c ]) (map-fst-ex-sorted {l} {r} {loc} {c} pdU[ l , c ] ind-hyp-l) (concatmap-pdinstance-snd-ex>-sorted {l} {r} {ε∈l} {loc} {c} pdU[ r , c ] ind-hyp-r homo-r) 
  where
    ind-hyp-l : Ex>-sorted pdU[ l , c ]
    ind-hyp-l = pdU-sorted {l} {c}
    ind-hyp-r : Ex>-sorted pdU[ r , c ]
    ind-hyp-r = pdU-sorted {r} {c}
    homo-r : Homogenous pdU[ r , c ]
    homo-r = pdU-Homogenous {r} {c} 




```

```agda
-- singleton definition not working 
{-
private 
  variable
    ℓ : Agda.Primitive.Level
    
data NilSingleton { A : Set ℓ } : List A → Set ℓ where
  isNil :  NilSingleton []
  isSingleton :  ( x : A ) → NilSingleton  (x ∷ [])

  


map-NilOrSingleton : ∀ { A B : Set } { f : A → B } { xs : List A }
  → NilSingleton xs
  ------------------------------
  → NilSingleton (List.map f xs)
map-NilOrSingleton {A} {B} {f} {[]} isNil = isNil
map-NilOrSingleton {A} {B} {f} {x ∷ []} (isSingleton .(x)) = isSingleton (f x) 

oplus-NilOrSingleton : ∀ { r : RE } { loc : ℕ } { c : Char }
  → ( pdis₁ : List (PDInstance r c ) )
  → ( pdis₂ : List (PDInstance r c ) )
  → NilSingleton pdis₁
  → NilSingleton pdis₂
  --------------------------------------------------------------
  → NilSingleton (pdinstance-oplus {r} {loc} {c} pdis₁ pdis₂)
oplus-NilOrSingleton {r} {loc} {c} [] pdis₂ isNil nilsingleton-pdis₂          = nilsingleton-pdis₂
oplus-NilOrSingleton {r} {loc} {c} (pdi₁ ∷ []) [] (isSingleton .(pdi₁)) isNil = isSingleton pdi₁
oplus-NilOrSingleton {r} {loc} {c} (pdi₁ ∷ []) (pdi₂ ∷ []) (isSingleton .(pdi₁)) (isSingleton .(pdi₂)) = isSingleton (PartialDerivative.fuse pdi₁ pdi₂) 


pdinstance-snd-NilOrSingleton : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( es-flat-[]-es : ∃[ e ] (Flat-[] l e ) )
  → ( pdis : List (PDInstance r c ) )
  → NilSingleton pdis
  --------------------------------------------------------------
  → NilSingleton (pdinstance-snd {l} {r} {loc} {c} es-flat-[]-es pdis)
pdinstance-snd-NilOrSingleton = {!!}   
  


concatmap-pdinstance-snd-NilOrSingleton : { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c  : Char }
  → ( pdis : List (PDInstance r c ) )
  → NilSingleton pdis
  ----------------------------------------------------------------------
  → NilSingleton (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis)
concatmap-pdinstance-snd-NilOrSingleton {l} {r} {ε∈l} {loc} {c} [] isNil   rewrite PosixOrder.concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c} =  isNil
concatmap-pdinstance-snd-NilOrSingleton {l} {r} {ε∈l} {loc} {c} (pdi ∷ []) (isSingleton .(pdi)) = sub e-flat-es
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l
    e-flat-es :  List ( ∃[ e ] (Flat-[] l e) )
    e-flat-es = zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es
    sub : (xs :  List ( ∃[ e ] (Flat-[] l e) )) →  NilSingleton (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x (pdi ∷ [])) xs)
    sub [] = isNil 
    sub (x ∷ xs) = {!!}  -- mkAllEmptyU is not singleton? hence  (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis) is not singleton
    -- can we nail down a counter example ?

    -- since Singleton is not guanranteed by pdU operations.
    -- we define a weaker property.
    -- all the partial derivative descendants in posix PDU must be sharing the same p, the partial derivative expression is the same.



    


pdU-NilOrSingleton : ∀ { r : RE } { c : Char }
  → NilSingleton pdU[ r  , c ]
pdU-NilOrSingleton {ε} {c} = isNil
pdU-NilOrSingleton {$ c ` loc} {c₁} with c Char.≟ c₁
... | no ¬c≡c₁ = isNil
... | yes c≡c₁ rewrite c≡c₁ = isSingleton
                              ( pdinstance {ε} {$ c₁ ` loc} {c₁} -- copied from PartialDerivative 
                                                 (λ u → LetterU {loc} c₁)
                                                 (λ EmptyU →                 -- ^ soundness ev
                                                   begin
                                                     [ c₁ ]
                                                    ≡⟨⟩
                                                     c₁ ∷ []
                                                    ≡⟨ cong ( λ x → ( c₁ ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                                                     c₁ ∷ (proj₁ (flat EmptyU))
                                                    ∎) )
pdU-NilOrSingleton {l + r ` loc} {c} = oplus-NilOrSingleton (List.map pdinstance-left pdU[ l , c ]) (List.map pdinstance-right pdU[ r , c ]) (map-NilOrSingleton ind-hyp-l) (map-NilOrSingleton ind-hyp-r)
  where
    ind-hyp-l :  NilSingleton pdU[ l  , c ]
    ind-hyp-l = pdU-NilOrSingleton {l} {c}
    ind-hyp-r :  NilSingleton pdU[ r  , c ]
    ind-hyp-r = pdU-NilOrSingleton {r} {c}    
    
pdU-NilOrSingleton {l ● r ` loc} {c} with ε∈? l
... | no ¬ε∈l = map-NilOrSingleton (pdU-NilOrSingleton {l} {c})
... | yes ε∈l = oplus-NilOrSingleton (List.map pdinstance-fst pdU[ l , c ]) ( concatmap-pdinstance-snd {l} {r} {ε∈l}   {loc} {c} pdU[ r , c ] ) (map-NilOrSingleton ind-hyp-l) (concatmap-pdinstance-snd-NilOrSingleton pdU[ r , c ] ind-hyp-r) 
  where
    ind-hyp-l :  NilSingleton pdU[ l  , c ]
    ind-hyp-l = pdU-NilOrSingleton {l} {c}
    ind-hyp-r :  NilSingleton pdU[ r  , c ]
    ind-hyp-r = pdU-NilOrSingleton {r} {c}
pdU-NilOrSingleton {r * ε∉r ` loc} {c} = map-NilOrSingleton ind-hyp-r
  where 
    ind-hyp-r :  NilSingleton pdU[ r  , c ]
    ind-hyp-r = pdU-NilOrSingleton {r} {c}




concatmap-advance-pdi*-with-c-NilOrSingleton : ∀ { r : RE } { pref : List Char } { c : Char }
  → (pdis : List (PDInstance* r pref))
  → NilSingleton pdis
  --------------------------------------
  → NilSingleton (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
concatmap-advance-pdi*-with-c-NilOrSingleton {r} {pref} {c} [] isNil = isNil
concatmap-advance-pdi*-with-c-NilOrSingleton {r} {pref} {c} (pdi@(pdinstance* {p} {r} {w} inj s-ev) ∷ []) (isSingleton .(pdi)) with pdU[ p , c ] | pdU-NilOrSingleton {p} {c} 
... | []         | isNil = isNil
... | qdi ∷ []  | isSingleton .(qdi) =  isSingleton (compose-pdi-with inj s-ev qdi)
  

pdUMany-aux-NilOrSingleton : ∀ { r : RE } { pref : List Char }
  → ( c : Char)
  → ( cs : List Char )
  → ( pdis : List (PDInstance*  r pref ) )
  → NilSingleton pdis
  -----------------------------------------
  → NilSingleton (pdUMany-aux (c ∷ cs) pdis)
pdUMany-aux-NilOrSingleton {r} {pref} c [] pdis nilorsingleton-pdis rewrite (++-identityʳ (pref ∷ʳ c) ) =  concatmap-advance-pdi*-with-c-NilOrSingleton pdis nilorsingleton-pdis
pdUMany-aux-NilOrSingleton {r} {pref} c (d ∷ cs) pdis nilorsingleton-pdis = pdUMany-aux-NilOrSingleton {r} {pref ∷ʳ c} d cs (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis) ( concatmap-advance-pdi*-with-c-NilOrSingleton pdis nilorsingleton-pdis ) 

pdUMany-NilOrSingleton : ∀ { r : RE } { w : List Char }
  → NilSingleton (pdUMany[ r , w ])
pdUMany-NilOrSingleton {r} {[]} = isSingleton
                                    (pdinstance* PartialDerivative.injId PartialDerivative.injId-sound)
pdUMany-NilOrSingleton {r} {c ∷ cs}  =  pdUMany-aux-NilOrSingleton {r} {[]} c cs  [ ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ] (isSingleton (pdinstance* (λ u → u) (λ u → refl)))    


map-inj-sorted : ∀ { p r : RE } 
  → ( us : List ( U p ) )
  → ( inj : U p → U r )
  → ( (u₁ : U p) → (u₂ : U p) → p ⊢ u₁ > u₂ → r ⊢ inj u₁ > inj u₂ )
  → >-sorted {p} us
  ---------------------------------
  → >-sorted {r} (List.map inj us)
map-inj-sorted {p} {r} [] inj >-inc-ev >-nil = >-nil
map-inj-sorted {p} {r} (u ∷ []) inj >-inc-ev (>-cons >-nil >-nothing)  = >-cons >-nil >-nothing
map-inj-sorted {p} {r} (u₁ ∷ (u₂ ∷  us)) inj >-inc-ev (>-cons u₂us-sorted (>-just u₁>u₂) )  = >-cons ind-hyp (>-just (>-inc-ev u₁ u₂ u₁>u₂))
  where
    ind-hyp : >-sorted {r} (List.map inj (u₂ ∷ us))
    ind-hyp = map-inj-sorted {p} {r} (u₂ ∷ us) inj >-inc-ev u₂us-sorted 



concatMap-buildU-sorted : ∀ { r : RE } { w : List Char }
  → ( pdis : List (PDInstance* r w ) )
  → NilSingleton pdis
  → All *>-Inc pdis
  → >-sorted {r} (concatMap buildU pdis)
concatMap-buildU-sorted {r} {w} [] isNil [] =  >-nil
concatMap-buildU-sorted {r} {w} ((pdi@(pdinstance* {p} {r} inj s-ev)) ∷ []) (isSingleton .(pdi)) ((*>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) ∷ [])  with ε∈? p
... | no _ = >-nil
... | yes  ε∈p rewrite (++-identityʳ (List.map inj (mkAllEmptyU ε∈p))) =  map-inj-sorted (mkAllEmptyU ε∈p) inj u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ (mkAllEmptyU-sorted ε∈p)


parseAll-is-posix-sorted : ∀ { r : RE } { w : List Char }
  →  >-sorted {r} (parseAll[ r , w ])
parseAll-is-posix-sorted {r} {w} = concatMap-buildU-sorted pdUMany[ r , w ] pdUMany-NilOrSingleton pdUMany-*>-inc 

-}




```

