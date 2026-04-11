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
  compose-pdi-with; compose-pdi-with-soundEv  ; concatmap-pdinstance-snd-[]≡[]
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
  >-Inc ; >-inc ;
  pdU->-inc ; 
  >-trans ; *>-Inc ; *>-inc ;
  concatmap-advance-pdi*-with-c-*>inc ;
  pdUMany-*>-inc ;
  >-inc-fuse-fst-pdi-flat-[]-fst-pdi ;
  >-inc-mk-snd-pdi ;
  >-inc-pdinstance-snd ;
  Flat-[]-Fst-PDI ; fst-flat-[] ; flat-[]-fst ;
  flat-[]-fst-pdinstance-snd 
  )



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
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalˡ ; ++-conicalʳ ;  ++-assoc ; map-++ )


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
    → ( s-ev : ∀ ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) )  -- ^ soundnes evidence
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


-- lifted out from concatmap-snd-inhabit⁺
map-snd-pdi-inhabit : ∀ {l r p : RE } {loc : ℕ } { c : Char}
  → ( e : U l )
  → ( flat-[]-e  :  (Flat-[] l e) ) 
  → ( qdis : List (PDInstance r c) )
  → All (Inhabit p ) qdis 
  → All (Inhabit p ) (List.map (mk-snd-pdi {l} {r} {loc} {c} (e , flat-[]-e) ) qdis)
map-snd-pdi-inhabit _  _ [] []  = []
map-snd-pdi-inhabit {l} {r} {p} {loc} {c}  e  flat-[]-e ( qdi@(pdinstance {- {p} {r} {c} -} inj s-ev) ∷ qdis ) ((hide .{p} .{r} .{c} .(inj) .(s-ev)) ∷ all-hide-p-qdis ) = 
  cong-mk-snd-pdi-inhabit {l} {r} {p} {loc} {c} (e , flat-[]-e) qdi (hide inj s-ev)
  ∷ map-snd-pdi-inhabit e  flat-[]-e   qdis all-hide-p-qdis 
  

concatmap-snd-inhabit⁺ :  ∀ { l r p : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char } { pdi : PDInstance r c } { pdis : List (PDInstance r c) }
  → Inhabit {r} {c} p pdi
  → All (Inhabit {r} {c} p) pdis
  --------------------------------------------
  → All (Inhabit {l ● r ` loc} {c} p) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} (pdi ∷ pdis))
  -- hm... p is the partial derivative here. not p ● r !!!
  -- so it is not weaksingleton or homomogenous
  -- posix has a very unique extended ordering
  -- it is like staircase, a list of pdis with the same partial derivative,
  -- the until a concat case... change to another partial derivative which should be following ≥ order.  let me think about how to write it down as data type in agda.
  -- update: it is ok, because (pˡ ● r) the fst'ed pd and pʳ the snd'ed pd, will be combined by oplus and become (pˡ ● r) + pʳ
  -- update2: the order is not total, it is a poset and a lattice. 
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
    prf ( (x , flat-[]-x) ∷ xs ) = all-concat (map-snd-pdi-inhabit x flat-[]-x ((pdinstance inj s-ev) ∷ pdis) (hide inj s-ev ∷ all-hide-p-pdis))  (prf xs)

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



-- this lemma is lifted out from oplus-Homoegenous, which can be resused.
map-fuse-inhabit : { r p₁ p₂ : RE } {loc : ℕ } { c : Char}
            → (pdi : PDInstance r c)
            → ( pdis₂' : List (PDInstance r c ) )
            → Inhabit {r} {c} p₁ pdi 
            → All (Inhabit {r} {c} p₂) pdis₂'
            → All (Inhabit {r} {c} (p₁ + p₂ ` loc)) (List.map (fuse  {r} {loc} {c} pdi) (pdis₂'))
map-fuse-inhabit (pdinstance in₁ s-ev₁)  [] hide-p₁-pdi₁ [] = []
map-fuse-inhabit {r} {p₁} {p₂} {loc} {c} pdi@(pdinstance in₁ s-ev₁) ((pdinstance in₂ s-ev₂) ∷ pdis₂')  hide-p₁-pdi@(hide .{p₁} {r} {c} .(in₁) .(s-ev₁)) (hide-p₂-pdi₂'@(hide .{p₂} {r} {c} .(in₂) .(s-ev₂)) ∷ hide-p₂-pdis₂') = (hide inj sound-ev) ∷ map-fuse-inhabit pdi pdis₂' hide-p₁-pdi hide-p₂-pdis₂' 
  where
    inj : U (p₁ + p₂ ` loc ) → U r
    inj = mkfuseInj in₁ in₂
    sound-ev : (u : U (p₁ + p₂ ` loc)) → proj₁ (flat (inj u))  ≡ c ∷ proj₁ (flat u)
    sound-ev = mkfuseInjSoundEv in₁ in₂ s-ev₁ s-ev₂

oplus-Homogenous : ∀ { r : RE } { loc : ℕ } { c : Char }
  → ( pdis₁ : List (PDInstance r c ) )
  → ( pdis₂ : List (PDInstance r c ) )
  → Homogenous pdis₁
  → Homogenous pdis₂
  --------------------------------------------------------------
  → Homogenous (pdinstance-oplus {r} {loc} {c} pdis₁ pdis₂)
oplus-Homogenous {r} {loc} {c} []             pdis₂ _  homo-pdis₂ = homo-pdis₂
oplus-Homogenous {r} {loc} {c} (pdi₁ ∷ pdis₁) []    homo-pdi₁pdis₁ _ = homo-pdi₁pdis₁
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
          sub-prf ( pdi₁' ∷ pdis₁') ( hide-p₁-pdi₁' ∷ hide-p₁-pdis₁' ) =
            all-concat ( map-fuse-inhabit {r} {p₁} {p₂} {loc} {c}  pdi₁' (pdi₂ ∷  pdis₂) hide-p₁-pdi₁' (hide-p₂-pdi₂ ∷ hide-p₂-pdis₂ ) )  (sub-prf pdis₁'  hide-p₁-pdis₁')              


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

We say pdi₁ is "posix" greater than pdi₂, r , c  ⊢ pdi₁ ≥ pdi₂ iff
  for all parse trees u₁ u₂  of r, |u₁| ≥ |u₂|, u₁ is constructible from pdi₁ and u₂ is constructibled from pdi₂ 
    then r ⊢ u₁ ≥ u₂ ?


.


```agda
  

-- does that mean that they are actually the same injection?? no...
-- this order is partial, not total. 
data _,_⊢_≥_ : ∀ ( r : RE ) → (c : Char ) → PDInstance r c → PDInstance r c → Set where
  ≥-pdi : ∀ { r p : RE } { c : Char }
    → ( injection₁ : U p → U r )
    → ( s-ev₁ : ∀ ( u : U p ) → (proj₁ ( flat {r} (injection₁ u)) ≡ c ∷ (proj₁ (flat {p} u))) )
    → ( injection₂ : U p → U r )
    → ( s-ev₂ : ∀ ( u : U p ) → (proj₁ ( flat {r} (injection₂ u)) ≡ c ∷ (proj₁ (flat {p} u))) )
    → ( ∀ ( v₁ : U p )
        → ( v₂ : U p ) 
        → p ⊢ v₁ > v₂ -- or v₁ ≡ v₂ then via >-inc pdi₁ and >-trans we got the same 
        → r ⊢ injection₁ v₁ > injection₂ v₂ )
    → ( ∀ ( v : U p ) → ( r ⊢ injection₁ v > injection₂ v ) ⊎ (injection₁ v ≡ injection₂ v ) ) -- ? strict inc? 
   → r , c ⊢ (pdinstance {p} {r} {c} injection₁ s-ev₁) ≥ (pdinstance {p} {r} {c} injection₂ s-ev₂)

```




### Definition 37 : (Extended) POSIX order lattice

```agda

data Ex≥-maybe : ∀ { r : RE } { c : Char } ( pdi : PDInstance r c ) → ( mpdi : Maybe (PDInstance r c) ) → Set where
  ex≥-nothing : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c } 
    ---------------------------
    → Ex≥-maybe {r} {c} pdi nothing
  ex≥-just : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c }
    → { pdi' : PDInstance r c }
    → r , c ⊢ pdi ≥ pdi' 
    ----------------------------------
    → Ex≥-maybe {r} {c} pdi (just pdi')

data Ex≥-maybe₂ : ∀ { r : RE } { c : Char } ( mpdi : Maybe (PDInstance r c )) → ( mpdi' : Maybe (PDInstance r c) ) → Set where
  ex≥-nothingʳ : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c } 
    ---------------------------
    → Ex≥-maybe₂ {r} {c} (just pdi) nothing
  ex≥-nothingˡ : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c } 
    ---------------------------
    → Ex≥-maybe₂ {r} {c} nothing (just pdi)

  ex≥-nothing₂ : ∀ { r : RE } { c : Char }
    ---------------------------
    → Ex≥-maybe₂ {r} {c} nothing nothing

  ex≥-just₂ : ∀ { r : RE } { c : Char }
    → { pdi : PDInstance r c }
    → { pdi' : PDInstance r c }
    → r , c ⊢ pdi ≥ pdi' 
    ----------------------------------
    → Ex≥-maybe₂ {r} {c} (just pdi )(just pdi')




```




### Lemma 38: the list of pdinstances from pdU[ r , c] is a complete lattice over the partial order r , c ⊢_≥_  


Let r be a non problematic regular expression.

Let c be a letter.

Then pdU[r , c] is complete lattice. 



TODO: we should change the descrption, it is not sortedness. 
#### Sub Lemma 38.1 - 38.22 : r , c ⊢ _≥_ order is preserved inductively over pdinstance operations.

```agda

-------------------------------------------------------------
-- Sub Lemma 38.1 - 38.22 BEGIN
-------------------------------------------------------------
-- not total order, we don't need tricholomy
{-
import Relation.Binary.Definitions
open  Relation.Binary.Definitions using (
  Tri ; tri< ; tri≈ ; tri> ) 
-} 

left-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁  : PDInstance l c )
  → (pdi₂ : PDInstance l c )
  → l , c ⊢ pdi₁ ≥ pdi₂ 
  -------------------------------------------------
  → (l + r ` loc) , c ⊢ pdinstance-left pdi₁ ≥ pdinstance-left pdi₂
left-ex-sorted {l} {r} {loc} {c} (pdinstance {p} .{l} .{c} in₁ s-ev₁) (pdinstance .{p} .{l} .{c} in₂ s-ev₂)
  (≥-pdi .{l} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v ) = ≥-pdi {l + r ` loc} {p} {c} inject₁ s-ev₁  inject₂ s-ev₂ prf₁ prf₂
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
    ... | inj₂ in₁v≡in₂v = inj₂ (cong LeftU in₁v≡in₂v ) 
    ... | inj₁ in₁v>in₂v = inj₁ (len-≡ len-|left-in₁-v|≡len-|left-in₂-v| (choice-ll in₁v>in₂v) ) 
      where
        len-|left-in₁-v|≡len-|left-in₂-v| : length (proj₁ (flat (inject₁ v))) ≡ length (proj₁ (flat (inject₂ v)))
        len-|left-in₁-v|≡len-|left-in₂-v| rewrite len-|in₁-u|≡len-|u|+1 v | len-|in₂-u|≡len-|u|+1 v = refl

right-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁  : PDInstance r c )
  → (pdi₂ : PDInstance r c )
  → r , c ⊢ pdi₁ ≥ pdi₂ 
  -------------------------------------------------
  → (l + r ` loc) , c ⊢ pdinstance-right pdi₁ ≥ pdinstance-right pdi₂
right-ex-sorted {l} {r} {loc} {c} (pdinstance {p} .{r} .{c} in₁ s-ev₁) (pdinstance .{p} .{r} .{c} in₂ s-ev₂)
  (≥-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v ) = ≥-pdi {l + r ` loc} {p} {c} inject₁ s-ev₁  inject₂ s-ev₂ prf₁ prf₂
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
    ... | inj₂ in₁v≡in₂v = inj₂ (cong RightU in₁v≡in₂v) 
    ... | inj₁ in₁v>in₂v = inj₁ (len-≡ len-|right-in₁-v|≡len-|right-in₂-v| (choice-rr in₁v>in₂v ) )
      where
        len-|right-in₁-v|≡len-|right-in₂-v| : length (proj₁ (flat (inject₁ v))) ≡ length (proj₁ (flat (inject₂ v)))
        len-|right-in₁-v|≡len-|right-in₂-v| rewrite len-|in₁-u|≡len-|u|+1 v | len-|in₂-u|≡len-|u|+1 v = refl


star-ex-sorted : ∀ { r : RE }  { ε∉r : ε∉ r } {loc : ℕ} { c : Char } 
  → (pdi₁ : PDInstance r c )
  → (pdi₂ : PDInstance r c )
  → r , c ⊢ pdi₁ ≥ pdi₂ 
  -------------------------------------------------
  → (r * ε∉r ` loc) , c ⊢ pdinstance-star pdi₁ ≥ pdinstance-star pdi₂
star-ex-sorted {r} {ε∉r} {loc} {c}  (pdinstance {p} .{r} .{c} in₁ s-ev₁) (pdinstance .{p} .{r} .{c} in₂ s-ev₂)
    (≥-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v) = ≥-pdi {r * ε∉r ` loc} {p ● (r * ε∉r ` loc) ` loc } {c} (mkinjList in₁) (mkinjListSoundEv in₁ s-ev₁) (mkinjList in₂) (mkinjListSoundEv in₂ s-ev₂) prf₁ prf₂ 
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
      ... | inj₂ in₁u≡in₂u = len-≡ len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| (star-tail  in₁v≡in₂u vs>us ) 
        where
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| : length (proj₁ (flat (mkinjList in₁ (PairU {p} { r * ε∉r ` loc} {loc}  v (ListU vs))))) ≡ length (proj₁ (flat (mkinjList in₂ (PairU {p} { r * ε∉r ` loc} {loc}  u (ListU us)))))
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v (ListU vs)) | len-|inject₂-u|≡len-|u|+1 (PairU u (ListU us)) | len|pair-vvs|≡len|pair-uus| = refl
          in₁v≡in₂u  : in₁ v ≡ in₂ u
          in₁v≡in₂u rewrite v≡u = in₁u≡in₂u 
      ... | inj₁ in₁u>in₂u = len-≡ len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| (star-head in₁v>in₂u  ) 
        where
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| : length (proj₁ (flat (mkinjList in₁ (PairU {p} { r * ε∉r ` loc} {loc}  v (ListU vs))))) ≡ length (proj₁ (flat (mkinjList in₂ (PairU {p} { r * ε∉r ` loc} {loc}  u (ListU us)))))
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-uus| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v (ListU vs)) | len-|inject₂-u|≡len-|u|+1 (PairU u (ListU us)) | len|pair-vvs|≡len|pair-uus| = refl
          in₁v>in₂u  : r ⊢ in₁ v > in₂ u
          in₁v>in₂u rewrite v≡u = in₁u>in₂u 

      prf₂ : (v : U (p ● r * ε∉r ` loc ` loc)) →
        ( (r * ε∉r ` loc) ⊢ mkinjList in₁ v > mkinjList in₂ v )  ⊎  ( mkinjList in₁ v ≡  mkinjList in₂ v  )
      prf₂ (PairU v (ListU vs)) with v→in₁v≥in₂v v
      ... | inj₂ in₁v≡in₂v = inj₂ (cong (λ x → ListU (x ∷ vs)) in₁v≡in₂v ) 
      ... | inj₁ in₁v>in₂v = inj₁ (len-≡ len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-vvs| (star-head in₁v>in₂v) )
        where
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-vvs| : length (proj₁ (flat (mkinjList in₁ (PairU {p} { r * ε∉r ` loc} {loc}  v (ListU vs))))) ≡ length (proj₁ (flat (mkinjList in₂ (PairU {p} { r * ε∉r ` loc} {loc}  v (ListU vs)))))
          len-|star-in₁-pair-vvs|≡len-|star-in₂-pair-vvs| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v (ListU vs)) | len-|inject₂-u|≡len-|u|+1 (PairU v (ListU vs))  = refl
          

-- do we need this ?
{-
map-star-ex-sorted : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
                     → ( pdis : List (PDInstance r c) )
                     → Ex>-sorted {r} pdis
                     → Ex>-sorted {r * ε∉r ` loc } (List.map pdinstance-star pdis)
map-star-ex-sorted {r} {ε∉r} {loc} {c} [] ex>-nil = ex>-nil
map-star-ex-sorted {r} {ε∉r} {loc} {c} (pdi ∷ [])  (ex>-cons ex>-nil ex>-nothing) = ex>-cons ex>-nil ex>-nothing
map-star-ex-sorted {r} {ε∉r} {loc} {c} (pdi₁ ∷ pdi₂ ∷ pdis)  (ex>-cons ex>-sorted-pdi2pdis (ex>-just pdi1>pdi2))
  = ex>-cons (map-star-ex-sorted (pdi₂ ∷ pdis) ex>-sorted-pdi2pdis)
             (ex>-just (star-ex-sorted pdi₁ pdi₂ pdi1>pdi2))
-}



fst-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁ : PDInstance l c )
  → (pdi₂ : PDInstance l c )
  → l , c ⊢ pdi₁ ≥ pdi₂ 
  -------------------------------------------------
  → (l ● r ` loc) , c ⊢ pdinstance-fst pdi₁ ≥ pdinstance-fst pdi₂
fst-ex-sorted {l} {r} {loc} {c}  (pdinstance {p} .{l} .{c} in₁ s-ev₁) (pdinstance .{p} .{l} .{c} in₂ s-ev₂)
  (≥-pdi .{l} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v) = ≥-pdi {l ● r ` loc } { p ● r ` loc } {c} inject₁ sound-ev₁ inject₂ sound-ev₂ prf₁ prf₂
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
    ... | inj₂ in₁v₂≡in₂v₂ =  len-≡ len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| (seq₂ in₁v≡in₂u u₁>u₂) 
      where
        len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| : length (proj₁ (flat (inject₁ (PairU {p} {r} {loc} v₁ u₁)))) ≡ length (proj₁ (flat (inject₂ (PairU {p} {r} {loc} v₂ u₂))))
                                               
        len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v₁ u₁) | len-|inject₂-u|≡len-|u|+1 (PairU v₂ u₂) | len|pair-v₁u₁|≡len|pair-v₂u₂|  = refl 
        in₁v≡in₂u  : in₁ v₁ ≡ in₂ v₂
        in₁v≡in₂u rewrite v₁≡v₂ =  in₁v₂≡in₂v₂  
    ... | inj₁ in₁v₂>in₂v₂ =  len-≡ len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| (seq₁ in₁v>in₂u )
      where
        len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| : length (proj₁ (flat (inject₁ (PairU {p} {r} {loc} v₁ u₁)))) ≡ length (proj₁ (flat (inject₂ (PairU {p} {r} {loc} v₂ u₂))))
                                               
        len-|pair-in₁-v₁-u₁|≡len-|pair-in₂-v₂-u₂| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v₁ u₁) | len-|inject₂-u|≡len-|u|+1 (PairU v₂ u₂) | len|pair-v₁u₁|≡len|pair-v₂u₂|  = refl 
        in₁v>in₂u  : l ⊢ in₁ v₁ > in₂ v₂
        in₁v>in₂u rewrite v₁≡v₂ =  in₁v₂>in₂v₂  

    prf₂ :  (v : U (p ● r ` loc)) 
      → ( (l ● r ` loc) ⊢ inject₁ v > inject₂ v ) ⊎ ( inject₁ v ≡ inject₂ v )
    prf₂ (PairU v u) with v→in₁v≥in₂v v
    ... | inj₂ in₁v≡in₂v = inj₂ (cong (λ x → (PairU x u) ) in₁v≡in₂v ) 
    ... | inj₁ in₁v>in₂v = inj₁ (len-≡ len-|pair-in₁-v-u|≡len-|pair-in₂-v-u| (seq₁ in₁v>in₂v ))
      where
        len-|pair-in₁-v-u|≡len-|pair-in₂-v-u| : length (proj₁ (flat (inject₁ (PairU {p} {r} {loc} v u)))) ≡ length (proj₁ (flat (inject₂ (PairU {p} {r} {loc} v u))))
                                               
        len-|pair-in₁-v-u|≡len-|pair-in₂-v-u| rewrite len-|inject₁-u|≡len-|u|+1 (PairU v u) | len-|inject₂-u|≡len-|u|+1 (PairU v u)  = refl 
        




-- reflexivity
ex≥-refl : ∀ { r : RE } { c : Char } { pd : PDInstance r c }
  → >-Inc pd 
  → r , c ⊢ pd ≥ pd
ex≥-refl  {r} {c} {pdinstance {p} .{r} .{c} in₁ s-ev₁} (>-inc v₁→v₂→v₁>v₂→in₁v₁>in₁v₂)  = ≥-pdi {r} {p} {c}  in₁ s-ev₁ in₁ s-ev₁ v₁→v₂→v₁>v₂→in₁v₁>in₁v₂ λ v → inj₂ refl 


-- transitivity
ex≥-trans : ∀ { r p : RE } { c : Char } { pd₁ pd₂ pd₃ : PDInstance r c  }
  { i₁ : Inhabit {r} {c} p pd₁ } 
  { i₂ : Inhabit {r} {c} p pd₂ } 
  { i₃ : Inhabit {r} {c} p pd₃ }
  → r , c ⊢ pd₁ ≥ pd₂
  → r , c ⊢ pd₂ ≥ pd₃
  -------------------
  → r , c ⊢ pd₁ ≥ pd₃
ex≥-trans {r} {p} {c}
          {pdinstance in₁ s-ev₁} {pdinstance in₂ s-ev₂} {pdinstance in₃ s-ev₃}
          {hide .(in₁) .(s-ev₁)}
          {hide .(in₂) .(s-ev₂)}
          {hide .(in₃) .(s-ev₃)}
          (≥-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v→in₁v>in₂v⊎in₁v≡in₂v )
          (≥-pdi .{r} .{p} .{c} .(in₂) .(s-ev₂) .(in₃) .(s-ev₃) v₂→v₃→v₂>v₃→in₂v₂>in₃v₃ v→in₂v>in₃v⊎in₂v≡in₃v ) =
          ≥-pdi {r} {p} {c} in₁ s-ev₁ in₃ s-ev₃ prf₁ prf₂
          where
            prf₂ :  (v : U p) → r ⊢ in₁ v > in₃ v ⊎ in₁ v ≡ in₃ v
            prf₂ v with v→in₁v>in₂v⊎in₁v≡in₂v v  | v→in₂v>in₃v⊎in₂v≡in₃v v 
            ... | inj₁ in₁v>in₂v₁ | inj₁ in₂v₁>in₃v₁ = inj₁ (>-trans in₁v>in₂v₁ in₂v₁>in₃v₁)
            ... | inj₁ in₁v>in₂v₁ | inj₂ in₂v₁≡in₃v₁ rewrite sym in₂v₁≡in₃v₁ = inj₁ in₁v>in₂v₁
            ... | inj₂ in₁v≡in₂v₁ | inj₂ in₂v₁≡in₃v₁ rewrite sym in₂v₁≡in₃v₁ = inj₂ in₁v≡in₂v₁
            ... | inj₂ in₁v≡in₂v₁ | inj₁ in₂v₁>in₃v₁ rewrite in₁v≡in₂v₁ = inj₁ in₂v₁>in₃v₁ 
            prf₁ : (v₁ v₃ : U p) → p ⊢ v₁ > v₃ → r ⊢ in₁ v₁ > in₃ v₃
            prf₁ v₁ v₃ v₁>v₃ with v→in₁v>in₂v⊎in₁v≡in₂v v₁
            ... | inj₁ in₁v₁>in₂v₁ = >-trans in₁v₁>in₂v₁ (v₂→v₃→v₂>v₃→in₂v₂>in₃v₃ v₁ v₃ v₁>v₃)
            ... | inj₂ in₁v₁≡in₂v₁ rewrite  in₁v₁≡in₂v₁ = v₂→v₃→v₂>v₃→in₂v₂>in₃v₃ v₁ v₃ v₁>v₃ 

ex≥-trans-map : ∀ { r p : RE } { c : Char } { pd₁ pd₂ : PDInstance r c }
  { pds₃ : List (PDInstance r c) }
  { i₁ : Inhabit {r} {c} p pd₁ } 
  { i₂ : Inhabit {r} {c} p pd₂ } 
  { is₃ : All (Inhabit {r} {c} p) pds₃ }
  → r , c ⊢ pd₁ ≥ pd₂
  → All (_,_⊢_≥_ r c pd₂)  pds₃
  ---------------------------------------
  → All (_,_⊢_≥_ r c pd₁)  pds₃
ex≥-trans-map pd₁≥pd₂ [] = []
ex≥-trans-map {r} {p} {c} {pd₁} {pd₂} {pd₃ ∷ pds₃} {i₁} {i₂} {i₃ ∷ is₃} pd₁≥pd₂ (pd₂≥pd₃ ∷ pd₂≥pds₃) = ex≥-trans {r} {p} {c} {pd₁} {pd₂} {pd₃} {i₁} {i₂} {i₃}  pd₁≥pd₂ pd₂≥pd₃ ∷  ex≥-trans-map {r} {p} {c} {pd₁} {pd₂} {pds₃} {i₁} {i₂} {is₃}  pd₁≥pd₂ pd₂≥pds₃ 
  

{-
-- irrefl
ex≥→¬≡ : ∀ { r p : RE } { c : Char } { pd₁ pd₂ : PDInstance r c  }
  { i₁ : Inhabit {r} {c} p pd₁ } 
  { i₂ : Inhabit {r} {c} p pd₂ }
  → r , c ⊢ pd₁ ≥ pd₂
  --------------------------
  → ¬ pd₁ ≡ pd₂
ex≥→¬≡ {r} {p} {c}
       {pdinstance in₁ s-ev₁} {pdinstance in₂ s-ev₂} 
       {hide .(in₁) .(s-ev₁)}
       {hide .(in₂) .(s-ev₂)}
       (≥-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v→in₁v>in₂⊎in₁v≡in₂v ) pd₁≡pd₂ rewrite pd₁≡pd₂ = {!!}  -- can't get a contradiction
-} 
-- if irrefl does not hold 
-- maybe > is ≥ ?


{-
-- stuck we can't get s-ev₁ ≡ s-sev₂ 
open import Axiom.Extensionality.Propositional using ( Extensionality ; ∀-extensionality ) 
open import Level using (0ℓ)
-- antisymmetry -- seems hard too., we need extensionality?

-- Postulate it at the level you need:
postulate
  ext : Extensionality 0ℓ 0ℓ
  
in-≡→pd-≡ : ∀ { r p : RE } { c : Char } 
  { in₁ in₂ : U p → U r }
  { s-ev₁ : ( u : U p ) → ( proj₁ ( flat {r} (in₁ u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) }  -- soundness evidence for in₁
  { s-ev₂ : ( u : U p ) → ( proj₁ ( flat {r} (in₂ u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) }  -- soundness evidence for in₂
  → ( ∀ ( u : U p )  → in₁ u ≡ in₂ u )
  ----------------------------------------------
  → pdinstance {p} {r} {c} in₁ s-ev₁ ≡ pdinstance {p} {r} {c} in₂ s-ev₂
-- in-≡→pd-≡ {r} {p} {c} {in₁} {in₂} {s-ev₁} {s-ev₂} u→in₁u≡in₂u = 
in-≡→pd-≡ {$ c ` loc} {ε} {c'}  {in₁} {in₂} {s-ev₁} {s-ev₂} u→in₁u≡in₂u with c Char.≟ c'
... | yes c≡c' rewrite c≡c' =
      begin
        pdinstance in₁ s-ev₁
      ≡⟨ cong (λ x → (pdinstance x s-ev₁) ) in₁≡in₂ ⟩
        pdinstance in₂ s-ev₁
      ≡⟨⟩ 
        pdinstance in₂ s-ev₂        
      ∎
      where
        in₁≡in₂ : in₁ ≡ in₂
        in₁≡in₂ =  ext u→in₁u≡in₂u
        s-ev₁≡s-ev₂ : ∀ ( u : U ε ) → ( in₁ u ≡ in₂ u )  →  ( s-ev₁ u ≡ s-ev₂ u )
        s-ev₁≡s-ev₂ =  ? 
... | no ¬c≡c' = {!!} 
--}   
    
-- a weaker anti-symetricity
ex≥-anti' : ∀ { r p : RE } { c : Char } { in₁ in₂ : U p → U r }
  { s-ev₁ : ( u : U p ) → ( proj₁ ( flat {r} (in₁ u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) }  -- soundness evidence for in₁
  { s-ev₂ : ( u : U p ) → ( proj₁ ( flat {r} (in₂ u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) }  -- soundness evidence for in₂
  → r , c ⊢ pdinstance in₁ s-ev₁ ≥ pdinstance in₂ s-ev₂ 
  → r , c ⊢ pdinstance in₂ s-ev₂ ≥ pdinstance in₁ s-ev₁
  -------------------------------------------------------
  → ( u : U p ) → in₁ u ≡ in₂ u
ex≥-anti'  {r} {p} {c} {in₁} {in₂}  { s-ev₁ } { s-ev₂ }
           (≥-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v→in₁v>in₂v⊎in₁v≡in₂v )
           (≥-pdi .{r} .{p} .{c} .(in₂) .(s-ev₂) .(in₁) .(s-ev₁) v₁→v₂→v₁>v₂→in₂v₁>in₁v₂ v→in₂v>in₁v⊎in₂v≡in₁v ) v
           with v→in₁v>in₂v⊎in₁v≡in₂v v |  v→in₂v>in₁v⊎in₂v≡in₁v v
... | inj₁ in₁v>in₂v | inj₁ in₂v>in₁v = Nullary.contradiction in₂v>in₁v ( PosixOrder.>-asym in₁v>in₂v ) 
... | inj₁ in₁v>in₂v | inj₂ in₂v≡in₁v = Nullary.contradiction (sym in₂v≡in₁v) (PosixOrder.>→¬≡ in₁v>in₂v)
... | inj₂ in₁v≡in₂v | inj₁ in₂v>in₁v = Nullary.contradiction (sym in₁v≡in₂v) (PosixOrder.>→¬≡ in₂v>in₁v)
... | inj₂ in₁v≡in₂v | inj₂ in₂v≡in₁v = in₁v≡in₂v 



-- orginal attempt:  this requires extensionality!!??
-- do we need this? maybe the ex≥-anti' is sufficient?
-- this requires in-≡→pd-≡ ; which is hard to be proven.
{-
ex≥-anti : ∀ { r p : RE } { c : Char } { pd₁ pd₂ : PDInstance r c  }
  { i₁ : Inhabit {r} {c} p pd₁ } 
  { i₂ : Inhabit {r} {c} p pd₂ }
  → r , c ⊢ pd₁ ≥ pd₂
  → r , c ⊢ pd₂ ≥ pd₁
  -----------------------------------
  → pd₁ ≡ pd₂ 
ex≥-anti  {r} {p} {c}
       {pdinstance in₁ s-ev₁} {pdinstance in₂ s-ev₂} 
       {hide .(in₁) .(s-ev₁)}
       {hide .(in₂) .(s-ev₂)}
       (≥-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v→in₁v>in₂⊎in₁v≡in₂v )
       (≥-pdi .{r} .{p} .{c} .(in₂) .(s-ev₂) .(in₁) .(s-ev₁) v₁→v₂→v₁>v₂→in₂v₁>in₁v₂ v→in₂v>in₁⊎in₂v≡in₁v ) = prf         
         where
           ev : (u : U p) →  in₁ u ≡ in₂ u
           ev = ex≥-anti' {r} {p} {c} {in₁} {in₂} {s-ev₁} {s-ev₂}
                  (≥-pdi in₁ s-ev₁ in₂ s-ev₂ v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v→in₁v>in₂⊎in₁v≡in₂v )
                  (≥-pdi in₂ s-ev₂ in₁ s-ev₁ v₁→v₂→v₁>v₂→in₂v₁>in₁v₂ v→in₂v>in₁⊎in₂v≡in₁v )
       --           in₁≡in₂ : in₁ ≡ in₂
       --           in₁≡in₂ = {!!}
           
           
           prf : pdinstance in₁ s-ev₁ ≡ pdinstance in₂ s-ev₂
           prf = in-≡→pd-≡ ev 
-} 


  
  
  

-- though we conjecture that it is a complete lattice, we only show that the left-most element is the join of the rest.
{- if we were to show it as a lattice, we need to remember the join and meet pair wise
   e.g. a <- b is a lattice (list), x <- y is a lattice (list)
        we know a <- x, we should also know b <- y
     a 
     ^^ 
     | \
     b  x  
     ^  ^
      \ | 
        y
   this can be generalized. For example, to combine lattice a b x y with lattice a' b' x' y'

                a
              / | \ 
             a' b  x
            | ×   × | 
            b'  x'  y 
             \  |  /
                y' 
-}
data Ex≥-lattice : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) ) → Set where
  ex-empty : ∀ { r : RE } { c : Char } → Ex≥-lattice {r} {c} []
  -- we don't need singleton 
  -- ex-singleton : ∀ { r : RE } { c : Char } → ( pdi : PDInstance r  c ) → Ex≥-lattice {r} {c} ( pdi  ∷ [])
  ex-join : ∀ { r : RE } { c : Char }
    → ( top : PDInstance r c )
    → ( pdis : List (PDInstance r c ) )
    →  All ( λ x → r , c ⊢ top ≥ x ) pdis   -- top is the join
    -----------------------------------------
    → Ex≥-lattice {r} {c} (top ∷ pdis )
    -- → ( bot : PDInstance r c ) -- don't care about meet for now
    -- → ( Ex≥-semilattice {r} {c} pdis ) -- no we don't have this.
    -- to make the data inductive, we need to define two kinds of lattice combination above
    -- 1) linear-sum == append  (two sub lists can be of diffrent lengths, but in our case, the should be same.)
    --   for linear sum == the first sub lattice's meet ≥ the 2nd sub lattice's join.
    --  when do we need linearly sum?
    -- 2) prod == oplus  (two sub lists must have the same length.)
    -- →  All ( λ x → r , c ⊢ top ≥ x ) (top ∷ pdis ∷ʳ bot)  -- top is the join
    -- →  All ( λ x → r , c ⊢ x ≥ bot ) (top ∷ pdis ∷ʳ bot)  -- bot is the meet
    -----------------------------------------
    -- → Ex≥-lattice {r} {c} (top ∷ pdis ∷ʳ bot)

map-left-all-ex-≥ : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ( pdis : List (PDInstance l c ) )
  → All ( λ x → l , c ⊢ pdi ≥ x ) pdis
  --------------------------------------
  → All ( λ x → (l + r ` loc) , c ⊢ pdinstance-left {l} {r} {loc} pdi ≥ x ) (List.map pdinstance-left pdis)
map-left-all-ex-≥ pdi [] [] = []
map-left-all-ex-≥ pdi (p ∷ ps) (pdi≥p ∷ all-pdi≥ps) = left-ex-sorted pdi p pdi≥p ∷ (map-left-all-ex-≥ pdi ps all-pdi≥ps)

map-left-ex-lattice : ∀ { l r : RE }  { loc : ℕ } { c : Char } 
  → ( pdis : List (PDInstance l c ) )
  → Ex≥-lattice {l} {c} pdis
  → Ex≥-lattice {l + r ` loc } {c} (List.map pdinstance-left pdis)
map-left-ex-lattice {l} {r} {loc} {c} []                  ex-empty = ex-empty
map-left-ex-lattice {l} {r} {loc} {c} ( pdi ∷ pdis ) (ex-join {l} {c} .(pdi) .(pdis) all-pdi≥pdis) = ex-join (pdinstance-left pdi) (List.map pdinstance-left pdis) (map-left-all-ex-≥ pdi pdis all-pdi≥pdis) 

map-right-all-ex-≥ : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance r c )
  → ( pdis : List (PDInstance r c ) )
  → All ( λ x → r , c ⊢ pdi ≥ x ) pdis
  --------------------------------------
  → All ( λ x → (l + r ` loc) , c ⊢ pdinstance-right {l} {r} {loc} pdi ≥ x ) (List.map pdinstance-right pdis)
map-right-all-ex-≥ pdi [] [] = []
map-right-all-ex-≥ pdi (p ∷ ps) (pdi≥p ∷ all-pdi≥ps) = right-ex-sorted pdi p pdi≥p ∷ (map-right-all-ex-≥ pdi ps all-pdi≥ps)


map-right-ex-lattice : ∀ { l r : RE }  { loc : ℕ } { c : Char } 
  → ( pdis : List (PDInstance r c ) )
  → Ex≥-lattice {r} {c} pdis
  → Ex≥-lattice {l + r ` loc } {c} (List.map pdinstance-right pdis)
map-right-ex-lattice {l} {r} {loc} {c} []                  ex-empty = ex-empty
map-right-ex-lattice {l} {r} {loc} {c} ( pdi ∷ pdis ) (ex-join {r} {c} .(pdi) .(pdis) all-pdi≥pdis) = ex-join (pdinstance-right pdi) (List.map pdinstance-right pdis)  (map-right-all-ex-≥ pdi pdis all-pdi≥pdis) 


map-fst-ex-lattice : ∀ { l r : RE } { loc : ℕ } { c : Char }
                    → ( pdis : List (PDInstance l c) )
                    → Ex≥-lattice {l} pdis
                    → Ex≥-lattice {l ● r ` loc } (List.map pdinstance-fst pdis)
map-fst-ex-lattice {l} {r} {loc} {c} []          ex-empty                        = ex-empty
map-fst-ex-lattice {l} {r} {loc} {c} (pdi@(pdinstance {p} {l} {c} in₁ s-ev₁) ∷ pdis) (ex-join .(pdi) .(pdis) pdi≥all-pdis ) = ex-join (pdinstance-fst pdi) (List.map pdinstance-fst pdis) (prf pdis pdi≥all-pdis )
  where
    prf : ( qdis : List (PDInstance l c ) )
      → All (_,_⊢_≥_ l c pdi) qdis 
      → All (_,_⊢_≥_ (l ● r ` loc) c (pdinstance-fst pdi))
        (List.map pdinstance-fst qdis)
    prf [] [] = []
    prf (qdi@(pdinstance .{p} .{l} .{c} in₂ s-ev₂) ∷ qdis) (( ≥-pdi  .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v ) ∷ pdi≥all-qdis) =  fst-pdi≥fst-qdi ∷ prf qdis pdi≥all-qdis
      where
        inject₁ : U (p ● r ` loc)  →  U (l ● r  ` loc )
        inject₁ = mkinjFst in₁

        inject₂ : U (p ● r ` loc)  →  U (l ● r  ` loc )
        inject₂ = mkinjFst in₂

        soundEv₁ : ( u :  U (p ● r ` loc) ) →  proj₁ (flat (inject₁ u)) ≡ c ∷ proj₁ (flat u)
        soundEv₁ = mkinjFstSoundEv in₁ s-ev₁ 

        soundEv₂ : ( u :  U (p ● r ` loc) ) →  proj₁ (flat (inject₂ u)) ≡ c ∷ proj₁ (flat u)
        soundEv₂ = mkinjFstSoundEv in₂ s-ev₂

        len-|in₁-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
        len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

        len-|in₂-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
        len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 

        |in₁-u|≡|in₂-u| : (u : U p) →  (proj₁ (flat (in₁ u))) ≡  (proj₁ (flat (in₂ u)))
        |in₁-u|≡|in₂-u| u rewrite (s-ev₁ u) | (s-ev₂ u) = refl 

        len-|inject₁-u|≡len-|u|+1 : (u : U ( p ● r  ` loc )) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject₁-u|≡len-|u|+1 u rewrite (soundEv₁ u) = refl 

        len-|inject₂-u|≡len-|u|+1 : (u : U ( p ● r  ` loc )) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject₂-u|≡len-|u|+1 u rewrite (soundEv₂ u) = refl

        prf₂ :  (v : U (p ● r ` loc)) →
                 (l ● r ` loc) ⊢ inject₁ v > inject₂ v ⊎ inject₁ v ≡ inject₂ v
        prf₂ (PairU v u) with v→in₁v≥in₂v v
        ... | inj₂ in₁v≡in₂v = inj₂ (cong (λ x → PairU {l} {r} {loc} x u) in₁v≡in₂v)
        ... | inj₁ in₁v>in₂v = inj₁ ( len-≡ len-|pair-in₁-v-u|≡len-|pair-in₂-v-u| (seq₁ in₁v>in₂v)  )
          where
            len-|pair-in₁-v-u|≡len-|pair-in₂-v-u| : length (proj₁ (flat (inject₁ (PairU v u)))) ≡ length (proj₁ (flat (inject₂ (PairU v u))))
            len-|pair-in₁-v-u|≡len-|pair-in₂-v-u| rewrite len-|in₁-u|≡len-|u|+1 v | len-|in₂-u|≡len-|u|+1 v |  |in₁-u|≡|in₂-u| v = refl 

        prf₁ : (v₁ v₂ : U (p ● r ` loc)) →
                   (p ● r ` loc) ⊢ v₁ > v₂ → (l ● r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
        prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|inject₁v₁|>len|inject₂v₂|
          where
            len|inject₁v₁|>len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.> length (proj₁ (flat (inject₂ v₂)))
            len|inject₁v₁|>len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
        prf₁ v₁@(PairU u₁ u₁') v₂@(PairU u₂ u₂') (len-≡ len|v₁|≡len|v₂| (seq₁ u₁>u₂)) = len-≡ len-|pair-in₁-u₁-u₁'|≡len-|pair-in₂-u₂-u₂'| (seq₁ (v₁>v₂→in₁v₁>in₂v₂ u₁ u₂ u₁>u₂))  
          where
            len-|pair-in₁-u₁-u₁'|≡len-|pair-in₂-u₂-u₂'| : length (proj₁ (flat (inject₁ (PairU u₁ u₁')))) ≡ length (proj₁ (flat (inject₂ (PairU u₂ u₂'))))
            len-|pair-in₁-u₁-u₁'|≡len-|pair-in₂-u₂-u₂'| rewrite len-|inject₁-u|≡len-|u|+1 v₁ | len-|inject₂-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂|  =  refl
        prf₁ v₁@(PairU u₁ u₁') v₂@(PairU u₂ u₂') (len-≡ len|v₁|≡len|v₂| (seq₂ u₁≡u₂ u₁'>u₂')) = len-≡ len-|pair-in₁-u₁-u₁'|≡len-|pair-in₂-u₂-u₂'| inject₁pair-u₁-u₁'>ⁱinject₂pair-u₂-u₂' 
          where
            len-|pair-in₁-u₁-u₁'|≡len-|pair-in₂-u₂-u₂'| : length (proj₁ (flat (inject₁ (PairU u₁ u₁')))) ≡ length (proj₁ (flat (inject₂ (PairU u₂ u₂'))))
            len-|pair-in₁-u₁-u₁'|≡len-|pair-in₂-u₂-u₂'| rewrite len-|inject₁-u|≡len-|u|+1 v₁ | len-|inject₂-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂|  =  refl
            inject₁pair-u₁-u₁'>ⁱinject₂pair-u₂-u₂' :  (l ● r ` loc) ⊢ inject₁ (PairU u₁ u₁') >ⁱ inject₂ (PairU u₂ u₂')
            inject₁pair-u₁-u₁'>ⁱinject₂pair-u₂-u₂' with v→in₁v≥in₂v u₂
            ... | inj₂ in₁u₂≡in₂u₂ rewrite u₁≡u₂ = seq₂ in₁u₂≡in₂u₂ u₁'>u₂'
            ... | inj₁ in₁u₂>in₂u₂ rewrite u₁≡u₂ = seq₁ in₁u₂>in₂u₂ 
        fst-pdi≥fst-qdi :  (l ● r ` loc) , c ⊢ pdinstance inject₁ soundEv₁  ≥ pdinstance inject₂ soundEv₂ 
        fst-pdi≥fst-qdi = ≥-pdi inject₁ soundEv₁ inject₂ soundEv₂ prf₁ prf₂  


-- concatenation of two ex lub bounded lists of pdis are lub bounded
-- if the lub of the first list exists then it is ≥ than the 2nd list's lub if it exists
concat-ex-lattice : ∀ { r p : RE } { c }
    → ( pdis₁ : List ( PDInstance r c ))
    → ( pdis₂ : List ( PDInstance r c ))
    → Ex≥-lattice { r } { c } pdis₁
    → Ex≥-lattice { r } { c } pdis₂
    → All (Inhabit {r} {c} p) pdis₁
    → All (Inhabit {r} {c} p) pdis₂    
    → Ex≥-maybe₂ {r} {c} (head pdis₁) (head pdis₂)
    -------------------------------------------------------
    → Ex≥-lattice { r } {c } (pdis₁ ++ pdis₂)
concat-ex-lattice []           pdis₂ ex-empty      ex-lattice-pdis₂ _ _ _  =  ex-lattice-pdis₂
concat-ex-lattice pdis₁        []    ex-lattice-pdis₁ ex-empty _ _ _ rewrite (++-identityʳ pdis₁) = ex-lattice-pdis₁
concat-ex-lattice {r} {p} {c} (pdi₁ ∷ pdis₁)  (pdi₂ ∷ pdis₂)  (ex-join .(pdi₁) .(pdis₁) all-pdi₁≥pdis₁ ) (ex-join .(pdi₂) .(pdis₂) all-pdi₂≥pdis₂ ) (i₁ ∷ is₁) (i₂ ∷ is₂) (ex≥-just₂ pdi₁≥pdi₂) 
  = ex-join pdi₁ (pdis₁ ++ pdi₂ ∷ pdis₂)
    (all-concat all-pdi₁≥pdis₁ (pdi₁≥pdi₂ ∷ ex≥-trans-map {r} {p} {c} {pdi₁} {pdi₂} {pdis₂} {i₁} {i₂} {is₂} pdi₁≥pdi₂ all-pdi₂≥pdis₂ ) )  -- we need to apply ex≥-trans to all pdis₂






map-fuse-+-ex-lattice :  ∀ { l r : RE } {loc : ℕ } { c : Char }
  → ( pdi₁ : PDInstance l c )
  → ( pdis₂ : List (PDInstance r c ))
  → Ex≥-lattice { r } {c}  pdis₂
  → >-Inc pdi₁
  → All >-Inc pdis₂ 
  → Homogenous pdis₂
  ------------------------------------------------------------
  → Ex≥-lattice { l + r ` loc } (List.map (fuse {l + r ` loc} {loc} {c} (pdinstance-left pdi₁)) (List.map pdinstance-right pdis₂))
map-fuse-+-ex-lattice {l} {r} {loc} {c}  pdi₁ [] ex-empty _ _ _ = ex-empty 
map-fuse-+-ex-lattice {l} {r} {loc} {c}  pdi₁@(pdinstance {p₁} {l} {c} in₁ s-ev₁) (pdi₂@(pdinstance {p₂} .{r} .{c} in₂ s-ev₂) ∷ [] ) (ex-join .{r} .{c} .(pdi₂) [] [] ) (>-inc v₁→v₂→v₁>v₂→in₁v₁>in₁v₂ ) (>-inc-pdi₂@(>-inc v₁→v₂→v₁>v₂→in₂v₁>in₂v₂) ∷ []) homo-pdi₂∷[] =
  ex-join
    (fuse (pdinstance-left (pdinstance in₁ s-ev₁))
          (pdinstance-right (pdinstance in₂ s-ev₂)))
          (List.map (fuse {l + r ` loc } {loc } (pdinstance-left (pdinstance in₁ s-ev₁)))
            (List.map pdinstance-right [])) []
map-fuse-+-ex-lattice {l} {r} {loc} {c}  pdi₁@(pdinstance {p₁} {l} {c} in₁ s-ev₁)
                                      (pdi₂@(pdinstance {p₂} .{r} .{c} in₂ s-ev₂) ∷ pdi₂' ∷ pdis₂ )
                                      (ex-join .{r} .{c} .(pdi₂) ( .(pdi₂') ∷ .(pdis₂)) (pdi₂>pdi₂' ∷ all-pdi₂>pdis₂) )
                                      (>-inc v₁→v₂→v₁>v₂→in₁v₁>in₁v₂ )
                                      (>-inc-pdi₂@(>-inc v₁→v₂→v₁>v₂→in₂v₁>in₂v₂) ∷ >-inc-pdi₂' ∷ >-inc-pdis₂ )
                                      (homogenous ( .(pdi₂) ∷ .(pdi₂') ∷ .(pdis₂) ) ( .(p₂) , (hide .{p₂} .{r} .{c} in₂ s-ev₂) ∷ hide-p₂-pdi₂' ∷ hide-p₂-pdis₂) )  =
  ex-join
    (fuse (pdinstance-left (pdinstance in₁ s-ev₁))
          (pdinstance-right (pdinstance in₂ s-ev₂)))
          (List.map (fuse (pdinstance-left (pdinstance in₁ s-ev₁))) (List.map pdinstance-right (pdi₂' ∷ pdis₂))) (prf (pdi₂' ∷ pdis₂)
                                                                                                                      (hide-p₂-pdi₂' ∷ hide-p₂-pdis₂) (>-inc-pdi₂' ∷ >-inc-pdis₂)  (pdi₂>pdi₂' ∷ all-pdi₂>pdis₂) )
  where
    prf : ( qdis : List ( PDInstance r c ) )
         → All (Inhabit {r} {c} p₂) qdis
         → All >-Inc qdis 
         → All (λ qdi → r , c ⊢ (pdinstance in₂ s-ev₂) ≥ qdi ) qdis
         → All (λ qdi → ( l + r ` loc ) , c ⊢ (fuse {l + r ` loc } {loc} (pdinstance-left (pdinstance in₁ s-ev₁))
                                                                         (pdinstance-right (pdinstance in₂ s-ev₂))) ≥ qdi )
              (List.map (fuse { l + r ` loc } {loc}  (pdinstance-left (pdinstance in₁ s-ev₁)))
                                                      (List.map pdinstance-right qdis))
    prf [] [] [] [] = []
    prf ( qdi@(pdinstance in₂' s-ev₂') ∷ qdis)  ((hide {p₂} .{r} .{c} .(in₂') .(s-ev₂')) ∷ hide-p₂-qdis)
        ( (>-inc v₁→v₂→v₁>v₂→in₂'v₁>in₂'v₂)  ∷ >-inc-qdis )
        ( (≥-pdi .(in₂) .(s-ev₂) .(in₂') .(s-ev₂') v₁→v₂→v₁>v₂→in₂v₁>in₂'v₂ v→in₂v≥in₂'v ) ∷ all-pdi₂≥qdis) =  sub ∷ prf qdis hide-p₂-qdis >-inc-qdis  all-pdi₂≥qdis 
      where
      sub : (l + r ` loc) , c ⊢
        fuse {l + r ` loc}  {loc} {c} (pdinstance-left (pdinstance in₁ s-ev₁)) (pdinstance-right (pdinstance in₂ s-ev₂))  ≥
        fuse {l + r ` loc}  {loc} {c} (pdinstance-left (pdinstance in₁ s-ev₁)) (pdinstance-right (pdinstance in₂' s-ev₂'))
      sub = (≥-pdi inject₁ sound-ev₁ inject₂ sound-ev₂ prf₁ prf₂)
        where 
          inject₁ : U (p₁ + p₂ ` loc) → U ( l + r  ` loc )
          inject₁ = mkfuseInj (LeftU ∘ in₁) (RightU ∘ in₂)
          inject₂ : U (p₁ + p₂ ` loc) → U ( l + r  ` loc )
          inject₂ = mkfuseInj (LeftU ∘ in₁) (RightU ∘ in₂')

          sound-ev₁ : ( u :  U (p₁ + p₂ ` loc) )  → proj₁ (flat (inject₁ u)) ≡ c ∷ proj₁ (flat u )
          sound-ev₁ = mkfuseInjSoundEv {p₁} {p₂} {l + r ` loc} {loc} {c}  (LeftU ∘ in₁) (RightU ∘ in₂) s-ev₁ s-ev₂ 
          sound-ev₂ : ( u :  U (p₁ + p₂ ` loc) )  → proj₁ (flat (inject₂ u)) ≡ c ∷ proj₁ (flat u )
          sound-ev₂ = mkfuseInjSoundEv {p₁} {p₂} {l + r ` loc} {loc} {c}  (LeftU ∘ in₁) (RightU ∘ in₂') s-ev₁ s-ev₂'

          len-|in₁-u|≡len-|u|+1 : ( u : U p₁ ) →  length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
          len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

          len-|in₂-u|≡len-|u|+1 : ( u : U p₂ ) →  length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
          len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 

          len-|in₂'-u|≡len-|u|+1 : ( u : U p₂ ) →  length (proj₁ (flat (in₂' u))) ≡ suc (length (proj₁ (flat u)))
          len-|in₂'-u|≡len-|u|+1 u rewrite (s-ev₂' u) = refl 


          len-|inject₁-u|≡len-|u|+1 : (u : U (p₁ + p₂ ` loc) ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
          len-|inject₁-u|≡len-|u|+1 u rewrite (sound-ev₁ u) = refl 
    
          len-|inject₂-u|≡len-|u|+1 : (u : U (p₁ + p₂ ` loc) ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
          len-|inject₂-u|≡len-|u|+1 u rewrite (sound-ev₂ u) = refl


          prf₂ : (v : U (p₁ + p₂ ` loc))
            →  (l + r ` loc) ⊢ inject₁ v > inject₂ v ⊎ inject₁ v ≡ inject₂ v
          prf₂ v@(RightU u) with v→in₂v≥in₂'v u
          ... | inj₁ (len-≡ len|in₂u|≡len|in₂'u| in₂u>ⁱin₂'u) = inj₁ (len-≡ len|in₂u|≡len|in₂'u| (choice-rr (len-≡ len|in₂u|≡len|in₂'u| in₂u>ⁱin₂'u))) 
          ... | inj₁ (len-> len|in₂u|>len|in₂'u|) =  Nullary.contradiction len|in₂u|>len|in₂'u| (<-irrefl (sym len|in₂u|≡len|in₂'u|)) 
                                                   --  inj₁ (len-> len|inju|>len|inj'u|) this also works but why? maybe it is an eventual contradiction? 
              where
                len|in₂u|≡len|in₂'u| : length (proj₁ (flat (in₂ u))) ≡ length (proj₁ (flat (in₂' u)))
                len|in₂u|≡len|in₂'u| rewrite len-|in₂-u|≡len-|u|+1 u |  len-|in₂'-u|≡len-|u|+1 u = refl                     
          ... | inj₂ inju≡in₂'u = inj₂ (cong RightU inju≡in₂'u ) 
          prf₂ v@(LeftU u) = inj₂ refl 


          prf₁ : (v₁ v₂ : U (p₁ + p₂ ` loc))
            → (p₁ + p₂ ` loc) ⊢ v₁ > v₂
            → (l + r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
          prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|inject₁v₁|>len|inject₂v₂|
            where
              len|inject₁v₁|>len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.> length (proj₁ (flat (inject₂ v₂)))
              len|inject₁v₁|>len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
          prf₁ v₁@(LeftU u₁) v₂@(LeftU u₂) (len-≡ len|v₁|≡len|v₂| (choice-ll u₁>u₂)) = len-≡ len|inject₁v₁|≡len|inject₂v₂| inject₁leftu₁>inject₂leftu₂
            where 
              len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) ≡ length (proj₁ (flat (inject₂ v₂)))
              len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
              inject₁leftu₁≡leftin₁u₁ : inject₁ (LeftU u₁) ≡ LeftU (in₁ u₁)
              inject₁leftu₁≡leftin₁u₁ = refl 
              inject₂leftu₂≡leftin₁u₂ : inject₂ (LeftU u₂) ≡ LeftU (in₁ u₂)
              inject₂leftu₂≡leftin₁u₂ = refl 
              inject₁leftu₁>inject₂leftu₂ : l + r ` loc  ⊢ inject₁ (LeftU u₁) >ⁱ inject₂ (LeftU u₂)
              inject₁leftu₁>inject₂leftu₂ rewrite inject₁leftu₁≡leftin₁u₁ | inject₂leftu₂≡leftin₁u₂  = choice-ll  (v₁→v₂→v₁>v₂→in₁v₁>in₁v₂ u₁ u₂ u₁>u₂)  
        

          prf₁ v₁@(RightU u₁) v₂@(RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rr u₁>u₂)) = len-≡ len|inject₁v₁|≡len|inject₂v₂| inject₁rightu₁>inject₂rightu₂
            where 
              len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) ≡ length (proj₁ (flat (inject₂ v₂)))
              len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
            
              inject₁rightu₁≡rightinju₁ : inject₁ (RightU u₁) ≡ RightU (in₂ u₁)
              inject₁rightu₁≡rightinju₁ = refl 
              inject₂rightu₂≡rightinj'u₂ : inject₂ (RightU u₂) ≡ RightU (in₂' u₂)
              inject₂rightu₂≡rightinj'u₂ = refl 
              inject₁rightu₁>inject₂rightu₂ : l + r ` loc  ⊢ inject₁ (RightU u₁) >ⁱ inject₂ (RightU u₂)
              inject₁rightu₁>inject₂rightu₂ rewrite inject₁rightu₁≡rightinju₁ | inject₂rightu₂≡rightinj'u₂  = choice-rr  (v₁→v₂→v₁>v₂→in₂v₁>in₂'v₂ u₁ u₂ u₁>u₂) 


          prf₁ v₁@(LeftU u₁) v₂@(RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|u₁|≥|len|u₂|)) =  inject₁left-u₁>inject₂right-u₂
            -- from prf₂ we have inject₁ (LeftU u₁) ≥ inject₂ (LeftU u₁)

            -- from >-inc pdi₂, we have inject₂ (LeftU u₁) > inject₂ (RightU u₂), because p₁ + p₂  ⊢  (LeftU u₁) >  (RightU u₂)
            -- from transitivity inject₁ (LeftU u₁) > inject₂ (RightU u₂)
            where
              len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) ≡ length (proj₁ (flat (inject₂ v₂)))
              len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
              inject₁left-u₁≥inject₂left-u₁ : l + r ` loc   ⊢ inject₁ (LeftU u₁) > inject₂ (LeftU u₁) ⊎ inject₁ (LeftU u₁) ≡ inject₂ (LeftU u₁)
              inject₁left-u₁≥inject₂left-u₁ = prf₂ (LeftU u₁)
              >-inc-fuse-in₁-in₂' : >-Inc (pdinstance {p₁ + p₂ ` loc} {l + r ` loc } {c} inject₂ sound-ev₂)
              >-inc-fuse-in₁-in₂' = 
                PosixOrder.>-inc-fuse-left-right pdi₁ qdi (PosixOrder.>-inc-left {l} {r} {loc} {c} (pdinstance in₁ s-ev₁) (>-inc v₁→v₂→v₁>v₂→in₁v₁>in₁v₂)) (PosixOrder.>-inc-right {l} {r} {loc} {c} (pdinstance in₂' s-ev₂') (>-inc v₁→v₂→v₁>v₂→in₂'v₁>in₂'v₂) ) 
              inject₂left-u₁>inject₂right-u₂ : l + r ` loc  ⊢ inject₂ (LeftU u₁) > inject₂ (RightU u₂)
              inject₂left-u₁>inject₂right-u₂ with >-inc-fuse-in₁-in₂'
              ... | >-inc v₁→v₂→v₁>v₂→inject₂v₁>inject₂v₂  = v₁→v₂→v₁>v₂→inject₂v₁>inject₂v₂ (LeftU u₁) (RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|u₁|≥|len|u₂|)) 
              inject₁left-u₁>inject₂right-u₂ : l + r ` loc  ⊢ inject₁ (LeftU u₁) > inject₂ (RightU u₂)
              inject₁left-u₁>inject₂right-u₂ with  inject₁left-u₁≥inject₂left-u₁
              ... | inj₂ inject₁-left-u₁≡inject₂left-u₁ rewrite inject₁-left-u₁≡inject₂left-u₁ =  inject₂left-u₁>inject₂right-u₂
              ... | inj₁ inject₁-left-u₁>inject₂left-u₁ = >-trans inject₁-left-u₁>inject₂left-u₁ inject₂left-u₁>inject₂right-u₂

          prf₁ v₁@(RightU u₁) v₂@(LeftU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rl len|u₁|>|len|u₂|)) = Nullary.contradiction len|u₁|>|len|u₂| (<-irrefl (sym len|v₁|≡len|v₂| ) )


oplus-+-ex-lattice : ∀ { l r : RE } {loc : ℕ } { c : Char }
    → ( pdis₁ : List ( PDInstance l c ))
    → ( pdis₂ : List ( PDInstance r c ))
    → Ex≥-lattice { l } {c} pdis₁
    → Ex≥-lattice { r } {c} pdis₂
    → All >-Inc pdis₁
    → All >-Inc pdis₂
    → Homogenous pdis₁
    → Homogenous pdis₂
    ---------------------------------------
    → Ex≥-lattice  { l + r ` loc } (pdinstance-oplus {l + r ` loc } {loc} {c}  (List.map pdinstance-left pdis₁) (List.map pdinstance-right pdis₂))
oplus-+-ex-lattice {l} {r} {loc} {c} [] pdis₂ ex-empty ex-lattice [] all->-inc-pdis₂ homo-pdis₁ homo-pdis₂ = map-right-ex-lattice pdis₂ ex-lattice 
oplus-+-ex-lattice {l} {r} {loc} {c} (pdi₁ ∷ pdis₁) [] ex-lattice ex-empty all->-inc-pdi₁pdis₁ [] homo-pdis₁ homo-pdis₂ = map-left-ex-lattice (pdi₁ ∷ pdis₁) ex-lattice

oplus-+-ex-lattice {l} {r} {loc} {c} (pdi₁@(pdinstance {p₁} .{l} {c} in₁ s-ev₁) ∷ pdis₁) (pdi₂@(pdinstance {p₂} .{r} .{c} in₂ s-ev₂) ∷ pdis₂)
                                                           (ex-join .(pdi₁) .(pdis₁) pdi₁≥pdis₁)
                                                           (ex-join .(pdi₂) .(pdis₂) pdi₂≥pdis₂)                                                            
                                                           (>-inc-pdi₁@(>-inc  v₁→v₂→v₁>v₂→in₁v₁>in₁v₂)  ∷ >-inc-pdis₁ )
                                                           (>-inc-pdi₂@(>-inc  v₁→v₂→v₁>v₂→in₂v₁>in₂v₂) ∷ >-inc-pdis₂ )
                                                           (homogenous {l} {c} (.(pdi₁) ∷ .(pdis₁)) ( .(p₁) , (hide-p₁-pdi₁@(hide .{p₁} .{l} .{c} .(in₁) .(s-ev₁))  ∷ hide-p₁-pdis₁)) )
                                                           (homogenous {r} {c} (.(pdi₂) ∷ .(pdis₂)) ( .(p₂) , (hide-p₂-pdi₂@(hide .{p₂} .{r} .{c} .(in₂) .(s-ev₂))  ∷ hide-p₂-pdis₂)) )
                                         = ex-join (fuse (pdinstance-left pdi₁) (pdinstance-right pdi₂))
                                                         (List.map (fuse (pdinstance-left pdi₁))
                                                                   (List.map pdinstance-right pdis₂)
                                                          ++
                                                            (concatMap
                                                              (λ pdiˡ₁ →
                                                                 List.map (fuse pdiˡ₁)
                                                                   (List.map pdinstance-right (pdi₂ ∷ pdis₂)))
                                                                    (List.map pdinstance-left pdis₁))
                                                                    )
                                                                    (all-concat (sub₁ pdis₂ >-inc-pdis₂ pdi₂≥pdis₂ ) ( sub₂ pdis₁ >-inc-pdis₁ pdi₁≥pdis₁ )  )  
  where
    sub₁ : ( qdis : (List (PDInstance r c ) ) )
      → All >-Inc qdis 
      → All (_,_⊢_≥_ r c pdi₂) qdis
      → All  (_,_⊢_≥_ (l + r ` loc) c  (fuse { l + r ` loc} {loc}  (pdinstance-left pdi₁) (pdinstance-right pdi₂))) 
             (List.map (fuse { l + r ` loc} {loc}  (pdinstance-left pdi₁)) (List.map pdinstance-right qdis))
    sub₁ [] [] [] = []
    sub₁ (qdi@(pdinstance in₂' s-ev₂') ∷ qdis) ((>-inc v₁→v₂→v₁>v₂→in₂'v₁>in₂'v₂ )  ∷ all->-inc-qdis ) (  (≥-pdi .{r} .{p₂} .{c} .(in₂) .(s-ev₂) .(in₂') .(s-ev₂') v₁→v₂→v₁>v₂→in₂v₁>in₂'v₂ v→in₂v≥in₂'v )  ∷ pdi₂≥qdis ) =
       fuse-left-pdi₁-right-pdi₂≥fuse-left-pdi₁-right-q ∷ sub₁  qdis all->-inc-qdis pdi₂≥qdis  
      where
        inject : U (p₁ + p₂ ` loc ) → U (l + r ` loc)
        inject = mkfuseInj (LeftU ∘ in₁) (RightU ∘ in₂)
        soundEv : ( u : U (p₁ + p₂ ` loc ) ) → proj₁ (flat (inject u)) ≡ c ∷ (proj₁ (flat u ))
        soundEv = mkfuseInjSoundEv {p₁}  {p₂} {l + r ` loc} {loc} {c}  (LeftU ∘ in₁) (RightU ∘ in₂) s-ev₁ s-ev₂
        inject' : U (p₁ + p₂ ` loc ) → U (l + r ` loc)
        inject' = mkfuseInj (LeftU ∘ in₁) (RightU ∘ in₂')
        soundEv' : ( u : U (p₁ + p₂ ` loc ) ) → proj₁ (flat (inject' u)) ≡ c ∷ (proj₁ (flat u ))
        soundEv' = mkfuseInjSoundEv {p₁}  {p₂} {l + r ` loc} {loc} {c}  (LeftU ∘ in₁) (RightU ∘ in₂') s-ev₁ s-ev₂'

        len-|in₁-u|≡len-|u|+1 : (u : U p₁) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
        len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

        len-|in₂-u|≡len-|u|+1 : (u : U p₂) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
        len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 

        len-|in₂'-u|≡len-|u|+1 : (u : U p₂) → length (proj₁ (flat (in₂' u))) ≡ suc (length (proj₁ (flat u)))
        len-|in₂'-u|≡len-|u|+1 u rewrite (s-ev₂' u) = refl


        len-|inject-u|≡len-|u|+1 : (u : U ( p₁ + p₂ ` loc )) → length (proj₁ (flat (inject u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject-u|≡len-|u|+1 u rewrite (soundEv u) = refl 

        len-|inject'-u|≡len-|u|+1 : (u : U ( p₁ + p₂ ` loc )) → length (proj₁ (flat (inject' u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject'-u|≡len-|u|+1 u rewrite (soundEv' u) = refl 

        prf₂ : (v : U (p₁ + p₂ ` loc)) →
                    (l + r ` loc) ⊢ inject v > inject' v ⊎ inject v ≡ inject' v
        prf₂ (LeftU {p₁} {p₂} {loc} u) = inj₂ refl
        prf₂ (RightU {p₁} {p₂} {loc} u) with  v→in₂v≥in₂'v u
        ... | inj₂ in₂u≡in₂'u = inj₂ (cong RightU in₂u≡in₂'u ) 
        ... | inj₁ in₂u>in₂'u = inj₁ (len-≡ len-|right-in₂-u|≡len-|right-in₂'-u| (choice-rr in₂u>in₂'u) )
          where
            len-|right-in₂-u|≡len-|right-in₂'-u| : length (proj₁ (flat ((RightU {l} {r} {loc} ∘ in₂) u))) ≡ 
                                               length (proj₁ (flat ((RightU {l} {r} {loc} ∘ in₂') u)))
            len-|right-in₂-u|≡len-|right-in₂'-u| rewrite len-|in₂-u|≡len-|u|+1 u | len-|in₂'-u|≡len-|u|+1 u = refl 
        prf₁ : (v₁ v₂ : U (p₁ + p₂ ` loc)) →
               (p₁ + p₂ ` loc) ⊢ v₁ > v₂ → (l + r ` loc) ⊢ inject v₁ > inject' v₂
        prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|injectv₁|>len|inject'v₂|
          where
            len|injectv₁|>len|inject'v₂| : length (proj₁ (flat (inject v₁))) Nat.> length (proj₁ (flat (inject' v₂)))
            len|injectv₁|>len|inject'v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject'-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
        prf₁ v₁@(LeftU u₁) v₂@(LeftU u₂) (len-≡ len|v₁|≡len|v₂| (choice-ll u₁>u₂)) = len-≡ len|injectv₁|≡len|inject'v₂| injectleftu₁>inject'leftu₂
          where 
            len|injectv₁|≡len|inject'v₂| : length (proj₁ (flat (inject v₁))) ≡ length (proj₁ (flat (inject' v₂)))
            len|injectv₁|≡len|inject'v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject'-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
            injectleftu₁≡leftin₁u₁ : inject (LeftU u₁) ≡ LeftU (in₁ u₁)
            injectleftu₁≡leftin₁u₁ = refl 
            inject'leftu₂≡leftin₁u₂ : inject' (LeftU u₂) ≡ LeftU (in₁ u₂)
            inject'leftu₂≡leftin₁u₂ = refl 
            injectleftu₁>inject'leftu₂ : l + r ` loc  ⊢ inject (LeftU u₁) >ⁱ inject' (LeftU u₂)
            injectleftu₁>inject'leftu₂ rewrite injectleftu₁≡leftin₁u₁ | inject'leftu₂≡leftin₁u₂  = choice-ll  (v₁→v₂→v₁>v₂→in₁v₁>in₁v₂ u₁ u₂ u₁>u₂)  
        

        prf₁ v₁@(RightU u₁) v₂@(RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rr u₁>u₂)) = len-≡ len|injectv₁|≡len|inject'v₂| injectrightu₁>inject'rightu₂
          where 
            len|injectv₁|≡len|inject'v₂| : length (proj₁ (flat (inject v₁))) ≡ length (proj₁ (flat (inject' v₂)))
            len|injectv₁|≡len|inject'v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject'-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
            
            injectrightu₁≡rightin₂u₁ : inject (RightU u₁) ≡ RightU (in₂ u₁)
            injectrightu₁≡rightin₂u₁ = refl 
            inject'rightu₂≡rightin₂'u₂ : inject' (RightU u₂) ≡ RightU (in₂' u₂)
            inject'rightu₂≡rightin₂'u₂ = refl 
            injectrightu₁>inject'rightu₂ : l + r ` loc  ⊢ inject (RightU u₁) >ⁱ inject' (RightU u₂)
            injectrightu₁>inject'rightu₂ rewrite injectrightu₁≡rightin₂u₁ | inject'rightu₂≡rightin₂'u₂  = choice-rr  (v₁→v₂→v₁>v₂→in₂v₁>in₂'v₂ u₁ u₂ u₁>u₂) 

        prf₁ v₁@(LeftU u₁) v₂@(RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|u₁|≥|len|u₂|)) =  injectleft-u₁>inject'right-u₂
          -- from prf₂ we have inject₁ (LeftU u₁) ≥ inject₂ (LeftU u₁)

          -- from >-inc qdi, we have inject₂ (LeftU u₁) > inject₂ (RightU u₂), because p₁ + p₂  ⊢  (LeftU u₁) >  (RightU u₂)
          -- from transitivity inject₁ (LeftU u₁) > inject₂ (RightU u₂)
          where
            len|injectv₁|≡len|inject'v₂| : length (proj₁ (flat (inject v₁))) ≡ length (proj₁ (flat (inject' v₂)))
            len|injectv₁|≡len|inject'v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject'-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
            injectleft-u₁≥inject'left-u₁ : l + r ` loc   ⊢ inject (LeftU u₁) > inject' (LeftU u₁) ⊎ inject (LeftU u₁) ≡ inject' (LeftU u₁)
            injectleft-u₁≥inject'left-u₁ = prf₂ (LeftU u₁)
            >-inc-fuse-in₁-in₂' : >-Inc (pdinstance {p₁ + p₂ ` loc} {l + r ` loc } {c} inject' soundEv')
            >-inc-fuse-in₁-in₂' = 
              PosixOrder.>-inc-fuse-left-right pdi₁ qdi (PosixOrder.>-inc-left {l} {r} {loc} {c} (pdinstance in₁ s-ev₁) (>-inc v₁→v₂→v₁>v₂→in₁v₁>in₁v₂)) (PosixOrder.>-inc-right {l} {r} {loc} {c} (pdinstance in₂' s-ev₂') (>-inc v₁→v₂→v₁>v₂→in₂'v₁>in₂'v₂) ) 
            inject'left-u₁>inject'right-u₂ : l + r ` loc  ⊢ inject' (LeftU u₁) > inject' (RightU u₂)
            inject'left-u₁>inject'right-u₂ with >-inc-fuse-in₁-in₂'
            ... | >-inc v₁→v₂→v₁>v₂→inject'v₁>inject'v₂  = v₁→v₂→v₁>v₂→inject'v₁>inject'v₂ (LeftU u₁) (RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|u₁|≥|len|u₂|)) 
            injectleft-u₁>inject'right-u₂ : l + r ` loc  ⊢ inject (LeftU u₁) > inject' (RightU u₂)
            injectleft-u₁>inject'right-u₂ with  injectleft-u₁≥inject'left-u₁
            ... | inj₂ inject-left-u₁≡inject'left-u₁ rewrite inject-left-u₁≡inject'left-u₁ =  inject'left-u₁>inject'right-u₂
            ... | inj₁ inject-left-u₁>inject'left-u₁ = >-trans inject-left-u₁>inject'left-u₁ inject'left-u₁>inject'right-u₂

        prf₁ v₁@(RightU u₁) v₂@(LeftU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rl len|u₁|>|len|u₂|)) = Nullary.contradiction len|u₁|>|len|u₂| (<-irrefl (sym len|v₁|≡len|v₂| ) )

        fuse-left-pdi₁-right-pdi₂≥fuse-left-pdi₁-right-q : (l + r ` loc) , c ⊢  (pdinstance inject soundEv) ≥ (pdinstance inject' soundEv')
        fuse-left-pdi₁-right-pdi₂≥fuse-left-pdi₁-right-q = ≥-pdi inject soundEv inject' soundEv' prf₁ prf₂
    sub₂ :  ( pdis : (List (PDInstance l c ) ) )
      → All >-Inc pdis 
      → All (_,_⊢_≥_ l c pdi₁) pdis
      → All  (_,_⊢_≥_ (l + r ` loc) c  (fuse { l + r ` loc} {loc}  (pdinstance-left pdi₁) (pdinstance-right pdi₂)))
            (concatMap (λ pdiˡ₁ → List.map (fuse { l + r ` loc} {loc}  pdiˡ₁)  (List.map pdinstance-right (pdi₂ ∷ pdis₂))) (List.map pdinstance-left pdis))
    sub₂ [] [] [] = []
    sub₂ (pdi@(pdinstance in₁' s-ev₁') ∷ pdis) ((>-inc v₁→v₂→v₁>v₂→in₁'v₁>in₁'v₂ ) ∷ all->-inc-pdis) (  (≥-pdi .{l} .{p₁} .{c} .(in₁) .(s-ev₁) .(in₁') .(s-ev₁') v₁→v₂→v₁>v₂→in₁v₁>in₁'v₂ v→in₁v≥in₁'v )  ∷ pdi₂≥pdis ) = all-concat ( fuse-left-pdi₁-right-pdi₂≥fuse-left-pdi₁'-right-pdi₂ ∷ (sub₃ pdis₂ >-inc-pdis₂  pdi₂≥pdis₂) )
                          -- (sub₃ (pdi₂ ∷ pdis₂) (>-inc-pdi₂ ∷ >-inc-pdis₂) ({!!} ∷ pdi₂≥pdis₂)  )
                          (sub₂ pdis all->-inc-pdis pdi₂≥pdis)
      where
        inject : U (p₁ + p₂ ` loc ) → U (l + r ` loc)
        inject = mkfuseInj (LeftU ∘ in₁) (RightU ∘ in₂)
        soundEv : ( u : U (p₁ + p₂ ` loc ) ) → proj₁ (flat (inject u)) ≡ c ∷ (proj₁ (flat u ))
        soundEv = mkfuseInjSoundEv {p₁}  {p₂} {l + r ` loc} {loc} {c}  (LeftU ∘ in₁) (RightU ∘ in₂) s-ev₁ s-ev₂
        inject' : U (p₁ + p₂ ` loc ) → U (l + r ` loc)
        inject' = mkfuseInj (LeftU ∘ in₁') (RightU ∘ in₂)
        soundEv' : ( u : U (p₁ + p₂ ` loc ) ) → proj₁ (flat (inject' u)) ≡ c ∷ (proj₁ (flat u ))
        soundEv' = mkfuseInjSoundEv {p₁}  {p₂} {l + r ` loc} {loc} {c}  (LeftU ∘ in₁') (RightU ∘ in₂) s-ev₁' s-ev₂


        len-|in₁-u|≡len-|u|+1 : (u : U p₁) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
        len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

        len-|in₂-u|≡len-|u|+1 : (u : U p₂) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
        len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 

        len-|in₁'-u|≡len-|u|+1 : (u : U p₁) → length (proj₁ (flat (in₁' u))) ≡ suc (length (proj₁ (flat u)))
        len-|in₁'-u|≡len-|u|+1 u rewrite (s-ev₁' u) = refl


        len-|inject-u|≡len-|u|+1 : (u : U ( p₁ + p₂ ` loc )) → length (proj₁ (flat (inject u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject-u|≡len-|u|+1 u rewrite (soundEv u) = refl 

        len-|inject'-u|≡len-|u|+1 : (u : U ( p₁ + p₂ ` loc )) → length (proj₁ (flat (inject' u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject'-u|≡len-|u|+1 u rewrite (soundEv' u) = refl

        prf₂ : (v : U (p₁ + p₂ ` loc)) →
                    (l + r ` loc) ⊢ inject v > inject' v ⊎ inject v ≡ inject' v
        prf₂ (RightU {p₁} {p₂} {loc} u) = inj₂ refl
        prf₂ (LeftU {p₁} {p₂} {loc} u) with  v→in₁v≥in₁'v u
        ... | inj₂ in₁u≡in₁'u = inj₂ (cong LeftU in₁u≡in₁'u ) 
        ... | inj₁ in₁u>in₁'u = inj₁ (len-≡ len-|left-in₁-u|≡len-|left-in₁'-u| (choice-ll in₁u>in₁'u) )
          where
            len-|left-in₁-u|≡len-|left-in₁'-u| : length (proj₁ (flat ((LeftU {l} {r} {loc} ∘ in₁) u))) ≡ 
                                               length (proj₁ (flat ((LeftU {l} {r} {loc} ∘ in₁') u)))
            len-|left-in₁-u|≡len-|left-in₁'-u| rewrite len-|in₁-u|≡len-|u|+1 u | len-|in₁'-u|≡len-|u|+1 u = refl

        prf₁ : (v₁ v₂ : U (p₁ + p₂ ` loc)) →
               (p₁ + p₂ ` loc) ⊢ v₁ > v₂ → (l + r ` loc) ⊢ inject v₁ > inject' v₂
        prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|injectv₁|>len|inject'v₂|
          where
            len|injectv₁|>len|inject'v₂| : length (proj₁ (flat (inject v₁))) Nat.> length (proj₁ (flat (inject' v₂)))
            len|injectv₁|>len|inject'v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject'-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
        prf₁ v₁@(LeftU u₁) v₂@(LeftU u₂) (len-≡ len|v₁|≡len|v₂| (choice-ll u₁>u₂)) = len-≡ len|injectv₁|≡len|inject'v₂| injectleftu₁>inject'leftu₂
          where 
            len|injectv₁|≡len|inject'v₂| : length (proj₁ (flat (inject v₁))) ≡ length (proj₁ (flat (inject' v₂)))
            len|injectv₁|≡len|inject'v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject'-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
            injectleftu₁≡leftin₁u₁ : inject (LeftU u₁) ≡ LeftU (in₁ u₁)
            injectleftu₁≡leftin₁u₁ = refl 
            inject'leftu₂≡leftin₁'u₂ : inject' (LeftU u₂) ≡ LeftU (in₁' u₂)
            inject'leftu₂≡leftin₁'u₂ = refl 
            injectleftu₁>inject'leftu₂ : l + r ` loc  ⊢ inject (LeftU u₁) >ⁱ inject' (LeftU u₂)
            injectleftu₁>inject'leftu₂ rewrite injectleftu₁≡leftin₁u₁ | inject'leftu₂≡leftin₁'u₂  = choice-ll  (v₁→v₂→v₁>v₂→in₁v₁>in₁'v₂ u₁ u₂ u₁>u₂)  
        prf₁ v₁@(RightU u₁) v₂@(RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rr u₁>u₂)) = len-≡ len|injectv₁|≡len|inject'v₂| injectrightu₁>inject'rightu₂
          where 
            len|injectv₁|≡len|inject'v₂| : length (proj₁ (flat (inject v₁))) ≡ length (proj₁ (flat (inject' v₂)))
            len|injectv₁|≡len|inject'v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject'-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
            
            injectrightu₁≡rightin₂u₁ : inject (RightU u₁) ≡ RightU (in₂ u₁)
            injectrightu₁≡rightin₂u₁ = refl 
            inject'rightu₂≡rightin₂u₂ : inject' (RightU u₂) ≡ RightU (in₂ u₂)
            inject'rightu₂≡rightin₂u₂ = refl 
            injectrightu₁>inject'rightu₂ : l + r ` loc  ⊢ inject (RightU u₁) >ⁱ inject' (RightU u₂)
            injectrightu₁>inject'rightu₂ rewrite injectrightu₁≡rightin₂u₁ | inject'rightu₂≡rightin₂u₂  = choice-rr  (v₁→v₂→v₁>v₂→in₂v₁>in₂v₂ u₁ u₂ u₁>u₂) 

        prf₁ v₁@(LeftU u₁) v₂@(RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|u₁|≥|len|u₂|)) =  injectleft-u₁>inject'right-u₂
          where
            len|injectv₁|≡len|inject'v₂| : length (proj₁ (flat (inject v₁))) ≡ length (proj₁ (flat (inject' v₂)))
            len|injectv₁|≡len|inject'v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject'-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
            injectleft-u₁≥inject'left-u₁ : l + r ` loc   ⊢ inject (LeftU u₁) > inject' (LeftU u₁) ⊎ inject (LeftU u₁) ≡ inject' (LeftU u₁)
            injectleft-u₁≥inject'left-u₁ = prf₂ (LeftU u₁)
            >-inc-fuse-in₁'-in₂ : >-Inc (pdinstance {p₁ + p₂ ` loc} {l + r ` loc } {c} inject' soundEv')
            >-inc-fuse-in₁'-in₂ = 
              PosixOrder.>-inc-fuse-left-right pdi pdi₂ (PosixOrder.>-inc-left {l} {r} {loc} {c} (pdinstance in₁' s-ev₁') (>-inc v₁→v₂→v₁>v₂→in₁'v₁>in₁'v₂)) (PosixOrder.>-inc-right {l} {r} {loc} {c} (pdinstance in₂ s-ev₂) (>-inc v₁→v₂→v₁>v₂→in₂v₁>in₂v₂) ) 
            inject'left-u₁>inject'right-u₂ : l + r ` loc  ⊢ inject' (LeftU u₁) > inject' (RightU u₂)
            inject'left-u₁>inject'right-u₂ with >-inc-fuse-in₁'-in₂
            ... | >-inc v₁→v₂→v₁>v₂→inject'v₁>inject'v₂  = v₁→v₂→v₁>v₂→inject'v₁>inject'v₂ (LeftU u₁) (RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|u₁|≥|len|u₂|)) 
            injectleft-u₁>inject'right-u₂ : l + r ` loc  ⊢ inject (LeftU u₁) > inject' (RightU u₂)
            injectleft-u₁>inject'right-u₂ with  injectleft-u₁≥inject'left-u₁
            ... | inj₂ inject-left-u₁≡inject'left-u₁ rewrite inject-left-u₁≡inject'left-u₁ =  inject'left-u₁>inject'right-u₂
            ... | inj₁ inject-left-u₁>inject'left-u₁ = >-trans inject-left-u₁>inject'left-u₁ inject'left-u₁>inject'right-u₂
        prf₁ v₁@(RightU u₁) v₂@(LeftU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rl len|u₁|>|len|u₂|)) = Nullary.contradiction len|u₁|>|len|u₂| (<-irrefl (sym len|v₁|≡len|v₂| ) )


        fuse-left-pdi₁-right-pdi₂≥fuse-left-pdi₁'-right-pdi₂ :  (l + r ` loc) , c ⊢  (pdinstance inject soundEv) ≥ (pdinstance inject' soundEv')
        fuse-left-pdi₁-right-pdi₂≥fuse-left-pdi₁'-right-pdi₂ =  ≥-pdi inject soundEv inject' soundEv' prf₁ prf₂  
        sub₃ : (qdis : (List (PDInstance r c )))
             → All >-Inc qdis
             → All (_,_⊢_≥_ r c pdi₂) qdis
             → All (_,_⊢_≥_ (l + r ` loc) c (fuse {l + r ` loc} {loc}  (pdinstance-left pdi₁) (pdinstance-right pdi₂)))
                 (List.map (fuse {l + r ` loc} {loc}  (pdinstance-left pdi) ) (List.map pdinstance-right qdis))
        sub₃ [] [] [] = []
        sub₃ (qdi@(pdinstance in₂' s-ev₂') ∷ qdis) ((>-inc v₁→v₂→v₁>v₂→in₂'v₁>in₂'v₂ )  ∷ all->-inc-qdis ) (  (≥-pdi .{r} .{p₂} .{c} .(in₂) .(s-ev₂) .(in₂') .(s-ev₂') v₁→v₂→v₁>v₂→in₂v₁>in₂'v₂ v→in₂v≥in₂'v )  ∷ pdi₂≥qdis ) =  fuse-left-pdi₁-right-pdi₂≥fuse-left-pdi₁'-right-pdi₂' ∷ sub₃ qdis all->-inc-qdis pdi₂≥qdis
          where
            len-|in₂'-u|≡len-|u|+1 : (u : U p₂) → length (proj₁ (flat (in₂' u))) ≡ suc (length (proj₁ (flat u)))
            len-|in₂'-u|≡len-|u|+1 u rewrite (s-ev₂' u) = refl
            
            inject'' : U (p₁ + p₂ ` loc ) → U (l + r ` loc)
            inject'' = mkfuseInj (LeftU ∘ in₁') (RightU ∘ in₂')
            soundEv'' : ( u : U (p₁ + p₂ ` loc ) ) → proj₁ (flat (inject'' u)) ≡ c ∷ (proj₁ (flat u ))
            soundEv'' = mkfuseInjSoundEv {p₁}  {p₂} {l + r ` loc} {loc} {c}  (LeftU ∘ in₁') (RightU ∘ in₂') s-ev₁' s-ev₂'

            len-|inject''-u|≡len-|u|+1 : (u : U ( p₁ + p₂ ` loc )) → length (proj₁ (flat (inject'' u))) ≡ suc (length (proj₁ (flat u)))
            len-|inject''-u|≡len-|u|+1 u rewrite (soundEv'' u) = refl

            prf₄ : (v : U (p₁ + p₂ ` loc)) →
                    (l + r ` loc) ⊢ inject v > inject'' v ⊎ inject v ≡ inject'' v
                    
            prf₄ (RightU {p₁} {p₂} {loc} u) with v→in₂v≥in₂'v u 
            ... | inj₂ in₂u≡in₂'u = inj₂ (cong RightU in₂u≡in₂'u)
            ... | inj₁ in₂u>in₂'u = inj₁ (len-≡ len-|right-in₁-u|≡len-|right-in₁'-u| (choice-rr in₂u>in₂'u) )
              where
                len-|right-in₁-u|≡len-|right-in₁'-u| : length (proj₁ (flat ((RightU {l} {r} {loc} ∘ in₂) u))) ≡ 
                                               length (proj₁ (flat ((RightU {l} {r} {loc} ∘ in₂') u)))
                len-|right-in₁-u|≡len-|right-in₁'-u| rewrite len-|in₂-u|≡len-|u|+1 u | len-|in₂'-u|≡len-|u|+1 u = refl
            prf₄ (LeftU {p₁} {p₂} {loc} u) with  v→in₁v≥in₁'v u
            ... | inj₂ in₁u≡in₁'u = inj₂ (cong LeftU in₁u≡in₁'u ) 
            ... | inj₁ in₁u>in₁'u = inj₁ (len-≡ len-|left-in₁-u|≡len-|left-in₁'-u| (choice-ll in₁u>in₁'u) )
              where
                len-|left-in₁-u|≡len-|left-in₁'-u| : length (proj₁ (flat ((LeftU {l} {r} {loc} ∘ in₁) u))) ≡ 
                                               length (proj₁ (flat ((LeftU {l} {r} {loc} ∘ in₁') u)))
                len-|left-in₁-u|≡len-|left-in₁'-u| rewrite len-|in₁-u|≡len-|u|+1 u | len-|in₁'-u|≡len-|u|+1 u = refl

            prf₃ : (v₁ v₂ : U (p₁ + p₂ ` loc)) →
                 (p₁ + p₂ ` loc) ⊢ v₁ > v₂ → (l + r ` loc) ⊢ inject v₁ > inject'' v₂
            prf₃ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|injectv₁|>len|inject''v₂|
              where
                len|injectv₁|>len|inject''v₂| : length (proj₁ (flat (inject v₁))) Nat.> length (proj₁ (flat (inject'' v₂)))
                len|injectv₁|>len|inject''v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject''-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|

            prf₃ v₁@(LeftU u₁) v₂@(LeftU u₂) (len-≡ len|v₁|≡len|v₂| (choice-ll u₁>u₂)) = len-≡ len|injectv₁|≡len|inject''v₂| injectleftu₁>inject''leftu₂
              where 
                len|injectv₁|≡len|inject''v₂| : length (proj₁ (flat (inject v₁))) ≡ length (proj₁ (flat (inject'' v₂)))
                len|injectv₁|≡len|inject''v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject''-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
                injectleftu₁≡leftin₁u₁ : inject (LeftU u₁) ≡ LeftU (in₁ u₁)
                injectleftu₁≡leftin₁u₁ = refl 
                inject''leftu₂≡leftin₁'u₂ : inject'' (LeftU u₂) ≡ LeftU (in₁' u₂)
                inject''leftu₂≡leftin₁'u₂ = refl 
                injectleftu₁>inject''leftu₂ : l + r ` loc  ⊢ inject (LeftU u₁) >ⁱ inject'' (LeftU u₂)
                injectleftu₁>inject''leftu₂ rewrite injectleftu₁≡leftin₁u₁ | inject''leftu₂≡leftin₁'u₂  = choice-ll  (v₁→v₂→v₁>v₂→in₁v₁>in₁'v₂ u₁ u₂ u₁>u₂)
            prf₃ v₁@(RightU u₁) v₂@(RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rr u₁>u₂)) = len-≡ len|injectv₁|≡len|inject''v₂| injectrightu₁>inject''rightu₂
              where 
                len|injectv₁|≡len|inject''v₂| : length (proj₁ (flat (inject v₁))) ≡ length (proj₁ (flat (inject'' v₂)))
                len|injectv₁|≡len|inject''v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject''-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
            
                injectrightu₁≡rightin₂u₁ : inject (RightU u₁) ≡ RightU (in₂ u₁)
                injectrightu₁≡rightin₂u₁ = refl 
                inject''rightu₂≡rightin₂'u₂ : inject'' (RightU u₂) ≡ RightU (in₂' u₂)
                inject''rightu₂≡rightin₂'u₂ = refl 
                injectrightu₁>inject''rightu₂ : l + r ` loc  ⊢ inject (RightU u₁) >ⁱ inject'' (RightU u₂)
                injectrightu₁>inject''rightu₂ rewrite injectrightu₁≡rightin₂u₁ | inject''rightu₂≡rightin₂'u₂  = choice-rr  (v₁→v₂→v₁>v₂→in₂v₁>in₂'v₂ u₁ u₂ u₁>u₂)                 

            prf₃ v₁@(LeftU u₁) v₂@(RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|u₁|≥|len|u₂|)) =  injectleft-u₁>inject''right-u₂
              where
                len|injectv₁|≡len|inject''v₂| : length (proj₁ (flat (inject v₁))) ≡ length (proj₁ (flat (inject'' v₂)))
                len|injectv₁|≡len|inject''v₂| rewrite len-|inject-u|≡len-|u|+1 v₁ |  len-|inject''-u|≡len-|u|+1 v₂ |  len|v₁|≡len|v₂| = refl
                injectleft-u₁≥inject''left-u₁ : l + r ` loc   ⊢ inject (LeftU u₁) > inject'' (LeftU u₁) ⊎ inject (LeftU u₁) ≡ inject'' (LeftU u₁)
                injectleft-u₁≥inject''left-u₁ = prf₄ (LeftU u₁)
                >-inc-fuse-in₁'-in₂' : >-Inc (pdinstance {p₁ + p₂ ` loc} {l + r ` loc } {c} inject'' soundEv'')
                >-inc-fuse-in₁'-in₂' = 
                  PosixOrder.>-inc-fuse-left-right pdi qdi (PosixOrder.>-inc-left {l} {r} {loc} {c} (pdinstance in₁' s-ev₁') (>-inc v₁→v₂→v₁>v₂→in₁'v₁>in₁'v₂)) (PosixOrder.>-inc-right {l} {r} {loc} {c} (pdinstance in₂' s-ev₂') (>-inc v₁→v₂→v₁>v₂→in₂'v₁>in₂'v₂) ) 
                inject''left-u₁>inject''right-u₂ : l + r ` loc  ⊢ inject'' (LeftU u₁) > inject'' (RightU u₂)
                inject''left-u₁>inject''right-u₂ with >-inc-fuse-in₁'-in₂'
                ... | >-inc v₁→v₂→v₁>v₂→inject''v₁>inject''v₂  = v₁→v₂→v₁>v₂→inject''v₁>inject''v₂ (LeftU u₁) (RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|u₁|≥|len|u₂|)) 
                injectleft-u₁>inject''right-u₂ : l + r ` loc  ⊢ inject (LeftU u₁) > inject'' (RightU u₂)
                injectleft-u₁>inject''right-u₂ with  injectleft-u₁≥inject''left-u₁
                ... | inj₂ inject-left-u₁≡inject''left-u₁ rewrite inject-left-u₁≡inject''left-u₁ =  inject''left-u₁>inject''right-u₂
                ... | inj₁ inject-left-u₁>inject''left-u₁ = >-trans inject-left-u₁>inject''left-u₁ inject''left-u₁>inject''right-u₂
            prf₃ v₁@(RightU u₁) v₂@(LeftU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rl len|u₁|>|len|u₂|)) = Nullary.contradiction len|u₁|>|len|u₂| (<-irrefl (sym len|v₁|≡len|v₂| ) )
                
            
            fuse-left-pdi₁-right-pdi₂≥fuse-left-pdi₁'-right-pdi₂' :  (l + r ` loc) , c ⊢  (pdinstance inject soundEv) ≥ (pdinstance inject'' soundEv'')
            fuse-left-pdi₁-right-pdi₂≥fuse-left-pdi₁'-right-pdi₂' =  ≥-pdi inject soundEv inject'' soundEv'' prf₃ prf₄  

mk-snd-≥-pdi-sorted : ∀ { l r p : RE } { loc : ℕ } { c : Char }
   → ( e : U l )
   → ( flat-[]-e : Flat-[] l e )
   → ( pdi₁ : PDInstance r c )
   → ( pdi₂ : PDInstance r c )
   → Inhabit {r} {c} p pdi₁
   → Inhabit {r} {c} p pdi₂
   → r , c ⊢ pdi₁ ≥ pdi₂ 
   -----------------------------------------------------------------------------------------
   → (l ● r ` loc) , c ⊢ mk-snd-pdi (e , flat-[]-e) pdi₁ ≥  mk-snd-pdi (e , flat-[]-e) pdi₂ 
mk-snd-≥-pdi-sorted {l} {r} {p} {loc} {c} e (flat-[] .(e) |e|≡[]  ) (pdinstance .{p} .{r} .{c} in₁ s-ev₁)  (pdinstance .{p} .{r} .{c} in₂ s-ev₂) (hide .(in₁) .(s-ev₁))  (hide .(in₂) .(s-ev₂)) (≥-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v→in₁v>in₂v⊎in₁v≡in₂v ) = ≥-pdi inject₁ soundEv₁ inject₂ soundEv₂ prf₁ prf₂
  where
    inject₁ : ∀ ( u : U p ) → U ( l ● r ` loc)
    inject₁ = mkinjSnd in₁ e

    inject₂ : ∀ ( u : U p ) → U ( l ● r ` loc)
    inject₂ = mkinjSnd in₂ e

    soundEv₁ : (u : U p) →  Product.proj₁ (flat (inject₁ u)) ≡ c ∷ Product.proj₁ (flat u)
    soundEv₁ = mkinjSndSoundEv {p} {l} {r} {loc} {c} in₁ s-ev₁ e (flat-[] e |e|≡[]) 

    soundEv₂ : (u : U p) →  Product.proj₁ (flat (inject₂ u)) ≡ c ∷ Product.proj₁ (flat u)
    soundEv₂ = mkinjSndSoundEv {p} {l} {r} {loc} {c} in₂ s-ev₂ e (flat-[] e |e|≡[])

    len-|in₁-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
    len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

    len-|in₂-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
    len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 

    |in₁-u|≡|in₂-u| : (u : U p) →  (proj₁ (flat (in₁ u))) ≡  (proj₁ (flat (in₂ u)))
    |in₁-u|≡|in₂-u| u rewrite (s-ev₁ u) | (s-ev₂ u) = refl 

    len-|inject₁-u|≡len-|u|+1 : (u : U  p ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
    len-|inject₁-u|≡len-|u|+1 u rewrite (soundEv₁ u) = refl 

    len-|inject₂-u|≡len-|u|+1 : (u : U  p ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
    len-|inject₂-u|≡len-|u|+1 u rewrite (soundEv₂ u) = refl


    prf₂ : (v : U p) → (l ● r ` loc) ⊢ inject₁ v > inject₂ v ⊎ inject₁ v ≡ inject₂ v
    prf₂ v with v→in₁v>in₂v⊎in₁v≡in₂v v
    ... | inj₂ in₁v≡in₂v = inj₂ (cong (λ x → (PairU e x)) in₁v≡in₂v )
    ... | inj₁ in₁v>in₂v = inj₁ (len-≡ len-|pair-e-in₁-v|≡len-|pair-e-in₂-v| (seq₂ refl in₁v>in₂v) ) 
      where
        len-|pair-e-in₁-v|≡len-|pair-e-in₂-v| : length (proj₁ (flat (inject₁ v ))) ≡ length (proj₁ (flat (inject₂ v )))
        len-|pair-e-in₁-v|≡len-|pair-e-in₂-v| rewrite len-|in₁-u|≡len-|u|+1 v | len-|in₂-u|≡len-|u|+1 v |  |in₁-u|≡|in₂-u| v = refl


    prf₁ : (v₁ v₂ : U p) → p ⊢ v₁ > v₂ → (l ● r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
    prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|inject₁v₁|>len|inject₂v₂|
      where
        len|inject₁v₁|>len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.> length (proj₁ (flat (inject₂ v₂)))
        len|inject₁v₁|>len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
    
    prf₁ v₁ v₂ (len-≡ len|v₁|≡len|v₂| v₁>ⁱv₂) = len-≡ len-|pair-e-in₁-v₁|≡len-|pair-e-in₂-v₂| (seq₂ refl (v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v₁ v₂ (len-≡ len|v₁|≡len|v₂| v₁>ⁱv₂) ) )
      where
        len-|in₁-v₁|≡len|in₂-v₂| : length (proj₁ (flat (in₁ v₁))) ≡  length (proj₁ (flat (in₂ v₂)))
        len-|in₁-v₁|≡len|in₂-v₂| rewrite  len-|in₁-u|≡len-|u|+1 v₁ | len-|in₂-u|≡len-|u|+1 v₂ | len|v₁|≡len|v₂| = refl 
        len-|pair-e-in₁-v₁|≡len-|pair-e-in₂-v₂| : length (proj₁ (flat (inject₁ v₁ ))) ≡ length (proj₁ (flat (inject₂ v₂ )))
        len-|pair-e-in₁-v₁|≡len-|pair-e-in₂-v₂| rewrite  |e|≡[] |  len-|in₁-v₁|≡len|in₂-v₂|  = refl 
      

    
    
concatmap-snd-ex-lattice : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( pdis : List (PDInstance r c ) )
  → All >-Inc pdis
  → Homogenous pdis
  → Ex≥-lattice {r} pdis  
  -------------------------------------------------------------------------------------
  → Ex≥-lattice { l ● r ` loc } (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  pdis)
concatmap-snd-ex-lattice {l} {r} {ε∈l} {loc} {c} [] []  homo-pdis  ex-empty rewrite concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c}  =  ex-empty
concatmap-snd-ex-lattice {l} {r} {ε∈l} {loc} {c} (pdi@(pdinstance {p} {r} {c} in₁ s-ev₁) ∷ pdis) (>-inc-pdi ∷ >-inc-pdis) (homogenous (.(pdi) ∷ .(pdis)) ( .(p) , (hide-p-pdi@(hide .{p} .{r} .{c} .(in₁) .(s-ev₁)) ∷ hide-p-pdis)) ) (ex-join .(pdi) .(pdis) pdi≥pdis) with mkAllEmptyU {l} ε∈l in mkAllEmpty-eq  | mkAllEmptyU-sound ε∈l | mkAllEmptyU-sorted ε∈l 
... | []     | _                      | _ = Nullary.contradiction mkAllEmpty-eq (mkAllEmptyU≢[] {l} ε∈l) -- we need a contradiction here 
... | e ∷ es | flat-[]-e@(flat-[] .(e) |e|≡[]) ∷ flat-[]-es | >-cons es->-sorted e>head-es =
  ex-join (mk-snd-pdi (e , flat-[]-e) pdi) (List.map (mk-snd-pdi (e , flat-[]-e)) pdis ++
                                                     (concatMap (λ x → List.map (mk-snd-pdi x) (pdi ∷ pdis))
                                                                       (zip-es-flat-[]-es  {l} {ε∈l} es flat-[]-es))) prf
  where
    sub_prf₁ : ( qdis : List (PDInstance r c ) )
      → All (_,_⊢_≥_  r c pdi) qdis 
      → All (_,_⊢_≥_ (l ● r ` loc) c (mk-snd-pdi (e , flat-[]-e) pdi)) (List.map (mk-snd-pdi (e , flat-[]-e)) qdis )
    sub_prf₁ [] [] = []
    sub_prf₁  (qdi@(pdinstance in₂ s-ev₂) ∷ qdis ) (  (≥-pdi .{r} .{p} .{c} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v ) ∷ pdi≥all-qdis) =
      mk-snd-≥-pdi-sorted e flat-[]-e (pdinstance in₁ s-ev₁) (pdinstance in₂ s-ev₂) (hide in₁ s-ev₁) (hide in₂ s-ev₂) (≥-pdi in₁ s-ev₁ in₂ s-ev₂ v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v)  ∷ sub qdis prf₁ pdi≥all-qdis

    sub_prf₂ : (es' : List (U l))
      → (flat-[]-es' : All (Flat-[] l) es')
      → All (_⊢_>_ l e ) es' 
      → All (_,_⊢_≥_ (l ● r ` loc) c
       (mk-snd-pdi (e , flat-[]-e) pdi))
      (concatMap (λ x → List.map (mk-snd-pdi x) (pdi ∷ pdis))  (zip-es-flat-[]-es {l} {ε∈l} es' flat-[]-es'))
    sub_prf₂ [] [] [] = []
    sub_prf₂ (x ∷ xs) ((flat-[] .(x) |x|≡[]) ∷ flat-[]-xs) (e>x ∷ e>xs)  = all-concat ( sub_sub_prf (pdi ∷ pdis) (hide in₁ s-ev₁ ∷ hide-p-pdis) (ex≥-refl >-inc-pdi ∷ pdi≥pdis) )  (sub_prf₂ xs flat-[]-xs e>xs)
      where
        sub_sub_prf : ( rdis : List (PDInstance r c) )
                    → All (Inhabit p) rdis 
                    → All (_,_⊢_≥_ r c pdi) rdis 
                    → All (_,_⊢_≥_ (l ● r ` loc) c (mk-snd-pdi (e , flat-[]-e) pdi)) 
                            ( List.map (mk-snd-pdi (x , flat-[] x |x|≡[])) rdis )
        sub_sub_prf [] [] [] = []
        sub_sub_prf (rdi@(pdinstance .{p} .{r} .{c} in₂ s-ev₂)  ∷ rdis) ( ( hide .{p} .{r} .{c} .(in₂) .(s-ev₂) ) ∷ hide-p-rdis ) (pdi≥rdi ∷ pdi≥rdis) = mk-snd-pdi-e-pdi≥mk-snd-pdi-x-rdi ∷ sub_sub_prf rdis hide-p-rdis pdi≥rdis 
          where
            inject₁ : ∀ ( u : U p ) → U ( l ● r ` loc)
            inject₁ = mkinjSnd in₁ e

            inject₂ : ∀ ( u : U p ) → U ( l ● r ` loc)
            inject₂ = mkinjSnd in₂ x

            soundEv₁ : (u : U p) →  Product.proj₁ (flat (inject₁ u)) ≡ c ∷ Product.proj₁ (flat u)
            soundEv₁ = mkinjSndSoundEv {p} {l} {r} {loc} {c} in₁ s-ev₁ e  flat-[]-e 

            soundEv₂ : (u : U p) →  Product.proj₁ (flat (inject₂ u)) ≡ c ∷ Product.proj₁ (flat u)
            soundEv₂ = mkinjSndSoundEv {p} {l} {r} {loc} {c} in₂ s-ev₂ x (flat-[] x |x|≡[])

            len-|in₁-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
            len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

            len-|in₂-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
            len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 

            |in₁-u|≡|in₂-u| : (u : U p) →  (proj₁ (flat (in₁ u))) ≡  (proj₁ (flat (in₂ u)))
            |in₁-u|≡|in₂-u| u rewrite (s-ev₁ u) | (s-ev₂ u) = refl 

            len-|inject₁-u|≡len-|u|+1 : (u : U  p ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
            len-|inject₁-u|≡len-|u|+1 u rewrite (soundEv₁ u) = refl 

            len-|inject₂-u|≡len-|u|+1 : (u : U  p ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
            len-|inject₂-u|≡len-|u|+1 u rewrite (soundEv₂ u) = refl

            prf₂ : (v : U p) → (l ● r ` loc) ⊢ inject₁ v > inject₂ v ⊎ inject₁ v ≡ inject₂ v
            prf₂ v  = inj₁ (len-≡ len-|pair-e-in₁-v|≡len-|pair-x-in₂-v| (seq₁ e>x ) ) 
              where
                len-|pair-e-in₁-v|≡len-|pair-x-in₂-v| : length (proj₁ (flat (inject₁ v ))) ≡ length (proj₁ (flat (inject₂ v )))
                len-|pair-e-in₁-v|≡len-|pair-x-in₂-v| rewrite len-|in₁-u|≡len-|u|+1 v | len-|in₂-u|≡len-|u|+1 v |  |in₁-u|≡|in₂-u| v | |e|≡[] | |x|≡[]  = refl 

            prf₁ : (v₁ v₂ : U p) →  p ⊢ v₁ > v₂ → (l ● r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
            prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|inject₁v₁|>len|inject₂v₂|
              where
                len|inject₁v₁|>len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.> length (proj₁ (flat (inject₂ v₂)))
                len|inject₁v₁|>len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|

            prf₁ v₁ v₂ (len-≡ len|v₁|≡len|v₂| v₁>ⁱv₂) = len-≡ len-|pair-e-in₁-v₁|≡len-|pair-x-in₂-v| (seq₁ e>x)
              where
                len-|in₁-v₁|≡len|in₂-v₂| : length (proj₁ (flat (in₁ v₁))) ≡  length (proj₁ (flat (in₂ v₂)))
                len-|in₁-v₁|≡len|in₂-v₂| rewrite  len-|in₁-u|≡len-|u|+1 v₁ | len-|in₂-u|≡len-|u|+1 v₂ | len|v₁|≡len|v₂| = refl 
              
                len-|pair-e-in₁-v₁|≡len-|pair-x-in₂-v| : length (proj₁ (flat (inject₁ v₁ ))) ≡ length (proj₁ (flat (inject₂ v₂ )))
                len-|pair-e-in₁-v₁|≡len-|pair-x-in₂-v| rewrite  |e|≡[] | |x|≡[] |  len-|in₁-v₁|≡len|in₂-v₂|  = refl 
            

            mk-snd-pdi-e-pdi≥mk-snd-pdi-x-rdi :  (l ● r ` loc) , c ⊢  mk-snd-pdi (e , flat-[]-e) pdi ≥ mk-snd-pdi (x , flat-[] x |x|≡[]) rdi
            -- mk-snd-pdi-e-pdi≥mk-snd-pdi-x-rdi :  (l ● r ` loc) , c ⊢ (pdinstance inject₁ soundEv₁) ≥ (pdinstance inject₂ soundEv₂ )
            mk-snd-pdi-e-pdi≥mk-snd-pdi-x-rdi = ≥-pdi inject₁ soundEv₁ inject₂ soundEv₂ prf₁ prf₂ 

    prf : All (_,_⊢_≥_ (l ● r ` loc) c (mk-snd-pdi (e , flat-[]-e) pdi))
                          (List.map (mk-snd-pdi (e , flat-[]-e)) pdis ++
                            concatMap (λ x →  List.map (mk-snd-pdi x) (pdi ∷  pdis))
                              (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es))
    prf = all-concat (sub_prf₁ pdis pdi≥pdis)  (sub_prf₂ es flat-[]-es (PosixOrder.>-cons→hd>tl (>-cons es->-sorted e>head-es) ) ) 
    


oplus-+●-ex-lattice : ∀ { l+s r : RE } { ε∈l+s : ε∈ l+s } { loc : ℕ } { c : Char }
    → ( pdis₁ : List ( PDInstance l+s c ))
    → ( pdis₂ : List ( PDInstance r c ))
    → Ex≥-lattice { l+s } {c} pdis₁
    → Ex≥-lattice { r } {c} pdis₂
    → All >-Inc pdis₁
    → All >-Inc pdis₂
    → Homogenous pdis₁
    → Homogenous pdis₂
    ---------------------------------------
    → Ex≥-lattice  { l+s ● r ` loc } (pdinstance-oplus {l+s ● r ` loc } {loc} {c}  (List.map (pdinstance-fst {l+s} {r} {loc} {c}) pdis₁) (concatmap-pdinstance-snd {l+s} {r} {ε∈l+s} {loc} {c} pdis₂))
oplus-+●-ex-lattice {l+s} {r} {ε∈l+s} {loc} {c} [] pdis₂ ex-empty ex-semi [] all->-inc-pdis₂ homo-pdis₁ homo-pdis₂ = concatmap-snd-ex-lattice pdis₂ all->-inc-pdis₂ homo-pdis₂  ex-semi       
oplus-+●-ex-lattice {l+s} {r} {ε∈l+s} {loc} {c} (pdi₁ ∷ pdis₁) []             ex-semi ex-empty all->-inc-pdi₁pdis₁ [] homo-pdis₁ homo-pdis₂ rewrite concatmap-pdinstance-snd-[]≡[] {l+s} {r} {ε∈l+s} {loc} {c} =  map-fst-ex-lattice (pdi₁ ∷ pdis₁) ex-semi
oplus-+●-ex-lattice {l+s} {r} {ε∈l+s} {loc} {c} (pdi₁@(pdinstance {p₁} .{l+s} .{c} in₁ s-ev₁) ∷ pdis₁)
                                                (pdi₂@(pdinstance {p₂} .{r} .{c} in₂ s-ev₂) ∷ pdis₂)
                                                (ex-join .(pdi₁) .(pdis₁) pdi₁≥pdis₁)
                                                (ex-join .(pdi₂) .(pdis₂) pdi₂≥pdis₂)
                                                (>-inc-pdi₁@(>-inc v₁→v₂→v₁>v₂→in₁v₁>in₁v₂) ∷ all->-inc-pdis₁)
                                                (>-inc-pdi₂ ∷ all->-inc-pdis₂ )
                                                homo-pdis₁@(homogenous (.(pdi₁) ∷ .(pdis₁)) ( .(p₁) , ( (hide .{p₁} .{l+s} .{c} .(in₁) .(s-ev₁)) ∷ hide-p₁-pdis₁ )))
                                                homo-pdis₂@(homogenous (.(pdi₂) ∷ .(pdis₂)) ( .(p₂) , ( (hide .{p₂} .{r} .{c} .(in₂) .(s-ev₂)) ∷ hide-p₂-pdis₂ )))
                    with mkAllEmptyU {l+s} ε∈l+s in mkAllEmpty-eq  | mkAllEmptyU-sound ε∈l+s | mkAllEmptyU-sorted ε∈l+s 
... | []     | _                      | _ = Nullary.contradiction mkAllEmpty-eq (mkAllEmptyU≢[] {l+s} ε∈l+s) -- we need a contradiction here 
... | e ∷ es | flat-[]-e@(flat-[] .(e) |e|≡[]) ∷ flat-[]-es | >-cons es->-sorted e>head-es =
  ex-join (fuse (pdinstance-fst pdi₁)
            (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂)) ((List.map (fuse (pdinstance-fst pdi₁))
                                                        (List.map (mk-snd-pdi (e , flat-[] e |e|≡[])) pdis₂ ++
                                                         (concatMap (λ x → List.map (mk-snd-pdi x) (pdi₂ ∷  pdis₂))
                                                          (zip-es-flat-[]-es {l+s} {ε∈l+s} es flat-[]-es))))
                                                        ++
                                                        (concatMap
                                                         (λ pdiˡ₁ →
                                                            List.map (fuse pdiˡ₁)
                                                             (concatMap (λ x → List.map (mk-snd-pdi x) (pdi₂ ∷ pdis₂)) 
                                                              (zip-es-flat-[]-es {l+s} {ε∈l+s}  (e ∷ es) (flat-[]-e ∷ flat-[]-es)))
                                                             )
                                                         (List.map pdinstance-fst pdis₁))) (all-concat sub_prf₁ (sub_prf₂ pdis₁ all->-inc-pdis₁ hide-p₁-pdis₁ pdi₁≥pdis₁) )
    where

      sub_prf₄ : ( e : U ( l+s ) )
        → ( |e|≡[] : proj₁ (flat e) ≡ [] )
        → (qdis : List (PDInstance r c))
        → All (Inhabit p₂) qdis 
        → All (_,_⊢_≥_ r c pdi₂) qdis 
        → All (_,_⊢_≥_ (l+s ● r ` loc) c (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂)))
                      (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁))
                                      (List.map (mk-snd-pdi (e , flat-[] e |e|≡[])) qdis)) -- induction over pdis₂
      sub_prf₄ e |e|≡[] [] [] [] = []
      sub_prf₄ e |e|≡[] (qdi@(pdinstance in₂' s-ev₂') ∷ qdis) ( (hide .{p₂} .{r} .{c} .(in₂') .(s-ev₂')) ∷ hide-p₂-qdis ) ((≥-pdi .(in₂) .(s-ev₂) .(in₂') .(s-ev₂') v₁→v₂→v₁>v₂→in₂v₁>in₂'v₂ v→in₂v≥in₂'v) ∷ pdi₂≥qdis) =
         ≥-pdi inject₁ soundEv₁ inject₂ soundEv₂ sub_sub_prf₁ sub_sub_prf₂  ∷ sub_prf₄ e |e|≡[] qdis hide-p₂-qdis  pdi₂≥qdis
         where
           inject₁ : U ((p₁ ● r ` loc) + p₂ ` loc ) → U (l+s ● r ` loc)
           inject₁ = mkfuseInj (mkinjFst in₁) (mkinjSnd in₂ e )
           
           inject₂ : U ((p₁ ● r ` loc) + p₂ ` loc ) → U (l+s ● r ` loc)
           inject₂ = mkfuseInj (mkinjFst in₁) (mkinjSnd in₂' e )

           soundEv₁ : ( u : U ( (p₁ ● r ` loc) + p₂ ` loc ) ) → proj₁ (flat (inject₁ u)) ≡ c ∷ (proj₁ (flat u ))
           soundEv₁ = mkfuseInjSoundEv {p₁ ● r ` loc}  {p₂} {l+s ● r ` loc} {loc} {c} (mkinjFst in₁) (mkinjSnd in₂ e ) (mkinjFstSoundEv in₁ s-ev₁) (mkinjSndSoundEv {p₂} {l+s} {r} {loc} {c} in₂ s-ev₂ e (flat-[] e |e|≡[])) 
           soundEv₂ : ( u : U ( (p₁ ● r ` loc) + p₂ ` loc ) ) → proj₁ (flat (inject₂ u)) ≡ c ∷ (proj₁ (flat u ))
           soundEv₂ = mkfuseInjSoundEv {p₁ ● r ` loc}  {p₂} {l+s ● r ` loc} {loc} {c} (mkinjFst in₁) (mkinjSnd in₂' e ) (mkinjFstSoundEv in₁ s-ev₁) (mkinjSndSoundEv {p₂} {l+s} {r} {loc} {c} in₂' s-ev₂' e (flat-[] e |e|≡[]))
           len-|in₁-u|≡len-|u|+1 : (u : U p₁) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
           len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

           len-|in₂-u|≡len-|u|+1 : (u : U p₂) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
           len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 

           len-|in₂'-u|≡len-|u|+1 : (u : U p₂) → length (proj₁ (flat (in₂' u))) ≡ suc (length (proj₁ (flat u)))
           len-|in₂'-u|≡len-|u|+1 u rewrite (s-ev₂' u) = refl

           len-|inject₁-u|≡len-|u|+1 : (u : U ( (p₁ ● r ` loc) + p₂ ` loc ) ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
           len-|inject₁-u|≡len-|u|+1 u rewrite (soundEv₁ u) = refl 

           len-|inject₂-u|≡len-|u|+1 : (u : U ( (p₁ ● r ` loc) + p₂ ` loc ) ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
           len-|inject₂-u|≡len-|u|+1 u rewrite (soundEv₂ u) = refl 

           sub_sub_prf₂ :  (v : U ((p₁ ● r ` loc) + p₂ ` loc)) →
                           (l+s ● r ` loc) ⊢ inject₁ v > inject₂ v ⊎ inject₁ v ≡ inject₂ v
           sub_sub_prf₂ v@(LeftU (PairU u u')) = inj₂ refl
           sub_sub_prf₂ v@(RightU u)          with v→in₂v≥in₂'v u
           ... | inj₂ in₂u≡in₂'u = inj₂ (cong (λ x → PairU e x) in₂u≡in₂'u )
           ... | inj₁ in₂u>in₂'u = inj₁ (len-≡ len|pair-e-in₂u|≡len|pair-e-in₂'u| (seq₂ refl  in₂u>in₂'u ) )
             where
               len|pair-e-in₂u|≡len|pair-e-in₂'u| :  length (Product.proj₁ (flat (PairU {l+s} {r} {loc}  e (in₂ u)))) ≡  length (Product.proj₁ (flat (PairU  {l+s} {r} {loc}  e (in₂' u))))
               len|pair-e-in₂u|≡len|pair-e-in₂'u| rewrite |e|≡[] |  len-|in₂-u|≡len-|u|+1 u | len-|in₂'-u|≡len-|u|+1 u  = refl
           -- out of curiosity and fun, I gave this sub sub proof to claude to play with.
           -- sub_sub_prf₁'s code is generated by opus 4.6 given the type annotation,
           -- generating the code hit the token limits for the per 4hr session. I have to tap into extra usage.
           -- in₁-preserves given by opus 4.6 contained a syntax error, which is an easy fix
           in₁-preserves : (u₁ u₂ : U p₁) → p₁ ⊢ u₁ > u₂ → l+s ⊢ in₁ u₁ > in₁ u₂
           in₁-preserves = v₁→v₂→v₁>v₂→in₁v₁>in₁v₂ 

           sub_sub_prf₁ : (v₁ v₂ : U ((p₁ ● r ` loc) + p₂ ` loc))
                          → ((p₁ ● r ` loc) + p₂ ` loc) ⊢ v₁ > v₂
                          → (l+s ● r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
           sub_sub_prf₁ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|inject₁v₁|>len|inject₂v₂|
             where
               len|inject₁v₁|>len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.> length (proj₁ (flat (inject₂ v₂)))
               len|inject₁v₁|>len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ | len-|inject₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
           sub_sub_prf₁ (LeftU (PairU u₁ w₁)) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-ll (len-> len|pair₁|>len|pair₂|))) rewrite len|v₁|≡len|v₂| = Nullary.contradiction len|pair₁|>len|pair₂| (<-irrefl refl)
           sub_sub_prf₁ (LeftU (PairU u₁ w₁)) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-ll (len-≡ len|pair₁|≡len|pair₂| (seq₁ u₁>u₂)))) = len-≡ len|inject₁v₁|≡len|inject₂v₂| (seq₁ (in₁-preserves u₁ u₂ u₁>u₂))
             where
               len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ (LeftU (PairU u₁ w₁))))) ≡ length (proj₁ (flat (inject₂ (LeftU (PairU u₂ w₂)))))
               len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 (LeftU (PairU u₁ w₁)) | len-|inject₂-u|≡len-|u|+1 (LeftU (PairU u₂ w₂)) | len|v₁|≡len|v₂| = refl
           sub_sub_prf₁ (LeftU (PairU u₁ w₁)) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-ll (len-≡ len|pair₁|≡len|pair₂| (seq₂ u₁≡u₂ w₁>w₂)))) = len-≡ len|inject₁v₁|≡len|inject₂v₂| (seq₂ (cong in₁ u₁≡u₂) w₁>w₂)
             where
               len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ (LeftU (PairU u₁ w₁))))) ≡ length (proj₁ (flat (inject₂ (LeftU (PairU u₂ w₂)))))
               len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 (LeftU (PairU u₁ w₁)) | len-|inject₂-u|≡len-|u|+1 (LeftU (PairU u₂ w₂)) | len|v₁|≡len|v₂| = refl
           sub_sub_prf₁ (LeftU (PairU u₁ w₁)) (RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|pair₁|≥len|u₂|)) = len-≡ len|inject₁v₁|≡len|inject₂v₂| (seq₁ (len-> len|in₁u₁|>len|e|))
             where
               len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ (LeftU (PairU u₁ w₁))))) ≡ length (proj₁ (flat (inject₂ (RightU u₂))))
               len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 (LeftU (PairU u₁ w₁)) | len-|inject₂-u|≡len-|u|+1 (RightU u₂) | len|v₁|≡len|v₂| = refl
               len|in₁u₁|>len|e| : length (proj₁ (flat (in₁ u₁))) Nat.> length (proj₁ (flat e))
               len|in₁u₁|>len|e| rewrite |e|≡[] | len-|in₁-u|≡len-|u|+1 u₁ = Nat.s≤s Nat.z≤n
           sub_sub_prf₁ (RightU u₁) (RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rr u₁>u₂)) = len-≡ len|inject₁v₁|≡len|inject₂v₂| (seq₂ refl (v₁→v₂→v₁>v₂→in₂v₁>in₂'v₂ u₁ u₂ u₁>u₂))
             where
               len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ (RightU u₁)))) ≡ length (proj₁ (flat (inject₂ (RightU u₂))))
               len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 (RightU u₁) | len-|inject₂-u|≡len-|u|+1 (RightU u₂) | len|v₁|≡len|v₂| = refl
           sub_sub_prf₁ (RightU u₁) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-rl len|u₁|>len|pair₂|)) rewrite len|v₁|≡len|v₂| = Nullary.contradiction len|u₁|>len|pair₂| (<-irrefl refl)
      sub_prf₅ : ( xs : List (U l+s))
        → (flat-[]-xs : All (Flat-[] l+s) xs )
        → All (_⊢_>_ l+s e) xs 
        → All (_,_⊢_≥_ (l+s ● r ` loc) c (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂)))
                     (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁))
                                     (concatMap (λ x → List.map (mk-snd-pdi x) (pdi₂ ∷ pdis₂))
                                                                    (zip-es-flat-[]-es {l+s} {ε∈l+s} xs flat-[]-xs)))  -- induction over es and flat-[]-es
      sub_prf₅ [] [] [] = []
      sub_prf₅ (x ∷ xs) ((flat-[] .(x) |x|≡[]) ∷  flat-[]-xs) (e>x ∷ e>all-xs) rewrite map-++  (fuse  {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁))
               (List.map (mk-snd-pdi (x , flat-[] x |x|≡[])) pdis₂)
               (concatMap (λ x₁ →  List.map (mk-snd-pdi x₁) (pdi₂ ∷  pdis₂))  (zip-es-flat-[]-es {l+s} {ε∈l+s} xs flat-[]-xs))
               = fuse-fst-pdi₁-mk-snd-e-pdi₂≥fuse-fst-pdi₁-mk-snd-x-pdi₂  ∷
                 all-concat
                   (ex≥-trans-map { (l+s ● r ` loc) } { ((p₁ ● r ` loc) + p₂ ` loc) } {c}
                                                       {fuse-fst-pdi₁-mk-snd-e-pdi₂}
                                                       {fuse-fst-pdi₁-mk-snd-x-pdi₂}
                                                       {(List.map (fuse (pdinstance-fst pdi₁))
                                                                   (List.map (mk-snd-pdi (x , flat-[] x |x|≡[])) pdis₂))}
                                                       {hide-p₁●r+p₂-fuse-fst-pdi₁-mk-snd-e-pdi₂}
                                                       {hide-p₁●r+p₂-fuse-fst-pdi₁-mk-snd-x-pdi₂}
                                                       {all-hide-p₁●r+p₂-map-fuse-pdi₁-map-mk-snd-x-pdis₂} 
                                    fuse-fst-pdi₁-mk-snd-e-pdi₂≥fuse-fst-pdi₁-mk-snd-x-pdi₂
                                    (sub_prf₄ x |x|≡[] pdis₂ hide-p₂-pdis₂ pdi₂≥pdis₂) )
                   (sub_prf₅ xs flat-[]-xs e>all-xs )
               where
                 injFst₁ : U (p₁ ● r ` loc) → U (l+s ● r ` loc)
                 injFst₁ = mkinjFst in₁
                 soundEvFst₁ : ( u : U (p₁ ● r ` loc) ) → proj₁ (flat (injFst₁ u)) ≡ c ∷ proj₁ (flat u)
                 soundEvFst₁ = mkinjFstSoundEv in₁ s-ev₁

                 injSnd₂-e : U p₂ → U (l+s ● r ` loc)
                 injSnd₂-e = mkinjSnd in₂ e
                 soundEvSnd₂-e : ( u : U p₂) → proj₁ (flat (injSnd₂-e u)) ≡ c ∷ proj₁ (flat u)
                 soundEvSnd₂-e = mkinjSndSoundEv {p₂} {l+s} {r} {loc} {c} in₂ s-ev₂ e (flat-[] e |e|≡[])

                 injSnd₂-x : U p₂ → U (l+s ● r ` loc)
                 injSnd₂-x = mkinjSnd in₂ x
                 soundEvSnd₂-x : ( u : U p₂) → proj₁ (flat (injSnd₂-x u)) ≡ c ∷ proj₁ (flat u)
                 soundEvSnd₂-x = mkinjSndSoundEv {p₂} {l+s} {r} {loc} {c} in₂ s-ev₂ x (flat-[] x |x|≡[]) 

                 inject₁ : U ( (p₁ ● r ` loc) + p₂ ` loc ) → U (l+s ● r ` loc)
                 inject₁ = mkfuseInj injFst₁ injSnd₂-e
                 
                 soundEv₁ :  ( u : U ((p₁ ● r ` loc) + p₂ ` loc) )  → proj₁ (flat (inject₁ u)) ≡ c ∷ proj₁ (flat u)
                 soundEv₁ = mkfuseInjSoundEv injFst₁ injSnd₂-e soundEvFst₁ soundEvSnd₂-e
                 
                 inject₂ : U ( (p₁ ● r ` loc) + p₂ ` loc ) → U (l+s ● r ` loc)
                 inject₂ = mkfuseInj injFst₁ injSnd₂-x
                 soundEv₂ :  ( u : U ((p₁ ● r ` loc) + p₂ ` loc) )  → proj₁ (flat (inject₂ u)) ≡ c ∷ proj₁ (flat u)
                 soundEv₂ = mkfuseInjSoundEv injFst₁ injSnd₂-x soundEvFst₁ soundEvSnd₂-x

                 len-|in₁-u|≡len-|u|+1 : (u : U p₁) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
                 len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl 

                 len-|in₂-u|≡len-|u|+1 : (u : U p₂) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
                 len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl


                 len-|inject₁-u|≡len-|u|+1 : (u : U ( (p₁ ● r ` loc) + p₂ ` loc ) ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
                 len-|inject₁-u|≡len-|u|+1 u rewrite (soundEv₁ u) = refl 

                 len-|inject₂-u|≡len-|u|+1 : (u : U ( (p₁ ● r ` loc) + p₂ ` loc ) ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
                 len-|inject₂-u|≡len-|u|+1 u rewrite (soundEv₂ u) = refl 

                 
                 fuse-fst-pdi₁-mk-snd-e-pdi₂ : PDInstance  (l+s ● r ` loc)  c 
                 fuse-fst-pdi₁-mk-snd-e-pdi₂ =  pdinstance inject₁ soundEv₁
                 fuse-fst-pdi₁-mk-snd-x-pdi₂ : PDInstance  (l+s ● r ` loc)  c                  
                 fuse-fst-pdi₁-mk-snd-x-pdi₂ = pdinstance inject₂ soundEv₂

                 hide-p₁●r+p₂-fuse-fst-pdi₁-mk-snd-e-pdi₂ : Inhabit ((p₁ ● r ` loc) + p₂ ` loc) fuse-fst-pdi₁-mk-snd-e-pdi₂
                 hide-p₁●r+p₂-fuse-fst-pdi₁-mk-snd-e-pdi₂ = hide inject₁ soundEv₁ 
                                                             

                 hide-p₁●r+p₂-fuse-fst-pdi₁-mk-snd-x-pdi₂ : Inhabit ((p₁ ● r ` loc) + p₂ ` loc) fuse-fst-pdi₁-mk-snd-x-pdi₂
                 hide-p₁●r+p₂-fuse-fst-pdi₁-mk-snd-x-pdi₂ = hide inject₂ soundEv₂

                 all-hide-p₂-map-mk-snd-x-pdis₂ : All (Inhabit p₂) (List.map (mk-snd-pdi {l+s} {r} {loc} {c}  (x , flat-[] x |x|≡[])) pdis₂)
                 all-hide-p₂-map-mk-snd-x-pdis₂ = map-snd-pdi-inhabit x (flat-[] x |x|≡[]) pdis₂ hide-p₂-pdis₂ 


                 all-hide-p₁●r+p₂-map-fuse-pdi₁-map-mk-snd-x-pdis₂ : All ( Inhabit ((p₁ ● r ` loc) + p₂ ` loc) )
                                                                         (List.map (fuse {l+s ● r ` loc} {loc}  (pdinstance-fst pdi₁))
                                                                           (List.map (mk-snd-pdi (x , flat-[] x |x|≡[])) pdis₂))
                 all-hide-p₁●r+p₂-map-fuse-pdi₁-map-mk-snd-x-pdis₂ =
                   map-fuse-inhabit {l+s ● r ` loc} {p₁ ● r ` loc} {p₂} (pdinstance-fst pdi₁) (List.map (mk-snd-pdi (x , flat-[] x |x|≡[])) pdis₂) (hide injFst₁  soundEvFst₁ )  all-hide-p₂-map-mk-snd-x-pdis₂


                 fuse-fst-pdi₁-mk-snd-e-pdi₂≥fuse-fst-pdi₁-mk-snd-x-pdi₂ : (l+s ● r ` loc) , c ⊢  fuse-fst-pdi₁-mk-snd-e-pdi₂ ≥  fuse-fst-pdi₁-mk-snd-x-pdi₂
                 fuse-fst-pdi₁-mk-snd-e-pdi₂≥fuse-fst-pdi₁-mk-snd-x-pdi₂ = ≥-pdi inject₁ soundEv₁ inject₂ soundEv₂ sub_sub_prf₃ sub_sub_prf₄  
                   where
                     sub_sub_prf₄ :  (v : U ((p₁ ● r ` loc) + p₂ ` loc)) →
                                     (l+s ● r ` loc) ⊢ inject₁ v > inject₂ v ⊎ inject₁ v ≡ inject₂ v
                     sub_sub_prf₄ v@(LeftU (PairU u u')) = inj₂ refl
                     sub_sub_prf₄ v@(RightU u)           = inj₁ (len-≡ len|pair-e-in₂u|≡len|pair-x-in₂u| (seq₁ e>x ) )
                       where
                         len|pair-e-in₂u|≡len|pair-x-in₂u| :  length (Product.proj₁ (flat (PairU {l+s} {r} {loc}  e (in₂ u)))) ≡  length (Product.proj₁ (flat (PairU  {l+s} {r} {loc} x (in₂ u))))
                         len|pair-e-in₂u|≡len|pair-x-in₂u| rewrite |e|≡[] | |x|≡[] |   len-|in₂-u|≡len-|u|+1 u | len-|in₂-u|≡len-|u|+1 u  = refl

                     sub_sub_prf₃ :  (v₁ v₂ : U ((p₁ ● r ` loc) + p₂ ` loc)) →
                                     ((p₁ ● r ` loc) + p₂ ` loc) ⊢ v₁ > v₂ →
                                     (l+s ● r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
                     in₁-preserves : (u₁ u₂ : U p₁) → p₁ ⊢ u₁ > u₂ → l+s ⊢ in₁ u₁ > in₁ u₂
                     in₁-preserves = v₁→v₂→v₁>v₂→in₁v₁>in₁v₂
                     sub_sub_prf₃ v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|inject₁v₁|>len|inject₂v₂|
                       where
                         len|inject₁v₁|>len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.> length (proj₁ (flat (inject₂ v₂)))
                         len|inject₁v₁|>len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ | len-|inject₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
                     sub_sub_prf₃ (LeftU (PairU u₁ w₁)) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-ll (len-> len|pair₁|>len|pair₂|))) rewrite len|v₁|≡len|v₂| = Nullary.contradiction len|pair₁|>len|pair₂| (<-irrefl refl)
                     sub_sub_prf₃ (LeftU (PairU u₁ w₁)) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-ll (len-≡ len|pair₁|≡len|pair₂| (seq₁ u₁>u₂)))) = len-≡ len|inject₁v₁|≡len|inject₂v₂| (seq₁ (in₁-preserves u₁ u₂ u₁>u₂))
                       where
                         len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ (LeftU (PairU u₁ w₁))))) ≡ length (proj₁ (flat (inject₂ (LeftU (PairU u₂ w₂)))))
                         len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 (LeftU (PairU u₁ w₁)) | len-|inject₂-u|≡len-|u|+1 (LeftU (PairU u₂ w₂)) | len|v₁|≡len|v₂| = refl
                     sub_sub_prf₃ (LeftU (PairU u₁ w₁)) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-ll (len-≡ len|pair₁|≡len|pair₂| (seq₂ u₁≡u₂ w₁>w₂)))) = len-≡ len|inject₁v₁|≡len|inject₂v₂| (seq₂ (cong in₁ u₁≡u₂) w₁>w₂)
                       where
                         len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ (LeftU (PairU u₁ w₁))))) ≡ length (proj₁ (flat (inject₂ (LeftU (PairU u₂ w₂)))))
                         len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 (LeftU (PairU u₁ w₁)) | len-|inject₂-u|≡len-|u|+1 (LeftU (PairU u₂ w₂)) | len|v₁|≡len|v₂| = refl
                     sub_sub_prf₃ (LeftU (PairU u₁ w₁)) (RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|pair₁|≥len|u₂|)) = len-≡ len|inject₁v₁|≡len|inject₂v₂| (seq₁ (len-> len|in₁u₁|>len|x|))
                       where
                         len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ (LeftU (PairU u₁ w₁))))) ≡ length (proj₁ (flat (inject₂ (RightU u₂))))
                         len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 (LeftU (PairU u₁ w₁)) | len-|inject₂-u|≡len-|u|+1 (RightU u₂) | len|v₁|≡len|v₂| = refl
                         len|in₁u₁|>len|x| : length (proj₁ (flat (in₁ u₁))) Nat.> length (proj₁ (flat x))
                         len|in₁u₁|>len|x| rewrite |x|≡[] | len-|in₁-u|≡len-|u|+1 u₁ = Nat.s≤s Nat.z≤n
                     sub_sub_prf₃ (RightU u₁) (RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rr u₁>u₂)) = len-≡ len|inject₁v₁|≡len|inject₂v₂| (seq₁ e>x)
                       where
                         len|inject₁v₁|≡len|inject₂v₂| : length (proj₁ (flat (inject₁ (RightU u₁)))) ≡ length (proj₁ (flat (inject₂ (RightU u₂))))
                         len|inject₁v₁|≡len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 (RightU u₁) | len-|inject₂-u|≡len-|u|+1 (RightU u₂) | len|v₁|≡len|v₂| = refl
                     sub_sub_prf₃ (RightU u₁) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-rl len|u₁|>len|pair₂|)) rewrite len|v₁|≡len|v₂| = Nullary.contradiction len|u₁|>len|pair₂| (<-irrefl refl)

      sub_prf₃ : All (_,_⊢_≥_ (l+s ● r ` loc) c (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂)))
                     ( (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁))
                                      (List.map (mk-snd-pdi (e , flat-[] e |e|≡[])) pdis₂)) ++
                       (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁))
                                     (concatMap (λ x → mk-snd-pdi x pdi₂ ∷ List.map (mk-snd-pdi x) pdis₂)
                                                                        (zip-es-flat-[]-es {l+s} {ε∈l+s} es flat-[]-es))) )
      sub_prf₃ = all-concat (sub_prf₄ e |e|≡[] pdis₂ hide-p₂-pdis₂  pdi₂≥pdis₂ ) (sub_prf₅ es flat-[]-es (PosixOrder.>-cons→hd>tl (>-cons es->-sorted e>head-es) ) )

      sub_prf₁ : All (_,_⊢_≥_ (l+s ● r ` loc) c (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂)))
                     (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁))
                                     (List.map (mk-snd-pdi (e , flat-[] e |e|≡[])) pdis₂ ++
                                                              concatMap (λ x → mk-snd-pdi x pdi₂ ∷ List.map (mk-snd-pdi x) pdis₂)
                                                                        (zip-es-flat-[]-es {l+s} {ε∈l+s} es flat-[]-es)))
      sub_prf₁ rewrite map-++ (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁)) (List.map (mk-snd-pdi (e , flat-[] e |e|≡[])) pdis₂) (concatMap (λ x → mk-snd-pdi x pdi₂ ∷ List.map (mk-snd-pdi x) pdis₂) (zip-es-flat-[]-es {l+s} {ε∈l+s} es flat-[]-es)) = sub_prf₃

      -- this sub lemma was given opus 4.6 to handle (I provided the type annotation and hints)
      -- it took 1 whole day (5 active hours) with 4 cooldown periods for opus 4.6
      sub_prf₂ : ( ps : List (PDInstance l+s c) )
               → All >-Inc ps
               → All (Inhabit p₁) ps
               → All (_,_⊢_≥_ l+s c pdi₁) ps
               → All (_,_⊢_≥_ (l+s ● r ` loc) c (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂)))
                     (concatMap (λ pdiˡ₁ → List.map (fuse {l+s ● r ` loc} {loc} pdiˡ₁) (concatMap (λ x → List.map (mk-snd-pdi x) (pdi₂ ∷ pdis₂))
                                                                                                  (zip-es-flat-[]-es {l+s} {ε∈l+s} (e ∷ es) (flat-[] e |e|≡[] ∷ flat-[]-es))))
                                   (List.map pdinstance-fst ps)) -- induction over ps
      sub_prf₂ [] [] [] [] = []
      sub_prf₂ (p@(pdinstance in₁' s-ev₁') ∷ ps') ((>-inc v₁→v₂→v₁>v₂→in₁'v₁>in₁'v₂) ∷ >-inc-ps') ((hide .{p₁} .{l+s} .{c} .(in₁') .(s-ev₁')) ∷ hide-ps') ((≥-pdi .(in₁) .(s-ev₁) .(in₁') .(s-ev₁') v₁→v₂→v₁>v₂→in₁v₁>in₁'v₂ v→in₁v≥in₁'v) ∷ pdi₁≥ps') =
        all-concat (per-p-proof all-snd-pdis
                                all->-inc-all-snd-pdis
                                all-flat-[]-fst-all-snd-pdis
                                all-hide-pdi₁
                                all-hide-p
                                (ex≥-refl >-inc-head-pdi ∷ sub_prf₁))
                   (sub_prf₂ ps' >-inc-ps' hide-ps' pdi₁≥ps')
        where
          all-snd-pdis : List (PDInstance (l+s ● r ` loc) c)
          all-snd-pdis = concatMap (λ x → List.map (mk-snd-pdi {l+s} {r} {loc} {c} x) (pdi₂ ∷ pdis₂))
                                   (zip-es-flat-[]-es {l+s} {ε∈l+s} (e ∷ es) (flat-[] e |e|≡[] ∷ flat-[]-es))

          >-inc-head-pdi : >-Inc (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂))
          >-inc-head-pdi = >-inc-fuse-fst-pdi-flat-[]-fst-pdi {l+s} {r} {ε∈l+s} {loc} {c}
                             pdi₁ (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂)
                             >-inc-pdi₁
                             (>-inc-mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂ >-inc-pdi₂)
                             (fst-flat-[] (mkinjSnd in₂ e) (mkinjSndSoundEv {p₂} {l+s} {r} {loc} {c} in₂ s-ev₂ e (flat-[] e |e|≡[])) (λ u → flat-[]-fst e (in₂ u) |e|≡[]))

          all-hide-p₂-all-snd-pdis : All (Inhabit p₂) all-snd-pdis
          all-hide-p₂-all-snd-pdis = aux (zip-es-flat-[]-es {l+s} {ε∈l+s} (e ∷ es) (flat-[] e |e|≡[] ∷ flat-[]-es))
            where
              aux : (xs : List (∃[ x ] Flat-[] l+s x))
                  → All (Inhabit p₂) (concatMap (λ x → List.map (mk-snd-pdi {l+s} {r} {loc} {c} x) (pdi₂ ∷ pdis₂)) xs)
              aux [] = []
              aux ((x , flat-[]-x) ∷ xs) = all-concat (map-snd-pdi-inhabit {l+s} {r} {p₂} {loc} {c} x flat-[]-x (pdi₂ ∷ pdis₂) ((hide in₂ s-ev₂) ∷ hide-p₂-pdis₂)) (aux xs)

          all-hide-pdi₁ : All (Inhabit ((p₁ ● r ` loc) + p₂ ` loc)) (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁)) all-snd-pdis)
          all-hide-pdi₁ = map-fuse-inhabit {l+s ● r ` loc} {p₁ ● r ` loc} {p₂} {loc} {c}
                            (pdinstance-fst pdi₁) all-snd-pdis
                            (hide (mkinjFst in₁) (mkinjFstSoundEv in₁ s-ev₁))
                            all-hide-p₂-all-snd-pdis

          all-hide-p : All (Inhabit ((p₁ ● r ` loc) + p₂ ` loc)) (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst p)) all-snd-pdis)
          all-hide-p = map-fuse-inhabit {l+s ● r ` loc} {p₁ ● r ` loc} {p₂} {loc} {c}
                         (pdinstance-fst p) all-snd-pdis
                         (hide (mkinjFst in₁') (mkinjFstSoundEv in₁' s-ev₁'))
                         all-hide-p₂-all-snd-pdis

          all->-inc-all-snd-pdis : All >-Inc all-snd-pdis
          all->-inc-all-snd-pdis = aux (zip-es-flat-[]-es {l+s} {ε∈l+s} (e ∷ es) (flat-[] e |e|≡[] ∷ flat-[]-es))
            where
              aux : (xs : List (∃[ x ] Flat-[] l+s x))
                  → All >-Inc (concatMap (λ x → List.map (mk-snd-pdi {l+s} {r} {loc} {c} x) (pdi₂ ∷ pdis₂)) xs)
              aux [] = []
              aux ((x , flat-[]-x) ∷ xs) = all-concat (>-inc-pdinstance-snd {l+s} {r} {ε∈l+s} {loc} {c} (x , flat-[]-x) (pdi₂ ∷ pdis₂) (>-inc-pdi₂ ∷ all->-inc-pdis₂)) (aux xs)

          all-flat-[]-fst-all-snd-pdis : All Flat-[]-Fst-PDI all-snd-pdis
          all-flat-[]-fst-all-snd-pdis = aux (zip-es-flat-[]-es {l+s} {ε∈l+s} (e ∷ es) (flat-[] e |e|≡[] ∷ flat-[]-es))
            where
              aux : (xs : List (∃[ x ] Flat-[] l+s x))
                  → All Flat-[]-Fst-PDI (concatMap (λ x → List.map (mk-snd-pdi {l+s} {r} {loc} {c} x) (pdi₂ ∷ pdis₂)) xs)
              aux [] = []
              aux ((x , flat-[]-x) ∷ xs) = all-concat (flat-[]-fst-pdinstance-snd {l+s} {r} {ε∈l+s} {loc} {c} (x , flat-[]-x) (pdi₂ ∷ pdis₂)) (aux xs)

          -- head ≥ fuse-pdi₁-snd ≥ fuse-p-snd, by transitivity for each snd-pdi
          per-p-proof : (snds : List (PDInstance (l+s ● r ` loc) c))
            → All >-Inc snds
            → All Flat-[]-Fst-PDI snds
            → All (Inhabit ((p₁ ● r ` loc) + p₂ ` loc)) (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁)) snds)
            → All (Inhabit ((p₁ ● r ` loc) + p₂ ` loc)) (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst p)) snds)
            → All (_,_⊢_≥_ (l+s ● r ` loc) c (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂)))
                  (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁)) snds)
            → All (_,_⊢_≥_ (l+s ● r ` loc) c (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂)))
                  (List.map (fuse {l+s ● r ` loc} {loc} (pdinstance-fst p)) snds)
          per-p-proof [] [] [] [] [] [] = []
          per-p-proof (snd ∷ snds') (>-inc-snd ∷ >-inc-snds') (flat-[]-fst-snd ∷ flat-[]-fst-snds') (hide-pdi₁-snd ∷ hides-pdi₁) (hide-p-snd ∷ hides-p) (head≥fuse-pdi₁-snd ∷ rest) =
            ex≥-trans { (l+s ● r ` loc) } { (p₁ ● r ` loc) + p₂ ` loc } {c}
                      { fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) (mk-snd-pdi (e , flat-[] e |e|≡[]) pdi₂) }
                      { fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) snd }
                      { fuse {l+s ● r ` loc} {loc} (pdinstance-fst p) snd }
                      { hide (mkfuseInj (mkinjFst in₁) (mkinjSnd in₂ e)) (mkfuseInjSoundEv (mkinjFst in₁) (mkinjSnd in₂ e) (mkinjFstSoundEv in₁ s-ev₁) (mkinjSndSoundEv {p₂} {l+s} {r} {loc} {c} in₂ s-ev₂ e (flat-[] e |e|≡[]))) }
                      { hide-pdi₁-snd }
                      { hide-p-snd }
                      head≥fuse-pdi₁-snd
                      (fuse-pdi₁-snd≥fuse-p-snd snd >-inc-snd flat-[]-fst-snd hide-pdi₁-snd hide-p-snd)
            ∷ per-p-proof snds' >-inc-snds' flat-[]-fst-snds' hides-pdi₁ hides-p rest
            where
              -- Changing fst from pdi₁ to p, same snd: fuse-pdi₁-snd ≥ fuse-p-snd
              fuse-pdi₁-snd≥fuse-p-snd : (snd-pdi : PDInstance (l+s ● r ` loc) c)
                → >-Inc snd-pdi
                → Flat-[]-Fst-PDI snd-pdi
                → Inhabit ((p₁ ● r ` loc) + p₂ ` loc) (fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) snd-pdi)
                → Inhabit ((p₁ ● r ` loc) + p₂ ` loc) (fuse {l+s ● r ` loc} {loc} (pdinstance-fst p) snd-pdi)
                → (l+s ● r ` loc) , c ⊢ fuse {l+s ● r ` loc} {loc} (pdinstance-fst pdi₁) snd-pdi ≥ fuse {l+s ● r ` loc} {loc} (pdinstance-fst p) snd-pdi
              fuse-pdi₁-snd≥fuse-p-snd (pdinstance snd-inj snd-sev)
                                        (>-inc snd-preserves)
                                        (fst-flat-[] .snd-inj .snd-sev fst-flat-[]-ev)
                                        (hide .(mkfuseInj (mkinjFst in₁) snd-inj) .(mkfuseInjSoundEv (mkinjFst in₁) snd-inj (mkinjFstSoundEv in₁ s-ev₁) snd-sev))
                                        (hide .(mkfuseInj (mkinjFst in₁') snd-inj) .(mkfuseInjSoundEv (mkinjFst in₁') snd-inj (mkinjFstSoundEv in₁' s-ev₁') snd-sev)) =
                ≥-pdi inject₁' soundEv₁' inject₂' soundEv₂' sub_sub_prf_strict sub_sub_prf_weak
                where
                  inject₁' : U ((p₁ ● r ` loc) + p₂ ` loc) → U (l+s ● r ` loc)
                  inject₁' = mkfuseInj (mkinjFst in₁) snd-inj
                  soundEv₁' : (u : U ((p₁ ● r ` loc) + p₂ ` loc)) → proj₁ (flat (inject₁' u)) ≡ c ∷ proj₁ (flat u)
                  soundEv₁' = mkfuseInjSoundEv (mkinjFst in₁) snd-inj (mkinjFstSoundEv in₁ s-ev₁) snd-sev
                  inject₂' : U ((p₁ ● r ` loc) + p₂ ` loc) → U (l+s ● r ` loc)
                  inject₂' = mkfuseInj (mkinjFst in₁') snd-inj
                  soundEv₂' : (u : U ((p₁ ● r ` loc) + p₂ ` loc)) → proj₁ (flat (inject₂' u)) ≡ c ∷ proj₁ (flat u)
                  soundEv₂' = mkfuseInjSoundEv (mkinjFst in₁') snd-inj (mkinjFstSoundEv in₁' s-ev₁') snd-sev

                  len-|in₁-u|≡len-|u|+1 : (u : U p₁) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
                  len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl
                  len-|in₁'-u|≡len-|u|+1 : (u : U p₁) → length (proj₁ (flat (in₁' u))) ≡ suc (length (proj₁ (flat u)))
                  len-|in₁'-u|≡len-|u|+1 u rewrite (s-ev₁' u) = refl
                  len-|inject₁'-u|≡len-|u|+1 : (u : U ((p₁ ● r ` loc) + p₂ ` loc)) → length (proj₁ (flat (inject₁' u))) ≡ suc (length (proj₁ (flat u)))
                  len-|inject₁'-u|≡len-|u|+1 u rewrite (soundEv₁' u) = refl
                  len-|inject₂'-u|≡len-|u|+1 : (u : U ((p₁ ● r ` loc) + p₂ ` loc)) → length (proj₁ (flat (inject₂' u))) ≡ suc (length (proj₁ (flat u)))
                  len-|inject₂'-u|≡len-|u|+1 u rewrite (soundEv₂' u) = refl

                  sub_sub_prf_weak : (v : U ((p₁ ● r ` loc) + p₂ ` loc)) →
                    (l+s ● r ` loc) ⊢ inject₁' v > inject₂' v ⊎ inject₁' v ≡ inject₂' v
                  sub_sub_prf_weak (LeftU (PairU u w)) with v→in₁v≥in₁'v u
                  ... | inj₂ in₁u≡in₁'u = inj₂ (cong (λ x → PairU x w) in₁u≡in₁'u)
                  ... | inj₁ in₁u>in₁'u = inj₁ (len-≡ len-eq (seq₁ in₁u>in₁'u))
                    where
                      len-eq : length (proj₁ (flat (PairU {l+s} {r} {loc} (in₁ u) w))) ≡ length (proj₁ (flat (PairU {l+s} {r} {loc} (in₁' u) w)))
                      len-eq rewrite s-ev₁ u | s-ev₁' u = refl
                  sub_sub_prf_weak (RightU u) = inj₂ refl

                  in₁-preserves : (u₁ u₂ : U p₁) → p₁ ⊢ u₁ > u₂ → l+s ⊢ in₁ u₁ > in₁' u₂
                  in₁-preserves = v₁→v₂→v₁>v₂→in₁v₁>in₁'v₂

                  sub_sub_prf_strict : (v₁ v₂ : U ((p₁ ● r ` loc) + p₂ ` loc)) →
                    ((p₁ ● r ` loc) + p₂ ` loc) ⊢ v₁ > v₂ →
                    (l+s ● r ` loc) ⊢ inject₁' v₁ > inject₂' v₂
                  sub_sub_prf_strict v₁ v₂ (len-> len|v₁|>len|v₂|) = len-> len|inject₁'v₁|>len|inject₂'v₂|
                    where
                      len|inject₁'v₁|>len|inject₂'v₂| : length (proj₁ (flat (inject₁' v₁))) Nat.> length (proj₁ (flat (inject₂' v₂)))
                      len|inject₁'v₁|>len|inject₂'v₂| rewrite len-|inject₁'-u|≡len-|u|+1 v₁ | len-|inject₂'-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|
                  sub_sub_prf_strict (LeftU (PairU u₁ w₁)) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-ll (len-> len|pair₁|>len|pair₂|))) rewrite len|v₁|≡len|v₂| = Nullary.contradiction len|pair₁|>len|pair₂| (<-irrefl refl)
                  sub_sub_prf_strict (LeftU (PairU u₁ w₁)) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-ll (len-≡ len|pair₁|≡len|pair₂| (seq₁ u₁>u₂)))) = len-≡ len|inject₁'v₁|≡len|inject₂'v₂| (seq₁ (in₁-preserves u₁ u₂ u₁>u₂))
                    where
                      len|inject₁'v₁|≡len|inject₂'v₂| : length (proj₁ (flat (inject₁' (LeftU (PairU u₁ w₁))))) ≡ length (proj₁ (flat (inject₂' (LeftU (PairU u₂ w₂)))))
                      len|inject₁'v₁|≡len|inject₂'v₂| rewrite len-|inject₁'-u|≡len-|u|+1 (LeftU (PairU u₁ w₁)) | len-|inject₂'-u|≡len-|u|+1 (LeftU (PairU u₂ w₂)) | len|v₁|≡len|v₂| = refl
                  sub_sub_prf_strict (LeftU (PairU u₁ w₁)) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-ll (len-≡ len|pair₁|≡len|pair₂| (seq₂ u₁≡u₂ w₁>w₂)))) with v→in₁v≥in₁'v u₂
                  ... | inj₂ in₁u₂≡in₁'u₂ rewrite u₁≡u₂ = len-≡ len|inject₁'v₁|≡len|inject₂'v₂| (seq₂ in₁u₂≡in₁'u₂ w₁>w₂)
                    where
                      len|inject₁'v₁|≡len|inject₂'v₂| : length (proj₁ (flat (inject₁' (LeftU (PairU u₂ w₁))))) ≡ length (proj₁ (flat (inject₂' (LeftU (PairU u₂ w₂)))))
                      len|inject₁'v₁|≡len|inject₂'v₂| rewrite len-|inject₁'-u|≡len-|u|+1 (LeftU (PairU u₂ w₁)) | len-|inject₂'-u|≡len-|u|+1 (LeftU (PairU u₂ w₂)) | len|v₁|≡len|v₂| = refl
                  ... | inj₁ in₁u₂>in₁'u₂ rewrite u₁≡u₂ = len-≡ len|inject₁'v₁|≡len|inject₂'v₂| (seq₁ in₁u₂>in₁'u₂)
                    where
                      len|inject₁'v₁|≡len|inject₂'v₂| : length (proj₁ (flat (inject₁' (LeftU (PairU u₂ w₁))))) ≡ length (proj₁ (flat (inject₂' (LeftU (PairU u₂ w₂)))))
                      len|inject₁'v₁|≡len|inject₂'v₂| rewrite len-|inject₁'-u|≡len-|u|+1 (LeftU (PairU u₂ w₁)) | len-|inject₂'-u|≡len-|u|+1 (LeftU (PairU u₂ w₂)) | len|v₁|≡len|v₂| = refl
                  sub_sub_prf_strict (LeftU (PairU u₁ w₁)) (RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-lr len|pair₁|≥len|u₂|)) with snd-inj u₂ | fst-flat-[]-ev u₂ | snd-sev u₂
                  ... | PairU a b | flat-[]-fst .a .b |a|≡[] | snd-sev-u₂ = len-≡ len-eq (seq₁ (len-> len|in₁u₁|>len|a|))
                    where
                      len-eq : length (proj₁ (flat (PairU {l+s} {r} {loc} (in₁ u₁) w₁))) ≡ length (proj₁ (flat (PairU {l+s} {r} {loc} a b)))
                      len-eq rewrite s-ev₁ u₁ | snd-sev-u₂ | len|v₁|≡len|v₂| = refl
                      len|in₁u₁|>len|a| : length (proj₁ (flat (in₁ u₁))) Nat.> length (proj₁ (flat a))
                      len|in₁u₁|>len|a| rewrite |a|≡[] | len-|in₁-u|≡len-|u|+1 u₁ = Nat.s≤s Nat.z≤n
                  sub_sub_prf_strict (RightU u₁) (RightU u₂) (len-≡ len|v₁|≡len|v₂| (choice-rr u₁>u₂)) = snd-preserves u₁ u₂ u₁>u₂
                  sub_sub_prf_strict (RightU u₁) (LeftU (PairU u₂ w₂)) (len-≡ len|v₁|≡len|v₂| (choice-rl len|u₁|>len|pair₂|)) rewrite len|v₁|≡len|v₂| = Nullary.contradiction len|u₁|>len|pair₂| (<-irrefl refl)



map-star-lattice : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  → (pdis : List ( PDInstance r c ) )
  → Ex≥-lattice {r} {c} pdis
  → All >-Inc pdis
  → Homogenous pdis
  --------------------------------------------------------------------------  
  → Ex≥-lattice (List.map (pdinstance-star {r} {ε∉r} {loc}) pdis)
map-star-lattice {r} {ε∉r} {loc} {c} []           ex-empty [] _ = ex-empty
map-star-lattice {r} {ε∉r} {loc} {c} (pdi@(pdinstance in₁ s-ev₁) ∷ pdis) (ex-join .(pdi) .(pdis) pdi≥pdis) ((>-inc v₁→v₂→v₁>v₂→in₁v₁>in₂v₂) ∷ all->-inc-pdis) (homogenous (.(pdi) ∷ .(pdis)) ( p , ((hide .(in₁) .(s-ev₁)) ∷ hide-p-pdis ) ) ) = ex-join (pdinstance-star (pdinstance in₁ s-ev₁)) (List.map pdinstance-star pdis) (prf pdis hide-p-pdis pdi≥pdis )  
  where
    inject₁ :  U ( p ● (r * ε∉r ` loc ) ` loc )  → U (r * ε∉r ` loc )
    inject₁ =  mkinjList in₁
    soundEv₁ : ( u : U ( p ● (r * ε∉r ` loc ) ` loc ) ) → ( proj₁ (flat (inject₁ u ) )  ≡ c ∷ (proj₁ (flat u)))
    soundEv₁ = mkinjListSoundEv in₁ s-ev₁

    len-|in₁-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₁ u))) ≡ suc (length (proj₁ (flat u)))
    len-|in₁-u|≡len-|u|+1 u rewrite (s-ev₁ u) = refl

    len-|inject₁-u|≡len-|u|+1 : (u : U  ( p ● (r * ε∉r ` loc ) ` loc) ) → length (proj₁ (flat (inject₁ u))) ≡ suc (length (proj₁ (flat u)))
    len-|inject₁-u|≡len-|u|+1 u rewrite (soundEv₁ u) = refl 

    prf : ( qdis : (List (PDInstance r c) ) )
        → All (Inhabit p) qdis
        → All (_,_⊢_≥_ r c (pdinstance in₁ s-ev₁)) qdis 
        → All (_,_⊢_≥_ (r * ε∉r ` loc) c (pdinstance inject₁ soundEv₁)) (List.map pdinstance-star qdis)
    prf [] [] [] = []
    prf (qdi@(pdinstance in₂ s-ev₂) ∷ qdis ) ((hide .(in₂) .(s-ev₂)) ∷ hide-p-qdis)  ((≥-pdi .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v ) ∷ pdi≥qdis) =  ≥-pdi inject₁ soundEv₁ inject₂ soundEv₂ prf₁ prf₂  ∷ prf qdis hide-p-qdis pdi≥qdis
      where
        inject₂ :  U ( p ● (r * ε∉r ` loc ) ` loc )  → U (r * ε∉r ` loc )
        inject₂ =  mkinjList in₂
        soundEv₂ : ( u : U ( p ● (r * ε∉r ` loc ) ` loc ) ) → ( proj₁ (flat (inject₂ u ) )  ≡ c ∷ (proj₁ (flat u)))
        soundEv₂ = mkinjListSoundEv in₂ s-ev₂


        len-|in₂-u|≡len-|u|+1 : (u : U p) → length (proj₁ (flat (in₂ u))) ≡ suc (length (proj₁ (flat u)))
        len-|in₂-u|≡len-|u|+1 u rewrite (s-ev₂ u) = refl 

        |in₁-u|≡|in₂-u| : (u : U p) →  (proj₁ (flat (in₁ u))) ≡  (proj₁ (flat (in₂ u)))
        |in₁-u|≡|in₂-u| u rewrite (s-ev₁ u) | (s-ev₂ u) = refl 


        len-|inject₂-u|≡len-|u|+1 : (u : U  ( p ● (r * ε∉r ` loc ) ` loc )  ) → length (proj₁ (flat (inject₂ u))) ≡ suc (length (proj₁ (flat u)))
        len-|inject₂-u|≡len-|u|+1 u rewrite (soundEv₂ u) = refl

        prf₂ : (v : U (p ● r * ε∉r ` loc ` loc)) →
               (r * ε∉r ` loc) ⊢ inject₁ v > inject₂ v ⊎ inject₁ v ≡ inject₂ v
        prf₂ v@(PairU u (ListU us)) with v→in₁v≥in₂v u
        ... | inj₂ in₁u≡in₂u = inj₂ (cong (λ x → ListU ( x ∷ us )) in₁u≡in₂u )
        ... | inj₁ in₁u>in₂u = inj₁ (len-≡ len-|list-in₁-u-us|≡len-|list-in₂-u-us| (star-head in₁u>in₂u) ) 
          where
            len-|list-in₁-u-us|≡len-|list-in₂-u-us| : length (proj₁ (flat (inject₁ v ))) ≡ length (proj₁ (flat (inject₂ v )))
            len-|list-in₁-u-us|≡len-|list-in₂-u-us| rewrite len-|in₁-u|≡len-|u|+1 u | len-|in₂-u|≡len-|u|+1 u |  |in₁-u|≡|in₂-u| u = refl
        prf₁ :  (v₁ v₂ : U (p ● r * ε∉r ` loc ` loc))
             →  (p ● r * ε∉r ` loc ` loc) ⊢ v₁ > v₂
             →  (r * ε∉r ` loc) ⊢ inject₁ v₁ > inject₂ v₂
        prf₁ v₁@(PairU u₁ (ListU us₁)) v₂@(PairU u₂ (ListU us₂)) (len-> len|v₁|>len|v₂|) = len-> len|inject₁v₁|>len|inject₂v₂| 
          where
            len|inject₁v₁|>len|inject₂v₂| : length (proj₁ (flat (inject₁ v₁))) Nat.> length (proj₁ (flat (inject₂ v₂)))
            len|inject₁v₁|>len|inject₂v₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ |  len-|inject₂-u|≡len-|u|+1 v₂ = Nat.s≤s len|v₁|>len|v₂|

        prf₁ v₁@(PairU u₁ (ListU us₁)) v₂@(PairU u₂ (ListU us₂)) (len-≡ len|v₁|≡len|v₂| (seq₁ u₁>u₂)) = len-≡ len-|list-in₁-u₁-us₁|≡len-|list-in₂-u₂-us₂| (star-head (v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ u₁ u₂ u₁>u₂))  
          where
            len-|list-in₁-u₁-us₁|≡len-|list-in₂-u₂-us₂| : length (proj₁ (flat (inject₁ v₁ ))) ≡ length (proj₁ (flat (inject₂ v₂ )))
            len-|list-in₁-u₁-us₁|≡len-|list-in₂-u₂-us₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ | len-|inject₂-u|≡len-|u|+1 v₂ | len|v₁|≡len|v₂| = refl
        prf₁ v₁@(PairU u₁ (ListU us₁)) v₂@(PairU u₂ (ListU us₂)) (len-≡ len|v₁|≡len|v₂| (seq₂ u₁≡u₂ list-us₁>list-us₂)) = len-≡ len-|list-in₁-u₁-us₁|≡len-|list-in₂-u₂-us₂| inject₁v₁>ⁱinject₂v₂
          where
            len-|list-in₁-u₁-us₁|≡len-|list-in₂-u₂-us₂| : length (proj₁ (flat (inject₁ v₁ ))) ≡ length (proj₁ (flat (inject₂ v₂ )))
            len-|list-in₁-u₁-us₁|≡len-|list-in₂-u₂-us₂| rewrite len-|inject₁-u|≡len-|u|+1 v₁ | len-|inject₂-u|≡len-|u|+1 v₂ | len|v₁|≡len|v₂| = refl
            inject₁v₁>ⁱinject₂v₂ :  (r * ε∉r ` loc) ⊢  ListU ((in₁ u₁) ∷  us₁)  >ⁱ ListU ( (in₂ u₂) ∷ us₂)
            inject₁v₁>ⁱinject₂v₂ rewrite u₁≡u₂ with v→in₁v≥in₂v u₂
            ... | inj₁ in₁u₂>in₂u₂ = star-head in₁u₂>in₂u₂
            ... | inj₂ in₁u₂≡in₂u₂ = star-tail in₁u₂≡in₂u₂ list-us₁>list-us₂ 

-- main lemma: 
pdU-ex-lattice : ∀ { r : RE } { c : Char }
  → Ex≥-lattice {r} {c} pdU[ r , c ]
pdU-ex-lattice {ε} {c} = ex-empty 
pdU-ex-lattice {$ c ` loc } {c'} with c Char.≟ c'
...                              | no _ = ex-empty
...                              | yes refl = ex-join pdi [] []
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
pdU-ex-lattice {l + r ` loc } {c} =   oplus-+-ex-lattice pdU[ l , c ] pdU[ r , c ] ind-hyp-l ind-hyp-r (pdU->-inc {l} {c}) (pdU->-inc {r} {c}) (pdU-Homogenous {l} {c}) (pdU-Homogenous {r} {c}) 
  where
    ind-hyp-l : Ex≥-lattice pdU[ l , c ]
    ind-hyp-l = pdU-ex-lattice {l} {c}
    ind-hyp-r : Ex≥-lattice pdU[ r , c ]
    ind-hyp-r = pdU-ex-lattice {r} {c}  

pdU-ex-lattice {l ● r ` loc } {c} with ε∈? l
... | no ¬ε∈l = map-fst-ex-lattice  pdU[ l , c ] ind-hyp-l 
  where
    ind-hyp-l : Ex≥-lattice pdU[ l , c ]
    ind-hyp-l = pdU-ex-lattice {l} {c}
... | yes ε∈l = oplus-+●-ex-lattice pdU[ l , c ] pdU[ r , c ]  ind-hyp-l ind-hyp-r (pdU->-inc {l} {c}) (pdU->-inc {r} {c}) (pdU-Homogenous {l} {c}) (pdU-Homogenous {r} {c}) 
  where
    ind-hyp-l : Ex≥-lattice pdU[ l , c ]
    ind-hyp-l = pdU-ex-lattice {l} {c}
    ind-hyp-r : Ex≥-lattice pdU[ r , c ]
    ind-hyp-r = pdU-ex-lattice {r} {c}
pdU-ex-lattice {r * ε∉r ` loc } {c} = map-star-lattice  pdU[ r , c ] ind-hyp-r (pdU->-inc {r} {c}) (pdU-Homogenous {r} {c})
  where
    ind-hyp-r : Ex≥-lattice pdU[ r , c ]
    ind-hyp-r = pdU-ex-lattice {r} {c}
  
```








### Definition 39 : (Extended) Posix ordering among PDInstance*'s 


Let r be a non problematic regular expression.

Let w be a word.

Let pdi₁ and pdi₂ be two partial derivative descendant instances of r w.r.t w.

We say pdi₁ is POSIX  greater than pdi₂, r , w  ⊢* pdi₁ ≥ pdi₂ iff
  for all parse trees u₁ u₂  of r, u₁ is constructable from pdi₁ and u₂ is constructabled from pdi₂ 
    then r ⊢ u₁ ≥ u₂ 

```agda

data _,_⊢*_≥_ : ∀ ( r : RE ) → (w : List Char ) → PDInstance* r w → PDInstance* r w → Set where
  *≥-pdi : ∀ { r p : RE } { w : List Char }
    → ( injection₁ : U p → U r )
    → ( s-ev₁ : ∀ ( u : U p ) → (proj₁ ( flat {r} (injection₁ u)) ≡ w ++ (proj₁ (flat {p} u))) )
    → ( injection₂ : U p → U r )
    → ( s-ev₂ : ∀ ( u : U p ) → (proj₁ ( flat {r} (injection₂ u)) ≡ w ++ (proj₁ (flat {p} u))) )
    → ( ∀ ( v₁ : U p )
        → ( v₂ : U p ) 
        → p ⊢ v₁ > v₂ 
        → r ⊢ injection₁ v₁ > injection₂ v₂ )
    → ( ∀ ( v : U p ) → ( r ⊢ injection₁ v > injection₂ v ) ⊎ (injection₁ v ≡ injection₂ v ) ) -- ? strict inc? 
   → r , w ⊢* (pdinstance* {p} {r} {w} injection₁ s-ev₁) ≥ (pdinstance* {p} {r} {w} injection₂ s-ev₂)

```


```agda

data Ex*≥-maybe : ∀ { r : RE } { w : List Char } ( pdi : PDInstance* r w ) → ( mpdi : Maybe (PDInstance* r w) ) → Set where
  ex*≥-nothing : ∀ { r : RE } { w : List Char }
    → { pdi : PDInstance* r w } 
    ---------------------------
    → Ex*≥-maybe {r} {w} pdi nothing
  ex*≥-just : ∀ { r : RE } { w : List Char }
    → { pdi : PDInstance* r w }
    → { pdi' : PDInstance* r w }
    → r , w ⊢* pdi ≥ pdi' 
    ----------------------------------
    → Ex*≥-maybe {r} {w} pdi (just pdi')

data Ex*≥-maybe₂ : ∀ { r : RE } { w : List Char } ( mpdi : Maybe (PDInstance* r w )) → ( mpdi' : Maybe (PDInstance* r w) ) → Set where
  ex*≥-nothingʳ : ∀ { r : RE } { w : List Char }
    → { pdi : PDInstance* r w } 
    ---------------------------
    → Ex*≥-maybe₂ {r} {w} (just pdi) nothing
  ex*≥-nothingˡ : ∀ { r : RE } { w : List Char }
    → { pdi : PDInstance* r w } 
    ---------------------------
    → Ex*≥-maybe₂ {r} {w} nothing (just pdi)

  ex*≥-nothing₂ : ∀ { r : RE } { w : List Char }
    ---------------------------
    → Ex*≥-maybe₂ {r} {w} nothing nothing

  ex*≥-just₂ : ∀ { r : RE } { w : List Char }
    → { pdi : PDInstance* r w }
    → { pdi' : PDInstance* r w }
    → r , w ⊢* pdi ≥ pdi' 
    ----------------------------------
    → Ex*≥-maybe₂ {r} {w} (just pdi )(just pdi')


```


### Lemma 40: the list of pdinstance*s from pdUMany[ r , w] is a complete lattice over the partial order r , w ⊢*_≥_  


Let r be a non problematic regular expression.

Let w be a word.

Then pdUMany[r , w] is complete lattice. 

```agda
data Ex*≥-lattice : ∀ { r : RE } { w : List Char } (pdis : List (PDInstance* r w) ) → Set where
  ex*-empty :  ∀ { r : RE } { w : List Char } → Ex*≥-lattice {r} {w} []
  ex*-join :  ∀ { r : RE } { w : List Char }
    → ( top : PDInstance* r w )
    → ( pdis : List (PDInstance* r w ) )
    →  All ( λ x → r , w ⊢* top ≥ x ) pdis   -- top is the join
    -----------------------------------------
    → Ex*≥-lattice {r} {w} (top ∷ pdis )

data Inhabit* : ∀ { r : RE } { w : List Char } → RE → PDInstance* r w → Set where
  hide* : ∀ { p r : RE } { w : List Char }
    → ( inj : U p → U r ) -- ^ the injection function
    → ( s-ev : ∀ ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ w ++ ( proj₁ (flat {p} u) )) )  -- ^ soundnes evidence
    → Inhabit* {r} {w} p (pdinstance* {p} {r} {w} inj s-ev) 


-- a list of pdinstance*s is homogenous iff all of them are hiding the same pd.
data Homogenous* : ∀ { r : RE } { w : List Char } → List (PDInstance* r w) → Set where
  homogenous* : ∀ { r : RE } { w : List Char } (pdis : List (PDInstance* r w ) )
    → ∃[ p ] (All (Inhabit* p) pdis)
    → Homogenous* {r} {w} pdis 

```



### Lemma 41: the list of pdinstance*'s from pdUMany[ r , c] is a lattice in extended POSIX order


Let r be a non problematic regular expression.

Let w be a word.

Then pdUMany[r , w] is a lattice in extended POSIX order. 


#### Sub Lemma 41.1 - 41.6 : Ex*>-lattice is inductively preserved over pdinstance*'s operations 

```agda
-------------------------------------------------------------
-- Sub Lemma 41.1 - 41.6 BEGIN
-------------------------------------------------------------

-- reflexivity
ex*≥-refl : ∀ { r : RE } { w : List Char } { pd : PDInstance* r w }
  → *>-Inc pd 
  → r , w ⊢* pd ≥ pd
ex*≥-refl  {r} {w} {pdinstance* {p} .{r} .{w} in₁ s-ev₁} (*>-inc v₁→v₂→v₁>v₂→in₁v₁>in₁v₂)  = *≥-pdi {r} {p} {w}  in₁ s-ev₁ in₁ s-ev₁ v₁→v₂→v₁>v₂→in₁v₁>in₁v₂ λ v → inj₂ refl 

-- transitivity
ex*≥-trans : ∀ { r p : RE } { w : List Char } { pd₁ pd₂ pd₃ : PDInstance* r w  }
  { i₁ : Inhabit* {r} {w} p pd₁ } 
  { i₂ : Inhabit* {r} {w} p pd₂ } 
  { i₃ : Inhabit* {r} {w} p pd₃ }
  → r , w ⊢* pd₁ ≥ pd₂
  → r , w ⊢* pd₂ ≥ pd₃
  -------------------
  → r , w ⊢* pd₁ ≥ pd₃
ex*≥-trans {r} {p} {w}
          {pdinstance* in₁ s-ev₁} {pdinstance* in₂ s-ev₂} {pdinstance* in₃ s-ev₃}
          {hide* .(in₁) .(s-ev₁)}
          {hide* .(in₂) .(s-ev₂)}
          {hide* .(in₃) .(s-ev₃)}
          (*≥-pdi .{r} .{p} .{w} .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v→in₁v>in₂v⊎in₁v≡in₂v )
          (*≥-pdi .{r} .{p} .{w} .(in₂) .(s-ev₂) .(in₃) .(s-ev₃) v₂→v₃→v₂>v₃→in₂v₂>in₃v₃ v→in₂v>in₃v⊎in₂v≡in₃v ) =
          *≥-pdi {r} {p} {w} in₁ s-ev₁ in₃ s-ev₃ prf₁ prf₂
          where
            prf₂ :  (v : U p) → r ⊢ in₁ v > in₃ v ⊎ in₁ v ≡ in₃ v
            prf₂ v with v→in₁v>in₂v⊎in₁v≡in₂v v  | v→in₂v>in₃v⊎in₂v≡in₃v v 
            ... | inj₁ in₁v>in₂v₁ | inj₁ in₂v₁>in₃v₁ = inj₁ (>-trans in₁v>in₂v₁ in₂v₁>in₃v₁)
            ... | inj₁ in₁v>in₂v₁ | inj₂ in₂v₁≡in₃v₁ rewrite sym in₂v₁≡in₃v₁ = inj₁ in₁v>in₂v₁
            ... | inj₂ in₁v≡in₂v₁ | inj₂ in₂v₁≡in₃v₁ rewrite sym in₂v₁≡in₃v₁ = inj₂ in₁v≡in₂v₁
            ... | inj₂ in₁v≡in₂v₁ | inj₁ in₂v₁>in₃v₁ rewrite in₁v≡in₂v₁ = inj₁ in₂v₁>in₃v₁ 
            prf₁ : (v₁ v₃ : U p) → p ⊢ v₁ > v₃ → r ⊢ in₁ v₁ > in₃ v₃
            prf₁ v₁ v₃ v₁>v₃ with v→in₁v>in₂v⊎in₁v≡in₂v v₁
            ... | inj₁ in₁v₁>in₂v₁ = >-trans in₁v₁>in₂v₁ (v₂→v₃→v₂>v₃→in₂v₂>in₃v₃ v₁ v₃ v₁>v₃)
            ... | inj₂ in₁v₁≡in₂v₁ rewrite  in₁v₁≡in₂v₁ = v₂→v₃→v₂>v₃→in₂v₂>in₃v₃ v₁ v₃ v₁>v₃ 


ex*≥-trans-map : ∀ { r p : RE } { w : List Char } { pd₁ pd₂ : PDInstance* r w }
  { pds₃ : List (PDInstance* r w) }
  { i₁ : Inhabit* {r} {w} p pd₁ } 
  { i₂ : Inhabit* {r} {w} p pd₂ } 
  { is₃ : All (Inhabit* {r} {w} p) pds₃ }
  → r , w ⊢* pd₁ ≥ pd₂
  → All (_,_⊢*_≥_ r w pd₂)  pds₃
  ---------------------------------------
  → All (_,_⊢*_≥_ r w pd₁)  pds₃
ex*≥-trans-map pd₁≥pd₂ [] = []
ex*≥-trans-map {r} {p} {w} {pd₁} {pd₂} {pd₃ ∷ pds₃} {i₁} {i₂} {i₃ ∷ is₃} pd₁≥pd₂ (pd₂≥pd₃ ∷ pd₂≥pds₃) = ex*≥-trans {r} {p} {w} {pd₁} {pd₂} {pd₃} {i₁} {i₂} {i₃}  pd₁≥pd₂ pd₂≥pd₃ ∷  ex*≥-trans-map {r} {p} {w} {pd₁} {pd₂} {pds₃} {i₁} {i₂} {is₃}  pd₁≥pd₂ pd₂≥pds₃ 
  


concat-ex*-lattice : ∀ { r p : RE } { w : List Char }
    → ( pdis₁ : List ( PDInstance* r w ))
    → ( pdis₂ : List ( PDInstance* r w ))
    → Ex*≥-lattice { r } { w } pdis₁
    → Ex*≥-lattice { r } { w } pdis₂
    → All (Inhabit* {r} {w} p) pdis₁
    → All (Inhabit* {r} {w} p) pdis₂    
    → Ex*≥-maybe₂  {r} {w} (head pdis₁) (head pdis₂)
    -------------------------------------------------------
    → Ex*≥-lattice { r } {w}  (pdis₁ ++ pdis₂)
concat-ex*-lattice []    pdis₂   ex*-empty  ex*-lattice-pdi₂ _ _ _ = ex*-lattice-pdi₂
concat-ex*-lattice pdis₁ []      ex*-lattice-pdi₁ ex*-empty  _ _  _ rewrite  (++-identityʳ pdis₁) = ex*-lattice-pdi₁
concat-ex*-lattice {r} {p} {w} (pdi₁ ∷ pdis₁) (pdi₂ ∷ pdis₂) (ex*-join .(pdi₁) .(pdis₁) all-pdi₁≥pdis₁ ) (ex*-join .(pdi₂) .(pdis₂) all-pdi₂≥pdis₂ ) (i₁ ∷ is₁) (i₂ ∷ is₂ ) (ex*≥-just₂ pdi₁≥pdi₂)
  = ex*-join pdi₁ (pdis₁ ++ pdi₂ ∷ pdis₂)  (all-concat all-pdi₁≥pdis₁ (pdi₁≥pdi₂ ∷ ex*≥-trans-map {r} {p} {w} {pdi₁} {pdi₂} {pdis₂} {i₁} {i₂} {is₂} pdi₁≥pdi₂ all-pdi₂≥pdis₂ ) ) 


compose-pdi-with-ex*≥-map-compose-pdi-with : ∀ { p d r : RE } { pref : List Char} { c : Char }
  → ( d→r : U d → U r )
  → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → ( >-inc-d→r :  (v₁ v₂ : U d) → d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂ ) -- strict inc evidence for d→r
  → ( pdi : PDInstance d c )
  → ( pdis : List (PDInstance d c) )
  → Inhabit p pdi
  → All (Inhabit p) pdis 
  → All (_,_⊢_≥_ d c pdi) pdis 
  -------------------------------------------------------------------------------------------------
  → All (_,_⊢*_≥_ r (pref ∷ʳ c) (compose-pdi-with d→r s-ev-d-r pdi)) (List.map (compose-pdi-with d→r s-ev-d-r) pdis)
compose-pdi-with-ex*≥-map-compose-pdi-with  {p} {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r pdi [] hide-p-pdi [] [] = []
compose-pdi-with-ex*≥-map-compose-pdi-with  {p} {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r
  pdi₁@(pdinstance .{p} .{d} .{c} in₁ s-ev₁)
  (pdi₂@(pdinstance .{p} .{d} .{c} in₂ s-ev₂) ∷ pdis )
  (hide .(in₁) .(s-ev₁)) ((hide .(in₂) .(s-ev₂)) ∷ hide-p-pdis) 
  ( (≥-pdi .(in₁) .(s-ev₁) .(in₂) .(s-ev₂) v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v→in₁v≥in₂v )  ∷ pdi₁≥pdis₂) =
   prf ∷  compose-pdi-with-ex*≥-map-compose-pdi-with {p} {d} {r}  d→r s-ev-d-r >-inc-d→r
           (pdinstance in₁ s-ev₁) pdis (hide in₁ s-ev₁) hide-p-pdis  pdi₁≥pdis₂  
  where
    inject₁ : U p → U r
    inject₁ = d→r ∘ in₁
    inject₂ : U p → U r
    inject₂ = d→r ∘ in₂
    soundEv₁ : (u : U p) → proj₁ (flat (inject₁ u )) ≡  pref ∷ʳ c ++ proj₁ (flat u)
    soundEv₁ = compose-pdi-with-soundEv  d→r s-ev-d-r in₁ s-ev₁ 
    soundEv₂ : (u : U p) → proj₁ (flat (inject₂ u )) ≡  pref ∷ʳ c ++ proj₁ (flat u)
    soundEv₂ = compose-pdi-with-soundEv  d→r s-ev-d-r in₂ s-ev₂

    len-|inject₁-u|≡len-pref-c++|u| : (u : U  p )
      → length (proj₁ (flat (inject₁ u))) ≡ length ((pref ∷ʳ c) ++ (proj₁ (flat u))) 
    len-|inject₁-u|≡len-pref-c++|u| u rewrite (soundEv₁ u) = refl 

    len-|inject₂-u|≡len-pref-c++|u| : (u : U  p )
      → length (proj₁ (flat (inject₂ u))) ≡ length ((pref ∷ʳ c) ++ (proj₁ (flat u))) 
    len-|inject₂-u|≡len-pref-c++|u| u rewrite (soundEv₂ u) = refl 
    -- prf :  r , pref ∷ʳ c ⊢*  compose-pdi-with d→r s-ev-d-r (pdinstance in₁ s-ev₁) ≥ compose-pdi-with d→r s-ev-d-r (pdinstance in₂ s-ev₂)
    prf :  r , (pref ∷ʳ c) ⊢*  pdinstance* inject₁ soundEv₁ ≥ pdinstance* inject₂ soundEv₂ 
    prf = *≥-pdi {r} {p} {(pref ∷ʳ c)} inject₁ soundEv₁  inject₂ soundEv₂  (λ v₁ v₂ z →
                                                                               >-inc-d→r (in₁ v₁) (in₂ v₂) (v₁→v₂→v₁>v₂→in₁v₁>in₂v₂ v₁ v₂ z)) sub_prf₂
      where
        sub_prf₂ : (v : U p) → r ⊢ inject₁ v > inject₂ v ⊎ inject₁ v ≡ inject₂ v
        sub_prf₂ v with v→in₁v≥in₂v v 
        ... | inj₂ in₁v≣in₂v = inj₂ (cong d→r in₁v≣in₂v )
        ... | inj₁ in₁v>in₁v = inj₁ (>-inc-d→r (in₁ v) (in₂ v) in₁v>in₁v) 

-- do we need this? 
map-compose-pdi-with-lattice : ∀ { p d r : RE } { pref : List Char} { c : Char }
  → ( d→r : U d → U r )
  → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → ( >-inc-d→r :  (v₁ v₂ : U d) → d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂ ) -- strict inc evidence for d→r  
  → ( pdis : List (PDInstance d c) )
  → All (Inhabit p) pdis
  → Ex≥-lattice pdis
  -------------------------------------------------------------
  → Ex*≥-lattice {r}  (List.map (compose-pdi-with d→r s-ev-d-r) pdis )
map-compose-pdi-with-lattice {p} {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r []           []  ex-empty = ex*-empty
map-compose-pdi-with-lattice {p} {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r (pdi ∷ pdis) (hide-p-pdi ∷ hide-p-pdis)  (ex-join .(pdi) .(pdis) pdi≥pdis) =  ex*-join (compose-pdi-with d→r s-ev-d-r pdi) (List.map (compose-pdi-with d→r s-ev-d-r) pdis) prf
  where
    prf :  All (_,_⊢*_≥_ r (pref ∷ʳ c) (compose-pdi-with d→r s-ev-d-r pdi))
           (List.map (compose-pdi-with d→r s-ev-d-r) pdis)
    prf = compose-pdi-with-ex*≥-map-compose-pdi-with  d→r s-ev-d-r >-inc-d→r pdi pdis hide-p-pdi hide-p-pdis pdi≥pdis  


advance-pdi*-with-c-lattice : ∀ { r : RE } { pref : List Char} { c : Char }
  → (pdi : PDInstance* r pref)
  → *>-Inc pdi
  ----------------------------------------------------------
  → Ex*≥-lattice (advance-pdi*-with-c {r} {pref} {c} pdi)
advance-pdi*-with-c-lattice {r} {pref} {c}  pdi@(pdinstance* {d} {r} {pref} d→r s-ev-d-r) (*>-inc d→r-inc-ev) 
  with pdU[ d , c ]    | pdU-ex-lattice { d } {c}         | pdU-Homogenous {d } {c} 
... | []               | _                                | _  = ex*-empty
... | (pdi ∷ pdis )    | ex-join  .(pdi) .(pdis) pdi≥pdis | homogenous _ ( p , hide-p-pdi ∷ hide-p-pdis) = ex*-join (compose-pdi-with d→r s-ev-d-r pdi) (List.map (compose-pdi-with d→r s-ev-d-r) pdis) (compose-pdi-with-ex*≥-map-compose-pdi-with  d→r s-ev-d-r d→r-inc-ev pdi pdis hide-p-pdi hide-p-pdis pdi≥pdis )

-- this lemma is generated by opus 4.6
-- A "cross" composition lemma. Given two outer injections in₁,in' (with pdi₁≥*pdi'),
-- and two inner pdinstances pdk≥pdj sharing inner type p, compose-pdi-with in₁ pdk
-- dominates compose-pdi-with in' pdj.
compose-pdi-with-cross : ∀ { p d r : RE } { pref : List Char } { c : Char }
  → ( in₁ : U d → U r )
  → ( s-ev₁ : ∀ ( v : U d ) → ( proj₁ ( flat {r} (in₁ v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → ( in' : U d → U r )
  → ( s-ev' : ∀ ( v : U d ) → ( proj₁ ( flat {r} (in' v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → ( pdk : PDInstance d c )
  → ( pdj : PDInstance d c )
  → d , c ⊢ pdk ≥ pdj
  → Inhabit p pdk
  → Inhabit p pdj
  → r , pref ⊢* (pdinstance* in₁ s-ev₁) ≥ (pdinstance* in' s-ev')
  ---------------------------------------------------------------------------------------
  → r , pref ∷ʳ c ⊢* compose-pdi-with in₁ s-ev₁ pdk ≥ compose-pdi-with in' s-ev' pdj
compose-pdi-with-cross {p} {d} {r} {pref} {c}
  in₁ s-ev₁ in' s-ev'
  pdk@(pdinstance .{p} .{d} .{c} pk-inj pk-sev)
  pdj@(pdinstance .{p} .{d} .{c} pj-inj pj-sev)
  (≥-pdi .(pk-inj) .(pk-sev) .(pj-inj) .(pj-sev) pk-strict pk-eqorgt)
  (hide .(pk-inj) .(pk-sev))
  (hide .(pj-inj) .(pj-sev))
  (*≥-pdi .(in₁) .(s-ev₁) .(in') .(s-ev') in₁-strict in₁-eqorgt) =
  *≥-pdi {r} {p} {pref ∷ʳ c}
    (in₁ ∘ pk-inj) (compose-pdi-with-soundEv in₁ s-ev₁ pk-inj pk-sev)
    (in' ∘ pj-inj) (compose-pdi-with-soundEv in' s-ev' pj-inj pj-sev)
    strict eqorgt
  where
    strict : ∀ (v₁ v₂ : U p) → p ⊢ v₁ > v₂ → r ⊢ in₁ (pk-inj v₁) > in' (pj-inj v₂)
    strict v₁ v₂ v₁>v₂ = in₁-strict (pk-inj v₁) (pj-inj v₂) (pk-strict v₁ v₂ v₁>v₂)
    eqorgt : ∀ (v : U p) → r ⊢ in₁ (pk-inj v) > in' (pj-inj v) ⊎ in₁ (pk-inj v) ≡ in' (pj-inj v)
    eqorgt v with pk-eqorgt v
    ... | inj₁ pkv>pjv         = inj₁ (in₁-strict (pk-inj v) (pj-inj v) pkv>pjv)
    ... | inj₂ pkv≡pjv rewrite pkv≡pjv = in₁-eqorgt (pj-inj v)


concatmap-advance-pdi*-with-c-lattice : ∀ { d  r : RE } { pref : List Char } { c : Char }
  → (pdis : List (PDInstance* r pref) )
  → Ex*≥-lattice pdis
  → All *>-Inc pdis
  → All (Inhabit* d) pdis
  -------------------------------------------------------------------------------------
  → Ex*≥-lattice (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
concatmap-advance-pdi*-with-c-lattice {d} {r} {pref} {c} [] ex*-empty [] [] =  ex*-empty
concatmap-advance-pdi*-with-c-lattice {d} {r} {pref} {c} (pdi@(pdinstance* .{d} .{r} .{pref} in₁ s-ev₁) ∷ pdis) (ex*-join .(pdi) .(pdis) pdi≥pdis)
  ((*>-inc v₁→v₂→v₁>v₂→in₁v₁>in₁v₂) ∷ all-*>-inc-pdis)
  ((hide* .{d} .(in₁) .(s-ev₁)) ∷ hide*-d-pdis )
  with pdU[ d , c ] in pdU-eq  | pdU-ex-lattice { d } {c}             |   pdU-Homogenous {d } {c}                  | pdU->-inc {d} {c}
... | []               | _                                    |   _                                              | _
  = subst Ex*≥-lattice (sym (empty-helper pdis hide*-d-pdis)) ex*-empty -- this sub case is generated by opus 4.6
  where
    -- every pdi' in pdis has inner type d (via Inhabit* d), so advance-pdi*-with-c pdi'
    -- reduces to List.map (compose-pdi-with ...) pdU[ d , c ] which is [] by pdU-eq.
    empty-helper : (xs : List (PDInstance* r pref))
                 → All (Inhabit* d) xs
                 → concatMap (advance-pdi*-with-c {r} {pref} {c}) xs ≡ []
    empty-helper [] [] = refl
    empty-helper (pdinstance* in' s-ev' ∷ xs) (hide* .(in') .(s-ev') ∷ ihs)
      rewrite pdU-eq = empty-helper xs ihs
... | (pdi₁ ∷ pdis₁ )  | ex-join  .(pdi₁) .(pdis₁) pdi₁≥pdis₁ | homogenous _ ( p , hide-p-pdi₁ ∷ hide-p-pdis₁) | (>-inc-pdi₁ ∷ all->-inc-pdis₁) =
  ex*-join (compose-pdi-with in₁ s-ev₁ pdi₁)
  (List.map (compose-pdi-with in₁ s-ev₁) pdis₁ ++
    (concatMap advance-pdi*-with-c pdis)) (all-concat prf₁ prf₂)
  where
    prf₁ : All (_,_⊢*_≥_ r (pref ∷ʳ c) (compose-pdi-with in₁ s-ev₁ pdi₁))
           (List.map (compose-pdi-with in₁ s-ev₁) pdis₁)
    prf₁ = compose-pdi-with-ex*≥-map-compose-pdi-with  in₁ s-ev₁ v₁→v₂→v₁>v₂→in₁v₁>in₁v₂ pdi₁ pdis₁ hide-p-pdi₁ hide-p-pdis₁ pdi₁≥pdis₁ 

    -- prf₂ and below are generated by opus 4.6 
    -- For each pdj ∈ pdU[d,c] = pdi₁ ∷ pdis₁, we have pdi₁ ≥ pdj.
    pdi₁≥pdU : All (_,_⊢_≥_ d c pdi₁) (pdi₁ ∷ pdis₁)
    pdi₁≥pdU = ex≥-refl >-inc-pdi₁ ∷ pdi₁≥pdis₁

    -- hide-p-pdU : All (Inhabit p) (pdi₁ ∷ pdis₁)
    -- hide-p-pdU = hide-p-pdi₁ ∷ hide-p-pdis₁

    -- for a single pdi' ∈ pdis, build proofs that compose-pdi-with in₁ s-ev₁ pdi₁
    -- dominates every element of advance-pdi*-with-c pdi'
    per-pdi'-list : (in' : U d → U r)
                  → (s-ev' : ∀ ( v : U d ) → ( proj₁ ( flat {r} (in' v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
                  → r , pref ⊢* (pdinstance* in₁ s-ev₁) ≥ (pdinstance* in' s-ev')
                  → (pdjs : List (PDInstance d c))
                  → All (_,_⊢_≥_ d c pdi₁) pdjs
                  → All (Inhabit p) pdjs
                  → All (_,_⊢*_≥_ r (pref ∷ʳ c) (compose-pdi-with in₁ s-ev₁ pdi₁))
                        (List.map (compose-pdi-with in' s-ev') pdjs)
    per-pdi'-list in' s-ev' pdi≥pdi' [] [] [] = []
    per-pdi'-list in' s-ev' pdi≥pdi' (pdj ∷ pdjs) (pdi₁≥pdj ∷ pdi₁≥pdjs) (i-pdj ∷ i-pdjs) =
      compose-pdi-with-cross in₁ s-ev₁ in' s-ev' pdi₁ pdj pdi₁≥pdj hide-p-pdi₁ i-pdj pdi≥pdi'
      ∷ per-pdi'-list in' s-ev' pdi≥pdi' pdjs pdi₁≥pdjs i-pdjs

    -- pdi is the pdinstance* from the top level
    -- in₁ and s-ev₁ are from pdi, not pdi₁
    -- pdi₁ is the pdinstance from the secondary level
    -- xs are the tails following pdi. hence pdi≥xs
    -- advance-pdi*-with-c xs is composing each pdinstance* with pdinstances coming from pdU[ d , c ]
    prf₂-helper : (xs : List (PDInstance* r pref))
                → All (Inhabit* d) xs
                → All (_,_⊢*_≥_ r pref pdi) xs 
                → All (_,_⊢*_≥_ r (pref ∷ʳ c) (compose-pdi-with in₁ s-ev₁ pdi₁)) 
                      (concatMap advance-pdi*-with-c xs)
    prf₂-helper [] [] [] = []
    prf₂-helper (pdinstance* in' s-ev' ∷ xs) (hide* .(in') .(s-ev') ∷ ihs) (pdi≥pdi' ∷ pdi≥xs)
      rewrite pdU-eq =
        all-concat (per-pdi'-list in' s-ev' pdi≥pdi' (pdi₁ ∷ pdis₁) pdi₁≥pdU (hide-p-pdi₁ ∷ hide-p-pdis₁))
                   (prf₂-helper xs ihs pdi≥xs)

    prf₂ : All (_,_⊢*_≥_ r (pref ∷ʳ c) (compose-pdi-with in₁ s-ev₁ pdi₁))
           (concatMap advance-pdi*-with-c pdis)
    prf₂ = prf₂-helper pdis hide*-d-pdis pdi≥pdis

                                                                                                                                                               

```
