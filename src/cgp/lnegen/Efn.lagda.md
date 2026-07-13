This module contains  the attempt of proving monotoncity of the pd injection over lnegen ordering by restricting to epsilon first normal form efn

```agda
{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module cgp.lnegen.Efn where
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
  pdinstance-star ; mkinjList ; mkinjListSoundEv ;
  pdinstance-fst ; mkinjFst ; mkinjFstSoundEv ;
  pdinstance-snd ; mkinjSnd ; mkinjSndSoundEv ; mk-snd-pdi ;
  concatmap-pdinstance-snd ; zip-es-flat-[]-es ; concatmap-pdinstance-snd-[]≡[] ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with
  ) 


import cgp.lnegen.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; 
  advance-pdi*-with-c ; 
  pdUMany[_,_]; pdUMany-aux ;
  mkinjLetter ; mkinjLetterSound 
  )


import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
import Data.List.Membership.Propositional.Properties as MembershipProperties
open MembershipProperties using (∈-concat⁺′ ; ∈-concat⁻′ ; ∈-map⁺ ; ∈-map⁻)

import cgp.lnegen.Order as Order
open Order -- we should only white list those are used here 


import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _+_ ; _<_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; _≟_ ; +-identityˡ )



import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ; length-++ )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning using ( begin_; step-≡;  step-≡-∣;  step-≡-⟩ ; _∎ )


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
-- epsilon first normal form
-- does not work, look at the comment "stuck here" below 

data Efn : ∀ (r : RE ) → Set where
  -- ε is in efn (base case)
  efn-ε : Efn ε
  -- p ● r is in efn if p is in efn (the source of any ● node is Efn by construction)
  efn-● : ∀ { p r : RE } { loc : ℕ }
    → Efn p
    ----------------------
    → Efn (p ● r ` loc)

data EfnPDInstance : ∀ {r : RE } { c : Char } → PDInstance r c → Set where
  -- A pdinstance is an EfnPDInstance if its source regex p is Efn
  efn-pdi : ∀ { p r : RE } { c : Char }
    → ( inj : U p → U r ) 
    → ( s-ev : ( u : U p ) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u))
    → Efn p
    → EfnPDInstance {r} {c} (pdinstance {p} {r} {c} inj s-ev)

-- Main theorem: all pdinstances in pdU[r, c] have Efn source
-- Proved by structural induction on r.
pdU-isEnf : ∀ { r : RE } { c : Char }
  → All (EfnPDInstance {r} {c}) pdU[ r , c ]

-- LEMMA: pdinstance-left preserves EfnPDInstance.
-- Proof idea: the source of (pdinstance-left pdi) is p (same as pdi's source),
-- which is already Efn by the inductive hypothesis. The injection is just wrapped
-- in LeftU, so the same Efn evidence applies.
-- Used in: efn-All-map-left (local helper for the + case of pdU-isEnf)
efn-pdinstance-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ∀ { p : RE } ( inj : U p → U l ) ( s-ev : ( u : U p ) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u))
  → EfnPDInstance {l} {c} (pdinstance {p} {l} {c} inj s-ev)
  → EfnPDInstance {l + r ` loc} {c} (pdinstance-left (pdinstance {p} {l} {c} inj s-ev))
efn-pdinstance-left {l} {r} {loc} {c} {p} inj s-ev (efn-pdi {p} {l} {c} .inj .s-ev efn-p) = efn-pdi {p} {l + r ` loc} {c} (λ u → LeftU (inj u)) s-ev efn-p


-- LEMMA: pdinstance-right preserves EfnPDInstance.
-- Proof idea: same as left - source p is unchanged, just wrapped in RightU.
-- Used in: efn-All-map-right (local helper for the + case of pdU-isEnf)
efn-pdinstance-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ∀ { p : RE } ( inj : U p → U r ) ( s-ev : ( u : U p ) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u))
  → EfnPDInstance {r} {c} (pdinstance {p} {r} {c} inj s-ev)
  → EfnPDInstance {l + r ` loc} {c} (pdinstance-right (pdinstance {p} {r} {c} inj s-ev))
efn-pdinstance-right {l} {r} {loc} {c} {p} inj s-ev (efn-pdi {p} {r} {c} .inj .s-ev efn-p) = efn-pdi {p} {l + r ` loc} {c} (λ u → RightU (inj u)) s-ev efn-p

-- LEMMA: pdinstance-fst preserves EfnPDInstance.
-- Proof idea: source of (pdinstance-fst pdi) is (p ● r), which is a ● node
-- and therefore Efn by the efn-● constructor.
-- Used in: efn-All-map-fst (local helper for the ● case of pdU-isEnf)
efn-pdinstance-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ∀ { p : RE } ( inj : U p → U l ) ( s-ev : ( u : U p ) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u))
  → EfnPDInstance {l} {c} (pdinstance {p} {l} {c} inj s-ev)
  → EfnPDInstance {l ● r ` loc} {c} (pdinstance-fst (pdinstance {p} {l} {c} inj s-ev))
efn-pdinstance-fst {l} {r} {loc} {c} {p} inj s-ev (efn-pdi {p} {l} {c} .inj .s-ev efn-p) = efn-pdi {p ● r ` loc} {l ● r ` loc} {c} (λ u → mkinjFst inj u) (mkinjFstSoundEv inj s-ev) (efn-● efn-p)

-- LEMMA: pdinstance-star preserves EfnPDInstance.
-- Proof idea: source of (pdinstance-star pdi) is (p ● (r * ε∉r)), which is a ● node
-- and therefore Efn by the efn-● constructor.
-- Used in: efn-All-map-star (local helper for the * case of pdU-isEnf)
efn-pdinstance-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  → ∀ { p : RE } ( inj : U p → U r ) ( s-ev : ( u : U p ) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u))
  → EfnPDInstance {r} {c} (pdinstance {p} {r} {c} inj s-ev)
  → EfnPDInstance {r * ε∉r ` loc} {c} (pdinstance-star (pdinstance {p} {r} {c} inj s-ev))
efn-pdinstance-star {r} {ε∉r} {loc} {c} {p} inj s-ev (efn-pdi {p} {r} {c} .inj .s-ev efn-p) = efn-pdi {p ● (r * ε∉r ` loc) ` loc} {r * ε∉r ` loc} {c} (mkinjList inj) (mkinjListSoundEv inj s-ev) (efn-● efn-p)

-- LEMMA: mk-snd-pdi preserves EfnPDInstance.
-- Proof idea: source of (mk-snd-pdi e pdi) is p (same as pdi's source),
-- which is Efn by the inductive hypothesis. The Efn evidence threads through
-- since mk-snd-pdi only changes the injection, not the source.
-- Used in: efn-map-pdinstance-snd, which is used in efn-concatmap-pdinstance-snd
--          for the ● (ε∈l) case of pdU-isEnf
efn-mk-snd-pdi : ∀ { l r p : RE } { loc : ℕ } { c : Char }
  → ( e : U l )
  → ( flat-e≡[] : proj₁ (flat e) ≡ [] )
  → ( inj : U p → U r )
  → ( s-ev : ∀ ( u : U p ) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u))
  → Efn p
  → EfnPDInstance {r} {c} (pdinstance {p} {r} {c} inj s-ev)
  → EfnPDInstance {l ● r ` loc} {c} (mk-snd-pdi {l} {r} {loc} {c} (e , flat-[] e flat-e≡[]) (pdinstance {p} {r} {c} inj s-ev))
efn-mk-snd-pdi {l} {r} {p} {loc} {c} e flat-e≡[] inj s-ev efn-p (efn-pdi {p} {r} {c} .inj .s-ev _) = efn-pdi {p} {l ● r ` loc} {c} (mkinjSnd inj e) s-ev-snd efn-p
  where
    s-ev-snd : ∀ ( u : U p ) → proj₁ (flat {l ● r ` loc} (mkinjSnd inj e u)) ≡ c ∷ proj₁ (flat {p} u)
    s-ev-snd u = mkinjSndSoundEv {p} {l} {r} {loc} {c} inj s-ev e (flat-[] e flat-e≡[]) u

-- LEMMA: mapping pdinstance-snd (for a single empty parse tree e) over a list
-- of pdinstances preserves EfnPDInstance.
-- Proof idea: for each pdi in the list, efn-mk-snd-pdi threads the Efn evidence.
-- Used in: efn-concatmap-pdinstance-snd (inner loop over each empty parse tree)
efn-map-pdinstance-snd : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( e-flat : ∃[ e ] Flat-[] l e )
  → ( pdis : List (PDInstance r c) )
  → All (EfnPDInstance {r} {c}) pdis
  → All (EfnPDInstance {l ● r ` loc} {c}) (pdinstance-snd {l} {r} {loc} {c} e-flat pdis)
efn-map-pdinstance-snd _ [] [] = []
efn-map-pdinstance-snd {l} {r} {loc} {c} (e , flat-[] .e flat-e≡[]) (_ ∷ ps) ((efn-pdi {p} {r} {c} inj s-ev efn-p) ∷ efns) = efn-mk-snd-pdi {l} {r} {p} {loc} {c} e flat-e≡[] inj s-ev efn-p (efn-pdi inj s-ev efn-p) ∷ efn-map-pdinstance-snd {l} {r} {loc} {c} (e , flat-[] e flat-e≡[]) ps efns

-- LEMMA: All P is preserved over list concatenation.
-- Proof idea: straightforward structural induction on the first list.
-- Used in: the + case (combines left and right branches) and the ● (ε∈l) case
--          (combines fst and snd branches) of pdU-isEnf
all-++ : ∀ {r : RE} {c : Char} {P : PDInstance r c → Set}
  → ( xs : List (PDInstance r c) )
  → ( ys : List (PDInstance r c) )
  → All P xs
  → All P ys
  → All P (xs ++ ys)
all-++ [] ys [] p₂ = p₂
all-++ (x ∷ xs) ys (p ∷ ps) p₂ = p ∷ all-++ xs ys ps p₂

-- LEMMA: concatmap-pdinstance-snd preserves EfnPDInstance.
-- Proof idea: decompose concatmap into a zip of (es × flat-[]-es) to get
-- a list of (e, Flat-[] e) pairs, then for each pair use efn-map-pdinstance-snd
-- and concatenate the results with all-++. The Efn evidence threads through
-- since each mk-snd-pdi preserves it.
-- Used in: the ● (ε∈l) case of pdU-isEnf for the second (snd) branch
efn-concatmap-pdinstance-snd : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( pdis : List (PDInstance r c) )
  → All (EfnPDInstance {r} {c}) pdis
  → All (EfnPDInstance {l ● r ` loc} {c}) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis)
efn-concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis all-efn-pdis = all-efn-concat
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l

    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l

    e-flat-es : List (∃[ e ] Flat-[] l e)
    e-flat-es = zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es

    all-efn-zip : All (EfnPDInstance {l ● r ` loc} {c}) (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x pdis ) e-flat-es)
    all-efn-zip = efn-map-zip e-flat-es
      where
        efn-map-zip : ∀ (es' : List (∃[ e ] Flat-[] l e))
          → All (EfnPDInstance {l ● r ` loc} {c}) (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x pdis ) es')
        efn-map-zip [] = []
        efn-map-zip ((e , flat-[] .e flat-e≡[]) ∷ xs) = all-++ _ _ (efn-map-pdinstance-snd {l} {r} {loc} {c} (e , flat-[] e flat-e≡[]) pdis all-efn-pdis) (efn-map-zip xs)

    all-efn-concat : All (EfnPDInstance {l ● r ` loc} {c}) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis)
    all-efn-concat = all-efn-zip

-- LEMMA: concatmap-pdinstance-snd over an empty pdi list yields [].
-- Proof idea: use subst with concatmap-pdinstance-snd-[]≡[] to rewrite
-- the result to [], then return [].
-- Used in: currently unused (left as a convenience lemma)
efn-concatmap-pdinstance-snd-[] : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → All (EfnPDInstance {r} {c}) []
  → All (EfnPDInstance {l ● r ` loc} {c}) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} [])
efn-concatmap-pdinstance-snd-[] {l} {r} {ε∈l} {loc} {c} [] = subst (All (EfnPDInstance {l ● r ` loc} {c})) (sym (concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c})) []

-- LEMMA: pdU[$ c, c] computes to the expected singleton list.
-- Proof idea: pattern-match on the same with clause (c Char.≟ c) as pdU uses,
-- which reduces pdU[$ c, c] to the concrete list, allowing refl.
-- Used in: pdU-isEnf-letter (rewrite clause to bridge the with abstraction)
pdU-letter≡∷ : ∀ { c : Char } { loc : ℕ }
  → pdU[ $ c ` loc , c ] ≡ [ pdinstance {ε} {$ c ` loc} {c} mkinjLetter mkinjLetterSound ]
pdU-letter≡∷ {c} {loc} with c Char.≟ c
... | yes refl = refl
... | no ¬c≡c = ⊥-elim (¬c≡c refl)

-- LEMMA: the letter case of pdU-isEnf.
-- Proof idea: match on (rc Char.≟ c) to thread pdU's internal with clause.
-- In the yes case, rewrite with pdU-letter≡∷ to expose the concrete list,
-- then construct efn-pdi with efn-ε. In the no case, the list is empty.
-- Used in: pdU-isEnf for the $ case
pdU-isEnf-letter : ∀ { rc c : Char } { loc : ℕ }
  → All (EfnPDInstance {$ rc ` loc} {c}) (pdU[ $ rc ` loc , c ])
pdU-isEnf-letter {rc} {c} {loc} with rc Char.≟ c
... | yes refl rewrite pdU-letter≡∷ {rc} {loc} = efn-pdi {ε} {$ rc ` loc} {rc} mkinjLetter mkinjLetterSound efn-ε ∷ []
... | no ¬rc≡c = []

pdU-isEnf {ε} {c} = []
pdU-isEnf {$ c' ` loc} {c} = pdU-isEnf-letter {c'} {c} {loc}

-- + case: pdU[l + r, c] = map left pdU[l,c] ++ map right pdU[r,c]
-- Map each branch through efn-pdinstance-left/right, then combine with all-++.
pdU-isEnf {l + r ` loc} {c} = all-++ _ _ (efn-All-map-left pdU[ l , c ] ind-hyp-l) (efn-All-map-right pdU[ r , c ] ind-hyp-r)
  where
    efn-All-map-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
      → ( pdis : List (PDInstance l c) )
      → All (EfnPDInstance {l} {c}) pdis
      → All (EfnPDInstance {l + r ` loc} {c}) (List.map pdinstance-left pdis)
    efn-All-map-left [] [] = []
    efn-All-map-left ((pdinstance {p} {l} {c} inj s-ev) ∷ pdis)
      (efn-pdi {p} {l} {c} inj s-ev efp ∷ pxs)
      = efn-pdinstance-left inj s-ev (efn-pdi {p} {l} {c} inj s-ev efp) ∷ efn-All-map-left pdis pxs

    efn-All-map-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
      → ( pdis : List (PDInstance r c) )
      → All (EfnPDInstance {r} {c}) pdis
      → All (EfnPDInstance {l + r ` loc} {c}) (List.map pdinstance-right pdis)
    efn-All-map-right [] [] = []
    efn-All-map-right ((pdinstance {p} {r} {c} inj s-ev) ∷ pdis)
      (efn-pdi {p} {r} {c} inj s-ev efp ∷ pxs)
      = efn-pdinstance-right inj s-ev (efn-pdi {p} {r} {c} inj s-ev efp) ∷ efn-All-map-right pdis pxs

    ind-hyp-l : All (EfnPDInstance {l} {c}) (pdU[ l , c ])
    ind-hyp-l = pdU-isEnf {l} {c}

    ind-hyp-r : All (EfnPDInstance {r} {c}) (pdU[ r , c ])
    ind-hyp-r = pdU-isEnf {r} {c}
-- * case: pdU[r*, c] = map star pdU[r,c]
-- Map through efn-pdinstance-star, which constructs efn-● from the Efn evidence of the source.
pdU-isEnf {r * ε∉r ` loc} {c} = efn-All-map-star pdU[ r , c ] ind-hyp-r
  where
    efn-All-map-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
      → ( pdis : List (PDInstance r c) )
      → All (EfnPDInstance {r} {c}) pdis
      → All (EfnPDInstance {r * ε∉r ` loc} {c}) (List.map pdinstance-star pdis)
    efn-All-map-star [] [] = []
    efn-All-map-star ((pdinstance {p} {r} {c} inj s-ev) ∷ pdis)
      (efn-pdi {p} {r} {c} inj s-ev efp ∷ pxs)
      = efn-pdinstance-star inj s-ev (efn-pdi {p} {r} {c} inj s-ev efp) ∷ efn-All-map-star pdis pxs

    ind-hyp-r : All (EfnPDInstance {r} {c}) (pdU[ r , c ])
    ind-hyp-r = pdU-isEnf {r} {c}
-- ● case (¬ε∈l): pdU[l ● r, c] = map fst pdU[l,c]
-- Map through efn-pdinstance-fst, which constructs efn-● from the Efn evidence.
pdU-isEnf {l ● r ` loc} {c} with ε∈? l
...                            | no ¬ε∈l = efn-All-map-fst pdU[ l , c ] ind-hyp-l
  where
    efn-All-map-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
      → ( pdis : List (PDInstance l c) )
      → All (EfnPDInstance {l} {c}) pdis
      → All (EfnPDInstance {l ● r ` loc} {c}) (List.map pdinstance-fst pdis)
    efn-All-map-fst [] [] = []
    efn-All-map-fst ((pdinstance {p} {l} {c} inj s-ev) ∷ pdis)
      (efn-pdi {p} {l} {c} inj s-ev efp ∷ pxs)
      = efn-pdinstance-fst inj s-ev (efn-pdi {p} {l} {c} inj s-ev efp) ∷ efn-All-map-fst pdis pxs

    ind-hyp-l : All (EfnPDInstance {l} {c}) (pdU[ l , c ])
    ind-hyp-l = pdU-isEnf {l} {c}
-- ● case (ε∈l): pdU[l ● r, c] = map fst pdU[l,c] ++ concatmap-snd pdU[r,c]
-- First branch maps through efn-pdinstance-fst, second uses efn-concatmap-pdinstance-snd.
...                            | yes ε∈l = all-++ _ _ (efn-All-map-fst pdU[ l , c ] ind-hyp-l) (efn-concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ] ind-hyp-r)
  where
    efn-All-map-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
      → ( pdis : List (PDInstance l c) )
      → All (EfnPDInstance {l} {c}) pdis
      → All (EfnPDInstance {l ● r ` loc} {c}) (List.map pdinstance-fst pdis)
    efn-All-map-fst [] [] = []
    efn-All-map-fst ((pdinstance {p} {l} {c} inj s-ev) ∷ pdis)
      (efn-pdi {p} {l} {c} inj s-ev efp ∷ pxs)
      = efn-pdinstance-fst inj s-ev (efn-pdi {p} {l} {c} inj s-ev efp) ∷ efn-All-map-fst pdis pxs

    ind-hyp-l : All (EfnPDInstance {l} {c}) (pdU[ l , c ])
    ind-hyp-l = pdU-isEnf {l} {c}

    ind-hyp-r : All (EfnPDInstance {r} {c}) (pdU[ r , c ])
    ind-hyp-r = pdU-isEnf {r} {c}


{-
why we need this?
this seems to be unprovable, the set of EfnPDInstance is larger than pdU[r, c]
efnInpdU : ∀ {r : RE } { c : Char }
  → (pdi :  PDInstance r c )
  → EfnPDInstance pdi
  → Any ( _≡ pdi ) pdU[ r , c ]
efnInpdU = {!!}
-}

{-
-- not in used,  it got stuck below
data >-Inc-efn : ∀ { r : RE } { c : Char } →  PDInstance r c  → Set where
  >-inc-efn : ∀ { p r : RE } { c : Char } { inj : U p →  U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → Efn p 
    → ( (u₁ : U p) → (u₂ : U p)
        → length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
        →  p ⊢ u₁ > u₂ → r ⊢ inj u₁ > inj u₂ ) -- strict increasing evidence 
    → >-Inc-efn {r} {c} (pdinstance {p} {r} {c} inj sound-ev)

>-inc-fst-efn : ∀ { l r : RE } { loc : ℕ } { c : Char }
               → ( pdi : PDInstance l c )
               → >-Inc-efn {l} {c} pdi
               ------------------------
               → >-Inc-efn {l ● r ` loc} {c} (pdinstance-fst {l} {r} {loc} {c} pdi)
>-inc-fst-efn {l} {r} {loc} {c} (pdinstance {ε} {l} {c}  inj sound-ev) (>-inc-efn efn-ε u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) = >-inc-efn (efn-● efn-ε) >-inc-ev
  where
    injFst : U (ε ● r ` loc)   → U (l ● r ` loc ) -- the p can only be seq ε or ●
    injFst = mkinjFst inj
    injFstSnd :  ( u : U (ε ● r ` loc) )  → proj₁ (flat (injFst u))  ≡ c ∷ proj₁ (flat u)
    injFstSnd = mkinjFstSoundEv inj sound-ev
    >-inc-ev : ∀ (uv₁ : U ( ε ● r ` loc ))
              → (uv₂ : U ( ε ● r ` loc ))
              → length (proj₁ (flat uv₁)) ≡ length (proj₁ (flat uv₂))
              → ε ● r ` loc  ⊢ uv₁ > uv₂
              ------------------------------------
              → l ● r ` loc ⊢ (injFst uv₁) > (injFst uv₂)

    |injFst-pair-u-v|>0 : ∀ {u v} → length (proj₁ (flat (PairU {l} {r} {loc} (inj u) v))) Nat.> 0
    |injFst-pair-u-v|>0 {u} {v} rewrite injFstSnd (PairU u v) = Nat.s≤s Nat.z≤n

    >-inc-ev (PairU EmptyU v₁) (PairU EmptyU v₂) _ (be _ len|pair-u₂v₂|≡0 (seq₂ refl v₁>v₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₂ refl v₁>v₂)
    >-inc-ev (PairU EmptyU v₁) (PairU EmptyU v₂) _ (be _ _ (seq₁ u₁>u₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ EmptyU EmptyU refl u₁>u₂))
    >-inc-ev (PairU EmptyU v₁) (PairU EmptyU v₂) _ (bne _ _ (seq₂ refl v₁>v₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₂ refl v₁>v₂)
    >-inc-ev (PairU EmptyU v₁) (PairU EmptyU v₂) _ (bne _ _ (seq₁ u₁>u₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ EmptyU EmptyU refl u₁>u₂))
    >-inc-ev (PairU EmptyU v₁) (PairU EmptyU v₂) _ (lne len|pair-u₁v₁|>0 len|pair-u₂v₂|≡0)
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₂ refl (lne len|pair-u₁v₁|>0 len|pair-u₂v₂|≡0))


>-inc-fst-efn {l} {r} {loc} {c} (pdinstance {p ● t ` loc'} {l} {c}  inj sound-ev) (>-inc-efn (efn-● efn-p) u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) = >-inc-efn (efn-● (efn-● efn-p)) >-inc-ev
  where
    injFst : U (( p ● t ` loc') ● r ` loc)   → U (l ● r ` loc ) -- the p can only be seq ε or ●
    injFst = mkinjFst inj
    injFstSnd :  ( u : U (( p ● t ` loc') ● r ` loc) )  → proj₁ (flat (injFst u))  ≡ c ∷ proj₁ (flat u)
    injFstSnd = mkinjFstSoundEv inj sound-ev
    >-inc-ev : ∀ (uv₁ : U ( ( p ● t ` loc') ● r ` loc ))
              → (uv₂ : U ( ( p ● t ` loc') ● r ` loc ))
              → length (proj₁ (flat uv₁)) ≡ length (proj₁ (flat uv₂))
              → ( p ● t ` loc') ● r ` loc  ⊢ uv₁ > uv₂
              ------------------------------------
              → l ● r ` loc ⊢ (injFst uv₁) > (injFst uv₂)

    |injFst-pair-u-v|>0 : ∀ {u v} → length (proj₁ (flat (PairU {l} {r} {loc} (inj u) v))) Nat.> 0
    |injFst-pair-u-v|>0 {u} {v} rewrite injFstSnd (PairU u v) = Nat.s≤s Nat.z≤n

    sound-ev-len : ∀ (u : U (p ● t ` loc')) → length (proj₁ (flat (inj u))) ≡ suc (length (proj₁ (flat u)))
    sound-ev-len u rewrite sound-ev u = refl

    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) len|uv₁|≡len|uv₂| (be len|pair-u₁v₁|≡len|pair-u₂v₂| len|pair-u₂v₂|≡0 (seq₁ u₁>u₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ len|u₁|≡len|u₂| u₁>u₂))
      where
        flat-u₂v₂≡[] : proj₁ (flat (PairU {p ● t ` loc'} {r} {loc}  u₂ v₂)) ≡ []
        flat-u₂v₂≡[] = Utils.length≡0→[] len|pair-u₂v₂|≡0
        flat-u₂≡[] : proj₁ (flat u₂) ≡ []
        flat-u₂≡[] = ++-conicalˡ (proj₁ (flat u₂)) (proj₁ (flat v₂)) flat-u₂v₂≡[]
        flat-u₁v₁≡[] : proj₁ (flat (PairU {p ● t ` loc'} {r} {loc} u₁ v₁)) ≡ []
        flat-u₁v₁≡[] = Utils.length≡0→[] (trans len|pair-u₁v₁|≡len|pair-u₂v₂| len|pair-u₂v₂|≡0)
        flat-u₁≡[] : proj₁ (flat u₁) ≡ []
        flat-u₁≡[] = ++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat v₁)) flat-u₁v₁≡[]
        len|u₁|≡len|u₂| : length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
        len|u₁|≡len|u₂| = trans (cong length flat-u₁≡[]) (sym (cong length flat-u₂≡[]))
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) _ (be _ _ (seq₂ u₁≡u₂ v₁>v₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₂ (cong inj u₁≡u₂) v₁>v₂)
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) _ (bne _ _ (seq₁ u₁>u₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ len|u₁|≡len|u₂| u₁>u₂))
      where
        len|u₁|≡len|u₂| : length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
        len|u₁|≡len|u₂| = {!!} -- stuck here
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) _ (bne _ _ (seq₂ u₁≡u₂ v₁>v₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₂ (cong inj u₁≡u₂) v₁>v₂)
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) len|pair-u₁v₁|≡len|pair-u₂v₂| (lne len|pair-u₁v₁|>0 len|pair-u₂v₂|≡0) =  Nullary.contradiction len|pair-u₁v₁|>0  (n≡0→¬n>0  len|pair-u₁v₁|≡0) 
      where
        len|pair-u₁v₁|≡0 : length (proj₁ (flat (PairU u₁ v₁))) ≡ 0
        len|pair-u₁v₁|≡0 rewrite len|pair-u₁v₁|≡len|pair-u₂v₂| = len|pair-u₂v₂|≡0

    -}         

    {-
      with length (proj₁ (flat u₁)) Nat.≟ 0
    ... | no ¬len|u₁|≡0 = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ len|u₁|≡len|u₂| (lne (Utils.¬≡0→>0 ¬len|u₁|≡0) len|u₂|≡0)))
      where
        len|u₂|≡0 : length (proj₁ (flat u₂)) ≡ 0
        len|u₂|≡0 = Utils.[]→length≡0 (++-conicalˡ (proj₁ (flat u₂)) (proj₁ (flat v₂)) (Utils.length≡0→[] len|pair-u₂v₂|≡0))
        len|u₁|≡len|u₂| : length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
        len|u₁|≡len|u₂| = {!!}
    ... | yes len|u₁|≡0 = {!!}  -- COUNTEREXAMPLE: when u₁ is empty but differs from u₂ (e.g. p = ε ● ((ε + $d) + (ε + $d)) with u₁ = PairU EmptyU (RightU (LeftU EmptyU)) and u₂ = PairU EmptyU (LeftU (RightU EmptyU))), the goal is unprovable because seq₂ requires inj u₁ ≡ inj u₂ and seq₁ requires an ordering in l that may not exist.
 -}



```


```agda

-- >-Inc is not working, pdU is not monotomic, refer to >-Inc


{-

data >-Inc : ∀ { r : RE } { c : Char } →  PDInstance r c  → Set where
  >-inc : ∀ { p r : RE } { c : Char } { inj : U p →  U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → Efn p
    → ( (v₁ : U p) → (v₂ : U p)
        → proj₁ (flat v₁) ≡ proj₁ (flat v₂)
        →  p ⊢ v₁ > v₂ → r ⊢ inj v₁ > inj v₂ )
    → >-Inc {r} {c} (pdinstance {p} {r} {c} inj sound-ev)

>-inc-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
                → ( pdi : PDInstance l c )
                → >-Inc {l} {c} pdi
                ------------------------
                → >-Inc {l ● r ` loc} {c} (pdinstance-fst {l} {r} {loc} {c} pdi)

>-inc-fst {l} {r} {loc} {c} (pdinstance {l'} {l} {c} inj sound-ev) (>-inc efn-l inc-ev) = >-inc (efn-● efn-l) inc-fst
  where
    injFst : U (l' ● r ` loc) → U (l ● r ` loc)
    injFst = mkinjFst inj

    |injFst-pair-u-v|>0 : ∀ {u v} → length (proj₁ (flat (PairU {l} {r} {loc} (inj u) v))) Nat.> 0
    |injFst-pair-u-v|>0 {u} {v} rewrite mkinjFstSoundEv inj sound-ev (PairU u v) = Nat.s≤s Nat.z≤n

    flat-pair : ∀ {l₁ r₁ loc₁} (u : U l₁) (v : U r₁) → proj₁ (flat (PairU u v)) ≡ proj₁ (flat u) ++ proj₁ (flat v)
    flat-pair u v with flat u | flat v
    flat-pair u v | xs , _ | ys , _ = refl

    u₁≡u₂-from-flat : ∀ (u₁ u₂ : U l') (v₁ v₂ : U r)
                       → proj₁ (flat (PairU u₁ v₁)) ≡ proj₁ (flat (PairU u₂ v₂))
                       → proj₁ (flat u₁) ≡ proj₁ (flat u₂)
    u₁≡u₂-from-flat u₁ u₂ v₁ v₂ uv₁≡uv₂ = ++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat v₁)) (trans (sym (flat-pair u₁ v₁)) (trans uv₁≡uv₂ (flat-pair u₂ v₂)))

    >-inc-seq₁ : ∀ (u₁ u₂ : U l') (v₁ v₂ : U r)
                  → proj₁ (flat u₁) ≡ proj₁ (flat u₂)
                  → l' ● r ` loc ⊢ PairU u₁ v₁ >ⁱ PairU u₂ v₂
                  → l ● r ` loc ⊢ PairU (inj u₁) v₁ >ⁱ PairU (inj u₂) v₂
    >-inc-seq₁ u₁ u₂ v₁ v₂ u₁≡u₂ (seq₁ u₁>u₂)
      = seq₁ (inc-ev u₁ u₂ u₁≡u₂ u₁>u₂)
    >-inc-seq₁ u₁ u₂ v₁ v₂ u₁≡u₂ (seq₂ u₁≡u₂' v₁>v₂) = seq₂ (cong inj (trans u₁≡u₂ (sym u₁≡u₂'))) v₁>v₂

    inc-fst : ∀ (uv₁ uv₂ : U (l' ● r ` loc))
              → proj₁ (flat uv₁) ≡ proj₁ (flat uv₂)
              → l' ● r ` loc ⊢ uv₁ > uv₂
              → l ● r ` loc ⊢ injFst uv₁ > injFst uv₂
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ >ⁱ)
      with length (proj₁ (flat u₁)) ≟ 0 | length (proj₁ (flat u₂)) ≟ 0
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ >ⁱ) | yes u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁ u₁ u₂ v₁ v₂ u₁≡u₂ >ⁱ)
      where
        u₁≡u₂ : proj₁ (flat u₁) ≡ proj₁ (flat u₂)
        u₁≡u₂ = trans (Utils.length≡0→[] u₁≡0) (sym (Utils.length≡0→[] u₂≡0))
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ >ⁱ) | no ¬u₁≡0 | no ¬u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁ u₁ u₂ v₁ v₂ (u₁≡u₂-from-flat u₁ u₂ v₁ v₂ uv₁≡uv₂) >ⁱ)
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ (seq₁ u₁>u₂)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (u₁>u₂-impossible u₁>u₂)
      where
        u₁>u₂-impossible : l' ⊢ u₁ > u₂ → ⊥
        u₁>u₂-impossible (be _ u₂≡0 _) = ¬u₂≡0 u₂≡0
        u₁>u₂-impossible (bne u₁>0 _ _) = n≡0→¬n>0 u₁≡0 u₁>0
        u₁>u₂-impossible (lne u₁>0 _) = n≡0→¬n>0 u₁≡0 u₁>0
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ (seq₂ u₁≡u₂ _)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 u₂≡0)
      where
        u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
        u₂≡0 rewrite trans (cong (length ∘ proj₁ ∘ flat) (sym u₁≡u₂)) u₁≡0 = refl
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ >ⁱ) | no ¬u₁≡0 | yes u₂≡0
      = ⊥-elim (¬u₁≡0 u₁≡0)
      where
        u₁≡0 : length (proj₁ (flat u₁)) ≡ 0
        u₁≡0 rewrite sym (cong (length ∘ proj₁ ∘ flat) (u₁≡u₂-from-flat u₁ u₂ v₁ v₂ uv₁≡uv₂)) = u₂≡0
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ >ⁱ)
      with length (proj₁ (flat u₁)) ≟ 0 | length (proj₁ (flat u₂)) ≟ 0
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ >ⁱ) | yes u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁ u₁ u₂ v₁ v₂ u₁≡u₂ >ⁱ)
      where
        u₁≡u₂ : proj₁ (flat u₁) ≡ proj₁ (flat u₂)
        u₁≡u₂ = trans (Utils.length≡0→[] u₁≡0) (sym (Utils.length≡0→[] u₂≡0))
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ >ⁱ) | no ¬u₁≡0 | no ¬u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁ u₁ u₂ v₁ v₂ (u₁≡u₂-from-flat u₁ u₂ v₁ v₂ uv₁≡uv₂) >ⁱ)
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ (seq₁ u₁>u₂)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (u₁>u₂-impossible u₁>u₂)
      where
        u₁>u₂-impossible : l' ⊢ u₁ > u₂ → ⊥
        u₁>u₂-impossible (be _ u₂≡0 _) = ¬u₂≡0 u₂≡0
        u₁>u₂-impossible (bne u₁>0 _ _) = n≡0→¬n>0 u₁≡0 u₁>0
        u₁>u₂-impossible (lne u₁>0 _) = n≡0→¬n>0 u₁≡0 u₁>0
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ (seq₂ u₁≡u₂ _)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 u₂≡0)
      where
        u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
        u₂≡0 rewrite trans (cong (length ∘ proj₁ ∘ flat) (sym u₁≡u₂)) u₁≡0 = refl
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ >ⁱ) | no ¬u₁≡0 | yes u₂≡0
      = ⊥-elim (¬u₁≡0 u₁≡0)
      where
        u₁≡0 : length (proj₁ (flat u₁)) ≡ 0
        u₁≡0 rewrite sym (cong (length ∘ proj₁ ∘ flat) (u₁≡u₂-from-flat u₁ u₂ v₁ v₂ uv₁≡uv₂)) = u₂≡0
    inc-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (lne _ uv₂≡0)
      = ⊥-elim (n≡0→¬n>0 (trans (cong length uv₁≡uv₂) uv₂≡0) (Nat.s≤s Nat.z≤n))
-}      

```


counter example from Inc.lagda.md


( ( (($ 'a' ` 1) ● ( ε + ε ` 2) ` 3) ● ( ε + ($ 'b' ` 4) ` 5) ` 6) ● (ε + ($ 'b' ` 7) ` 8) ` 9 )

( (a ● (ε + ε) ) ● ( ε + b ) ) ● (ε + b )

/ a ( inj₀ )



= [ ( ( ε ● ( ε + ε ) ) ● (ε + b) ) ● (ε + b ) ]

/ b ( inj₁ inj₂ inj₃ inj₄ )

= [ ε ● ( ε + b ) , ε  ]

inj₀ : U ( ( ε ● ( ε + ε ) ) ● (ε + b) ) ● (ε + b ) → U ( (a ● (ε + ε) ) ● ( ε + b ) ) ● (ε + b )
inj₀ (PairU (PairU (PairU EmptyU (LeftU EmptyU))  (RightU (LetterU b))) (LeftU EmptyU))  = PairU (PairU (PairU (LetterU a) (LeftU EmptyU))  (RightU (LetterU b))) (LeftU EmptyU)       -- (t1)
inj₀ (PairU (PairU (PairU EmptyU (RightU EmptyU)) (RightU (LetterU b))) (LeftU EmptyU))  = PairU (PairU (PairU (LetterU a) (RightU EmptyU)) (RightU (LetterU b))) (LeftU EmptyU)       -- (t2)
inj₀ (PairU (PairU (PairU EmptyU (LeftU EmptyU))  (LeftU EmptyU)) (RightU (LetterU b)))  = PairU (PairU (PairU (LetterU a) (LeftU EmptyU))  (LeftU EmptyU) )      (RightU (LetterU b)) -- (t3)  t3 > t2
inj₀ (PairU (PairU (PairU EmptyU (RightU EmptyU)) (LeftU EmptyU)) (RightU (LetterU b)))  = PairU (PairU (PairU (LetterU a) (RightU EmptyU)) (LeftU EmptyU) )      (RightU (LetterU b)) -- (t4)


t1 > t2 is witness by (seq₁ (seq₁ (seq₂ choice-lr))) -- does not change
t1 > t3 is witness by (seq₁ (seq₂ lne))
t1 > t4 is witness by (seq₁ (seq₂ lne))

s1 > s2 is witness by (seq₁ (seq₁ (seq₂ choice-lr))) -- choice-lr does not limit the word length 
s1 > s3 is witness by (seq₁ lne)
s1 > s4 is witness by (seq₁ lne)
s2 > s3 is witness by (seq₁ lne)

inj₁ inj₂ : U (ε ● ( ε + b )) → U ( ( ε ● ( ε + ε ) ) ● (ε + b) ) ● (ε + b )

inj₁ (PairU EmptyU (LeftU EmptyU)) = PairU (PairU (PairU EmptyU (LeftU EmptyU))  (RightU (LetterU b))) (LeftU EmptyU)     -- (s1)   
inj₂ (PairU EmptyU (LeftU EmptyU)) = PairU (PairU (PairU EmptyU (RightU EmptyU)) (RightU (LetterU b))) (LeftU EmptyU)    -- (s2)  s1 > s2 


inj₃ inj₄ : U ε               → U ( ( ε ● ( ε + ε ) ) ● (ε + b) ) ● (ε + b )
inj₃ _ = PairU ( PairU ( PairU EmptyU (LeftU EmptyU))   (LeftU EmptyU) ) (RightU (LetterU b))                             -- (s3)  s2 > s3
inj₄ _ = PairU ( PairU ( PairU EmptyU (RightU EmptyU))  (LeftU EmptyU) ) (RightU (LetterU b))                            -- (s4)  s3 > s4


inj₀ is an injection from a pdinstance, hence pdU are ex>-sorted


inj₀ ∘ inj₁ , inj₀ ∘ inj₂ , inj₀ ∘ inj₃  and  inj₀ ∘ inj₄ are injections from pdinstance*  pdUMany are not sorted.


all pdinstances's injections are local max preserve, i.e. for all u in p, max {p} |u| u, for all v in p, |u| >= |v|,  inj u > inj v
  note: it is not max |inj u| (inj u| yet!!! (see MaxWord.lagda.md pdU-preseve-local )
  we need pdU completeness and pdU sorted
  the idea is is if each pdinstance is local max preserving, we need all pdinstances are sorted,
  there should be the max-preserving, starting from r all the way to the pd descendants (each descendants is a pdinstance*)
  


