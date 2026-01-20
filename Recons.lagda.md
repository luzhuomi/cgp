This module contains the common definitions of the Recons and Recons* being used in greedy/PartialDerivative.lagda.md and lne/PartialDerivative.lagda.md


```agda

{-# OPTIONS --rewriting #-}
module cgp.Recons  where


import cgp.RE as RE
open RE using (RE;  ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;   ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ; first ; ε∉r→¬first-r≡[] )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU;  unListU ; listU∘unListU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU )

import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; Flat-[] ; flat-[] ;  mkAllEmptyU≢[])


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ;
  pdinstance-left; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ;
  concatmap-pdinstance-snd  ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc ; assoc ; assoc-inv-assoc-u≡u ;
  compose-pdi-with 
  ) 

import cgp.Utils as Utils
open Utils using (any-right-concat; any-left-concat ; all-concat ;  ∷-inj ; ¬∷≡[] ; inv-map-[] ; inv-concatMap-map-f-[]  )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_  )

import Data.List.Properties
open Data.List.Properties using (  ++-assoc ;  ++-identityʳ ; ++-identityˡ ; {-  unfold-reverse ; -} ∷ʳ-++ ; ++-cancelˡ ;  ++-conicalʳ ;  ++-conicalˡ  )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map)
open import Data.List.Relation.Unary.Any using (Any; here; there ; map)

import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)


import Relation.Nullary as Nullary 
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)


```
### Definition 18 (Reconstructability):
Let r be a non problematic regular expression.
Let c be a character.
Let u be a parse tree of r.
Let pdi be a partial derivative (instance) of r w.r.t c,
such that pdi = { p , inj , sound-ev }
  where
    1. p is the partial derivative instance of p/c;
    2. inj is the injection function from parse tree of p back to parse tree of r;
    3. sound-ev is the soundness evidence pdi
Then we say pdi is u-reconstructable w.r.t c iff there exists a word w ∈ ⟦p⟧ such that inj (unflat w∈p) ≡ u.

```agda


data Recons : { r : RE } { c : Char } → ( u : U r ) → ( PDInstance r c )  → Set where
  recons : ∀ { p r : RE } { c : Char } { w : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → (u : U r)
    → ∃[ w∈⟦p⟧ ] ( (inj (unflat {p} {w}  w∈⟦p⟧)) ≡ u )    -- the completeness property.
    → Recons {r} {c} u (pdinstance {p} {r} {c} inj sound-ev) -- <- the input PDI obj

```


#### Sub Lemmas 19.1 - 19.7 Reconstructability is preserved inductively over pdinstance operations. 
These sub lemmas are require for the proof of pdU completeness result (Lemma 19 in lne/PartialDerivative.lagda.md, greedy/PartialDerivative.lagda.md and posix/PartialDerivative.lagda.md)

```agda
-----------------------------------------------------------------------------------------
-- Sub Lemmas 19.1 - 19.7 BEGIN
----------------------------------------------------------------------------------------


any-recons-left : ∀ { l r : RE } { loc : ℕ } {c : Char } { w : List Char} { u : U l }
    → ( pdis : List (PDInstance l c) )
    → Any (Recons {l} {c} u) pdis 
    ---------------------------------------------------------
    → Any (Recons {l + r ` loc } {c} (LeftU u)) (List.map pdinstance-left pdis)
any-recons-left ( pdi ∷ pdis' ) (here {pd} {pds} (recons {p} {l} {c} {w} {inj} {sound-ev} u ( w∈⟦p⟧ ,  inj∘unflat≡u ))) = here (recons (LeftU u) ( w∈⟦p⟧ ,  cong LeftU  inj∘unflat≡u )) 
any-recons-left {l} {r} {loc} {c} {w} {u} ( pdi ∷ pdis' ) (there {pd} {pds} pxs) = there (any-recons-left {l} {r} {loc} {c} {w} {u} pdis' pxs) 



any-recons-right : ∀ { l r : RE } { loc : ℕ } {c : Char } { w : List Char} { u : U r }
    → ( pdis : List (PDInstance r c) )
    → Any (Recons {r} {c} u) pdis 
    ---------------------------------------------------------
    → Any (Recons {l + r ` loc } {c} (RightU u)) (List.map pdinstance-right pdis)
any-recons-right ( pdi ∷ pdis' ) (here {pd} {pds} (recons {p} {r} {c} {w} {inj} {sound-ev} u ( w∈⟦p⟧ ,  inj∘unflat≡u ))) = here (recons (RightU u) ( w∈⟦p⟧ , cong RightU  inj∘unflat≡u)) 
any-recons-right {l} {r} {loc} {c} {w} {u} ( pdi ∷ pdis' ) (there {pd} {pds} pxs) = there (any-recons-right {l} {r} {loc} {c} {w} {u} pdis' pxs) 


any-recons-fst : ∀ { l r : RE } { loc : ℕ } { c : Char } { w : List Char } { u : U l } { v : U r }
    → ( pdis : List (PDInstance l c) )
    → Any (Recons {l} {c} u) pdis
    -----------------------------------------------------------
    → Any (Recons {l ● r ` loc } {c} (PairU u v)) (List.map pdinstance-fst pdis)
any-recons-fst {l} {r} {loc} {c} {w} {u} {v} ( pdi ∷ pdis' ) (here {pd} {pds} (recons {p} {l} {c} {w₁} {inj} {sound-ev} u' ( w₁∈⟦p⟧ ,  inj∘unflat≡u ))) = 
  here (recons (PairU u' v) ((w₁∈⟦p⟧ ● proj₂ (flat v) ⧺ refl) , Eq.cong₂ (λ x y → PairU x y) inj∘unflat≡u (unflat∘proj₂∘flat {r} {v}) ))
any-recons-fst {l} {r} {loc} {c} {w} {u} {v} ( pdi ∷ pdis' ) (there {pd} {pds} pxs)  = there (any-recons-fst {l} {r} {loc} {c} {w} {u} {v} pdis' pxs) 


any-recons-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char } { w : List Char } { u : U r } { us : List (U r) }
    → ( pdis : List (PDInstance r c ) )
    → Any (Recons {r} {c} u) pdis
    ------------------------------------------------------------
    → Any (Recons { r * ε∉r ` loc } {c} (ListU (u ∷ us))) (List.map pdinstance-star pdis)
any-recons-star {r} {ε∉r} {loc} {c} {w} {u} {us} ( pdi ∷ pdis' ) (here {pd} {pds} (recons {p} {r} {c} {w₁} {inj} {sound-ev} _ ( w₁∈⟦p⟧ , inj∘unflatw₁∈p≡u ))) =
  let
    injList = mkinjList {p} {r} {ε∉r} {loc} inj
  in here (recons {- { p ● (r * ε∉r ` loc) ` loc } {r * ε∉r ` loc} {c} {w} {injList} {_} -} -- ignoring the implict para help to simplify to use refl, just like any-recons-fst
                  (ListU (u ∷ us)) ((w₁∈⟦p⟧ ● proj₂ (flat (ListU {r} {ε∉r} {loc} us)) ⧺ refl) , (
    begin
      mkinjList inj (PairU (unflat w₁∈⟦p⟧) (unflat (Product.proj₂ (flat (ListU us)))))
    ≡⟨ cong (λ x → mkinjList inj (PairU (unflat w₁∈⟦p⟧) x )) (unflat∘proj₂∘flat {r * ε∉r ` loc} {ListU us}) ⟩
      mkinjList inj (PairU (unflat w₁∈⟦p⟧) (ListU us))
    ≡⟨⟩
      ListU (inj (unflat w₁∈⟦p⟧) ∷ us)
    ≡⟨ cong ( λ x → ListU (x ∷ us) )  inj∘unflatw₁∈p≡u ⟩ 
      ListU (u ∷ us)
    ∎) )) 
any-recons-star {r} {ε∉r} {loc} {c} {w} {u} {us} ( pdi ∷ pdis' ) (there {pd} {pds} pxs) = there (any-recons-star {r} {ε∉r} {loc} {c} {w} {u} {us} pdis' pxs) 




any-recons-pdinstance-snd : ∀ { l r : RE } { loc : ℕ } { c : Char } { w : List Char } { e : U l } { v : U r }
  → ( flat-[]-e : Flat-[] l e )
  → ( pdis : List (PDInstance r c) )
  → Any (Recons {r} {c} v) pdis  
  -------------------------------------------------------------------------------------------------------------------
  → Any (Recons {l ● r ` loc } {c} (PairU e v)) (pdinstance-snd {l} {r} {loc} {c} ( e , flat-[]-e )  pdis )
any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v} (flat-[] _ proj₁-flat-e≡[]) [] any-recons-v = Nullary.contradiction any-recons-v ¬Any[]
any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v} (flat-[] _ proj₁-flat-e≡[]) (pdi ∷ pdis) (here (recons v ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡v ))) = here (recons (PairU e v) ( w∈⟦p⟧ ,  cong (λ x → PairU e x ) inj-unflat-w∈⟦p⟧≡v ))
any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v} flat-[]-e@(flat-[] _ proj₁-flat-e≡[]) (pdi ∷ pdis) (there pxs) = -- there (any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v} (flat-[] e proj₁-flat-e≡[]) pdis pxs) 
  there next
  where
    next : Any (Recons {l ● r ` loc } {c} (PairU e v)) (pdinstance-snd {l} {r} {loc} {c} ( e , flat-[]-e )  pdis )
    next = any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v} (flat-[] e proj₁-flat-e≡[]) pdis pxs


any-recons-concatmap-pdinstance-snd : ∀ { l r : RE } { ε∈l : ε∈ l} { loc : ℕ } { c : Char } { w : List Char } { u : U l } { v : U r }
    → ( proj1-flat-u≡[] : proj₁ (flat u) ≡ [] )
    → ( pdis : List (PDInstance r c) ) 
    → Any (Recons {r} {c} v) pdis
    ----------------------------------------------------------- 
    -- → Any (Recons {l ● r ` loc } {c} (PairU u v)) (concatMap (pdinstance-snd {l} {r} {ε∈l} {loc} {c})  pdis) -- inlined to make it easier to prove
    → Any (Recons {l ● r ` loc } {c} (PairU u v)) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  pdis) 
any-recons-concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdis any-recons-v-pdis = any-Snd (mkAllEmptyU ε∈l) (mkAllEmptyU-sound ε∈l)  u∈mkAllEmptU-ε∈l pdis any-recons-v-pdis  
  where

    u∈mkAllEmptU-ε∈l : Any ( u ≡_ ) (mkAllEmptyU {l} ε∈l)
    u∈mkAllEmptU-ε∈l = mkAllEmptyU-complete ε∈l u (flat-[] u proj1-flat-u≡[])
    any-Snd :  (es : List (U l))
      → (flat-[]-es : All (Flat-[] l) es )
      → Any ( u ≡_ ) es
      → ( pdis : List (PDInstance r c) )
      → Any (Recons {r} {c} v) pdis
      --------------------------------------------------------------------------------------------------------
      -- → Any (Recons {l ● r ` loc } {c} (PairU u v)) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  pdis)
      → Any (Recons {l ● r ` loc } {c} (PairU u v)) (concatMap (λ x →  pdinstance-snd {l} {r} {loc} {c} x pdis) (zip-es-flat-[]-es  {l} {ε∈l} es flat-[]-es))
    any-Snd []        _                         u∈[]        _    _                 = Nullary.contradiction u∈[] ¬Any[]
    any-Snd (e ∷ es) (flat-[]-e ∷ flat-[]-es) (there u∈es) pdis any-recons-v-pdis = any-right-concat (any-Snd es flat-[]-es u∈es pdis any-recons-v-pdis)
    -- the first parse tree is found, we need to search for the 2nd parse tree 
    any-Snd (e ∷ es) (flat-[]-e ∷ flat-[]-es) (here refl)  pdis any-recons-v-pdis  = any-left-concat any-recons-pair-e-v-pdinstance-snd
      where
        any-recons-pair-e-v-pdinstance-snd :  Any (Recons {l ● r ` loc } {c} (PairU e v)) (pdinstance-snd {l} {r} {loc} {c} ( e , flat-[]-e ) pdis )
        any-recons-pair-e-v-pdinstance-snd = any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v}  flat-[]-e pdis  any-recons-v-pdis


-- TODO: do we need {w} in all these any-recons lemmas? 
any-recons-assoc : ∀ { l t s : RE } { loc₁ loc₂ : ℕ } { c : Char } { w : List Char } {u₁ : U l } {u₂ : U t } { v : U s }
    → ( pdis :  List (PDInstance  ( l ● ( t ● s ` loc₂) ` loc₁ )  c ) )
    → Any (Recons { l ● ( t ● s ` loc₂) ` loc₁ } {c} ( PairU u₁ (PairU u₂ v)) ) pdis
    → Any (Recons { ( l ● t ` loc₁) ● s ` loc₂ } {c} ( PairU (PairU u₁ u₂) v) ) (List.map pdinstance-assoc pdis)
any-recons-assoc {l} {t} {s} {loc₁} {loc₂} {c} {w} {u₁} {u₂} {v} [] any-recons-pdis = Nullary.contradiction any-recons-pdis ¬Any[]
any-recons-assoc {l} {t} {s} {loc₁} {loc₂} {c} {w} {u₁} {u₂} {v} (pdi ∷ pdis) (there pxs) = there (any-recons-assoc {l} {t} {s} {loc₁} {loc₂} {c} {w} {u₁} {u₂} {v} pdis pxs)
any-recons-assoc {l} {t} {s} {loc₁} {loc₂} {c} {w} {u₁} {u₂} {v} (pdi@(pdinstance inj sound-ev) ∷ pdis)
  (here (recons pair-u₁-pair-u₂v ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡PairU-u₁-PairU-u₂-v ) ))
        = here (recons (PairU (PairU u₁ u₂) v) ( w∈⟦p⟧ , complete-evidence))
        where
          complete-evidence : mkinjAssoc inj (unflat w∈⟦p⟧) ≡ PairU (PairU u₁ u₂) v
          complete-evidence =
            begin
              mkinjAssoc inj (unflat w∈⟦p⟧)
            ≡⟨⟩
              inv-assoc (inj (unflat w∈⟦p⟧))
            ≡⟨ cong (λ x → inv-assoc x ) inj-unflat-w∈⟦p⟧≡PairU-u₁-PairU-u₂-v ⟩
              PairU (PairU u₁ u₂) v             
            ∎

-----------------------------------------------------------------------------------------
-- Sub Lemmas 19.1 - 19.7 END
----------------------------------------------------------------------------------------
```


### Definition 22 (Parse Tree Reconstructability of PD Descendants):

Let r be a non problematic regular expression.
Let pref be a word,
LEt u be a parse tree of r.
Let pdi be a partial derivative descendant (instance) of r w.r.t. prefix pref,
such that pdi = { p , inj , sound-ev }
  where
    1. p is the partial derivative descendant instance of r / pref
    2. inj is the injection function from the parse tree of p back to the parse tree of r;
    3. sound-ev is the soundness evidence pdi
Then we say pdi is prefix reconstructable w.r.t. pre iff there exists a word w ∈⟦p⟧ such that inj (unflat w∈⟦p⟧) ≡ u.


```agda

data Recons* : { r : RE } { pref : List Char } → ( u : U r ) → ( PDInstance* r pref ) → Set where
  recons* : ∀ { p r : RE } { w : List Char } { pref : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ pref ++ ( proj₁ (flat {p} x) )) }
    → ( u : U r )
    → ∃[ w∈⟦p⟧ ] ( (inj (unflat {p} {w} w∈⟦p⟧)) ≡ u ) -- the completeness property.
    → Recons* {r} {pref} u (pdinstance* {p} {r} {pref} inj sound-ev) -- <- the input PDI obj
```


Sub lemma 23.1 is moved here. 

```agda

compose-pdi-with-can-recons* : ∀ { r d : RE } { pref : List Char } { c : Char } 
                   → ( u : U r ) 
                   → ( v : U d ) 
                   → ( d→r : U d → U r )
                   → ( d→r-v≡u : d→r v ≡ u)  -- can we derive this w/o passing it in from the call site?
                   → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
                   → ( pdi : PDInstance d c)
                   → Recons {d} {c} v pdi  -- can we get rid of this premise? 
                   → Recons* {r} {pref ∷ʳ c} u (compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d-r pdi)
compose-pdi-with-can-recons* {r} {d} {pref} {c}  u v d→r d→r-v≡u s-ev-d-r pdi@(pdinstance {p} {d} {c} p→d s-ev-p-d) (recons v ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡v ) )
  = recons*  u (w∈⟦p⟧ , (begin
    d→r (p→d (unflat w∈⟦p⟧)) ≡⟨ cong (λ x → (d→r x) ) inj-unflat-w∈⟦p⟧≡v ⟩
    d→r v ≡⟨ d→r-v≡u ⟩
    u 
                         ∎ )) 




```


### Auxilary Lemmas needed in the ExtendedOrder.lagda.md proofs.


#### Aux Lemma: Reconstructibility can be inversedly preserved via the pdinstance's and pdinstance*'s operations.

```agda
-------------------------------------------------
-- Inversed reconstructibility Aux Lemmas BEGIN 
-------------------------------------------------

inv-recons-left : ∀ { l r : RE } { loc : ℕ } { c : Char } 
    → ( u : U l ) 
    → ( pdi : PDInstance l c )
    → Recons (LeftU {l} {r} {loc} u) (pdinstance-left pdi )
    ---------------------------------------------------------
    → Recons u pdi
inv-recons-left {l} {r} {loc} {c} u (pdinstance {p} {l} {c} inj s-ev) (recons (LeftU u') ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡LeftU-u ))
  = recons u (w∈⟦p⟧ , inv-leftU (inj (unflat w∈⟦p⟧)) u inj-unflat-w∈⟦p⟧≡LeftU-u) 


inv-recons-right : ∀ { l r : RE } { loc : ℕ } { c : Char } 
    → ( u : U r ) 
    → ( pdi : PDInstance r c )
    → Recons (RightU {l} {r} {loc} u) (pdinstance-right pdi )
    ---------------------------------------------------------
    → Recons u pdi
inv-recons-right {l} {r} {loc} {c} u (pdinstance {p} {r} {c} inj s-ev) (recons (RightU u') ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡RightU-u ))
  = recons u (w∈⟦p⟧ , inv-rightU (inj (unflat w∈⟦p⟧)) u inj-unflat-w∈⟦p⟧≡RightU-u)

inv-recons-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( u : U l )
    → ( v : U r )  
    → ( pdi : PDInstance l c )
    → Recons (PairU {l} {r} {loc} u v) (pdinstance-fst pdi )
    -------------------------------------------------------- 
    → Recons u pdi
inv-recons-fst {l} {r} {loc} {c} u v (pdinstance {p} {l} {c} inj s-ev)
  (recons {p ● r ` loc} {l ● r ` loc} {c} {w'} {inj'} {s-ev'} (PairU u' v') ( _●_⧺_  {xs} {ys} {w'} {p} {r} {loc} xs∈⟦p⟧  ys∈⟦r⟧ xs++ys≡w'  , inj-unflat-w'∈⟦p●r⟧≡PairU-u-v ))
  = recons {p} {l} {c} {xs} {inj} {s-ev}  u (xs∈⟦p⟧  , proj₁ inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r⟧≡v ) 
    where 
      inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r⟧≡v : ( inj (unflat xs∈⟦p⟧) ≡ u ) × ( unflat ys∈⟦r⟧ ≡ v )
      inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r⟧≡v = inv-pairU (inj (unflat xs∈⟦p⟧)) (unflat ys∈⟦r⟧) u v inj-unflat-w'∈⟦p●r⟧≡PairU-u-v



inv-recons-snd : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( e : U l ) -- empty parse tree from l
  → ( v : U r )
  → ( flat-[]-e :  Flat-[] l e )  
  → ( pdi : PDInstance r c )
  → Recons (PairU {l} {r} {loc} e v) (mk-snd-pdi ( e , flat-[]-e ) pdi )
  -----------------------------------------------------------------------
  → Recons v pdi
inv-recons-snd {l} {r} {loc} {c} e v ( flat-[] _ proj₁flat-e≡[]) (pdinstance inj s-ev) (recons (PairU _ _ ) ( w∈⟦p⟧ , inj∘unflat-w∈⟦p⟧≡pair-e-v ) )
  = recons v (w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡v)
    where
      e≡e×inj-unflat-w∈⟦p⟧≡v : ( e ≡ e ) × ((inj (unflat w∈⟦p⟧)) ≡ v )
      e≡e×inj-unflat-w∈⟦p⟧≡v = inv-pairU e (inj (unflat w∈⟦p⟧)) e v inj∘unflat-w∈⟦p⟧≡pair-e-v
      inj-unflat-w∈⟦p⟧≡v : inj (unflat w∈⟦p⟧) ≡ v
      inj-unflat-w∈⟦p⟧≡v = proj₂ e≡e×inj-unflat-w∈⟦p⟧≡v 


inv-recons-star : ∀ { r : RE } {ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  → ( u : U r )
  → ( us : List (U r) )
  → ( pdi : PDInstance r c )
  → Recons (ListU {r} {ε∉r} {loc} ( u ∷ us ) ) (pdinstance-star pdi )
  ---------------------------------------------------------------------
  → Recons u pdi
inv-recons-star {r} {ε∉r} {loc} {c} u us (pdinstance {p} {r} {c} inj s-ev)
  (recons {p ● ( r * ε∉r ` loc ) ` loc } { r * ε∉r ` loc } {c} {w'} {inj'} {s-ev'} (ListU {r} {ε∉r} {loc} ( u ∷ us )) (  _●_⧺_  {xs} {ys} {w'} {p} {r * ε∉r ` loc } {loc} xs∈⟦p⟧ ys∈⟦r*⟧ xs++ys≡w' , inj'-unflat-w'∈⟦p●r*⟧≡ListU-u-us )  ) = recons {p} {r} {c} {xs} {inj} {s-ev}  u (xs∈⟦p⟧  , proj₁ inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r*⟧≡list-us ) 
    where
      listu-u-us≡listu-inj-unflat-xs∈⟦p⟧-unListU-unflat-ys∈⟦r*⟧ : ListU (u ∷ us) ≡ ListU (inj (unflat xs∈⟦p⟧) ∷ unListU (unflat ys∈⟦r*⟧))
      listu-u-us≡listu-inj-unflat-xs∈⟦p⟧-unListU-unflat-ys∈⟦r*⟧ =
        begin
          ListU (u ∷ us)
        ≡⟨ sym  inj'-unflat-w'∈⟦p●r*⟧≡ListU-u-us ⟩
          mkinjList inj (PairU (unflat xs∈⟦p⟧) (unflat ys∈⟦r*⟧))
        ≡⟨ cong (λ x →  mkinjList inj (PairU (unflat xs∈⟦p⟧) x) ) ( sym listU∘unListU )  ⟩
          mkinjList inj (PairU (unflat xs∈⟦p⟧) (ListU (unListU (unflat ys∈⟦r*⟧))))
        ≡⟨⟩ 
          ListU (inj (unflat xs∈⟦p⟧) ∷ unListU (unflat ys∈⟦r*⟧))
        ∎ 
      inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r*⟧≡list-us : ( inj (unflat xs∈⟦p⟧) ≡ u ) × ( unListU (unflat ys∈⟦r*⟧) ≡ us )
      inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r*⟧≡list-us = inv-listU (inj (unflat xs∈⟦p⟧)) (unListU (unflat ys∈⟦r*⟧)) u us ((sym listu-u-us≡listu-inj-unflat-xs∈⟦p⟧-unListU-unflat-ys∈⟦r*⟧)) 

inv-recons-assoc : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
  → ( v₁ : U l )
  → ( v₂ : U s )
  → ( v₃ : U r )
  → ( pdi : PDInstance (l ● (s ● r ` loc₂) ` loc₁) c )
  → Recons (PairU (PairU v₁ v₂) v₃) (pdinstance-assoc pdi )
  ----------------------------------------------------------------
  → Recons (PairU v₁ (PairU v₂ v₃)) pdi
inv-recons-assoc {l} {s} {r} {loc₁} {loc₂} {c}  v₁ v₂ v₃ pdi@(pdinstance inj s-ev)
  (recons {p} { ( l ● s  ` loc₁ ) ● r ` loc₂} {c} {w} (PairU (PairU v₁ v₂) v₃) ( w∈⟦p⟧ , mkinjAssoc-inj-unflat-w∈⟦p⟧≡pair-pair-v₁v₂v₃))
    = recons (PairU v₁ (PairU v₂ v₃)) (w∈⟦p⟧ , sym pair-v₁-pair-v₂v₃≡inj-unflat-w∈⟦p⟧)
    where
      pair-v₁-pair-v₂v₃≡inj-unflat-w∈⟦p⟧ : PairU v₁ (PairU v₂ v₃) ≡ inj (unflat w∈⟦p⟧) 
      pair-v₁-pair-v₂v₃≡inj-unflat-w∈⟦p⟧ =
        begin
          PairU v₁ (PairU v₂ v₃)
        ≡⟨⟩
          assoc (PairU (PairU v₁ v₂) v₃)
        ≡⟨ cong ( λ x → assoc x ) (sym mkinjAssoc-inj-unflat-w∈⟦p⟧≡pair-pair-v₁v₂v₃ ) ⟩
          assoc (mkinjAssoc inj (unflat w∈⟦p⟧))
        ≡⟨⟩
          assoc (inv-assoc (inj (unflat w∈⟦p⟧)))
        ≡⟨ assoc-inv-assoc-u≡u ⟩
          inj (unflat w∈⟦p⟧)  
        ∎ 


inv-recons*-compose-pdi-with : ∀ { r d : RE } {pref : List Char } { c : Char }
  → ( u : U r )
  → ( pdi : PDInstance d c )
  → ( d→r : U d → U r )
  → ( s-ev-dr : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → Recons* {r} {pref ∷ʳ c}  u (compose-pdi-with d→r s-ev-dr pdi) 
  ----------------------------------------------------
  → Recons* {r} {pref} u (pdinstance* d→r s-ev-dr) 
inv-recons*-compose-pdi-with {r} {d} {pref} {c} u (pdinstance {p} {d} {c} p→d s-ev-pd) d→r s-ev-dr
  (recons* {p} {r} {w} {pref++c} u ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧ ) ) =
    recons* {- {d} {r} {c ∷ w} {pref} {d→r} {s-ev-dr} -}  u  ( proj₂ (flat (p→d (unflat w∈⟦p⟧))) , prf )
    where
      prf :  d→r (unflat (Product.proj₂ (flat (p→d (unflat w∈⟦p⟧))))) ≡ u
      prf =
        begin
          d→r (unflat (proj₂ (flat (p→d (unflat w∈⟦p⟧)))))
        ≡⟨ cong (λ x → (d→r x) ) unflat∘proj₂∘flat ⟩
          d→r (p→d (unflat w∈⟦p⟧))
        ≡⟨ inj-unflat-w∈⟦p⟧ ⟩ 
          u
        ∎

-------------------------------------------------
-- Inversed reconstructibility Aux Lemmas END
-------------------------------------------------
```



#### Aux Lemma: Impossibilities of parse tree reconstructions through pdinstance operations.

e.g. we can reconstruct a RightU from a pdinstance-left operation. 

```agda
-------------------------------------------------
-- Impossible reconstructibility Aux Lemmas BEGIN
-------------------------------------------------

-- A RightU parse tree cannot be reconstructed from a pdinstance-left created pdisntance
¬recons-right-from-pdinstance-left : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( u : U r ) 
  → ( pdi : PDInstance l c )
    ------------------------------------------------------------
  → ¬ (Recons (RightU {l} {r} {loc} u) (pdinstance-left pdi ))
¬recons-right-from-pdinstance-left {l} {r} {loc} {c} u pdi@(pdinstance {p} {l} inj s-ev) (recons {p'} {l + r ` loc } {c} {w} {inj'} {s-ev'} (RightU u) ( w∈⟦p'⟧ , inj∘unflat≡rightu-u ) )
  = (LeftU≢RightU {l} {r} {loc} (inj (unflat w∈⟦p'⟧)) u)  inj∘unflat≡rightu-u 


-- A LeftU parse tree cannot be reconstructed from a pdinstance-right created pdisntance
¬recons-left-from-pdinstance-right : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( u : U l ) 
  → ( pdi : PDInstance r c )
    ------------------------------------------------------------
  → ¬ (Recons (LeftU {l} {r} {loc} u) (pdinstance-right pdi ))
¬recons-left-from-pdinstance-right {l} {r} {loc} {c} u pdi@(pdinstance {p} {r} inj s-ev) (recons {p'} {l + r ` loc } {c} {w} {inj'} {s-ev'} (LeftU u) ( w∈⟦p'⟧ , inj∘unflat≡leftu-u ) )
  = (RightU≢LeftU {l} {r} {loc} (inj (unflat w∈⟦p'⟧)) u) inj∘unflat≡leftu-u




-- An ListU [] parse tree cannot be constructed from a pdinstance-map created pdinstance
¬recons-[]-from-pdinstance-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  -- → ( u : U r )
  → ( pdi : PDInstance r c )
  --------------------------------------------------------------
  → ¬ (Recons (ListU {r} {ε∉r} {loc} []) (pdinstance-star pdi ))
¬recons-[]-from-pdinstance-star {r} {ε∉r} {loc} {c} pdi@(pdinstance {p} {r} inj s-ev) (recons {p'} {r * ε∉r ` loc} {c} {w} {inj'} {s-ev'} (ListU []) ( w∈⟦p'⟧ , inj∘unflat≡list-[] ) )
   =  (Word.¬c∷w≡[] {c}  {proj₁ (flat (unflat w∈⟦p'⟧))})  c∷proj₁-flat-unflat-w∈⟦p'⟧≡[]  
   where
     proj₁flat-inj'-unflat-w∈⟦p'⟧≡c∷proj₁flat-unflat-w∈⟦p'⟧ : proj₁ (flat ( inj' (unflat w∈⟦p'⟧)) ) ≡ c ∷ proj₁ (flat (unflat w∈⟦p'⟧))
     proj₁flat-inj'-unflat-w∈⟦p'⟧≡c∷proj₁flat-unflat-w∈⟦p'⟧ = s-ev' (unflat w∈⟦p'⟧)
     proj₁flat-NilU≡c∷proj₁-flat-unflat-w∈⟦p'⟧ : proj₁ (flat (ListU  {r} {ε∉r} {loc} [])) ≡ c ∷ proj₁ (flat (unflat w∈⟦p'⟧))
     proj₁flat-NilU≡c∷proj₁-flat-unflat-w∈⟦p'⟧  = 
       begin
          proj₁ (flat (ListU  {r} {ε∉r} {loc} []))
       ≡⟨ cong (λ x →  proj₁ (flat x)) (sym inj∘unflat≡list-[] ) ⟩
          proj₁ (flat ( inj' (unflat w∈⟦p'⟧)) )
       ≡⟨ proj₁flat-inj'-unflat-w∈⟦p'⟧≡c∷proj₁flat-unflat-w∈⟦p'⟧ ⟩ 
          c ∷ proj₁ (flat (unflat w∈⟦p'⟧))
       ∎
     c∷proj₁-flat-unflat-w∈⟦p'⟧≡[] : c ∷ proj₁ (flat (unflat w∈⟦p'⟧)) ≡ [] 
     c∷proj₁-flat-unflat-w∈⟦p'⟧≡[] =
       begin
         c ∷ proj₁ (flat (unflat w∈⟦p'⟧))
       ≡⟨ sym proj₁flat-NilU≡c∷proj₁-flat-unflat-w∈⟦p'⟧ ⟩
         proj₁ (flat (ListU  {r} {ε∉r} {loc} []))
       ≡⟨⟩
         []
       ∎

-------------------------------------------------
-- Impossible reconstructibility Aux Lemmas END 
-------------------------------------------------       

```

