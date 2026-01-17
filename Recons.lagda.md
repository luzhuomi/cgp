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
