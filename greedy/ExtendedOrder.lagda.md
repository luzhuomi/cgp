```agda
{-# OPTIONS --rewriting #-}
module cgp.greedy.ExtendedOrder where

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
  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; unListU ; listU∘unListU ;
  u-of-r*-islist ; pair-≡ ; left-≡ ; right-≡ ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU)

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ; mkAllEmptyU≢[] )


import cgp.greedy.PartialDerivative as PartialDerivative
open PartialDerivative using (
  pdU[_,_] ; pdUConcat ; PDInstance ; pdinstance ;
  pdinstance-left ; pdinstance-right; pdinstance-fst ;
  mkinjFst ;  pdinstance-snd ; concatmap-pdinstance-snd ;
  zip-es-flat-[]-es ; mk-snd-pdi ; mkinjSnd ;
  pdinstance-star ; mkinjList ; flat-Uε≡[];
  pdinstance-assoc; inv-assoc; assoc; assoc-inv-assoc-u≡u ; inv-assoc-assoc-u≡u ; mkinjAssoc ;
  pdinstance-dist ; inv-dist ; dist ; dist-inv-dist-u≡u ; inv-dist-dist-u≡u ; mkinjDist ;
  pdUMany[_,_]; pdUMany-aux;  PDInstance* ; pdinstance* ;
  advance-pdi*-with-c ; compose-pdi-with ; 
  Recons ; recons ;
  Recons* ; recons* ;
  injId ;
  pdUMany-aux-cs-[]≡[];
  parseAll[_,_] ; buildU ) 


import cgp.greedy.Order as GreedyOrder
open GreedyOrder using ( _⊢_>_ ; seq₁ ; seq₂ ; choice-ll ; choice-rr ; choice-lr ; star-head ; star-cons-nil ;
  >-sorted ; >-nil ; >-cons ;
  mkAllEmptyU-sorted ;
  >-maybe ; >-nothing ; >-just ;
  >-trans ; *>-Inc ; *>-inc ;
  concatmap-advance-pdi*-with-c-*>inc ;
  pdUMany-*>-inc ) 


import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_  )

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


### Definition 34 : (Extended) greedy ordering among PDInstances 

Let r be a non problematic regular expression.

Let c be a letter.

Let pdi₁ and pdi₂ be two partial derivative instances of r w.r.t c.

We say pdi₁ is greedier than pdi₂, r , c  ⊢ pdi₁ > pdi₂ iff
  for all parse trees u₁ u₂  of r, u₁ is constructable from pdi₁ and u₂ is constructabled from pdi₂ 
    then r ⊢ u₁ > u₂ 


```agda

data _,_⊢_>_ : ∀ ( r : RE ) → (c : Char ) → PDInstance r c → PDInstance r c → Set where
  >-pdi : ∀ { r : RE } { c : Char }
    → ( pdi₁ : PDInstance r c )
    → ( pdi₂ : PDInstance r c )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r ) → (Recons u₁ pdi₁ ) → (Recons u₂ pdi₂) → ( r ⊢ u₁ > u₂) )
    → r , c ⊢ pdi₁ > pdi₂ 
```


### Definition 35 : (Extended) greedy order sortedness

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
```



### Lemma 36: the list of pdinstances from pdU[ r , c] is extended greedily sorted. 


Let r be a non problematic regular expression.

Let c be a letter.

Then pdU[r , c] is extended greedily sorted. 


```agda

-- these should be moved to PartialDerivative

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



inv-recons-dist-left  : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char }
  → ( v₁ : U l )
  → ( v₃ : U r )
  → ( pdi :  PDInstance  ( l ● r ` loc₂ )  c )
  → Recons (PairU {l + s ` loc₁} {r} {loc₂} (LeftU {l} {s} {loc₁} v₁) v₃) (pdinstance-dist (pdinstance-left pdi ))
  ------------------------------------------------------------------
  → Recons (dist {l} {s} {r} {loc₁} {loc₂} (PairU (LeftU v₁) v₃)) (pdinstance-left pdi )
inv-recons-dist-left  v₁ v₃ pdi@(pdinstance inj sev) (recons (PairU (LeftU v₁) v₃) ( w∈⟦p⟧ , inj∘unflat-w∈⟦p⟧≡Pair-left-v₁-v₃ ) ) =
  recons (dist (PairU (LeftU v₁) v₃)) (w∈⟦p⟧ , sym left-pair-v₁-v₃≡left-inj-unflat-w∈⟦p⟧) 
  where
    pair-left-v₁-v₃≡inv-dist-left-inj-unflat-w∈⟦p⟧ : PairU (LeftU v₁) v₃ ≡  inv-dist (LeftU (inj (unflat w∈⟦p⟧)))
    pair-left-v₁-v₃≡inv-dist-left-inj-unflat-w∈⟦p⟧ =
      begin
        PairU (LeftU v₁) v₃
      ≡⟨ sym inj∘unflat-w∈⟦p⟧≡Pair-left-v₁-v₃ ⟩
        mkinjDist (λ u → LeftU (inj u)) (unflat w∈⟦p⟧)
      ≡⟨⟩
        inv-dist ((λ u → LeftU (inj u)) (unflat w∈⟦p⟧))
      ≡⟨⟩
        inv-dist (LeftU (inj (unflat w∈⟦p⟧)))
      ∎
    left-pair-v₁-v₃≡left-inj-unflat-w∈⟦p⟧ : LeftU (PairU v₁ v₃) ≡ LeftU (inj (unflat w∈⟦p⟧))
    left-pair-v₁-v₃≡left-inj-unflat-w∈⟦p⟧ =
      begin
        LeftU (PairU v₁ v₃)
      ≡⟨⟩
        dist (PairU (LeftU v₁) v₃)
      ≡⟨ cong (λ x → dist x ) pair-left-v₁-v₃≡inv-dist-left-inj-unflat-w∈⟦p⟧ ⟩ 
        dist (inv-dist (LeftU (inj (unflat w∈⟦p⟧))))
      ≡⟨ dist-inv-dist-u≡u ⟩
        LeftU (inj (unflat w∈⟦p⟧))
      ∎ 


inv-recons-dist-left-collary : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char }
  → ( v₁ : U l )
  → ( v₃ : U r )
  → ( pdi :  PDInstance  ( l ● r ` loc₂ )  c )
  → Recons (PairU {l + s ` loc₁} {r} {loc₂} (LeftU {l} {s} {loc₁} v₁) v₃) (pdinstance-dist (pdinstance-left pdi ))
  ------------------------------------------------------------------
  → Recons (PairU {l} {r} {loc₂} v₁ v₃) pdi 
inv-recons-dist-left-collary  v₁ v₃ pdi@(pdinstance inj sev) (recons .(PairU (LeftU v₁) v₃) ( w∈⟦p⟧ , inj∘unflat-w∈⟦p⟧≡Pair-left-v₁-v₃) )
  with inv-recons-dist-left  v₁ v₃ pdi (recons (PairU (LeftU v₁) v₃) ( w∈⟦p⟧ , inj∘unflat-w∈⟦p⟧≡Pair-left-v₁-v₃) )
... | recons (LeftU (PairU v₁ v₃)) ( w∈⟦p⟧ , left-inj-unflat-w∈⟦p⟧≡left-pair-v₁-v₃ )  =
  recons (PairU v₁ v₃) ( w∈⟦p⟧ , inv-leftU (inj (unflat w∈⟦p⟧)) (PairU v₁ v₃)   left-inj-unflat-w∈⟦p⟧≡left-pair-v₁-v₃) 



inv-recons-dist-right  : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char }
  → ( v₂ : U s )
  → ( v₃ : U r )
  → ( pdi :  PDInstance  ( s ● r ` loc₂ )  c )
  → Recons (PairU {l + s ` loc₁} {r} {loc₂} (RightU {l} {s} {loc₁} v₂) v₃) (pdinstance-dist (pdinstance-right pdi ))
  ------------------------------------------------------------------
  → Recons (dist {l} {s} {r} {loc₁} {loc₂} (PairU (RightU v₂) v₃)) (pdinstance-right pdi )
inv-recons-dist-right  v₂ v₃ pdi@(pdinstance inj sev) (recons (PairU (RightU v₂) v₃) ( w∈⟦p⟧ , inj∘unflat-w∈⟦p⟧≡Pair-right-v₂-v₃ ) ) =
  recons (dist (PairU (RightU v₂) v₃)) (w∈⟦p⟧ , sym right-pair-v₂-v₃≡right-inj-unflat-w∈⟦p⟧) 
  where
    pair-right-v₂-v₃≡inv-dist-right-inj-unflat-w∈⟦p⟧ : PairU (RightU v₂) v₃ ≡  inv-dist (RightU (inj (unflat w∈⟦p⟧)))
    pair-right-v₂-v₃≡inv-dist-right-inj-unflat-w∈⟦p⟧ =
      begin
        PairU (RightU v₂) v₃
      ≡⟨ sym inj∘unflat-w∈⟦p⟧≡Pair-right-v₂-v₃ ⟩
        mkinjDist (λ u → RightU (inj u)) (unflat w∈⟦p⟧)
      ≡⟨⟩
        inv-dist ((λ u → RightU (inj u)) (unflat w∈⟦p⟧))
      ≡⟨⟩
        inv-dist (RightU (inj (unflat w∈⟦p⟧)))
      ∎
    right-pair-v₂-v₃≡right-inj-unflat-w∈⟦p⟧ : RightU (PairU v₂ v₃) ≡ RightU (inj (unflat w∈⟦p⟧))
    right-pair-v₂-v₃≡right-inj-unflat-w∈⟦p⟧ =
      begin
        RightU (PairU v₂ v₃)
      ≡⟨⟩
        dist (PairU (RightU v₂) v₃)
      ≡⟨ cong (λ x → dist x ) pair-right-v₂-v₃≡inv-dist-right-inj-unflat-w∈⟦p⟧ ⟩ 
        dist (inv-dist (RightU (inj (unflat w∈⟦p⟧))))
      ≡⟨ dist-inv-dist-u≡u ⟩
        RightU (inj (unflat w∈⟦p⟧))
      ∎ 


inv-recons-dist-right-collary : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char }
  → ( v₂ : U s )
  → ( v₃ : U r )
  → ( pdi :  PDInstance  ( s ● r ` loc₂ )  c )
  → Recons (PairU {l + s ` loc₁} {r} {loc₂} (RightU {l} {s} {loc₁} v₂) v₃) (pdinstance-dist (pdinstance-right pdi ))
  ------------------------------------------------------------------
  → Recons (PairU {s} {r} {loc₂} v₂ v₃) pdi 
inv-recons-dist-right-collary  v₂ v₃ pdi@(pdinstance inj sev) (recons .(PairU (RightU v₂) v₃) ( w∈⟦p⟧ , inj∘unflat-w∈⟦p⟧≡Pair-right-v₂-v₃) )
  with inv-recons-dist-right  v₂ v₃ pdi (recons (PairU (RightU v₂) v₃) ( w∈⟦p⟧ , inj∘unflat-w∈⟦p⟧≡Pair-right-v₂-v₃) )
... | recons (RightU (PairU v₂ v₃)) ( w∈⟦p⟧ , right-inj-unflat-w∈⟦p⟧≡right-pair-v₂-v₃ )  =
  recons (PairU v₂ v₃) ( w∈⟦p⟧ , inv-rightU (inj (unflat w∈⟦p⟧)) (PairU v₂ v₃)  right-inj-unflat-w∈⟦p⟧≡right-pair-v₂-v₃) 


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
    recons* {- {d} {r} {c ∷ w} {pref} {d→r} {s-ev-dr} -}  u  ( proj₂ (flat (p→d (unflat w∈⟦p⟧))) , prove )
    where
      prove :  d→r (unflat (Product.proj₂ (flat (p→d (unflat w∈⟦p⟧))))) ≡ u
      prove =
        begin
          d→r (unflat (proj₂ (flat (p→d (unflat w∈⟦p⟧)))))
        ≡⟨ cong (λ x → (d→r x) ) unflat∘proj₂∘flat ⟩
          d→r (p→d (unflat w∈⟦p⟧))
        ≡⟨ inj-unflat-w∈⟦p⟧ ⟩ 
          u
        ∎


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


¬recons-pair-right-from-pdinstance-dist-left : ∀ { l s r : RE } { loc₁ loc₂ : ℕ } { c : Char }
  → ( v₂ : U s )
  → ( v₃ : U r )
  → ( pdi :  PDInstance  ( l ● r ` loc₂ )  c )
  -------------------------------------------------------------------------------------------
  → ¬ (Recons (PairU { l + s ` loc₁ } {r} {loc₂} (RightU {l} {s} {loc₁} v₂) v₃) (pdinstance-dist (pdinstance-left pdi)))
¬recons-pair-right-from-pdinstance-dist-left {l} {s} {r} {loc₁} {loc₂} {c} v₂ v₃ pdi@(pdinstance inj s-ev)
  (recons {p} {(l + s ` loc₁) ● r ` loc₂} {c} {w} {inj'} {s-ev'} (PairU (RightU v₂) v₃) ( w∈⟦p⟧ , inj'∘unflatw∈⟦p⟧≡pair-right-v₂-v₂ ) )
   with inj (unflat w∈⟦p⟧)  
... | PairU v₁ v₄
  = (proj₁∘LeftU≢proj₁∘RightU {l} {s} {r} {loc₁} {loc₂}  v₁  v₂ v₄ v₃ )  inj'∘unflatw∈⟦p⟧≡pair-right-v₂-v₂

¬recons-pair-left-from-pdinstance-dist-right : ∀ { l s r : RE } { loc₁ loc₂ : ℕ } { c : Char }
  → ( v₁ : U l )
  → ( v₃ : U r )
  → ( pdi :  PDInstance  ( s ● r ` loc₂ )  c )
  ------------------------------------------------------------------------------
  → ¬ (Recons (PairU { l + s ` loc₁ } {r} {loc₂} (LeftU {l} {s} {loc₁} v₁) v₃) (pdinstance-dist (pdinstance-right pdi)))
¬recons-pair-left-from-pdinstance-dist-right {l} {s} {r} {loc₁} {loc₂} {c} v₁ v₃
  pdi@(pdinstance inj s-ev)
  (recons {p} {(l + s ` loc₁) ● r ` loc₂} {c} {w} {inj'} {s-ev'} (PairU (LeftU v₁) v₃) ( w∈⟦p⟧ , inj'∘unflatw∈⟦p⟧≡pair-left-v₁-v₃ ) )
    with inj (unflat w∈⟦p⟧)
... | PairU v₂ v₄     
  = (proj₁∘LeftU≢proj₁∘RightU {l} {s} {r} {loc₁} {loc₂}   v₁ v₂ v₃ v₄)  ( (sym  inj'∘unflatw∈⟦p⟧≡pair-left-v₁-v₃))  


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
       
         

left-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁  : PDInstance l c )
  → (pdi₂ : PDInstance l c )
  → l , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (l + r ` loc) , c ⊢ pdinstance-left pdi₁ > pdinstance-left pdi₂
left-ex-sorted {l} {r} {loc} {c} pdi₁ pdi₂ (>-pdi _ _ pdi₁>-pdi₂-ev ) = >-pdi left-pdi₁ left-pdi₂ ev
  where
    left-pdi₁ : PDInstance ( l + r ` loc ) c
    left-pdi₁ = pdinstance-left pdi₁
    left-pdi₂ : PDInstance ( l + r ` loc ) c    
    left-pdi₂ = pdinstance-left pdi₂    
 
    ev : ∀ ( u₁ : U  (l + r ` loc) )
          → ( u₂ : U  (l + r ` loc) )
          → ( Recons u₁ left-pdi₁ )
          → ( Recons u₂ left-pdi₂ )
          -------------------------
          → ( (l + r ` loc) ⊢ u₁ > u₂ )
    ev (LeftU v₁) (LeftU v₂)  recons-left-v₁-pdi-left recons-left-v₂-pdi-left =
             {-
             to make use of
              1) pdi₁>-pdi₂-ev : (u₃ u₄ : U l₁) → Recons u₃ pdi₁ → Recons u₄ pdi₂ → l₁ ⊢ u₃ > u₄
              we need to compute recons v pd₁ from recons (Left v) left-pdi₁
              2) then we have l ⊢ v > u , we can apply choice-ll rule to get l + r ` loc ⊢ LeftU v > LeftU u
             -} 
       let recons-v₁-pdi₁ = inv-recons-left {l} {r} {loc} v₁  pdi₁  recons-left-v₁-pdi-left 
           recons-v₂-pdi₂ = inv-recons-left {l} {r} {loc} v₂  pdi₂  recons-left-v₂-pdi-left
       in choice-ll (pdi₁>-pdi₂-ev v₁ v₂  recons-v₁-pdi₁ recons-v₂-pdi₂) 
    ev (RightU v₁)  _          recons-right-v₁-pdi-left _  =  Nullary.contradiction recons-right-v₁-pdi-left (¬recons-right-from-pdinstance-left v₁ pdi₁ ) -- impossible cases
    ev (LeftU _)   (RightU v₂) _  recons-right-v₂-pdi-left =   Nullary.contradiction recons-right-v₂-pdi-left (¬recons-right-from-pdinstance-left v₂ pdi₂  )




right-ex-sorted : ∀ { l r : RE } {loc : ℕ} { c : Char } 
  → (pdi₁ : PDInstance r c )
  → (pdi₂ : PDInstance r c )
  → r , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (l + r ` loc) , c ⊢ pdinstance-right pdi₁ > pdinstance-right pdi₂
right-ex-sorted {l} {r} {loc} {c} pdi₁ pdi₂ (>-pdi _ _ pdi₁>-pdi₂-ev ) = >-pdi right-pdi₁ right-pdi₂ ev
  where
    right-pdi₁ : PDInstance ( l + r ` loc ) c
    right-pdi₁ = pdinstance-right pdi₁
    right-pdi₂ : PDInstance ( l + r ` loc ) c    
    right-pdi₂ = pdinstance-right pdi₂    
 
    ev : ∀ ( u₁ : U  (l + r ` loc) )
          → ( u₂ : U  (l + r ` loc) )
          → ( Recons u₁ right-pdi₁ )
          → ( Recons u₂ right-pdi₂ )
          -------------------------
          → ( (l + r ` loc) ⊢ u₁ > u₂ )
    ev (RightU v₁) (RightU v₂)  recons-right-v₁-pdi-right recons-right-v₂-pdi-right =
       let recons-v₁-pdi₁ = inv-recons-right {l} {r} {loc} v₁  pdi₁  recons-right-v₁-pdi-right 
           recons-v₂-pdi₂ = inv-recons-right {l} {r} {loc} v₂  pdi₂  recons-right-v₂-pdi-right
       in choice-rr (pdi₁>-pdi₂-ev v₁ v₂  recons-v₁-pdi₁ recons-v₂-pdi₂) 
    ev (LeftU v₁)  _             recons-left-v₁-pdi-right _  =  Nullary.contradiction recons-left-v₁-pdi-right (¬recons-left-from-pdinstance-right v₁ pdi₁ ) -- impossible cases
    ev (RightU _)  (LeftU v₂) _  recons-left-v₂-pdi-right =   Nullary.contradiction recons-left-v₂-pdi-right (¬recons-left-from-pdinstance-right v₂ pdi₂  )




-- the following look like can be combined polymorphically with map-leftU-sorted, map-rightU-sorted, map-leftU-rightU-sorted from Greedy.lagda.md
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

map-left-right-ex-sorted : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( pdis  : List (PDInstance l c) )
  → ( pdis' : List (PDInstance r c) )
  → Ex>-sorted {l} pdis
  → Ex>-sorted {r} pdis'
  → Ex>-sorted {l + r ` loc } ((List.map pdinstance-left pdis) ++ (List.map pdinstance-right pdis'))
map-left-right-ex-sorted               []              pdis'  ex>-sorted-l-[]   ex>-sorted-r-pdis' = map-right-ex-sorted pdis' ex>-sorted-r-pdis'
map-left-right-ex-sorted {l} {r} {loc} pdis            []     ex>-sorted-l-pdis ex>-sorted-r-[] rewrite (cong (λ x → Ex>-sorted x) (++-identityʳ (List.map (pdinstance-left {l} {r} {loc}) pdis)))
  = map-left-ex-sorted  pdis ex>-sorted-l-pdis 
map-left-right-ex-sorted {l} {r} {loc} (pdi ∷ [])      (pdi' ∷ pdis')    ex>-sorted-l-pdis  ex>-sorted-r-pdis'
  = ex>-cons (map-right-ex-sorted (pdi' ∷ pdis') ex>-sorted-r-pdis') (ex>-just (>-pdi (pdinstance-left pdi) (pdinstance-right pdi')
    (λ { (LeftU v₁) (RightU v₂) recons-left-u-from-pdinstance-left   recons-right-u-from-pdinstance-right → choice-lr
        -- impossible cases
       ; (RightU v₁) _          recons-right-u-from-pdinstance-left  _              → Nullary.contradiction recons-right-u-from-pdinstance-left  (¬recons-right-from-pdinstance-left v₁ pdi )
       ; (LeftU v₁) (LeftU v₂)  _  recons-left-u-from-pdinstance-right              → Nullary.contradiction recons-left-u-from-pdinstance-right  (¬recons-left-from-pdinstance-right v₂ pdi' ) 
       }
    )))
map-left-right-ex-sorted {l} {r} {loc} (pdi₁ ∷ pdi₂ ∷ pdis)   (pdi' ∷ pdis') ex>-sorted-l-pdi₁pdi₂pdis ex>-sorted-r-pdipdis' with ex>-sorted-l-pdi₁pdi₂pdis
... | ex>-cons {l} ex>-sorted-pdi₂pdis (ex>-just (>-pdi _ _ pdi₁>pdi₂-ev) ) 
  = ex>-cons (map-left-right-ex-sorted (pdi₂ ∷ pdis) (pdi' ∷ pdis')   ex>-sorted-pdi₂pdis  ex>-sorted-r-pdipdis' ) ((ex>-just (>-pdi (pdinstance-left pdi₁) (pdinstance-left pdi₂)
    (λ { (LeftU v₁) (LeftU v₂)  recons-left-v1-from-pdinstance-left-pdi₁ recons-left-v2-from-pdinstance-left-pdi₂ →
         let recons-v₁-pdi₁ = inv-recons-left {l} {r} {loc} v₁  pdi₁  recons-left-v1-from-pdinstance-left-pdi₁
             recons-v₂-pdi₂ = inv-recons-left {l} {r} {loc} v₂  pdi₂  recons-left-v2-from-pdinstance-left-pdi₂
         in choice-ll ( pdi₁>pdi₂-ev v₁ v₂ recons-v₁-pdi₁ recons-v₂-pdi₂ )
        -- impossible cases         
       ; (RightU v₁)  _         recons-right-u-from-pdinstance-left-pdi₁ _ → Nullary.contradiction recons-right-u-from-pdinstance-left-pdi₁ ( ¬recons-right-from-pdinstance-left v₁ pdi₁ )
       ; (LeftU v₁) (RightU v₂) _ recons-right-u-from-pdinstance-left-pdi₂ → Nullary.contradiction recons-right-u-from-pdinstance-left-pdi₂ ( ¬recons-right-from-pdinstance-left v₂ pdi₂ )       
       }
    )))) 



star-ex-sorted : ∀ { r : RE }  { ε∉r : ε∉ r } {loc : ℕ} { c : Char } 
  → (pdi₁ : PDInstance r c )
  → (pdi₂ : PDInstance r c )
  → r , c ⊢ pdi₁ > pdi₂ 
  -------------------------------------------------
  → (r * ε∉r ` loc) , c ⊢ pdinstance-star pdi₁ > pdinstance-star pdi₂
star-ex-sorted {r} {ε∉r} {loc} {c} pdi₁ pdi₂ (>-pdi _ _ pdi₁>-pdi₂-ev ) = >-pdi star-pdi₁ star-pdi₂ ev
  where
    star-pdi₁ : PDInstance ( r * ε∉r ` loc ) c
    star-pdi₁ = pdinstance-star pdi₁
    star-pdi₂ : PDInstance ( r * ε∉r ` loc ) c    
    star-pdi₂ = pdinstance-star pdi₂    
 
    ev : ∀ ( t₁ : U  (r * ε∉r ` loc) )
          → ( t₂ : U  (r * ε∉r ` loc) )
          → ( Recons t₁ star-pdi₁ )
          → ( Recons t₂ star-pdi₂ )
          -------------------------
          → ( (r * ε∉r ` loc) ⊢ t₁ > t₂ )
    ev (ListU []) _ recons-[]-star-pdi₁ _ = Nullary.contradiction  recons-[]-star-pdi₁ (¬recons-[]-from-pdinstance-star pdi₁)
    ev _ (ListU []) _ recons-[]-star-pdi₂ = Nullary.contradiction  recons-[]-star-pdi₂ (¬recons-[]-from-pdinstance-star pdi₂)
    ev (ListU (v₁ ∷ vs₁)) (ListU (v₂ ∷ vs₂)) recons-list-vvs₁-star-pdi₁ recons-list-vvs₂-star-pdi₂ =
      let recons-v₁-pdi₁ = inv-recons-star v₁ vs₁ pdi₁ recons-list-vvs₁-star-pdi₁ 
          recons-v₂-pdi₂ = inv-recons-star v₂ vs₂ pdi₂ recons-list-vvs₂-star-pdi₂
      in star-head (pdi₁>-pdi₂-ev v₁ v₂ recons-v₁-pdi₁ recons-v₂-pdi₂)

  

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
fst-ex-sorted {l} {r} {loc} {c} pdi₁ pdi₂ (>-pdi _ _ pdi₁>-pdi₂-ev ) = >-pdi fst-pdi₁ fst-pdi₂ ev
  where
    fst-pdi₁ : PDInstance ( l ● r ` loc ) c
    fst-pdi₁ = pdinstance-fst pdi₁
    fst-pdi₂ : PDInstance ( l ● r ` loc ) c    
    fst-pdi₂ = pdinstance-fst pdi₂    
 
    ev : ∀ ( t₁ : U  (l ● r ` loc) )
          → ( t₂ : U  (l ● r ` loc) )
          → ( Recons t₁ fst-pdi₁ )
          → ( Recons t₂ fst-pdi₂ )
          -------------------------
          → ( (l ● r ` loc) ⊢ t₁ > t₂ )
    ev (PairU u₁ v₁) (PairU u₂ v₂)  recons-pair-u₁v₁-pdi-fst recons-pair-u₁v₂-pdi-fst =
       let recons-u₁-pdi₁ = inv-recons-fst {l} {r} {loc} u₁ v₁ pdi₁  recons-pair-u₁v₁-pdi-fst 
           recons-u₂-pdi₂ = inv-recons-fst {l} {r} {loc} u₂ v₂ pdi₂  recons-pair-u₁v₂-pdi-fst
       in seq₁ (pdi₁>-pdi₂-ev u₁ u₂  recons-u₁-pdi₁ recons-u₂-pdi₂) 




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



mk-snd-pdi-fst-pair-≡ : ∀ { l r : RE } { loc : ℕ } { c : Char }
                      → ( pdi : PDInstance r c ) 
                      → ( e : U l ) -- empty parse tree from l
                      → ( flat-[]-e :  Flat-[] l e )
                      → ( u : U l )
                      → ( v : U r )                      
                      →  Recons (PairU {l} {r} {loc} u v) (mk-snd-pdi ( e , flat-[]-e ) pdi )
                      ----------------------------------------------
                      → u ≡ e 
mk-snd-pdi-fst-pair-≡ {l} {r} {loc} {c} pdi@(pdinstance inj s-ev) e (flat-[] {l} e proj₁∘flat-e≡[]) u v (recons {p} { l ● r ` loc } {c} {w} {injSnd} {injSnd-s} (PairU _ _) ( w∈⟦p⟧ , injSnd∘unflat-w∈⟦p⟧≡pair-u-v ) )  = proj₁ u≡e×v≡inj-unflat-w∈⟦p⟧                       
  where
    injSnd-unflat-w∈⟦p⟧≡pair-u-inj-unflat-w∈⟦p⟧ : mkinjSnd {l} {r} {p} {loc} inj u (unflat w∈⟦p⟧) ≡ PairU u (inj (unflat w∈⟦p⟧))
    injSnd-unflat-w∈⟦p⟧≡pair-u-inj-unflat-w∈⟦p⟧ =
      begin
        mkinjSnd {l} {r} {p} {loc} inj u (unflat w∈⟦p⟧)
      ≡⟨⟩
        PairU {l} {r} {loc} u (inj (unflat w∈⟦p⟧))
      ∎
    pair-u-v≡pair-e-inj-unflat-w∈⟦p⟧  : PairU u v ≡ PairU {l} {r} {loc} e (inj (unflat w∈⟦p⟧) )
    pair-u-v≡pair-e-inj-unflat-w∈⟦p⟧ =
      begin
        PairU u v
      ≡⟨ sym injSnd∘unflat-w∈⟦p⟧≡pair-u-v ⟩
        PairU e (inj (unflat w∈⟦p⟧) )
      ∎
    u≡e×v≡inj-unflat-w∈⟦p⟧ : (u ≡ e) × (v ≡ inj (unflat w∈⟦p⟧))
    u≡e×v≡inj-unflat-w∈⟦p⟧ = inv-pairU u v e (inj (unflat w∈⟦p⟧)) pair-u-v≡pair-e-inj-unflat-w∈⟦p⟧



-- main sub lemma :
-- pdinstances generated by pdinstance-snd is ex>-sorted.

pdinstance-snd-ex>-sorted : ∀ { l r : RE } { loc : ℕ } { c : Char }
                → (e-flat-[]-e : ∃[ e ] Flat-[] l e ) 
                → (pdis : List (PDInstance r c) )
                → Ex>-sorted {r} pdis 
                → Ex>-sorted { l ● r ` loc } (List.map (mk-snd-pdi {l} {r} {loc} {c}  e-flat-[]-e) pdis)
pdinstance-snd-ex>-sorted {l} {r} {loc} {c}  (e , flat-[]-e ) []            ex>-nil                                   = ex>-nil
pdinstance-snd-ex>-sorted {l} {r} {loc} {c}  (e , flat-[]-e ) (pdi ∷ [] ) (ex>-cons ex>-nil ex>-nothing)              = ex>-cons ex>-nil ex>-nothing

pdinstance-snd-ex>-sorted {l} {r} {loc} {c}  (e , flat-[]-e) (pdi₁ ∷ pdi₂ ∷ pdis ) (ex>-cons pdi₂pdis-ex>-sorted (ex>-just (>-pdi pdi₁ pdi₂ u₁→u₂→recons-u₁→recons-u₂→u₁>u₂)))  =
  ex>-cons (pdinstance-snd-ex>-sorted (e , flat-[]-e) (pdi₂ ∷ pdis) pdi₂pdis-ex>-sorted)
           (ex>-just (>-pdi (mk-snd-pdi (e , flat-[]-e) pdi₁)
                            (mk-snd-pdi (e , flat-[]-e) pdi₂)
                            (λ { (PairU e₁ u₁) (PairU e₂ u₂)
                                 recons-pair-e-u1 recons-pair-e-u2 
                                  → ev-> e₁ u₁ e₂ u₂ recons-pair-e-u1 recons-pair-e-u2  }  )) )

  where

     ev-> : (v₁ : U l )
          → (v₁' : U r )
          → (v₂ : U l )
          → (v₂' : U r )
          → Recons {l ● r ` loc} {c} (PairU v₁ v₁')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e ) pdi₁)
          → Recons {l ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e ) pdi₂ )
          --------------------------------------------------
          → (l ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂' 
     ev-> v₁ v₁' v₂ v₂' recons1 recons2
          =  seq₂ v₁≡v₂ v₁'>v₂' 
          where
            v₁≡e : v₁ ≡ e
            v₁≡e = mk-snd-pdi-fst-pair-≡ pdi₁ e flat-[]-e v₁ v₁' recons1
            v₂≡e : v₂ ≡ e
            v₂≡e = mk-snd-pdi-fst-pair-≡ pdi₂ e flat-[]-e v₂ v₂' recons2
            v₁≡v₂ : v₁ ≡ v₂ 
            v₁≡v₂ rewrite v₁≡e | v₂≡e = refl
            recons1' :  Recons {l ● r ` loc} {c} (PairU e v₁')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e) pdi₁)
            recons1' rewrite cong (λ x → Recons {l ● r ` loc} {c} (PairU x v₁')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e ) pdi₁) ) (sym v₁≡e) = recons1
            recons2' :  Recons {l ● r ` loc} {c} (PairU e v₂')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e) pdi₂)
            recons2' rewrite cong (λ x → Recons {l ● r ` loc} {c} (PairU x v₂')  ( mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e ) pdi₂) ) (sym v₂≡e) = recons2
            recons-v₁' : Recons v₁' pdi₁
            recons-v₁' = inv-recons-snd {l} {r} {loc} {c}  e v₁' flat-[]-e pdi₁ recons1' 
            recons-v₂' : Recons v₂' pdi₂
            recons-v₂' = inv-recons-snd {l} {r} {loc} {c}  e v₂' flat-[]-e pdi₂ recons2'
            v₁'>v₂' = u₁→u₂→recons-u₁→recons-u₂→u₁>u₂ v₁' v₂'  recons-v₁'  recons-v₂'



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


-- same as the above, instead of ex sorted, it cover sorted 
concat-sorted : ∀ { r : RE } 
  → ( us₁ : List ( U r ) )
  → ( us₂ : List ( U r ) )
  → >-sorted { r } us₁
  → >-sorted { r } us₂
  → All (λ u₁ → >-maybe {r} u₁ (head us₂)) us₁
  ----------------------------------------------
  → >-sorted { r } (us₁ ++ us₂)
concat-sorted []               us₂        >-nil        us₂-sorted    []                            = us₂-sorted
concat-sorted us₁              []         us₁-sorted   >-nil         _  rewrite (++-identityʳ us₁) = us₁-sorted
concat-sorted (u₁ ∷ [])        (u₂ ∷ us₂) us₁-sorted   u₂us₂-sorted  (>-just u₁>u₂ ∷ [] )          = >-cons u₂us₂-sorted (>-just u₁>u₂)
concat-sorted (u₁ ∷ u₁' ∷ us₁) (u₂ ∷ us₂) (>-cons u₁'us₁-sorted (>-just u₁>u₁'))  u₂us₂-sorted (>-just u₁>u₂ ∷ pxs) = >-cons ind-hyp (>-just u₁>u₁')
  where
    ind-hyp = concat-sorted (u₁' ∷ us₁) (u₂ ∷ us₂) u₁'us₁-sorted u₂us₂-sorted pxs



---------------------------------------------------------------------------------------------------
-- concatmap-pdinstance-snd-ex>-sorted and its sub lemma
--------------------------------------------------------------------------------------------------

pdinstance-snd-fst-all->concatmap-pdinstance-snd : ∀ { l r : RE } {ε∈l : ε∈ l } { loc : ℕ } { c : Char }
    → ( e  : U l )
    → ( flat-[]-e : Flat-[] l e )
    → ( es : List (U l) )
    → ( flat-[]-es : All ( Flat-[] l ) es )
    → ( e>-head-es : >-maybe e (head es))
    → ( es->-sorted : >-sorted es ) 
    → ( pdis : List (PDInstance r c ) )
    -----------------------------------------------------------------
    → All (λ pdi₁ → Ex>-maybe {l ● r ` loc } pdi₁ (head (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es))))
       (List.map (mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e)) pdis)
pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e (flat-[] e proj₁flat-e≡[]) [] [] >-nothing ex->-nil pdis = prove  (List.map (mk-snd-pdi (e , flat-[] e proj₁flat-e≡[])) pdis)
  where
    prove : (pdis : List (PDInstance (l ● r ` loc) c) )
          → All  (λ pdi₁ → Ex>-maybe pdi₁ nothing) pdis
    prove [] = []
    prove (pdi ∷ pdis) = ex>-nothing ∷ prove pdis
pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e₁ flat-[]-e₁  (e₂ ∷ es) (flat-[]-e₂ ∷ flat-[]-es) (>-just e₁>e₂) e₂es->sorted [] = [] 
pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e₁ flat-[]-e₁  (e₂ ∷ es) (flat-[]-e₂ ∷ flat-[]-es) (>-just e₁>e₂) e₂es->sorted (pdi ∷ pdis) = prove (pdi ∷ pdis)
  where
    prove : ( pdis' : List (PDInstance r c) )
          →  All (λ pdi₁ → Ex>-maybe pdi₁
                    (head
                      (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x (pdi ∷ pdis))
                                 ((e₂ , flat-[]-e₂) ∷ zip-es-flat-[]-es {l} {ε∈l}  es flat-[]-es))))
                    (List.map (mk-snd-pdi (e₁ , flat-[]-e₁)) pdis')
    prove [] = []
    prove (pdi'@(pdinstance {p} {r} {c}  inj' s-ev') ∷ pdis' ) = 
          ex>-just (>-pdi (mk-snd-pdi (e₁ , flat-[]-e₁) pdi')
                          (mk-snd-pdi (e₂ , flat-[]-e₂) pdi) λ { (PairU v₁ v₁') (PairU v₂ v₂') recons₁ recons₂ → ev-> v₁ v₁' v₂ v₂' recons₁ recons₂ } ) ∷ prove pdis'
          where
          ev-> : (v₁ : U l )
               → (v₁' : U r )
               → (v₂ : U l )
               → (v₂' : U r )
               → Recons {l ● r ` loc} {c} (PairU v₁ v₁')  ( mk-snd-pdi {l} {r} {loc} {c}  (e₁ , flat-[]-e₁ ) pdi')
               → Recons {l ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi {l} {r} {loc} {c}  (e₂ , flat-[]-e₂ ) pdi )
               --------------------------------------------------
               → (l ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂' 
          ev-> v₁ v₁' v₂ v₂' recons1 recons2 = seq₁ v₁>v₂
            where
              v₁≡e₁ : v₁ ≡ e₁
              v₁≡e₁ = mk-snd-pdi-fst-pair-≡ pdi' e₁ flat-[]-e₁ v₁ v₁' recons1
              v₂≡e₂ : v₂ ≡ e₂
              v₂≡e₂ = mk-snd-pdi-fst-pair-≡ pdi e₂ flat-[]-e₂ v₂ v₂' recons2
              v₁>v₂ : l ⊢ v₁ > v₂
              v₁>v₂ rewrite v₁≡e₁ | v₂≡e₂ = e₁>e₂ 
            

concatmap-pdinstance-snd-ex>-sorted-sub : ∀ { l r : RE } {ε∈l : ε∈ l } {loc : ℕ } { c : Char }
                                     → ( es : List (U l) )
                                     → ( flat-[]-es : All ( Flat-[] l ) es ) 
                                     → ( ex->-sorted : >-sorted es ) 
                                     → ( pdis : List (PDInstance r c ) )
                                     → Ex>-sorted {r} pdis
                                     ----------------------------------------------------------------
                                     → Ex>-sorted {l ● r ` loc} (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es))
concatmap-pdinstance-snd-ex>-sorted-sub {l} {r} {ε∈l} {loc} {c} []       []                        >-nil                          _    _              = ex>-nil
concatmap-pdinstance-snd-ex>-sorted-sub {l} {r} {ε∈l} {loc} {c} (e ∷ es) (flat-[]-e ∷ flat-[]-es)  (>-cons es->-sorted e>head-es) pdis pdis-ex>-sorted =
  concat-ex-sorted
    (List.map (mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e)) pdis)                                          -- ^ curr batch
    (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es)) -- ^ next bacth
    curr-sorted
    next-sorted
    (pdinstance-snd-fst-all->concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  e flat-[]-e es flat-[]-es e>head-es es->-sorted pdis ) 
  where
    curr-sorted : Ex>-sorted {l ● r ` loc} (List.map (mk-snd-pdi {l} {r} {loc} {c}  (e , flat-[]-e)) pdis)
    curr-sorted = pdinstance-snd-ex>-sorted {l} {r} {loc} {c} (e , flat-[]-e) pdis pdis-ex>-sorted
    next-sorted : Ex>-sorted {l ● r ` loc} (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es))
    next-sorted = concatmap-pdinstance-snd-ex>-sorted-sub {l} {r} {ε∈l} {loc} {c} es flat-[]-es es->-sorted pdis pdis-ex>-sorted 


-- pdinstances generated by concatmap-pdinstance-snd must be ex sorted. 
concatmap-pdinstance-snd-ex>-sorted : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
                                     → ( pdis : List (PDInstance r c ) )
                                     → Ex>-sorted {r} pdis
                                     → Ex>-sorted {l ● r ` loc } (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis)
concatmap-pdinstance-snd-ex>-sorted {l} {r} {ε∈l} {loc} {c} pdis ex>-sorted-pdis = concatmap-pdinstance-snd-ex>-sorted-sub {l} {r}  {ε∈l} {loc} {c}  es flat-[]-es es->-sorted pdis ex>-sorted-pdis
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

---------------------------------------------------------------------------------------------------
-- map-pdinstance-assoc-ex>-sorted and its sub lemma 
---------------------------------------------------------------------------------------------------

inv-assoc-> : ∀ { l s r : RE } {loc₁ loc₂ : ℕ }
          → { u₁ : U ( l ● (s ● r ` loc₂) ` loc₁) }
          → { u₂ : U ( l ● (s ● r ` loc₂) ` loc₁) }
          → (l ● (s ● r ` loc₂) ` loc₁) ⊢ u₁ > u₂
          -------------------------------------------------------------          
          → ((l ● s ` loc₁) ● r ` loc₂) ⊢ inv-assoc u₁ > inv-assoc u₂
inv-assoc-> {l} {s} {r} {loc₁} {loc₂} {PairU v₁ (PairU v₁' v₁'')} {PairU v₂ (PairU v₂' v₂'')} pair-v1-pair-v1'-v1''>pair-v2-pair-v2'-v2''
  with pair-v1-pair-v1'-v1''>pair-v2-pair-v2'-v2''
... | seq₁ v₁>v₂                          = seq₁ (seq₁ v₁>v₂)
... | seq₂ v₁≡v₂ (seq₁ v₁'>v₂')           = seq₁ (seq₂ v₁≡v₂ v₁'>v₂')
... | seq₂ v₁≡v₂ (seq₂ v₁'≡v₂' v₁''>v₂'') = seq₂ (pair-≡ v₁≡v₂ v₁'≡v₂') v₁''>v₂'' 


pdinstance-assoc-ex> : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
                       → ( pdi₁ : PDInstance (l ● (s ● r ` loc₂) ` loc₁) c )
                       → ( pdi₂ : PDInstance (l ● (s ● r ` loc₂) ` loc₁) c )                       
                       → (l ● (s ● r ` loc₂) ` loc₁) , c ⊢ pdi₁ > pdi₂
                       ------------------------------------------------------------
                       → (( l ● s ` loc₁) ● r ` loc₂) , c ⊢ (pdinstance-assoc pdi₁) > (pdinstance-assoc pdi₂)
pdinstance-assoc-ex> {l} {s} {r} {loc₁} {loc₂} {c} pdi₁ pdi₂ (>-pdi _ _  u₁→u₂→rec₁→rec₂→u₁>u₂ )
    = >-pdi (pdinstance-assoc pdi₁)
            (pdinstance-assoc pdi₂) 
            (λ { (PairU (PairU v₁ v₁') v₁'') (PairU (PairU v₂ v₂') v₂'') recons₁ recons₂ →
               (inv-assoc-> {l} {s} {r} {loc₁} {loc₂} ( u₁→u₂→rec₁→rec₂→u₁>u₂ (PairU v₁ (PairU v₁' v₁'')) (PairU v₂ (PairU v₂' v₂''))
                                                    (inv-recons-assoc v₁ v₁' v₁'' pdi₁ recons₁) (inv-recons-assoc v₂ v₂' v₂'' pdi₂ recons₂) ))   })
  

pdinstance-assoc-ex>-maybe : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
                             → ( pdi : PDInstance (l ● (s ● r ` loc₂) ` loc₁) c )
                             → ( pdis : List (PDInstance (l ● (s ● r ` loc₂) ` loc₁) c) )
                             → Ex>-maybe pdi (head pdis)
                             -------------------------------------------------------------
                             → Ex>-maybe (pdinstance-assoc pdi)
                                         (head (List.map pdinstance-assoc pdis))
pdinstance-assoc-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi [] ex>-nothing = ex>-nothing      
pdinstance-assoc-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi₁ (pdi₂ ∷ pdis) (ex>-just pdi₁>pdi₂) = ex>-just (pdinstance-assoc-ex> {l} {s} {r} {loc₁} {loc₂} {c} pdi₁ pdi₂ pdi₁>pdi₂ )

map-pdinstance-assoc-ex>-sorted : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
                                → ( pdis : List (PDInstance (l ● (s ● r ` loc₂) ` loc₁) c) )
                                → Ex>-sorted {l ● (s ● r ` loc₂) ` loc₁} pdis
                                ---------------------------------------------------------------
                                → Ex>-sorted {(l ● s ` loc₁) ● r ` loc₂} (List.map pdinstance-assoc pdis)
map-pdinstance-assoc-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} [] ex>-nil = ex>-nil
map-pdinstance-assoc-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} (pdi ∷ pdis) (ex>-cons pdis-ex>-sorted pdi>head-pdis) = ex>-cons (map-pdinstance-assoc-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} pdis pdis-ex>-sorted) (pdinstance-assoc-ex>-maybe  {l} {s} {r} {loc₁} {loc₂} {c} pdi pdis pdi>head-pdis)


---------------------------------------------------------------------------------------------------
-- map-pdinstance-assoc-ex>-sorted and its sub lemma 
---------------------------------------------------------------------------------------------------

inv-dist-> : ∀ { l s r : RE } {loc₁ loc₂ : ℕ }
             → { u₁ : U (( l ● r ` loc₂) + ( s ● r ` loc₂ ) ` loc₁)  }
             → { u₂ : U (( l ● r ` loc₂) + ( s ● r ` loc₂ ) ` loc₁)  }
             → (( l ● r ` loc₂) + ( s ● r ` loc₂ ) ` loc₁ ) ⊢ u₁ > u₂
             -------------------------------------------------------------          
             → (( l + s ` loc₁) ● r ` loc₂)  ⊢ inv-dist u₁ > inv-dist u₂ 
inv-dist-> {l} {s} {r} {loc₁} {loc₂} {LeftU (PairU v₁ v₁')} {LeftU (PairU v₂ v₂')} (choice-ll (seq₁ v₁>v₂)) = seq₁ (choice-ll v₁>v₂)
inv-dist-> {l} {s} {r} {loc₁} {loc₂} {LeftU (PairU v₁ v₁')} {LeftU (PairU v₂ v₂')} (choice-ll (seq₂ v₁≡v₂ v₁'>v₂')) = seq₂ (left-≡ v₁≡v₂) v₁'>v₂'
inv-dist-> {l} {s} {r} {loc₁} {loc₂} {RightU (PairU v₁ v₁')} {RightU (PairU v₂ v₂')} (choice-rr (seq₁ v₁>v₂)) = seq₁ (choice-rr v₁>v₂)
inv-dist-> {l} {s} {r} {loc₁} {loc₂} {RightU (PairU v₁ v₁')} {RightU (PairU v₂ v₂')} (choice-rr (seq₂ v₁≡v₂ v₁'>v₂')) = seq₂ (right-≡ v₁≡v₂) v₁'>v₂'
inv-dist-> {l} {s} {r} {loc₁} {loc₂} {LeftU (PairU v₁ v₁')} {RightU (PairU v₂ v₂')} choice-lr = seq₁ choice-lr
-- the RightU vs LeftU case is not required, it leads to λ() automatically


inv-dist-right-> : ∀ { l s r : RE } {loc₁ loc₂ : ℕ }  { v₁ v₁' : U s } { v₂ v₂' : U r } 
   → (s ● r ` loc₂) ⊢ PairU v₁ v₂ > PairU v₁' v₂'
   -----------------------------------------------------------------------------
   → ((l + s ` loc₁) ● r ` loc₂) ⊢ PairU (RightU v₁) v₂ > PairU (RightU v₁') v₂'
inv-dist-right->  {l} {s} {r} {loc₁} {loc₂} {v₁} {v₁'} {v₂} {v₂'} (seq₁ v₁>v₁') = seq₁ (choice-rr v₁>v₁')
inv-dist-right->  {l} {s} {r} {loc₁} {loc₂} {v₁} {v₁'} {v₂} {v₂'} (seq₂ v₁≡v₁' v₂>v₂') = seq₂ (right-≡ v₁≡v₁')  v₂>v₂'


dist-left-right-ex>-maybe : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
  → ( pdi : ( PDInstance ( l ● r ` loc₂ ) c ))
  → ( pdis : ( List (PDInstance ( s ● r ` loc₂ ) c ) ))
  -----------------------------------------------------------------------------------------------------------------------
  → Ex>-maybe (pdinstance-dist {l} {s} {r} {loc₁} {loc₂} {c} (pdinstance-left pdi))  (head (List.map pdinstance-dist (List.map pdinstance-right pdis)))
dist-left-right-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi [] = ex>-nothing
dist-left-right-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdiˡ (pdiʳ ∷ pdisʳ)  = ex>-just (>-pdi (pdinstance-dist (pdinstance-left pdiˡ)) (pdinstance-dist (pdinstance-right pdiʳ)) ev->)
  where
    ev-> : (u₁ u₂ : U ((l + s ` loc₁) ● r ` loc₂))
         → Recons u₁ (pdinstance-dist (pdinstance-left pdiˡ))
         → Recons u₂ (pdinstance-dist (pdinstance-right pdiʳ))
         → ((l + s ` loc₁) ● r ` loc₂) ⊢ u₁ > u₂
    ev-> (PairU (LeftU v₁) v₂) (PairU (RightU v₁') v₂') recons₁ recons₂ = seq₁ choice-lr
    ev-> (PairU (RightU v₁) v₂) _ recons₁ _ =  Nullary.contradiction recons₁ (¬recons-pair-right-from-pdinstance-dist-left  v₁ v₂ pdiˡ)
    ev-> _ (PairU (LeftU v₁') v₂') _ recons₂  =  Nullary.contradiction recons₂ (¬recons-pair-left-from-pdinstance-dist-right  v₁' v₂' pdiʳ)      
    

dist-right-ex>-maybe : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
  → ( pdi : ( PDInstance ( s ● r ` loc₂ ) c ))
  → ( pdis : ( List (PDInstance ( s ● r ` loc₂ ) c ) ))
  → Ex>-maybe (pdinstance-right { l ● r ` loc₂} { s ● r ` loc₂} {loc₁} {c}  pdi) (head (List.map pdinstance-right pdis))
  --------------------------------------------------
  → Ex>-maybe (pdinstance-dist  {l} {s} {r} {loc₁} {loc₂} {c} (pdinstance-right pdi))
    (head (List.map pdinstance-dist (List.map pdinstance-right pdis)))
dist-right-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi [] ex>-nothing = ex>-nothing
dist-right-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi₁ (pdi₂ ∷ pdis) (ex>-just (>-pdi _ _ u₁→u₂→r₁→r₂→u₁>u₂)) = ex>-just (>-pdi (pdinstance-dist (pdinstance-right pdi₁)) (pdinstance-dist (pdinstance-right pdi₂)) ev->)
  where
    ev-> : (u₁ u₂ : U ((l + s ` loc₁) ● r ` loc₂))
         → Recons u₁ (pdinstance-dist (pdinstance-right pdi₁))
         → Recons u₂ (pdinstance-dist (pdinstance-right pdi₂))
         → ((l + s ` loc₁) ● r ` loc₂) ⊢ u₁ > u₂
    ev-> (PairU (RightU v₁) v₂) (PairU (RightU v₁') v₂') recons₁ recons₂ = inv-dist-right->  pair-v₁-v₂>pair-v₁'-v₂'
      where
        right-pair-v₁-v₂>right-pair-v₁'-v₂' :  ((l ● r ` loc₂) + s ● r ` loc₂ ` loc₁) ⊢ RightU (PairU v₁ v₂) > RightU (PairU v₁' v₂')
        right-pair-v₁-v₂>right-pair-v₁'-v₂' =  
                                u₁→u₂→r₁→r₂→u₁>u₂ (RightU (PairU v₁ v₂)) (RightU (PairU v₁' v₂')) (inv-recons-dist-right v₁ v₂ pdi₁ recons₁) (inv-recons-dist-right v₁' v₂' pdi₂ recons₂)
        pair-v₁-v₂>pair-v₁'-v₂' :  s ● r ` loc₂ ⊢ PairU v₁ v₂ > PairU v₁' v₂'
        pair-v₁-v₂>pair-v₁'-v₂' with right-pair-v₁-v₂>right-pair-v₁'-v₂'
        ...                       | choice-rr ev = ev 
    ev-> (PairU (LeftU v₁) v₂) _ recons₁ _    =  Nullary.contradiction recons₁ (¬recons-pair-left-from-pdinstance-dist-right  v₁ v₂ pdi₁)      
    ev-> _ (PairU (LeftU v₁') v₂') _ recons₂  =  Nullary.contradiction recons₂ (¬recons-pair-left-from-pdinstance-dist-right  v₁' v₂' pdi₂)      
  


map-dist-right-ex>-sorted : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
                            → ( pdis : List (PDInstance ( s ● r ` loc₂ ) c ) )
                            → Ex>-sorted {( l ● r ` loc₂) + ( s ● r ` loc₂) ` loc₁ } (List.map pdinstance-right pdis)
                            ---------------------------------------------------------------
                            → Ex>-sorted { (l + s ` loc₁) ● r ` loc₂} (List.map pdinstance-dist (List.map pdinstance-right pdis))
map-dist-right-ex>-sorted   {l} {s} {r} {loc₁} {loc₂} {c} []     ex>-nil = ex>-nil
map-dist-right-ex>-sorted   {l} {s} {r} {loc₁} {loc₂} {c} (pdi ∷ pdis) (ex>-cons pdis-ex>-sorted pdi>head-pdis) = ex>-cons (map-dist-right-ex>-sorted pdis pdis-ex>-sorted) (dist-right-ex>-maybe pdi pdis pdi>head-pdis) 



map-dist-left++right-ex>-sorted : ∀ {l s r : RE } { loc₁ loc₂ : ℕ } { c : Char }
                         → ( pdisˡ : (List (PDInstance  (l ● r ` loc₂) c) )) 
                         → Ex>-sorted {( l ● r ` loc₂) + ( s ● r ` loc₂) ` loc₁ } (List.map pdinstance-left pdisˡ)
                         → ( pdisʳ : (List (PDInstance  (s ● r ` loc₂) c) )) 
                         → Ex>-sorted {( l ● r ` loc₂) + ( s ● r ` loc₂) ` loc₁ } (List.map pdinstance-right pdisʳ)                         
                         ---------------------------------------------------------------
                         → Ex>-sorted { (l + s ` loc₁) ● r ` loc₂} (List.map pdinstance-dist ((List.map pdinstance-left pdisˡ) ++ (List.map pdinstance-right pdisʳ ) ))
map-dist-left++right-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} [] ex>-nil pdisʳ map-right-pdisʳ-ex>-sorted rewrite cong (λ x →  Ex>-sorted (List.map (pdinstance-dist {l} {s} {r} {loc₁} {loc₂} {c}) x)) (++-identityˡ (List.map pdinstance-right pdisʳ))  =
  map-dist-right-ex>-sorted pdisʳ map-right-pdisʳ-ex>-sorted
map-dist-left++right-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} (pdiˡ ∷ []) (ex>-cons ex->nil ex->-nothing) pdisʳ map-right-pdisʳ-ex>-sorted =
  ex>-cons (map-dist-left++right-ex>-sorted [] ex->nil pdisʳ map-right-pdisʳ-ex>-sorted)
    (dist-left-right-ex>-maybe pdiˡ pdisʳ) 
             
map-dist-left++right-ex>-sorted {l} {s} {r} {loc₁} {loc₂} {c} (pdiˡ ∷ (pdiˡ' ∷ pdisˡ)  ) (ex>-cons pdiˡ'pdis-ex->sorted (ex>-just (>-pdi _ _  u₁→u₂→r₁→r₂→u₁>u₂ )))  pdisʳ map-right-pdisʳ-ex>-sorted =
  ex>-cons (map-dist-left++right-ex>-sorted (pdiˡ' ∷ pdisˡ) pdiˡ'pdis-ex->sorted pdisʳ map-right-pdisʳ-ex>-sorted)
    (ex>-just (>-pdi (pdinstance-dist (pdinstance-left pdiˡ))
                     (pdinstance-dist (pdinstance-left pdiˡ')) ev-> ))
    where
      ev->  : (u₁ u₂ : U ((l + s ` loc₁) ● r ` loc₂))
            → Recons u₁ (pdinstance-dist (pdinstance-left pdiˡ))
            → Recons u₂ (pdinstance-dist (pdinstance-left pdiˡ'))
            -------------------------------------------------
            → ((l + s ` loc₁) ● r ` loc₂) ⊢ u₁ > u₂
      ev-> (PairU (LeftU v₁) v₃) (PairU (LeftU v₁') v₃') recons₁ recons₂ =
        inv-dist-> {l} {s} {r} {loc₁} {loc₂} {LeftU (PairU v₁ v₃)} {LeftU (PairU v₁' v₃')}
          (u₁→u₂→r₁→r₂→u₁>u₂ (LeftU (PairU v₁ v₃)) (LeftU (PairU v₁' v₃')) (inv-recons-dist-left v₁ v₃ pdiˡ recons₁) (inv-recons-dist-left v₁' v₃' pdiˡ' recons₂) )
      ev-> (PairU (RightU v₂) v₃) _ recons₁ _   = Nullary.contradiction recons₁ (¬recons-pair-right-from-pdinstance-dist-left v₂ v₃ pdiˡ)   -- need to create a contradiction
      ev-> _ (PairU (RightU v₂') v₃') _ recons₂ = Nullary.contradiction recons₂ (¬recons-pair-right-from-pdinstance-dist-left v₂' v₃' pdiˡ')   -- need to create a contradiction

---------------------------------------------------------------------------------------------------
-- map-pdinstance-dist-ex>-sorted and its sub lemma END 


------------------------------------------------------------------------------------------
-- aux lemmas for the pdUConcat l * case. 
-- the parse tree generated by  pdi : PDInstance (r * ε∉r ` loc₁) c must be a consU
pdinstance-r*-is-cons : ∀ { r : RE } {ε∉r : ε∉ r } {loc : ℕ } { c : Char }
  → ( pdi : PDInstance (r * ε∉r ` loc ) c )
  → ( u : U (r * ε∉r ` loc) )
  → Recons u  pdi
  -------------------------------------
  → ∃[ x ] ∃[ xs ] u ≡ (ListU (x ∷ xs ))
pdinstance-r*-is-cons {r} {ε∉r} {loc} {c} (pdinstance inj s-ev) u (recons {p} {r * ε∉r ` loc } {c} {w} u' ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡u )) = prove
  where
    prove :  ∃[ x ] ∃[ xs ] u ≡ (ListU (x ∷ xs ))
    prove with u-of-r*-islist u
    ... | inj₂ ex-u≡list-x::xs = ex-u≡list-x::xs
    ... | inj₁ u≡list-[] = Nullary.contradiction  c∷w≡[] Word.¬c∷w≡[] 
      where
        proj₁-flat-u≡[] : ( proj₁ (flat u)) ≡ [] 
        proj₁-flat-u≡[] =
          begin
            proj₁ (flat u)
          ≡⟨ cong (λ x → proj₁ ( flat x ) ) u≡list-[] ⟩
            proj₁ (flat (ListU {r} {ε∉r} {loc} []))
          ≡⟨⟩
            []
          ∎
          
        proj₁-flat-u≡cw : (proj₁ (flat u)) ≡ (c ∷ proj₁ (flat (unflat w∈⟦p⟧)))
        proj₁-flat-u≡cw = 
          begin
            proj₁ (flat u)
          ≡⟨ cong (λ x → proj₁ (flat x) ) (sym inj-unflat-w∈⟦p⟧≡u) ⟩
            proj₁ (flat (inj (unflat w∈⟦p⟧) ) )
          ≡⟨ s-ev  (unflat w∈⟦p⟧) ⟩ 
           c ∷ proj₁ (flat ( unflat w∈⟦p⟧ ) )
          ∎
        c∷w≡[] :  (c ∷ proj₁ (flat (unflat w∈⟦p⟧))) ≡ []
        c∷w≡[] =
          begin
            (c ∷ proj₁ (flat (unflat w∈⟦p⟧)))
          ≡⟨ sym  proj₁-flat-u≡cw ⟩
            (proj₁ (flat u))
          ≡⟨ proj₁-flat-u≡[] ⟩
            []
          ∎ 
            

-- the first of the pair from pdi : PDInstance (l * ε∉l ` loc₁) c must be a consU
pdinstance-fst-pair-l*-is-cons : ∀ { l r : RE } {ε∉l : ε∉ l} { loc₁ loc₂ : ℕ } { c : Char }
                      → ( pdi : PDInstance (l * ε∉l ` loc₁) c )
                      → ( u : U (l * ε∉l ` loc₁) )
                      → ( v : U r )                       
                      → Recons (PairU {(l * ε∉l ` loc₁)} {r} {loc₂} u v) (pdinstance-fst pdi)
                      -------------------------------------------------------
                      → ∃[ x ] ∃[ xs ] u ≡ (ListU (x ∷ xs) )
pdinstance-fst-pair-l*-is-cons {l} {r} {ε∉l} {loc₁} {loc₂} {c} pdi (ListU us) v rec = pdinstance-r*-is-cons pdi (ListU us) recons-list-us
  where
    recons-list-us : Recons (ListU us) pdi 
    recons-list-us = inv-recons-fst {l * ε∉l ` loc₁} {r} {loc₂} {c} (ListU us) v pdi rec

-------------------------------------------------------------------------------------------
-------------------------------------------------------------------------------------------



-- main lemma: 
pdU-sorted : ∀ { r : RE } { c : Char }
  → Ex>-sorted {r} {c} pdU[ r , c ]

pdUConcat-sorted : ∀ { l r : RE } { ε∈l : ε∈ l } {loc : ℕ } { c : Char }
  → Ex>-sorted {l ● r ` loc } {c} (pdUConcat l r ε∈l loc c)
  

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
                             
pdU-sorted {l + r ` loc } {c} =  map-left-right-ex-sorted pdU[ l , c ] pdU[ r , c ] ind-hyp-l ind-hyp-r 
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
...  | yes ε∈l = pdUConcat-sorted {l} {r} {ε∈l} {loc} {c} 
 
{-# TERMINATING #-}
pdUConcat-sorted {ε} {r} {ε∈ε} {loc} {c} = 
   concatmap-pdinstance-snd-ex>-sorted {ε} {r} {ε∈ε} {loc} {c} pdU[ r , c ] ind-hyp-r
  where
    ind-hyp-r : Ex>-sorted pdU[ r , c ]
    ind-hyp-r = pdU-sorted {r} {c}
pdUConcat-sorted {l * ε∉l ` loc₂} {r} {ε∈*} {loc} {c} = 
  concat-ex-sorted {(l * ε∉l ` loc₂) ● r ` loc } {c}
                    (List.map pdinstance-fst  pdU[ l * ε∉l ` loc₂ , c ] )
                    (concatmap-pdinstance-snd { l * ε∉l ` loc₂ } {r} {ε∈*} {loc} {c} pdU[ r , c ])
                    map-pdinstance-fst-ex>sorted
                    concatmap-pdinstance-snd-is-ex>-sorted
                    (all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd  pdU[ l * ε∉l ` loc₂ , c ]   pdU[ r , c ]) 
  where
    ind-hyp-l : Ex>-sorted pdU[ l * ε∉l ` loc₂ , c ]
    ind-hyp-l = pdU-sorted {l * ε∉l ` loc₂} {c}
    
    ind-hyp-r : Ex>-sorted pdU[ r , c ]
    ind-hyp-r = pdU-sorted {r} {c}
    -- we need to concat the following two, but we need to know all fst in map-pdinstance-fst-ex>sorted  >  concatmap-pdinstance-snd-ex>-sorted
    map-pdinstance-fst-ex>sorted : Ex>-sorted { (l * ε∉l ` loc₂) ● r ` loc } (List.map pdinstance-fst  pdU[ l * ε∉l ` loc₂ , c ] )
    map-pdinstance-fst-ex>sorted = map-fst-ex-sorted pdU[ l * ε∉l ` loc₂ , c ] ind-hyp-l 

    concatmap-pdinstance-snd-is-ex>-sorted : Ex>-sorted { (l * ε∉l ` loc₂) ● r ` loc } (concatmap-pdinstance-snd { l * ε∉l ` loc₂ } {r} {ε∈*} {loc} {c} pdU[ r , c ])
    concatmap-pdinstance-snd-is-ex>-sorted = concatmap-pdinstance-snd-ex>-sorted {l * ε∉l ` loc₂} {r} {ε∈*} {loc} {c}  pdU[ r , c ] ind-hyp-r 

    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd :
         (pdis : List (PDInstance (l * ε∉l ` loc₂) c ))
      →  (pdis' : List (PDInstance r c))
      →  All (λ pdi → Ex>-maybe { (l * ε∉l ` loc₂) ● r ` loc } pdi (head (concatmap-pdinstance-snd { l * ε∉l ` loc₂ } {r} {ε∈*} {loc} {c} pdis'))) (List.map
      (pdinstance-fst {l * ε∉l ` loc₂} {r} {loc} {c}) pdis )
    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd [] _ = []
    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd (pdi ∷ pdis) [] = ( ex>-nothing ∷ all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd pdis [] )
    all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd (pdi ∷ pdis) (pdi' ∷ pdis')
       =
      ex>-just (>-pdi (pdinstance-fst pdi)  (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl) pdi') λ { (PairU v₁ v₁') (PairU v₂ v₂') recons₁ recons₂ → ev-> v₁ v₁' v₂ v₂' recons₁ recons₂ } )  ∷
        (all-ex->-maybe-map-pdinstance-fst-concatmap-pdinstance-snd pdis (pdi' ∷ pdis'))

      where
        ev-> : (v₁ : U (l * ε∉l ` loc₂) )
             → (v₁' : U r )
             → (v₂ : U (l * ε∉l ` loc₂) )
             → (v₂' : U r )
             → Recons {(l * ε∉l ` loc₂) ● r ` loc} {c} (PairU v₁ v₁')  ( pdinstance-fst {l * ε∉l ` loc₂} {r} {loc} {c}  pdi )
             → Recons {(l * ε∉l ` loc₂) ● r ` loc} {c} (PairU v₂ v₂')  ( mk-snd-pdi {l * ε∉l ` loc₂} {r} {loc} {c}  (ListU [] ,  flat-[] (ListU []) refl) pdi' )
             --------------------------------------------------
             → ((l * ε∉l ` loc₂) ● r ` loc) ⊢ PairU v₁ v₁'  >  PairU v₂ v₂'
        ev-> v₁ v₁' v₂ v₂' recons1 recons2  = seq₁ v₁>v₂
          where 
            v₂≡list-[] : v₂ ≡ (ListU [])
            v₂≡list-[] = mk-snd-pdi-fst-pair-≡ pdi' (ListU []) (flat-[] (ListU []) refl)  v₂ v₂' recons2
            v₁-is-cons : ∃[ x ] ∃[ xs ] (v₁ ≡ ListU (x ∷ xs))
            v₁-is-cons = pdinstance-fst-pair-l*-is-cons pdi v₁ v₁' recons1
            x  = proj₁ v₁-is-cons
            xs = proj₁ (proj₂ v₁-is-cons)
            v₁≡list-x-xs = proj₂ (proj₂ v₁-is-cons)
            list-x-xs>e : (l * ε∉l ` loc₂) ⊢ ListU (x ∷ xs) > (ListU []) 
            list-x-xs>e = star-cons-nil
            v₁>v₂ : (l * ε∉l ` loc₂) ⊢ v₁ > v₂
            v₁>v₂ rewrite  v₁≡list-x-xs | v₂≡list-[] = list-x-xs>e


pdUConcat-sorted {l ● s ` loc₂} {r} {ε∈ ε∈l ● ε∈s } {loc} {c} =
  map-pdinstance-assoc-ex>-sorted {l} {s} {r} {loc₂} {loc} {c} pdU[ l ● ( s ● r ` loc) ` loc₂ , c ] ind-hyp 
  where
    ind-hyp : Ex>-sorted pdU[ l ● ( s ● r ` loc) ` loc₂ , c ]
    ind-hyp = pdU-sorted {l ● ( s ● r ` loc) ` loc₂} {c}
    
pdUConcat-sorted {l + s ` loc₂} {r} {ε∈l+s} {loc} {c} = map-dist-left++right-ex>-sorted  pdU[ ( l ● r ` loc) , c ]  ind-hyp-left-l●r  pdU[ ( s ● r ` loc) , c ] ind-hyp-right-s●r
  where

    ind-hyp-l●r : Ex>-sorted pdU[ ( l ● r ` loc) , c ]
    ind-hyp-l●r = pdU-sorted {l ● r ` loc} {c}

    ind-hyp-left-l●r : Ex>-sorted (List.map pdinstance-left pdU[ ( l ● r ` loc) , c ])
    ind-hyp-left-l●r = map-left-ex-sorted pdU[ ( l ● r ` loc) , c ] ind-hyp-l●r
    

    ind-hyp-s●r : Ex>-sorted pdU[ ( s ● r ` loc) , c ]
    ind-hyp-s●r = pdU-sorted {s ● r ` loc} {c}

    ind-hyp-right-s●r : Ex>-sorted (List.map pdinstance-right pdU[ ( s ● r ` loc) , c ])
    ind-hyp-right-s●r = map-right-ex-sorted pdU[ ( s ● r ` loc) , c ] ind-hyp-s●r
    

```



### Definition 37 : (Extended) greedy ordering among PDInstance*'s 

Let r be a non problematic regular expression.

Let w be a word.

Let pdi₁ and pdi₂ be two partial derivative descendant instances of r w.r.t w.

We say pdi₁ is greedier than pdi₂, r , w  ⊢* pdi₁ > pdi₂ iff
  for all parse trees u₁ u₂  of r, u₁ is constructable from pdi₁ and u₂ is constructabled from pdi₂ 
    then r ⊢ u₁ > u₂ 

```agda

data _,_⊢*_>_ : ∀ ( r : RE ) → (w : List Char ) → PDInstance* r w → PDInstance* r w → Set where
  *>-pdi : ∀ { r : RE } { w : List Char }
    → ( pdi₁ : PDInstance* r w )
    → ( pdi₂ : PDInstance* r w )
    → ( ∀ ( u₁ : U r ) → ( u₂ : U r ) → (Recons* u₁ pdi₁ ) → (Recons* u₂ pdi₂) → ( r ⊢ u₁ > u₂) )
    → r , w ⊢* pdi₁ > pdi₂ 
```

### Definition 38 : (Extended) greedy order sortedness among pdinstance*'s 

```agda

data Ex*>-maybe : ∀ { r : RE } { w : List Char } ( pdi : PDInstance* r w ) → ( mpdi : Maybe (PDInstance* r w) ) → Set where
  ex*>-nothing : ∀ { r : RE } { w : List Char }
    → { pdi : PDInstance* r w } 
    ---------------------------
    → Ex*>-maybe {r} {w} pdi nothing
  ex*>-just : ∀ { r : RE } { w : List Char }
    → { pdi : PDInstance* r w }
    → { pdi' : PDInstance* r w }
    → r , w ⊢* pdi > pdi' 
    ----------------------------------
    → Ex*>-maybe {r} {w} pdi (just pdi')

data Ex*>-sorted : ∀ { r : RE } { w : List Char } ( pdis : List (PDInstance* r w) ) → Set where
  ex*>-nil  : ∀ { r : RE } { w : List Char } → Ex*>-sorted {r} {w} []
  ex*>-cons : ∀ { r : RE } { w : List Char } 
    → { pdi : PDInstance* r w }
    → { pdis : List (PDInstance* r w) } 
    → Ex*>-sorted  {r} {w} pdis 
    → Ex*>-maybe {r} {w} pdi (head pdis)
    --------------------------------------
    → Ex*>-sorted {r} {w} ( pdi ∷ pdis ) 
```


### Lemma 39: the list of pdinstance*'s from pdUMany[ r , c] is extended greedily sorted. 


Let r be a non problematic regular expression.

Let w be a word.

Then pdUMany[r , w] is extended greedily sorted.


```agda

-- TODO: can we define a "polymoprhic" version of concat-ex-sorted and concat-ex*-sorted? 
-- concatenation of two ex sorted lists of pdis are sorted if all the pdis from the first list are ex-> than the head of the 2nd list. 
concat-ex*-sorted : ∀ { r : RE } { w : List Char }
    → ( pdis₁ : List ( PDInstance* r w ))
    → ( pdis₂ : List ( PDInstance* r w ))
    → Ex*>-sorted { r } pdis₁
    → Ex*>-sorted { r } pdis₂
    → All (λ pdi₁ → Ex*>-maybe  {r} pdi₁ (head pdis₂)) pdis₁
    -------------------------------------------------------
    → Ex*>-sorted { r } (pdis₁ ++ pdis₂)
concat-ex*-sorted []                       pdis₂          ex*>-nil                                       pdis₂-sorted     []                              = pdis₂-sorted
concat-ex*-sorted pdis₁                    []             pdis₁-sorted                                  ex*>-nil           _  rewrite (++-identityʳ pdis₁) = pdis₁-sorted
concat-ex*-sorted (pdi₁ ∷ [])             (pdi₂ ∷ pdis₂) pdis₁-sorted                                  pdi₂pdis₂-sorted (ex*>-just pdi₁>pdi₂  ∷ [])      = ex*>-cons pdi₂pdis₂-sorted (ex*>-just pdi₁>pdi₂) 
concat-ex*-sorted (pdi₁ ∷ pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) (ex*>-cons pdi₁'pdis₁-sorted pdi₁>head-pdis₁)  pdi₂pdis₂-sorted (ex*>-just pdi₁>pdi₂  ∷ pxs)     = ex*>-cons ind-hyp pdi₁>head-pdis₁
  where
    ind-hyp = concat-ex*-sorted (pdi₁' ∷ pdis₁) (pdi₂ ∷ pdis₂) pdi₁'pdis₁-sorted  pdi₂pdis₂-sorted  pxs 



compose-pdi-with-ex*>-head-map-compose-pdi-with : ∀ { d r : RE } { pref : List Char} { c : Char }
  → ( d→r : U d → U r )
  → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → ( >-inc-d→r :  (v₁ v₂ : U d) → d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂ ) -- strict inc evidence for d→r
  → ( pdi : PDInstance d c )
  → ( pdis : List (PDInstance d c) )
  → Ex>-maybe pdi (head pdis)
  -------------------------------------------------------------------------------------------------
  → Ex*>-maybe (compose-pdi-with d→r s-ev-d-r pdi) (head (List.map (compose-pdi-with d→r s-ev-d-r) pdis))
compose-pdi-with-ex*>-head-map-compose-pdi-with {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r pdi []  ex>-nothing = ex*>-nothing   
compose-pdi-with-ex*>-head-map-compose-pdi-with {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r
  pdi₁@(pdinstance {p₁} {d} {c} p₁→d s-ev-p₁-d)
  (pdi₂@(pdinstance {p₂} {d} {c} p₂→d s-ev-p₂-d) ∷ pdis )
  (ex>-just pdi₁>pdi₂@(>-pdi _ _ u₁→u₂→rec₁→rec₂→u₁>u₂ ) ) = ex*>-just (*>-pdi -- u₁ and u₂ of U d
                             {r} {pref ∷ʳ c}
                             (compose-pdi-with d→r s-ev-d-r pdi₁)
                             (compose-pdi-with d→r s-ev-d-r pdi₂) -- from the same pdinstance* 
                             ex*>-ev ) 
  where
            -- 1) from inv-recons*-compose-pdi-with we note that
            -- u₁ is reconstructable from pdinstance* d→r s-ev-d-r
            -- u₂ is reconstructable from pdinstance* d→r s-ev-d-r
            --   same pdinstance* but different w∈⟦d⟧
            -- 2) all pdinstance*s must be *>-inc , namely
            --    v1 v2 : d,  d |- v1 > v2 → d→r v₁ > d→r v₂
            --  if can we show u₁ = d→r v₁ and u₂ = d→ r v₂ ? 

    ex*>-ev : ∀ (u₁ u₂ : U r )
      → Recons* u₁ (compose-pdi-with d→r s-ev-d-r (pdinstance p₁→d s-ev-p₁-d))
      → Recons* u₂ (compose-pdi-with d→r s-ev-d-r (pdinstance p₂→d s-ev-p₂-d))
      ----------------------------------------------------------------------------
      → r ⊢ u₁ > u₂
    ex*>-ev u₁ u₂
            rec*₁@(recons* {- {p₁} {r} {w₁} {pref++c} -} u₁ ( w₁∈⟦p₁⟧ , d→r∘p₁→d-unflat-w₁∈⟦p₁⟧≡u₁ ) )
            rec*₂@(recons* {- {p₂} {r} {w₂} {pref++c} -} u₂ ( w₂∈⟦p₂⟧ , d→r∘p₁→d-unflat-w₂∈⟦p₂⟧≡u₂ ) )
            with inv-recons*-compose-pdi-with u₁ pdi₁ d→r s-ev-d-r rec*₁     | inv-recons*-compose-pdi-with u₂ pdi₂ d→r s-ev-d-r rec*₂             
    ... | recons* {d} {r} {cw₁} {pref} u₁ ( cw₁∈⟦d⟧ , d→r-unflat-cw₁∈⟦d⟧≡u₁ ) | recons* {d} {r} {cw₂} {pref} u₂ ( cw₂∈⟦d⟧ , d→r-unflat-cw₂∈⟦d⟧≡u₂ ) 
            rewrite sym d→r∘p₁→d-unflat-w₁∈⟦p₁⟧≡u₁ | sym  d→r∘p₁→d-unflat-w₂∈⟦p₂⟧≡u₂ = 
                >-inc-d→r (p₁→d (unflat w₁∈⟦p₁⟧) ) (p₂→d (unflat w₂∈⟦p₂⟧)  )  (u₁→u₂→rec₁→rec₂→u₁>u₂ (p₁→d (unflat w₁∈⟦p₁⟧))
                                                                                               (p₂→d (unflat w₂∈⟦p₂⟧))
                                                                                               (recons (p₁→d (unflat w₁∈⟦p₁⟧)) (w₁∈⟦p₁⟧ , refl))
                                                                                               (recons (p₂→d (unflat w₂∈⟦p₂⟧)) (w₂∈⟦p₂⟧ , refl)))
          

map-compose-pdi-with-sorted : ∀ { d r : RE } { pref : List Char} { c : Char }
  → ( d→r : U d → U r )
  → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → ( >-inc-d→r :  (v₁ v₂ : U d) → d ⊢ v₁ > v₂ → r ⊢ d→r v₁ > d→r v₂ ) -- strict inc evidence for d→r  
  → ( pdis : List (PDInstance d c) )
  → Ex>-sorted pdis
  -------------------------------------------------------------
  → Ex*>-sorted {r}  (List.map (compose-pdi-with d→r s-ev-d-r) pdis )
map-compose-pdi-with-sorted {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r [] ex>-nil = ex*>-nil
map-compose-pdi-with-sorted {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r (pdi ∷ pdis)  (ex>-cons pdis-sorted pdi>head-pdis) =
  ex*>-cons ind-hyp
  (compose-pdi-with-ex*>-head-map-compose-pdi-with d→r s-ev-d-r >-inc-d→r pdi pdis pdi>head-pdis)
  where
    ind-hyp : Ex*>-sorted {r}  (List.map (compose-pdi-with d→r s-ev-d-r) pdis )
    ind-hyp = map-compose-pdi-with-sorted {d} {r} {pref} {c} d→r s-ev-d-r >-inc-d→r pdis pdis-sorted 


-- need
advance-pdi*-with-c-sorted : ∀ { r : RE } { pref : List Char} { c : Char }
  → (pdi : PDInstance* r pref)
  → *>-Inc pdi 
  ----------------------------------------------------------
  → Ex*>-sorted (advance-pdi*-with-c {r} {pref} {c} pdi)
advance-pdi*-with-c-sorted {r} {pref} {c} pdi@(pdinstance* {d} {r} {pref} d→r s-ev-d-r) (*>-inc d→r-inc-ev) 
  with pdU[ d , c ]    | pdU-sorted { d } {c} 
... | []               | _                                          = ex*>-nil
... | (pdi₁ ∷ pdis₁ ) | ex>-cons ex>-sorted-pdis₁ pdi₁>head-pdis₁  = ex*>-cons (map-compose-pdi-with-sorted d→r s-ev-d-r d→r-inc-ev pdis₁ ex>-sorted-pdis₁)
                                                                               (compose-pdi-with-ex*>-head-map-compose-pdi-with d→r s-ev-d-r d→r-inc-ev pdi₁ pdis₁ pdi₁>head-pdis₁  )




```

```agda

{- we don't need this? 
>-pdi-trans : ∀ { r : RE } { c : Char } 
  → { pdi₁ : PDInstance r c }
  → { pdi₂ : PDInstance r c }
  → { pdi₃ : PDInstance r c }
  → r , c ⊢ pdi₁ > pdi₂
  → r , c ⊢ pdi₂ > pdi₃
  -------------------------------------------  
  → r , c ⊢ pdi₁ > pdi₃
>-pdi-trans {r} {c} {pdi₁} {pdi₂} {pdi₃} (>-pdi pdi₁ pdi₂  u₁→u₂→rec₁→rec₂→u₁>u₂)  (>-pdi .pdi₂ pdi₃ u₂→u₃→rec₂→rec₃→u₂>u₃)  = >-pdi pdi₁ pdi₃ >-ev 
  where
    >-ev : ( u₁ : U r )
          → ( u₃ : U r )
          → Recons u₁ pdi₁
          → Recons u₃ pdi₃
          ------------------------------
          → r ⊢ u₁ > u₃
    >-ev u₁ u₃ recons₁ recons₃ =
      let u₂-recons₂ = pdi-∃ pdi₂
      in >-trans (u₁→u₂→rec₁→rec₂→u₁>u₂ u₁ (proj₁ u₂-recons₂) recons₁ (proj₂ u₂-recons₂))
                  (u₂→u₃→rec₂→rec₃→u₂>u₃ (proj₁ u₂-recons₂) u₃ (proj₂ u₂-recons₂) recons₃)  -- where to get u₂ and recons₂ ?
-}

-- these two lemmas should be moved to PartialDerivative.lagda.md 
first≢[]→¬pdUConcat≡[] : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char } { cs : List Char } 
  → first l ++ first r ≡ c ∷ cs
  --------------------------------------------------------------------
  → ¬ ( pdUConcat l r ε∈l loc c ≡ [] ) 


first≢[]→¬pdU≡[] : ∀ { r : RE } { c : Char } { cs : List Char }
    → ( first r ≡ c ∷ cs )
    ------------------------
    → ¬ ( pdU[ r , c ] ≡ [] )
first≢[]→¬pdU≡[] {ε} {c} {cs} = λ()
first≢[]→¬pdU≡[] {$ c ` loc} {c₁} {[]} first-c≡c∷[] = prf
  where
    c≡c₁ : c ≡ c₁
    c≡c₁ = proj₁ (∷-inj first-c≡c∷[])
    
    prf : ¬ ( pdU[ $ c ` loc , c₁ ] ≡ [] )
    prf pdU-r-c≡[] with c Char.≟ c₁
    ...             | no ¬c≡c₁ = ¬c≡c₁ c≡c₁ 
    ...             | yes refl with pdU[ $ c ` loc , c₁ ]  in eq 
    ...                        | pdi ∷ [] = ¬∷≡[] pdU-r-c≡[]
first≢[]→¬pdU≡[] { l + r ` loc } {c} {cs} first-l+r≡c∷cs with first l in l-eq | first r in r-eq 
... | [] | c₁ ∷ cs₁ = prf 
  where
    c₁≡c×cs₁≡cs : (c₁ ≡ c) × (cs₁ ≡ cs)
    c₁≡c×cs₁≡cs = (∷-inj first-l+r≡c∷cs)
    ind-hyp : ¬ ( pdU[ r , c₁ ] ≡ [] )
    ind-hyp =  first≢[]→¬pdU≡[] r-eq   
    prf : ¬ ( List.map (pdinstance-left {l} {r} {loc}) pdU[ l , c ] ++ List.map (pdinstance-right {l} {r} {loc})  pdU[ r , c ] ≡ [] )
    prf  map-pdinstance-left-pdu-l-c++map-pdinstance-right-pdu-r-c≡[] rewrite sym (proj₁ c₁≡c×cs₁≡cs) =  ind-hyp (inv-map-[] map-right-pdu-r-c≡[])
      where
        map-right-pdu-r-c≡[] : List.map (pdinstance-right {l} {r} {loc})  pdU[ r , c₁ ] ≡ [] 
        map-right-pdu-r-c≡[] = ++-conicalʳ (List.map (pdinstance-left {l} {r} {loc}) pdU[ l , c₁ ]) (List.map (pdinstance-right {l} {r} {loc})  pdU[ r , c₁ ] )  map-pdinstance-left-pdu-l-c++map-pdinstance-right-pdu-r-c≡[]
... | c₁ ∷ cs₁ | cs₂ =  prf
  where 
    c₁≡c×cs₁cs₂≡cs : (c₁ ≡ c) × (cs₁ ++ cs₂ ≡ cs)
    c₁≡c×cs₁cs₂≡cs  = ∷-inj first-l+r≡c∷cs 
    ind-hyp : ¬ ( pdU[ l , c₁ ] ≡ [] )
    ind-hyp =  first≢[]→¬pdU≡[] l-eq   
    prf : ¬ ( List.map (pdinstance-left {l} {r} {loc}) pdU[ l , c ] ++ List.map (pdinstance-right {l} {r} {loc})  pdU[ r , c ] ≡ [] )
    prf  map-pdinstance-left-pdu-l-c++map-pdinstance-right-pdu-r-c≡[] rewrite sym (proj₁ c₁≡c×cs₁cs₂≡cs) =  ind-hyp (inv-map-[] map-left-pdu-l-c≡[])
      where
        map-left-pdu-l-c≡[] : List.map (pdinstance-left {l} {r} {loc})  pdU[ l , c₁ ] ≡ [] 
        map-left-pdu-l-c≡[] = ++-conicalˡ (List.map (pdinstance-left {l} {r} {loc}) pdU[ l , c₁ ]) (List.map (pdinstance-right {l} {r} {loc})  pdU[ r , c₁ ] )  map-pdinstance-left-pdu-l-c++map-pdinstance-right-pdu-r-c≡[]
first≢[]→¬pdU≡[] { r * ε∉r ` loc } {c} {cs} first-r*≡c∷cs map-star-pdU-r-c≡[] = ind-hyp (inv-map-[] map-star-pdU-r-c≡[])
  where
    ind-hyp : ¬ ( pdU[ r , c ] ≡ [] )
    ind-hyp = first≢[]→¬pdU≡[] {r} {c} {cs} first-r*≡c∷cs

first≢[]→¬pdU≡[] { l ● r ` loc } {c} {cs} first-l●r≡c∷cs with ε∈? l
... | no ¬ε∈l = λ map-fst-pdU-l-cs≡[] → ind-hyp (inv-map-[] map-fst-pdU-l-cs≡[])
  where
    ind-hyp : ¬ ( pdU[ l , c ] ≡ [] )
    ind-hyp = first≢[]→¬pdU≡[] {l} {c} {cs} first-l●r≡c∷cs
... | yes ε∈l = prf
  where
    prf : ¬ ( pdUConcat l r ε∈l loc c ≡ [] )
    prf = first≢[]→¬pdUConcat≡[] first-l●r≡c∷cs 

{-# TERMINATING #-}
first≢[]→¬pdUConcat≡[] {ε} {r} {ε∈ε} {loc} {c} {cs} first-r≡c∷cs
  with (zip-es-flat-[]-es {ε} {ε∈ε} (mkAllEmptyU {ε} ε∈ε) (mkAllEmptyU-sound {ε} ε∈ε)) in eq 
... | [] = λ map-mk-snd-pdi-es → ¬∷≡[] eq   
... | (EmptyU , flat-[] EmptyU refl ) ∷ xs rewrite ++-identityʳ ( List.map (mk-snd-pdi {ε} {r} {loc} {c} (EmptyU , flat-[] EmptyU refl)) pdU[ r , c ] ) =
    λ map-mk-snd-pdi-pdu-r-c≡[] → (first≢[]→¬pdU≡[] first-r≡c∷cs) (inv-map-[] map-mk-snd-pdi-pdu-r-c≡[])  
first≢[]→¬pdUConcat≡[] {l * ε∉l ` loc₁} {r} {ε∈*} {loc₂} {c} {cs} first-l*●r≡c∷cs
  with first l in first-l-eq  | first r in first-r-eq 
... | []                      | []        =  λ x → ¬∷≡[] (sym first-l*●r≡c∷cs)
... | []                      | c₁ ∷ cs₁ rewrite ++-identityʳ (List.map (mk-snd-pdi {l * ε∉l ` loc₁} {r} {loc₂} {c} (ListU [] , flat-[] (ListU []) refl)) pdU[ r , c ]) = prf
  where
    c₁≡c×cs₁≡cs : (c₁ ≡ c) × (cs₁ ≡ cs)
    c₁≡c×cs₁≡cs = (∷-inj first-l*●r≡c∷cs)
    ind-hyp : ¬ ( pdU[ r , c₁ ] ≡ [] )
    ind-hyp =  first≢[]→¬pdU≡[] first-r-eq
    prf : ¬ ( List.map (pdinstance-fst  {l * ε∉l ` loc₁} {r} {loc₂} {c}) (List.map pdinstance-star pdU[ l , c ]) ++ List.map (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl))  pdU[ r , c ] ≡ [] ) 
    prf map-fst-map-star-pdu-l-c++map-mk-snd-pdi-pdu-r-c≡[] rewrite sym (proj₁ c₁≡c×cs₁≡cs) = ind-hyp (inv-map-[] (++-conicalʳ (List.map pdinstance-fst (List.map pdinstance-star pdU[ l , c₁ ])) (List.map (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl)) pdU[ r , c₁ ])  map-fst-map-star-pdu-l-c++map-mk-snd-pdi-pdu-r-c≡[]))
... | c₁ ∷ cs₁               | cs₂       rewrite ++-identityʳ (List.map (mk-snd-pdi {l * ε∉l ` loc₁} {r} {loc₂} {c} (ListU [] , flat-[] (ListU []) refl)) pdU[ r , c ]) = prf 
  where
    c₁≡c×cs₁cs₂≡cs : (c₁ ≡ c) × (cs₁ ++ cs₂ ≡ cs)
    c₁≡c×cs₁cs₂≡cs = (∷-inj first-l*●r≡c∷cs) 
    ind-hyp : ¬ ( pdU[ l , c₁ ] ≡ [] )
    ind-hyp =  first≢[]→¬pdU≡[] first-l-eq
    prf : ¬ ( List.map (pdinstance-fst  {l * ε∉l ` loc₁} {r} {loc₂} {c}) (List.map pdinstance-star pdU[ l , c ]) ++ List.map (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl))  pdU[ r , c ] ≡ [] ) 
    prf map-fst-map-star-pdu-l-c++map-mk-snd-pdi-pdu-r-c≡[] rewrite sym (proj₁ c₁≡c×cs₁cs₂≡cs) = ind-hyp (inv-map-[] (inv-map-[] (++-conicalˡ (List.map pdinstance-fst (List.map pdinstance-star pdU[ l , c₁ ])) (List.map (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl)) pdU[ r , c₁ ])  map-fst-map-star-pdu-l-c++map-mk-snd-pdi-pdu-r-c≡[])))
first≢[]→¬pdUConcat≡[] {l ● s ` loc₁} {r} {ε∈ ε∈l ● ε∈s} {loc₂} {c} {cs} first-l●s-●r≡c∷cs with  ε∈? l in l-eq | ε∈? s in s-eq 
... | no ¬ε∈l | _ = Nullary.contradiction ε∈l ¬ε∈l
... | yes ε∈l | no ¬ε∈s = Nullary.contradiction ε∈s ¬ε∈s 
... | yes ε∈l | yes ε∈s = λ x →  ind-hyp (inv-map-[] x)  
    where
      first-s●r≡first-s++first-r : first (s ● r ` loc₂) ≡ first s ++ first r
      first-s●r≡first-s++first-r rewrite s-eq = refl 
      first-l●s-●r≡first-l-●s●r : first l ++ (first (s ● r ` loc₂)) ≡ c ∷ cs 
      first-l●s-●r≡first-l-●s●r  = 
        begin
          (first l) ++ (first (s ● r ` loc₂)) 
        ≡⟨ cong ((first l) ++_ )  first-s●r≡first-s++first-r ⟩
          (first l) ++ ((first s)  ++ (first r)) 
        ≡⟨ sym ( ++-assoc (first l) (first s) (first r) ) ⟩
          (first l ++ first s)  ++ first r 
        ≡⟨ first-l●s-●r≡c∷cs ⟩
          c ∷ cs 
        ∎  
      ind-hyp : ¬ (pdUConcat l ( s ● r ` loc₂) ε∈l loc₁ c ≡ [] )
      ind-hyp  = first≢[]→¬pdUConcat≡[] {l}  {s ● r ` loc₂} {ε∈l} {loc₁} {c} {cs}   first-l●s-●r≡first-l-●s●r
first≢[]→¬pdUConcat≡[] {l + s ` loc₁} {r} {ε∈ ε∈l + ε∈s} {loc₂} {c} {cs} first-l+s●r≡c∷cs with  ε∈? l in l-eq | ε∈? s in s-eq 
... | no ¬ε∈l | _ = Nullary.contradiction ε∈l ¬ε∈l
... | yes ε∈l | no ¬ε∈s =  Nullary.contradiction ε∈s ¬ε∈s
... | yes ε∈l | yes ε∈s with first l in first-l-eq
...            | [] = λ x → ind-hyp-s  ( inv-map-[] (++-conicalʳ (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c)) (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c))  (inv-map-[] x)))
  where
    ind-hyp-s : ¬ (pdUConcat s r ε∈s loc₂ c ≡ [] )
    ind-hyp-s = first≢[]→¬pdUConcat≡[] {s} {r } {ε∈s} {loc₂} {c} {cs} first-l+s●r≡c∷cs
    
...            | c₁ ∷ cs₁ = λ x → ind-hyp-l (inv-map-[] (++-conicalˡ (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c)) (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c)) (inv-map-[] x)))
  where
    c₁≡c×cs₁++first-s++first-r≡cs : (c₁ ≡ c) × ((cs₁ ++ first s) ++ first r ≡ cs)
    c₁≡c×cs₁++first-s++first-r≡cs = (∷-inj first-l+s●r≡c∷cs)

    first-l++first-r≡c₁∷cs₁++first-r : first l ++ first r ≡ c₁ ∷ cs₁ ++ first r
    first-l++first-r≡c₁∷cs₁++first-r =                                              
      begin
        first l ++ first r
      ≡⟨ cong ( _++ first r ) first-l-eq ⟩ 
        c₁ ∷ cs₁ ++ first r
      ∎ 
    
    ind-hyp-l : ¬ (pdUConcat l r ε∈l loc₂ c ≡ [] )
    ind-hyp-l rewrite sym (proj₁ c₁≡c×cs₁++first-s++first-r≡cs) |
                      sym (proj₂ c₁≡c×cs₁++first-s++first-r≡cs)  = first≢[]→¬pdUConcat≡[] {l} {r} {ε∈l} {loc₂} {c₁} {cs₁ ++ first r} first-l++first-r≡c₁∷cs₁++first-r 
first≢[]→¬pdUConcat≡[] {l + s ` loc₁} {r} {ε∈ ε∈l <+ ε∉s} {loc₂} {c} {cs} first-l+s●r≡c∷cs with  ε∈? l in l-eq
... | no ¬ε∈l = Nullary.contradiction ε∈l ¬ε∈l
... | yes ε∈l with first l in first-l-eq | first s in first-s-eq
...            | []                       | []          = prf   
  where
    first-l++first-r≡c∷cs : first l ++ first r ≡ c ∷ cs
    first-l++first-r≡c∷cs rewrite first-l-eq = first-l+s●r≡c∷cs 
  
    ind-hyp : ¬ ( pdUConcat l r ε∈l loc₂ c  ≡ [] )
    ind-hyp = first≢[]→¬pdUConcat≡[]  {l} {r} {ε∈l} {loc₂} {c} {cs} first-l++first-r≡c∷cs 
    prf :  ¬ ( List.map (pdinstance-dist {l} {s} {r} {loc₁} {loc₂} {c})  (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ++  List.map pdinstance-right (pdU[ s ● r ` loc₂ , c ] ) ) ≡ [] )
    prf map-dist-map-left-pduconcat-l-r++map-right-pdu-s-r≡[] = ind-hyp pduconcat-l-r≡[]
      where
        map-left-pduconcat-l-r++map-right-pdu-s-r≡[] : (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ++  List.map pdinstance-right (pdU[ s ● r ` loc₂ , c ] ) ) ≡ []
        map-left-pduconcat-l-r++map-right-pdu-s-r≡[] = inv-map-[] map-dist-map-left-pduconcat-l-r++map-right-pdu-s-r≡[]
        map-left-pduconcat-l-r≡[] : (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ) ≡ []
        map-left-pduconcat-l-r≡[] = ++-conicalˡ (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ) (List.map pdinstance-right (pdU[ s ● r ` loc₂ , c ] ) ) map-left-pduconcat-l-r++map-right-pdu-s-r≡[]
        pduconcat-l-r≡[] : (pdUConcat l r ε∈l loc₂ c) ≡ []
        pduconcat-l-r≡[] = inv-map-[] map-left-pduconcat-l-r≡[]
        
...            | []                       | c₁ ∷ cs₁   = prf
  where
    c₁≡c×cs₁++first-r≡cs : (c₁ ≡ c) × ( (cs₁ ++ first r) ≡ cs )
    c₁≡c×cs₁++first-r≡cs = ∷-inj first-l+s●r≡c∷cs

    first-s●r≡c₁∷cs₁ : (first (s ● r ` loc₂))  ≡ c₁ ∷ cs₁
    first-s●r≡c₁∷cs₁ with ε∈? s
    ... | yes ε∈s = Nullary.contradiction ε∈s (ε∉r→¬ε∈r ε∉s)
    ... | no ¬ε∈s = first-s-eq 


    ind-hyp : ¬ ( pdU[ s ● r ` loc₂ , c ] ≡ [] )
    ind-hyp rewrite sym (proj₁ c₁≡c×cs₁++first-r≡cs) = first≢[]→¬pdU≡[] {s ● r ` loc₂} {c₁} {cs₁} first-s●r≡c₁∷cs₁ 

    prf :  ¬ ( List.map (pdinstance-dist {l} {s} {r} {loc₁} {loc₂} {c})  (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ++  List.map pdinstance-right (pdU[ s ● r ` loc₂ , c ] ) ) ≡ [] )
    prf map-dist-map-left-pduconcat-l-r++map-right-pdu-s-r≡[] = ind-hyp pdu-s-r≡[] 
      where
        map-left-pduconcat-l-r++map-right-pdu-s-r≡[] : (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ++  List.map pdinstance-right (pdU[ s ● r ` loc₂ , c ] ) ) ≡ []
        map-left-pduconcat-l-r++map-right-pdu-s-r≡[] = inv-map-[] map-dist-map-left-pduconcat-l-r++map-right-pdu-s-r≡[]
        map-right-pdu-s-r≡[] : (List.map pdinstance-right (pdU[ s ● r ` loc₂ , c ] )) ≡ []
        map-right-pdu-s-r≡[] = ++-conicalʳ (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ) (List.map pdinstance-right (pdU[ s ● r ` loc₂ , c ] ) ) map-left-pduconcat-l-r++map-right-pdu-s-r≡[]
        pdu-s-r≡[] : pdU[ s ● r ` loc₂ , c ] ≡ []
        pdu-s-r≡[] = inv-map-[] map-right-pdu-s-r≡[]

...            | c₁ ∷ cs₁                | cs₂  = prf 
  where
    c₁≡c×cs₁++cs₂++first-r≡cs : (c₁ ≡ c) × ( ((cs₁ ++ cs₂) ++ first r) ≡ cs )
    c₁≡c×cs₁++cs₂++first-r≡cs = ∷-inj first-l+s●r≡c∷cs

    first-l++first-r≡c₁∷cs₁++first-r : first l ++ first r ≡ c₁ ∷ cs₁ ++ first r
    first-l++first-r≡c₁∷cs₁++first-r rewrite first-l-eq = refl 
    
    ind-hyp : ¬ (pdUConcat l r ε∈l loc₂ c ≡ [] )
    ind-hyp rewrite sym (proj₁ c₁≡c×cs₁++cs₂++first-r≡cs )  = first≢[]→¬pdUConcat≡[] {l} {r } {ε∈l} {loc₂} {c₁} {cs₁ ++ first r} first-l++first-r≡c₁∷cs₁++first-r

    prf :  ¬ ( List.map (pdinstance-dist {l} {s} {r} {loc₁} {loc₂} {c})  (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ++  List.map pdinstance-right (pdU[ s ● r ` loc₂ , c ] ) ) ≡ [] )
    prf map-dist-map-left-pduconcat-l-r++map-right-pdu-s-r≡[] = ind-hyp pduconcat-l-r≡[]
      where
        map-left-pduconcat-l-r++map-right-pdu-s-r≡[] : (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ++  List.map pdinstance-right (pdU[ s ● r ` loc₂ , c ] ) ) ≡ []
        map-left-pduconcat-l-r++map-right-pdu-s-r≡[] = inv-map-[] map-dist-map-left-pduconcat-l-r++map-right-pdu-s-r≡[]
        map-left-pduconcat-l-r≡[] : (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ) ≡ []
        map-left-pduconcat-l-r≡[] = ++-conicalˡ (List.map pdinstance-left (pdUConcat l r ε∈l loc₂ c) ) (List.map pdinstance-right (pdU[ s ● r ` loc₂ , c ] ) ) map-left-pduconcat-l-r++map-right-pdu-s-r≡[]
        pduconcat-l-r≡[] : (pdUConcat l r ε∈l loc₂ c) ≡ []
        pduconcat-l-r≡[] = inv-map-[] map-left-pduconcat-l-r≡[]

first≢[]→¬pdUConcat≡[] {l + s ` loc₁} {r} {ε∈ ε∉l +> ε∈s} {loc₂} {c} {cs} first-l+s●r≡c∷cs with  ε∈? s in s-eq
... | no ¬ε∈s = Nullary.contradiction ε∈s ¬ε∈s
... | yes ε∈s with first l in first-l-eq | first s in first-s-eq
...            | []                       | []       = prf
  where
    first-s++first-r≡c∷cs : first s ++ first r ≡ c ∷ cs
    first-s++first-r≡c∷cs rewrite first-s-eq = first-l+s●r≡c∷cs 
  
    ind-hyp : ¬ ( pdUConcat s r ε∈s loc₂ c  ≡ [] )
    ind-hyp = first≢[]→¬pdUConcat≡[]  {s} {r} {ε∈s} {loc₂} {c} {cs} first-s++first-r≡c∷cs

    prf :  ¬ ( List.map (pdinstance-dist {l} {s} {r} {loc₁} {loc₂} {c})  ( (List.map pdinstance-left pdU[ l ● r ` loc₂ ,  c ]) ++  (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c) ))  ≡ [] )
    prf  map-dist-map-left-pdu-l-r++map-right-pduconcat-s-r≡[] = ind-hyp pduconcat-s-r≡[]
      where
        map-left-pdu-l-r++map-right-pduconcat-s-r≡[] :  ( (List.map pdinstance-left pdU[ l ● r ` loc₂ ,  c ]) ++  (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c) ))  ≡ []
        map-left-pdu-l-r++map-right-pduconcat-s-r≡[] = inv-map-[] map-dist-map-left-pdu-l-r++map-right-pduconcat-s-r≡[] 
        map-right-pduconcat-s-r≡[] : (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c) ) ≡ []
        map-right-pduconcat-s-r≡[] = ++-conicalʳ (List.map pdinstance-left pdU[ l ● r ` loc₂ ,  c ])  (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c))   map-left-pdu-l-r++map-right-pduconcat-s-r≡[]
        pduconcat-s-r≡[] :  (pdUConcat s r ε∈s loc₂ c) ≡ []
        pduconcat-s-r≡[] = inv-map-[] map-right-pduconcat-s-r≡[]
...            | []                       | c₁ ∷ cs₁   = prf  
  where
    c₁≡c×cs₁++first-r≡cs : (c₁ ≡ c) × ( (cs₁ ++ first r) ≡ cs )
    c₁≡c×cs₁++first-r≡cs = ∷-inj first-l+s●r≡c∷cs

    first-s++first-r≡c₁∷cs₁++first-r : first s ++ first r ≡ c₁ ∷ cs₁ ++ first r
    first-s++first-r≡c₁∷cs₁++first-r rewrite first-s-eq = refl 

    ind-hyp : ¬ ( pdUConcat s r ε∈s loc₂ c ≡ [] )
    ind-hyp rewrite sym (proj₁ c₁≡c×cs₁++first-r≡cs) = first≢[]→¬pdUConcat≡[] {s} {r} {ε∈s} {loc₂} {c₁} {cs₁ ++ first r}  first-s++first-r≡c₁∷cs₁++first-r


    prf :  ¬ ( List.map (pdinstance-dist {l} {s} {r} {loc₁} {loc₂} {c})  ( (List.map pdinstance-left pdU[ l ● r ` loc₂ ,  c ]) ++  (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c) ))  ≡ [] )
    prf  map-dist-map-left-pdu-l-r++map-right-pduconcat-s-r≡[] = ind-hyp pduconcat-s-r≡[]
      where
        map-left-pdu-l-r++map-right-pduconcat-s-r≡[] :  ( (List.map pdinstance-left pdU[ l ● r ` loc₂ ,  c ]) ++  (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c) ))  ≡ []
        map-left-pdu-l-r++map-right-pduconcat-s-r≡[] = inv-map-[] map-dist-map-left-pdu-l-r++map-right-pduconcat-s-r≡[] 
        map-right-pduconcat-s-r≡[] : (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c) ) ≡ []
        map-right-pduconcat-s-r≡[] = ++-conicalʳ (List.map pdinstance-left pdU[ l ● r ` loc₂ ,  c ])  (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c))   map-left-pdu-l-r++map-right-pduconcat-s-r≡[]
        pduconcat-s-r≡[] :  (pdUConcat s r ε∈s loc₂ c) ≡ []
        pduconcat-s-r≡[] = inv-map-[] map-right-pduconcat-s-r≡[]

...           | c₁ ∷ cs₁               | cs₂        = prf
  where
    c₁≡c×cs₁++cs₂++first-r≡cs : (c₁ ≡ c) × ( ((cs₁ ++ cs₂) ++ first r) ≡ cs )
    c₁≡c×cs₁++cs₂++first-r≡cs = ∷-inj first-l+s●r≡c∷cs

    first-l●r≡c₁∷cs₁ : (first (l ● r ` loc₂))  ≡ c₁ ∷ cs₁
    first-l●r≡c₁∷cs₁ with ε∈? l
    ... | yes ε∈l = Nullary.contradiction ε∈l (ε∉r→¬ε∈r ε∉l)
    ... | no ¬ε∈l = first-l-eq
    
    ind-hyp : ¬ ( pdU[ l ● r ` loc₂ , c ] ≡ [] )
    ind-hyp rewrite sym (proj₁ c₁≡c×cs₁++cs₂++first-r≡cs) = first≢[]→¬pdU≡[] {l ● r ` loc₂} {c₁} {cs₁} first-l●r≡c₁∷cs₁

    prf :  ¬ ( List.map (pdinstance-dist {l} {s} {r} {loc₁} {loc₂} {c})  ( (List.map pdinstance-left pdU[ l ● r ` loc₂ ,  c ]) ++  (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c) ))  ≡ [] )
    prf  map-dist-map-left-pdu-l-r++map-right-pduconcat-s-r≡[] = ind-hyp pdu-l-r≡[] 
      where
        map-left-pdu-l-r++map-right-pduconcat-s-r≡[] :  ( (List.map pdinstance-left pdU[ l ● r ` loc₂ ,  c ]) ++  (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c) ))  ≡ []
        map-left-pdu-l-r++map-right-pduconcat-s-r≡[] = inv-map-[] map-dist-map-left-pdu-l-r++map-right-pduconcat-s-r≡[] 

        map-left-pdu-l-r≡[] : (List.map pdinstance-left pdU[ l ● r ` loc₂ ,  c ]) ≡ []
        map-left-pdu-l-r≡[] = ++-conicalˡ  (List.map pdinstance-left pdU[ l ● r ` loc₂ ,  c ])  (List.map pdinstance-right (pdUConcat s r ε∈s loc₂ c))   map-left-pdu-l-r++map-right-pduconcat-s-r≡[]
        pdu-l-r≡[] : pdU[ l ● r ` loc₂ ,  c ] ≡ []
        pdu-l-r≡[] = inv-map-[] map-left-pdu-l-r≡[]



-- postulate
{-# TERMINATING #-}
pdi*-∃ : ∀ { r : RE } { pref : List Char }
       → ( pdi : PDInstance* r pref )
       → ∃[ u ] Recons* u pdi

pdi*-∃ {r} {pref} pdi@(pdinstance* {d} {r} {pref}  inj s-ev)
  with ε∈? d
... |  yes ε∈d with (mkAllEmptyU ε∈d )in mkAllEmptyU-e∈p-eq 
...              | ( e ∷ es ) = inj e , recons* (inj e) ((proj₂ (flat e)) , prf) -- base case, 
  where
    prf  : inj (unflat (Product.proj₂ (flat e))) ≡ inj e
    prf = cong (λ x → inj x ) unflat∘proj₂∘flat
...              | [] = Nullary.contradiction  mkAllEmptyU-e∈p-eq ( mkAllEmptyU≢[] ε∈d)     -- we need to create a contradiction here. mkAllEmptyU is not empty

pdi*-∃ {r} {pref} pdi@(pdinstance* {d} {r} {pref}  d→r s-ev-d-r)
    |  no ¬ε∈d  with first d in first-d-eq
...               |  [] =   Nullary.contradiction first-d-eq (ε∉r→¬first-r≡[] {d} {¬ε∈r→ε∉r ¬ε∈d})      
...               |  ( c₁ ∷ cs₁ ) with pdU[ d , c₁ ] in pdU-d-c₁-eq 
...                                | []  =  Nullary.contradiction pdU-d-c₁-eq (first≢[]→¬pdU≡[] first-d-eq)  -- since c₁ is in first d, pdU[ d , c₁ ] should not be [] 
...                                | (pdi'@(pdinstance {p} {d} {c₁} p→d s-ev-p-d) ∷ _ )
                                          with pdi*-∃ {r} {pref ∷ʳ c₁} (compose-pdi-with {r} {d} {pref} {c₁} d→r s-ev-d-r pdi' )
...                                         | ( u , recons* {p} {r} {w} { pref∷ʳc₁ } {p→r} {s-ev-p-r} .u (w∈⟦p⟧ , d→r∘p→d-unflat-w∈⟦p⟧≡u ) )
                                                with flat {d} (p→d (unflat w∈⟦p⟧)) in flat-p→d-unflat-w∈⟦p⟧-eq 
...                                              | c₁w , c₁w∈⟦d⟧ = prf 
                                                          where
                                                              -- sub goals
                                                              unflat-c₁w∈⟦d⟧≡p→d-unflat-w∈⟦p⟧ :  unflat c₁w∈⟦d⟧ ≡ p→d (unflat w∈⟦p⟧)
                                                              unflat-c₁w∈⟦d⟧≡p→d-unflat-w∈⟦p⟧ =
                                                                begin
                                                                  unflat c₁w∈⟦d⟧
                                                                ≡⟨ cong (λ x → unflat ( proj₂ x ) ) (sym flat-p→d-unflat-w∈⟦p⟧-eq)  ⟩
                                                                  unflat ( proj₂ (flat (p→d (unflat w∈⟦p⟧))) )
                                                                ≡⟨ unflat∘proj₂∘flat {d} {(p→d (unflat w∈⟦p⟧))} ⟩
                                                                  p→d (unflat w∈⟦p⟧)
                                                                ∎
                                                              d→r-unflat-c₁w∈⟦d⟧≡u : d→r (unflat c₁w∈⟦d⟧) ≡ u
                                                              d→r-unflat-c₁w∈⟦d⟧≡u rewrite  unflat-c₁w∈⟦d⟧≡p→d-unflat-w∈⟦p⟧ | d→r∘p→d-unflat-w∈⟦p⟧≡u = refl 

                                                              -- main goal 
                                                              prf : ∃[ u ] Recons* u (pdinstance* d→r s-ev-d-r)
                                                              prf   = u , recons*   u ( c₁w∈⟦d⟧  ,  d→r-unflat-c₁w∈⟦d⟧≡u )     



-- transitivity of *>-pdi 
*>-pdi-trans : ∀ { r : RE }  { pref : List Char } 
  → { pdi₁ : PDInstance* r pref }
  → { pdi₂ : PDInstance* r pref }
  → { pdi₃ : PDInstance* r pref }
  → r , pref ⊢* pdi₁ > pdi₂
  → r , pref ⊢* pdi₂ > pdi₃
  -------------------------------------------  
  → r , pref ⊢* pdi₁ > pdi₃ 
*>-pdi-trans {r} {pref}  {pdi₁} {pdi₂} {pdi₃} (*>-pdi pdi₁ pdi₂ u₁→u₂→rec₁→rec₂→u₁>u₂)  (*>-pdi .pdi₂ pdi₃ u₂→u₃→rec₂→rec₃→u₂>u₃)  = *>-pdi pdi₁ pdi₃ *>-ev
  
  where
    *>-ev : ( u₁ : U r )
          → ( u₃ : U r )
          → Recons* u₁ pdi₁
          → Recons* u₃ pdi₃
          ------------------------------
          → r ⊢ u₁ > u₃
    *>-ev u₁ u₃ recons₁ recons₃ =
      let u₂-recons₂ = pdi*-∃  {r} {pref} pdi₂ 
      in  >-trans (u₁→u₂→rec₁→rec₂→u₁>u₂ u₁ (proj₁ u₂-recons₂) recons₁ (proj₂ u₂-recons₂))
                  (u₂→u₃→rec₂→rec₃→u₂>u₃ (proj₁ u₂-recons₂) u₃ (proj₂ u₂-recons₂) recons₃)  -- where to get u₂ and recons₂ ?

    

advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c : ∀ { r : RE } { pref : List Char } { c : Char }
  → ( pdi :  PDInstance* r pref )
  → ( pdis : List (PDInstance* r pref ) )
  → Ex*>-sorted pdis
  → Ex*>-maybe pdi (head pdis)
  --------------------------------------------------------------------------
  → All (λ pdi₁ → Ex*>-maybe pdi₁ (head (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis))) (advance-pdi*-with-c {r} {pref} {c} pdi)
advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c {r}  {pref} {c} pdi [] ex*>-nil ex*>-nothing = prove (advance-pdi*-with-c {r} {pref} {c} pdi)
  where
    prove : (pdis : List (PDInstance* r  ( pref ∷ʳ c ) ) )
          → All  (λ pdi₁ → Ex*>-maybe pdi₁ nothing) pdis
    prove [] = []
    prove (pdi ∷ pdis) = ex*>-nothing ∷ prove pdis
advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c {r}  {pref} {c}
  pdi₁@(pdinstance* {d₁} {r} d₁→r s-ev-d₁r)
  (pdi₂@(pdinstance* {d₂} {r} d₂→r s-ev-d₂r) ∷ pdis) (ex*>-cons pdis-*>sorted pdi₂>head-pdis) (ex*>-just pdi₁>pdi₂@(*>-pdi .pdi₁ .pdi₂ u₁→u₂→rec₁→rec₂→u₁>u₂))
  with pdU[ d₂ , c ] -- this case needs to be reassessed, is the induction correct here? -- TODO: what about ϕ≡ d₂ ? 
                     -- is it even possible? e.g. c,w ∈ d₁ but c,w ∉ d₂, and c,w∈d₃ where d₁ d₂ are partial derivative descendents of r via pref?
                     -- that means 
... | [] =  advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c {r}  {pref} {c}  pdi₁ pdis pdis-*>sorted (pdi₁>head pdis pdi₂>head-pdis) 
  where
    pdi₁>head : ( pdis : List (PDInstance* r pref) )
        →  Ex*>-maybe pdi₂ (head pdis) 
        →  Ex*>-maybe pdi₁ (head pdis)
    pdi₁>head [] ex*>-nothing = ex*>-nothing
    pdi₁>head (pdi₃ ∷ pdis) (ex*>-just pdi₂>pdi₃) = ex*>-just (*>-pdi-trans {r} {pref} {pdi₁} {pdi₂} {pdi₃} pdi₁>pdi₂ pdi₂>pdi₃)
... | pdi₂' ∷ pdis₂' = go pdU[ d₁ , c ] 
  where
      go : ( pdis₁' : List ( PDInstance d₁ c ) )
        → All ( λ pdi' → Ex*>-maybe pdi' (head
                ((List.map (compose-pdi-with d₂→r s-ev-d₂r) (pdi₂' ∷ pdis₂')) ++ (List.foldr _++_ [] (List.map advance-pdi*-with-c pdis))))) (List.map (compose-pdi-with d₁→r s-ev-d₁r) pdis₁')
      go [] = []
      go (pdi₁' ∷ pdis₁' ) = (ex*>-just (*>-pdi (compose-pdi-with d₁→r s-ev-d₁r pdi₁') (compose-pdi-with d₂→r s-ev-d₂r pdi₂') ev->)) ∷ (go pdis₁')
        where
          ev-> : ( u₁ : U r)
               → ( u₂ : U r)
               → ( Recons* u₁ (compose-pdi-with d₁→r s-ev-d₁r pdi₁') )
               → ( Recons* u₂ (compose-pdi-with d₂→r s-ev-d₂r pdi₂') ) 
               → r ⊢ u₁ > u₂
          ev-> u₁ u₂ recons₁ recons₂ = u₁→u₂→rec₁→rec₂→u₁>u₂ u₁ u₂ (inv-recons*-compose-pdi-with u₁ pdi₁' d₁→r s-ev-d₁r recons₁) (inv-recons*-compose-pdi-with u₂ pdi₂' d₂→r s-ev-d₂r recons₂)  
        

concatmap-advance-pdi*-with-c-sorted : ∀ { r : RE } { pref : List Char } { c : Char }
  → (pdis : List (PDInstance* r pref) )
  → Ex*>-sorted pdis
  → All *>-Inc pdis
  -------------------------------------------------------------------------------------
  → Ex*>-sorted (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
concatmap-advance-pdi*-with-c-sorted {r}  {pref} {c} [] ex*>-nil []  = ex*>-nil
concatmap-advance-pdi*-with-c-sorted {r}  {pref} {c} (pdi ∷ pdis) (ex*>-cons pdis-ex*>-sorted pdi>head-pdis) (*>-inc-pdi ∷ *>-inc-pdis ) = concat-ex*-sorted (advance-pdi*-with-c {r} {pref} {c} pdi) (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis) advance-pdi*-with-c-pdi-sorted ind-hyp advance-pdi*-with-c-pdi-all>head-ind-hyp
  where
    advance-pdi*-with-c-pdi-sorted : Ex*>-sorted (advance-pdi*-with-c {r} {pref} {c} pdi)
    advance-pdi*-with-c-pdi-sorted = advance-pdi*-with-c-sorted pdi *>-inc-pdi

    ind-hyp : Ex*>-sorted (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    ind-hyp = concatmap-advance-pdi*-with-c-sorted {r}  {pref} {c} pdis pdis-ex*>-sorted *>-inc-pdis

    advance-pdi*-with-c-pdi-all>head-ind-hyp : All (λ pdi₁ → Ex*>-maybe pdi₁ (head (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis))) (advance-pdi*-with-c pdi)
    advance-pdi*-with-c-pdi-all>head-ind-hyp =  advance-pdi*-with-c-all>head-concatmap-advance-pdi*-with-c {r}  {pref} {c}  pdi pdis pdis-ex*>-sorted pdi>head-pdis




pdUMany-aux-sorted : ∀ { r : RE }  { pref : List Char }
  → ( c : Char )
  → ( cs : List Char )
  → ( pdis : List (PDInstance* r pref ) )
  → Ex*>-sorted pdis
  → All *>-Inc pdis -- we need to thread through *>-Inc for all the sub lemmas so that we can use it in compose-pdi-with-ex*>-head-map-compose-pdi-with 
  -------------------------------------------------------
  → Ex*>-sorted (pdUMany-aux (c ∷ cs) pdis)
pdUMany-aux-sorted {r}  {pref} c [] pdis pdis-ex*>-sorted *>-inc-pdis  rewrite (++-identityʳ (pref ∷ʳ c) )   = concatmap-advance-pdi*-with-c-pdis-sorted
  where
    concatmap-advance-pdi*-with-c-pdis-sorted : Ex*>-sorted (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    concatmap-advance-pdi*-with-c-pdis-sorted = concatmap-advance-pdi*-with-c-sorted {r}  {pref} {c} pdis pdis-ex*>-sorted *>-inc-pdis 
-- pdis-ex*>-sorted
pdUMany-aux-sorted {r}  {pref} c (d ∷ cs) pdis pdis-ex*>-sorted *>-inc-pdis =
  pdUMany-aux-sorted {r}  {pref ∷ʳ c} d cs (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis) concatmap-advance-pdi*-with-c-pdis-sorted (concatmap-advance-pdi*-with-c-*>inc pdis *>-inc-pdis)
  where
    concatmap-advance-pdi*-with-c-pdis-sorted : Ex*>-sorted (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    concatmap-advance-pdi*-with-c-pdis-sorted = concatmap-advance-pdi*-with-c-sorted {r}  {pref} {c} pdis pdis-ex*>-sorted *>-inc-pdis 


  
pdUMany-sorted : ∀ { r : RE } { w : List Char }
  → Ex*>-sorted {r} {w} pdUMany[ r , w ]
pdUMany-sorted {r} {[]} = ex*>-cons ex*>-nil ex*>-nothing
pdUMany-sorted {r} {c ∷ cs} = pdUMany-aux-sorted {r}  {[]} c cs [  ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ] (ex*>-cons ex*>-nil ex*>-nothing)  pdUMany-*>-inc


```

### Theorem : ParseAll is greedy (sorted)

```agda

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

{-
buildU-is-sorted : ∀ { r : RE } { w : List Char }
  → (pdi : PDInstance* r w)
  → *>-Inc pdi 
  → >-sorted {r} (buildU {r} {w} pdi) 
buildU-is-sorted {r} {w} (pdinstance* {p} {r} inj s-ev)  (*>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) with ε∈? p
... | no _ = >-nil
... | yes ε∈p = map-inj-sorted (mkAllEmptyU ε∈p) inj u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ (mkAllEmptyU-sorted ε∈p)-} 

buildU-all>head-concatmap-buildU : ∀ { r : RE } { w : List Char }
  → ( pdi : PDInstance* r w )
  → ( pdis : List (PDInstance* r w ) )
  → Ex*>-sorted pdis
  → Ex*>-maybe pdi (head pdis)
  -------------------------------------------------------------------------------------------
  → All (λ u₁ → >-maybe  u₁ (head (concatMap (buildU {r} {w}) pdis)) ) (buildU {r} {w} pdi)
buildU-all>head-concatmap-buildU = {!!} 

concatMap-buildU-sorted : ∀ { r : RE } { w : List Char }
  → ( pdis : List (PDInstance* r w) )
  → Ex*>-sorted pdis
  → All *>-Inc pdis
  → >-sorted {r} (concatMap buildU pdis)
concatMap-buildU-sorted {r} {w} [] ex*>-nil [] = >-nil
concatMap-buildU-sorted {r} {w} (pdi@(pdinstance* {p} {r} inj s-ev) ∷ []) (ex*>-cons ex*>-nil ex*>-nothing) ((*>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) ∷ []) with ε∈? p
... | no _ = >-nil
... | yes ε∈p rewrite (++-identityʳ (List.map inj (mkAllEmptyU ε∈p))) =  map-inj-sorted (mkAllEmptyU ε∈p) inj u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ (mkAllEmptyU-sorted ε∈p)  
concatMap-buildU-sorted {r} {w} (pdi₁@(pdinstance* {p₁} {r} p₁→r s-ev₁ ) ∷ ( pdi₂@(pdinstance* {p₂} {r} p₂→r s-ev₂ ) ∷ pdis ) ) (ex*>-cons pdi₂pdis-sorted (ex*>-just pdi₁>pdi₂)) 
  (inc₁@(*>-inc u₁→u₂→u₁>u₂→p₁→r-u₁>p₁→r-u₂) ∷ ( inc₂@(*>-inc u₁→u₂→u₁>u₂→p₂→r-u₁>p₂→r-u₂) ∷ *>-inc-pdis ) ) with ε∈? p₁
... | no _  = concatMap-buildU-sorted {r} {w} (pdi₂ ∷ pdis)  pdi₂pdis-sorted (inc₂ ∷ *>-inc-pdis)
... | yes ε∈p₁ = concat-sorted ( List.map p₁→r (mkAllEmptyU ε∈p₁))  (concatMap buildU (pdi₂ ∷ pdis)) us₁-sorted ind-hyp map-p₁→r-mkAllEmptyU-ε∈p₁-all>head-concatMap-buildU-pdi₂pdis  
  where
    ind-hyp : >-sorted {r} (concatMap buildU (pdi₂ ∷ pdis))
    ind-hyp = concatMap-buildU-sorted {r} {w} (pdi₂ ∷ pdis)  pdi₂pdis-sorted (inc₂ ∷ *>-inc-pdis)

    us₁-sorted : >-sorted ( List.map p₁→r (mkAllEmptyU ε∈p₁) )
    us₁-sorted =  map-inj-sorted (mkAllEmptyU ε∈p₁) p₁→r  u₁→u₂→u₁>u₂→p₁→r-u₁>p₁→r-u₂ (mkAllEmptyU-sorted ε∈p₁)

    map-p₁→r-mkAllEmptyU-ε∈p₁-all>head-concatMap-buildU-pdi₂pdis : All (λ u₁ → >-maybe u₁ (head (concatMap buildU (pdinstance* p₂→r s-ev₂ ∷ pdis)))) (buildU (pdinstance* p₁→r s-ev₁)) -- (List.map p₁→r (mkAllEmptyU ε∈p₁))
    map-p₁→r-mkAllEmptyU-ε∈p₁-all>head-concatMap-buildU-pdi₂pdis = buildU-all>head-concatmap-buildU pdi₁ (pdi₂ ∷ pdis) pdi₂pdis-sorted  (ex*>-just pdi₁>pdi₂) -- {! !} 

parseAll-is-greedy : ∀ { r : RE } { w : List Char }
  →  >-sorted {r} (parseAll[ r , w ])
parseAll-is-greedy {r} {w} = concatMap-buildU-sorted pdUMany[ r , w ] pdUMany-sorted  pdUMany-*>-inc 
```

