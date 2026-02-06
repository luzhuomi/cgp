```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.StrongOrder where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat {- ; ¬≡[]→¬length≡0 ; ¬≡0→>0 ; []→length≡0  ; ¬0>0 -}  )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ) 

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ; proj₁flat-v≡[]→ε∈r )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ) 


{-
import cgp.lne.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; pdUConcat ;
  -- PDInstance ; pdinstance ;
  pdinstance-left ; pdinstance-right;  pdinstance-fst ; mkinjFst ;  pdinstance-snd ; zip-es-flat-[]-es;   mk-snd-pdi ; mkinjSnd ; compose-pdi-with;  advance-pdi*-with-c ; concatmap-pdinstance-snd; pdinstance-star ; mkinjList ; pdinstance-assoc ; mkinjAssoc ; pdUMany[_,_]; pdUMany-aux ) 
-- ;   PDInstance* ; pdinstance*  ) 
-} 

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _>_ ; _≥_ ; _≤_  )

import Data.Nat.Properties as NatProperties
open NatProperties using ( <⇒≤ ; ≤-trans )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
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

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

open import Function using (_∘_ ; flip)

```



### Definition : POSIX ordering among parse trees




```agda
infix 4 _⊢_>_


data _⊢_>_ : ∀ ( r : RE ) → U r → U r → Set where
  seq₁ : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U  l } { v₂ v₂' : U r }
    →   l ⊢ v₁ >  v₁'   
    ------------------------------------------------------------------
    →   l  ● r ` loc ⊢ PairU v₁ v₂ > PairU v₁' v₂'

  seq₂ : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U l } { v₂ v₂' : U r }
    → v₁ ≡ v₁'
    → r ⊢ v₂ > v₂'
    -------------------------------------------------------------------
    →  ( l ● r ` loc) ⊢ (PairU v₁ v₂) > (PairU v₁' v₂')

  choice-lr : ∀ { l r : RE } { loc : ℕ } { v₁ : U l } { v₂ : U r }
    → length (proj₁ (flat v₁)) ≥ length (proj₁ (flat v₂))
    -------------------------------------------------------------------    
    → ( l + r ` loc ) ⊢ (LeftU v₁) > (RightU v₂)


  choice-rl : ∀ { l r : RE } { loc : ℕ } { v₁ : U r } { v₂ : U l }
    → length (proj₁ (flat v₁)) > length (proj₁ (flat v₂))
    -------------------------------------------------------------------    
    → ( l + r ` loc ) ⊢ (RightU v₁) > (LeftU v₂)

  choice-ll : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U l }
    →  l ⊢ v₁ >  v₁'
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (LeftU v₁) > (LeftU v₁')

  choice-rr : ∀ { l r : RE } { loc : ℕ } { v₂ v₂'  : U r }
    →  r ⊢ v₂ >  v₂'
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (RightU v₂) > (RightU v₂')


  star-cons-nil : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v : U r } { vs : List (U r) }
    → ( r * nε ` loc ) ⊢ (ListU (v ∷ vs)) > ( ListU [] )

  -- star-nil-cons rule is not needed as we are dealing with non problematic regular expression.
  
  star-head : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v₁ v₂ : U r } { vs₁ vs₂ : List (U r) }
    → r ⊢ v₁ > v₂
    ----------------------------------------------------------------------
    → ( r * nε ` loc ) ⊢ (ListU (v₁ ∷ vs₁)) > (ListU (v₂ ∷ vs₂))


  star-tail : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } { v₁ v₂ : U r } { vs₁ vs₂ : List (U r) }
    → v₁ ≡ v₂
    → ( r * nε ` loc ) ⊢ (ListU vs₁) > (ListU vs₂)
    ----------------------------------------------------------------------
    → ( r * nε ` loc ) ⊢ (ListU (v₁ ∷ vs₁)) > (ListU (v₂ ∷ vs₂))


```


F. Ausaf, R. Dyckhoff, and C. Urban. “POSIX Lexing with Derivatives of Regular Expressions (Proof Pearl)”. In: Proc. of the 7th International Conference on
Interactive Theorem Proving (ITP). Vol. 9807. LNCS. 2016, pp. 69–86.

has the following definition of POSIX relation

P1

-------------------
([], ε) --> EmptyU


PC

-------------------
([c], $ c) --> LetterU c



P + L

(s, r₁) --> v₁
------------------------
(s, r₁ + r₂) --> LeftU v₁


P + R

(s, r₂) --> v₂   s∉ ⟦r₁⟧  
------------------------
(s, r₁ + r₂) --> RightU v₂



PS

(s₁, r₁) --> v₁     (s₂, r₂) --> v₂
¬∃ ( s₃ , s₄ ) . s₃ ≢ [] ∧ (s₃ ++ s₄) ≡ s₂ ∧ (s₁ ++ s₃) ∈⟦ r₁ ⟧ ∧ s₄ ∈⟦ r₂ ⟧ )
------------------------------------------------------------------------------
(s₁ ++ s₂, r₁ ● r₂) --> PairU v₁ v₂



P[]

---------------------------------------
([], r*) --> ListU []


P*

(s1, r) --> v       (s2, r*) --> ListU vs       |v| ≢ []
¬∃ ( s3 , s4 ) . s3 ≢ [] ∧ (s3 ++ s4) ≡ s2 ∧ (s1 ++ s3) ∈⟦ r ⟧ ∧ s4 ∈⟦ r* ⟧ 
-----------------------------------------------------------------------------
(s1 ++ s2, r* ) --> ListU (v ∷ vs)


It seems that the relationship is weaker. It fixes a particular word. 

```agda
infix 4 _,_⇒_

data _,_⇒_ : ∀ ( w : List Char ) → ( r : RE ) → U r → Set where
  p₁  : [] , ε ⇒ EmptyU 
  pc  : ∀ {c : Char} {loc : ℕ}  → [ c ] , $ c ` loc ⇒ LetterU c
  p+l : ∀ { w : List Char } { l r : RE } { loc : ℕ } { v : U l }
    →  w , l ⇒ v   
    ------------------------------------------------------------
    → w , l + r ` loc ⇒ LeftU v
  p+r : ∀ { w : List Char } { l r : RE } { loc : ℕ } { v : U r } 
    →  w , r ⇒ v
    → ¬ ( w ∈⟦ l ⟧ )
    ------------------------------------------------------------
    → w , l + r ` loc ⇒ RightU v
  ps : ∀ { w₁ w₂ : List Char } { l r : RE } { loc : ℕ } { v₁ : U l } { v₂ : U r }
    →  w₁ , l ⇒ v₁
    →  w₂ , r ⇒ v₂
    → ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) × (w₃ ++ w₄ ≡ w₂) × ( (w₁ ++ w₃) ∈⟦ l ⟧ ) × w₄ ∈⟦ r ⟧ )
    ------------------------------------------------------------
    → (w₁ ++ w₂) , l ● r ` loc ⇒ PairU v₁ v₂
    
  p[] : ∀ { r : RE } {ε∉r : ε∉ r } { loc : ℕ }
    → [] , r * ε∉r ` loc ⇒ ListU []
    
  p* : ∀ { w₁ w₂ : List Char } { r : RE } {ε∉r : ε∉ r } { loc : ℕ } {v : U r } { vs : List (U r) }
    →  w₁ , r ⇒ v
    →  w₂ , r * ε∉r ` loc ⇒ ListU vs
    →  ¬ w₁ ≡ []
    → ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) × (w₃ ++ w₄ ≡ w₂) × ( (w₁ ++ w₃) ∈⟦ r ⟧ ) × w₄ ∈⟦ r * ε∉r ` loc ⟧ )
    -----------------------------------------------------------
    → (w₁ ++ w₂) , r * ε∉r ` loc ⇒ ListU (v ∷ vs)
    
```


Lemma : a posix value is the largest value in posix ordering


```agda
postulate
  ⇒>-max : ∀ { r : RE } { v : U r } { w : List Char} 
    → w , r ⇒ v
    → ( u : U r )
    ------------------------
    → ( v ≡ u ) ⊎ ( r ⊢ v > u )


```



Note : The > order is transitive. 

```agda

>-trans : { r : RE } { u₁ u₂ u₃ : U r }
  → r ⊢ u₁ > u₂
  → r ⊢ u₂ > u₃
  -----------------
  → r ⊢ u₁ > u₃
>-trans {ε} = λ()
>-trans {$ c ` loc} = λ()
>-trans {r * ε∉r ` loc} star-cons-nil = λ()
>-trans {r * ε∉r ` loc} (star-head v₁>v₂)         (star-head v₂>v₃) = star-head (>-trans v₁>v₂ v₂>v₃)
>-trans {r * ε∉r ` loc} (star-head v₁>v₂)         (star-tail v₂≡v₃ vs₂>vs₃) rewrite (sym v₂≡v₃) = star-head v₁>v₂
>-trans {r * ε∉r ` loc} (star-head v₁>v₂)         star-cons-nil  = star-cons-nil
>-trans {r * ε∉r ` loc} (star-tail v₁≡v₂ vs₁>vs₂) (star-tail v₂≡v₃ vs₂>vs₃) rewrite (sym v₂≡v₃) = star-tail v₁≡v₂ (>-trans vs₁>vs₂ vs₂>vs₃)
>-trans {r * ε∉r ` loc} (star-tail v₁≡v₂ vs₁>vs₂) (star-head v₂>v₃) rewrite v₁≡v₂ = star-head v₂>v₃ 
>-trans {r * ε∉r ` loc} (star-tail v₁≡v₂ vs₁>vs₂) star-cons-nil  = star-cons-nil
>-trans {l + r ` loc} (choice-ll {l} {r} {.loc} {v₁} {v₂} v₁>v₂) (choice-lr {l} {r} {.loc} {.v₂} {v₃} |v₂|≥|v₃|) = choice-lr ( ≤-trans |v₂|≥|v₃| {!!} ) -- we have l ⊢ v₁ > v₂, how to get |v₁| ≥ |v₂|

```



the posix > we defined in FLOPS 2014 is not transitive, b/c of the ll, lr, rl and rr rules.

Consider r = (a* ● a*) + a*

u₁ = L (Pair [] [a,a])
u₂ = R [a,a]

according to choice-lr rule, r ⊢ u₁ > u₂

u₃ = L (Pair [a] [] )

according to choice-rl rule, r ⊢ u₂ > u₃

according to choice-ll rule, r ⊢ u₃ > u₁


Why this is bad? Consider another regular expression t = r ● a*

what is the max value according to the > order?

v₁ = Pair u₁ []
v₂ = Pair u₂ []
v₃ = Pair u₃ [a]

A proposed solution. change the choice-ll and choice-rr to use len||>len|| instead of r ⊢ _ > _




choice-ll-> : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U l }
    → length (proj₁ (flat v₁)) > length (proj₁ (flat v₁'))
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (LeftU v₁) > (LeftU v₁')


choice-ll-= : ∀ { l r : RE } { loc : ℕ } { v₁ v₁'  : U l }
    → length (proj₁ (flat v₁)) ≡ length (proj₁ (flat v₁'))
    → l ⊢ v₁ > v₁' 
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (LeftU v₁) > (LeftU v₁')



choice-rr-> : ∀ { l r : RE } { loc : ℕ } { v₂ v₂'  : U r }
    → length (proj₁ (flat v₂)) > length (proj₁ (flat v₂'))
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (LeftU v₁) > (LeftU v₁')



choice-rr-= : ∀ { l r : RE } { loc : ℕ } { v₂ v₂'  : U r }
    → length (proj₁ (flat v₂)) ≡ length (proj₁ (flat v₂'))
    →  r ⊢ v₂ >  v₂'
    -------------------------------------------------------------------
    → ( l + r ` loc ) ⊢ (RightU v₂) > (RightU v₂')









> The following is probably not necessary.


Maybe we need to weaken the transitivity lemma to include the underlying word.

a) Does r ⊢ v₁ > v₂ imply |v₁| ≥ |v₂| ? no.
counter example: r = ( a ● (a + ε) )*

r ⊢ 
 Cons (Pair a (L a))     (Cons (Pair a (R Empty)) Nil)
 > 
 Cons (Pair a (R Empty)) (Cons (Pair a (L a)) (Cons (Pair a (R Empty)) Nil))

with star-head (seq₂ (choice-rl 1>0)) as the proof

but | Cons (Pair a (L a))     (Cons (Pair a (R Empty)) Nil) | = aaa
    | Cons (Pair a (R Empty)) (Cons (Pair a (L a)) (Cons (Pair a (R Empty)) Nil)) | = aaaa
    

b) Does |v₁| ≥ |v₂| imply  r ⊢ v₁ > v₂ ? no. 

same counter example above i.e. a).


For a) to hold, the only rule that we need to weaken is star-head

we need to ensure that |v₁| ≥ |v₂| and |v₁| + |vs₁| ≥ |v₂| + |vs₂|

which will reject the counter example above. 

>>> what about nested *, the ≡ won't hold but that's problematic.


