```agda
{-# OPTIONS --rewriting #-}
module cgp.posix.Related where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ∷-inj  ;
  w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ ;
  w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ ;
  ¬m>n→n≡m⊎n>m ;
  len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ ; concatmap-λx→[]-xs≡[] 
  {- ; ¬≡[]→¬length≡0 ; ¬≡0→>0 ; []→length≡0  ; ¬0>0 -}  )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;
  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unListU ; listU∘unListU ; 
  unflat∘proj₂∘flat ; flat∘unflat ;
  inv-listU ; inv-listU1 ; inv-pairU ; inv-leftU ; inv-rightU ;
  _⊢_≟_  ; ¬|list-u∷us|≡[] ) 

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ;
  proj₁flat-v≡[]→ε∈r ; flat-[]→flat-[]-left ; flat-[]→flat-[]-right ; mkAllEmptyU≢[]  )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ;
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ;
  concatmap-pdinstance-snd ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with ;
  concatmap-pdinstance-snd-[]≡[] 
  ) 



import cgp.posix.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; -- pdUConcat ;
  pdUMany[_,_]; pdUMany-aux ;
  pdinstance-oplus ; fuse ; mkfuseInj ;  mkfuseInjSoundEv ; 
  advance-pdi*-with-c
  )


import cgp.posix.Order as PosixOrder
open PosixOrder using ( _⊢_>_ ; len-≡ ; len-> ; 
  _⊢_>ⁱ_ ; seq₁ ; seq₂ ;
  choice-ll ; choice-rr ;
  choice-lr ;
  choice-rl ; star-head ; star-cons-nil ; star-tail ;
  >→¬≡ 
  )

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _>_ ; _≥_ ; _≤_  ; _+_  )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ;
  length-++ ; ++-assoc 
  -- ; length-++-sucʳ -- this is only available after v2.3
  )


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
  ps : ∀ { w₁ w₂ w : List Char } { l r : RE } { loc : ℕ } { v₁ : U l } { v₂ : U r }
    →  w ≡ w₁ ++ w₂  -- having a separate index variable w make the proof easier  
    →  w₁ , l ⇒ v₁
    →  w₂ , r ⇒ v₂
    → ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) × (w₃ ++ w₄ ≡ w₂) × ( (w₁ ++ w₃) ∈⟦ l ⟧ ) × w₄ ∈⟦ r ⟧ )
    -----------------s-------------------------------------------
    → w , l ● r ` loc ⇒ PairU v₁ v₂
    
  p[] : ∀ { r : RE } {ε∉r : ε∉ r } { loc : ℕ } -- why we need this case if ε∉r ? because w.r.t to empty word [], ListU [] is the posix parse tree.
    → [] , r * ε∉r ` loc ⇒ ListU []
    
  p* : ∀ { w₁ w₂ w : List Char } { r : RE } {ε∉r : ε∉ r } { loc : ℕ } {v : U r } { vs : List (U r) }
    →  w ≡ w₁ ++ w₂  -- having a separate index variable w make the proof easier
    →  w₁ , r ⇒ v
    →  w₂ , r * ε∉r ` loc ⇒ ListU vs
    →  ¬ w₁ ≡ []
    → ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) × (w₃ ++ w₄ ≡ w₂) × ( (w₁ ++ w₃) ∈⟦ r ⟧ ) × w₄ ∈⟦ r * ε∉r ` loc ⟧ )
    -----------------------------------------------------------
    → w , r * ε∉r ` loc ⇒ ListU (v ∷ vs)
    
```

Lemma : a posix parse tree must be flattened to the indexed word. 


```agda

⇒-member : ∀ { r : RE } { v : U r } { w : List Char} 
    → w , r ⇒ v
    → proj₁ (flat {r} v) ≡ w
⇒-member {ε}             {EmptyU}     {[]}      p₁                 = refl
⇒-member {$ c ` loc}     {LetterU .c} {.c ∷ []} (pc .{c} .{loc})   = refl
⇒-member {l ● r ` loc}   {PairU v u}  {w}       (ps {w₁} {w₂} .{w} .{l} .{r} .{loc} .{v} .{u} w≡w₁++w₂ w₁,l→v w₂,r→u longest-ev) = prf
  where
    ind-hyp-l : proj₁ (flat {l} v) ≡ w₁
    ind-hyp-l = ⇒-member w₁,l→v 
    ind-hyp-r : proj₁ (flat {r} u) ≡ w₂
    ind-hyp-r = ⇒-member w₂,r→u
    prf : proj₁ (flat (PairU {l} {r} {loc} v u)) ≡ w
    prf rewrite  ind-hyp-l |  ind-hyp-r = sym w≡w₁++w₂
⇒-member {l + r ` loc}   {LeftU v}  {w}       (p+l .{w} .{l} .{r} .{loc} .{v} w,l→v)       = ⇒-member w,l→v 
⇒-member {l + r ` loc}   {RightU v} {w}       (p+r .{w} .{l} .{r} .{loc} .{v} w,r→v ¬w∈⟦l⟧) = ⇒-member w,r→v 
⇒-member {r * ε∉r ` loc} {ListU []} {[]}      (p[] .{r} .{ε∉r} .{loc}) = refl 
⇒-member {r * ε∉r ` loc} {ListU (x ∷ xs)} {w} (p* {w₁} {w₂} .{w} .{r} .{ε∉r} .{loc} .{x} .{xs} w≡w₁++w₂ w₁,r→x w₂,r*→list-xs ¬w₁≡[] longest-ev) = prf
  where
    ind-hyp-x : proj₁ (flat {r} x) ≡ w₁
    ind-hyp-x = ⇒-member w₁,r→x
    ind-hyp-list-xs : proj₁ (flat {r * ε∉r ` loc} (ListU xs)) ≡ w₂
    ind-hyp-list-xs = ⇒-member w₂,r*→list-xs 
    prf : proj₁ (flat {r * ε∉r ` loc} (ListU (x ∷ xs))) ≡ w
    prf rewrite  ind-hyp-x |  ind-hyp-list-xs = sym w≡w₁++w₂

```

Lemma : a posix parse tree is the max value in posix ordering > 

```agda

⇒→>-max : ∀ { r : RE } { v : U r } { w : List Char} 
    → w , r ⇒ v
    → ( u : U r )
    → ¬ ( v ≡ u )
    → proj₁ (flat v) ≡ proj₁ (flat u) 
    ------------------
    → ( r ⊢ v > u )
⇒→>-max {ε}           {EmptyU}    {[]}      p₁          EmptyU      ¬empty≡empty       refl   = Nullary.contradiction refl ¬empty≡empty
⇒→>-max {$ c ` loc}   {LetterU _} .{c ∷ []} pc          (LetterU _) ¬letter-c≡letter-c refl = Nullary.contradiction refl ¬letter-c≡letter-c
⇒→>-max {l + r ` loc} {LeftU v}   {w}       (p+l w,l→v) (LeftU u)   ¬left-v≡left-u     |left-v|≡|left-u|  = len-≡  len|left-v|≡len|left-u| (choice-ll v>u )
  where
    len|left-v|≡len|left-u| : length (proj₁ (flat (LeftU {l} {r} {loc} v))) ≡ length (proj₁ (flat (LeftU {l} {r} {loc} u)))
    len|left-v|≡len|left-u| rewrite |left-v|≡|left-u| = refl

    ¬v≡u : ¬ v ≡ u
    ¬v≡u v≡u = ¬left-v≡left-u (cong LeftU v≡u) 

    v>u : l ⊢ v > u
    v>u = ⇒→>-max {l} {v} {w} w,l→v u ¬v≡u |left-v|≡|left-u|

⇒→>-max {l + r ` loc} {RightU v}   {w}       (p+r w,r→v ¬w∈⟦l⟧) (RightU u)   ¬right-v≡right-u     |right-v|≡|right-u|  = len-≡  len|right-v|≡len|right-u| (choice-rr v>u )
  where
    len|right-v|≡len|right-u| : length (proj₁ (flat (RightU {l} {r} {loc} v))) ≡ length (proj₁ (flat (RightU {l} {r} {loc} u)))
    len|right-v|≡len|right-u| rewrite |right-v|≡|right-u| = refl

    ¬v≡u : ¬ v ≡ u
    ¬v≡u v≡u = ¬right-v≡right-u (cong RightU v≡u) 

    v>u : r ⊢ v > u
    v>u = ⇒→>-max {r} {v} {w} w,r→v u ¬v≡u |right-v|≡|right-u|


⇒→>-max {l + r ` loc} {RightU v}   {w}       (p+r w,r→v ¬w∈⟦l⟧) (LeftU u)   ¬right-v≡left-u     |right-v|≡|left-u|  = Nullary.contradiction w∈⟦l⟧ ¬w∈⟦l⟧
  where
    |left-u|≡w : proj₁ (flat {l + r ` loc} (LeftU {l} {r} {loc} u)) ≡ w
    |left-u|≡w rewrite (sym  |right-v|≡|left-u| )  =  ⇒-member (p+r {w} {l} {r} {loc} {v}  w,r→v ¬w∈⟦l⟧)
    w∈⟦l⟧ : w ∈⟦ l ⟧
    w∈⟦l⟧ rewrite (sym |left-u|≡w) =  proj₂ (flat {l} u)  

⇒→>-max {l + r ` loc} {LeftU v}   {w}       (p+l w,l→v) (RightU u)   ¬left-v≡Right-u     |left-v|≡|right-u|  = len-≡  len|left-v|≡len|right-u| (choice-lr len|v|≥len|u| )
  where
    len|left-v|≡len|right-u| : length (proj₁ (flat (LeftU {l} {r} {loc} v))) ≡ length (proj₁ (flat (RightU {l} {r} {loc} u)))
    len|left-v|≡len|right-u| rewrite |left-v|≡|right-u| = refl

    len|v|≥len|u| : length (proj₁ (flat {l} v)) ≥ length (proj₁ (flat {r} u))
    len|v|≥len|u| rewrite |left-v|≡|right-u| = ≤-refl  


⇒→>-max {r * ε∉r ` loc} {ListU []} {[]}             (p[] .{r} .{ε∉r} .{loc}) (ListU []) ¬list-[]≡list-[] |list-[]|≡|list-[]| = Nullary.contradiction refl ¬list-[]≡list-[]

⇒→>-max {r * ε∉r ` loc} {ListU []} {[]}             (p[] .{r} .{ε∉r} .{loc}) (ListU (u ∷ us)) ¬list-[]≡list-u∷us |list-[]|≡|list-u∷us| =  Nullary.contradiction  (sym  |list-[]|≡|list-u∷us|)  (¬|list-u∷us|≡[] {r} {ε∉r} {loc} {u} {us})

⇒→>-max {r * ε∉r ` loc} {ListU (v ∷ vs)}  {w}  (p*  {w₁} {w₂} .{w} {r} {ε∉r} {loc} .{v} .{vs} w≡w₁++w₂ w₁,r→v w₂,r*→list-vs ¬w₁≡[] longest-ev) (ListU []) ¬list-v∷vs≡list-[] |list-v∷vs|≡|list-[]| =  Nullary.contradiction  |list-v∷vs|≡|list-[]| (¬|list-u∷us|≡[] {r} {ε∉r} {loc} {v} {vs}) 

⇒→>-max {r * ε∉r ` loc} {ListU (v ∷ vs)}  {w}  (p*  {w₁} {w₂} .{w} {r} {ε∉r} {loc} .{v} .{vs} w≡w₁++w₂ w₁,r→v w₂,r*→list-vs ¬w₁≡[] longest-ev) (ListU (u ∷ us)) ¬list-v∷vs≡list-u∷us |list-v∷vs|≡|list-u∷us| = len-≡ len|left-v∷vs|≡len|left-u∷us| list-v∷vs>ˡlist-u∷us 
  where
    len|left-v∷vs|≡len|left-u∷us| : length (proj₁ (flat (ListU {r} {ε∉r} {loc} (v ∷ vs)))) ≡ length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ us))))
    len|left-v∷vs|≡len|left-u∷us| rewrite |list-v∷vs|≡|list-u∷us| = refl
    list-v∷vs>ˡlist-u∷us : (r * ε∉r ` loc) ⊢ ListU (v ∷ vs) >ⁱ ListU (u ∷ us)
    list-v∷vs>ˡlist-u∷us with length (proj₁ (flat v)) Nat.<? length (proj₁ (flat u))
    ... | yes len|v|<len|u| rewrite sym (⇒-member w₂,r*→list-vs) | sym (⇒-member w₁,r→v)
          = Nullary.contradiction anti-longest-ev  longest-ev 

        where
          anti-longest-ev-part1 : ∃[ w₅ ] ( ¬ w₅ ≡ [] ) ×
                                          ( (proj₁ (flat {r} v)) ++ w₅ ≡ (proj₁ (flat {r} u)) ) ×
                                          ( (proj₁ (flat {r * ε∉r ` loc} (ListU vs))) ≡ w₅ ++ (proj₁ (flat {r * ε∉r ` loc} (ListU us)))) 
          anti-longest-ev-part1 rewrite sym (⇒-member w₂,r*→list-vs)  = w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ {proj₁ (flat {r} v)} {proj₁ (flat {r * ε∉r ` loc} (ListU vs))} {proj₁ (flat {r} u)} {proj₁ (flat {r * ε∉r ` loc} (ListU us))}  |list-v∷vs|≡|list-u∷us|   len|v|<len|u|
          anti-longest-ev : ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) ×
                                            ( w₃ ++ w₄ ≡ proj₁ (flat {r * ε∉r ` loc} (ListU vs)) ) ×
                                            ( ( (proj₁ (flat {r} v)) ++ w₃ ) ∈⟦ r ⟧ ) ×
                                            ( w₄ ∈⟦ r * ε∉r ` loc ⟧ ) 
          anti-longest-ev = (proj₁ anti-longest-ev-part1 , ( (proj₁ (flat {r * ε∉r ` loc} (ListU us))) ,
                                      ( proj₁ (proj₂ anti-longest-ev-part1 ) ) ,
                                         ( sym (proj₂ (proj₂ (proj₂ anti-longest-ev-part1))) ,
                                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦r⟧  , proj₂ (flat { r * ε∉r ` loc}  (ListU us))   ) ) )
                          where
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦r⟧ : (Product.proj₁ (flat v) ++ Product.proj₁ anti-longest-ev-part1)  ∈⟦ r ⟧
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦r⟧ rewrite (proj₁ (proj₂ (proj₂  anti-longest-ev-part1 ))) =  proj₂ (flat {r} u) 
          
    ... | no ¬len|v|<len|u| with (¬m>n→n≡m⊎n>m ¬len|v|<len|u|)
    ...                      | inj₂ len|v|>len|u| = star-head (len-> len|v|>len|u|)
    ...                      | inj₁ len|v|≡len|u| with r ⊢ v ≟ u
    ...                                            | no ¬v≡u = star-head (⇒→>-max  w₁,r→v u ¬v≡u  (proj₁ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |list-v∷vs|≡|list-u∷us| len|v|≡len|u|)) )
    ...                                            | yes v≡u = star-tail v≡u (⇒→>-max w₂,r*→list-vs (ListU us)  ¬list-vs≡list-us  (proj₂ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |list-v∷vs|≡|list-u∷us| len|v|≡len|u|)))
                                                         where
                                                           ¬list-vs≡list-us : ¬ (ListU {r}  {ε∉r} {loc} vs) ≡ (ListU {r}  {ε∉r} {loc} us)
                                                           ¬list-vs≡list-us list-vs≡list-us =  ¬list-v∷vs≡list-u∷us ( Eq.cong₂ (λ x xs → ListU  {r}  {ε∉r} {loc} (x ∷ xs)) v≡u vs≡us )
                                                             where
                                                               vs≡us : vs ≡ us
                                                               vs≡us = inv-listU1 vs us list-vs≡list-us 


    
⇒→>-max {l ● r ` loc} {PairU {l} {r} {loc} v₁ v₂} {w}   (ps {w₁} {w₂} .{w} .{l} .{r} .{loc} .{v₁} .{v₂} w≡w₁++w₂ w₁,l→v₁ w₂,r→v₂ longest-ev) (PairU u₁ u₂) ¬pair-v₁v₂≡pair-u₁u₂ |pair-v₁v₂|≡|pair-u₁u₂| =
  len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| pair-v₁v₂>ˡpair-u₁u₂ 
  where
    len|pair-v₁v₂|≡len|pair-u₁u₂| : length (proj₁ (flat (PairU  {l} {r} {loc} v₁ v₂))) ≡ length (proj₁ (flat (PairU  {l} {r} {loc} u₁ u₂)))
    len|pair-v₁v₂|≡len|pair-u₁u₂| rewrite |pair-v₁v₂|≡|pair-u₁u₂|  =  refl 
    pair-v₁v₂>ˡpair-u₁u₂ : (l ● r ` loc) ⊢ PairU v₁ v₂ >ⁱ PairU u₁ u₂
    pair-v₁v₂>ˡpair-u₁u₂ with length (proj₁ (flat v₁)) Nat.<? length (proj₁ (flat u₁))
    ... | yes len|v₁|<len|u₁| rewrite sym (⇒-member w₂,r→v₂) | sym (⇒-member w₁,l→v₁) =  Nullary.contradiction anti-longest-ev  longest-ev 
        where
          anti-longest-ev-part1 : ∃[ w₅ ] ( ¬ w₅ ≡ [] ) ×
                                          ( (proj₁ (flat {l} v₁)) ++ w₅ ≡ (proj₁ (flat {l} u₁)) ) ×
                                          ( (proj₁ (flat {r} v₂)) ≡ w₅ ++ (proj₁ (flat {r} u₂))) 
          anti-longest-ev-part1 rewrite sym (⇒-member w₂,r→v₂)  = w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄  {proj₁ (flat {l} v₁)} {proj₁ (flat {r} v₂)} {proj₁ (flat {l} u₁)} {proj₁ (flat {r} u₂)} |pair-v₁v₂|≡|pair-u₁u₂|   len|v₁|<len|u₁|
          anti-longest-ev : ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) ×
                                            ( w₃ ++ w₄ ≡ proj₁ (flat {r} v₂) ) ×
                                            ( ( (proj₁ (flat {l} v₁)) ++ w₃ ) ∈⟦ l ⟧ ) ×
                                            ( w₄ ∈⟦ r ⟧ ) 
          anti-longest-ev = (proj₁ anti-longest-ev-part1 , ( (proj₁ (flat {r} u₂)) ,
                                      ( proj₁ (proj₂ anti-longest-ev-part1 ) ) ,
                                         ( sym (proj₂ (proj₂ (proj₂ anti-longest-ev-part1))) ,
                                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦l⟧  , proj₂ (flat {r}  u₂)   ) ) )
                          where
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦l⟧ : (Product.proj₁ (flat v₁) ++ Product.proj₁ anti-longest-ev-part1)  ∈⟦ l ⟧
                            proj₁flat-v++proj₁-anti-longest-ev-part1∈⟦l⟧ rewrite (proj₁ (proj₂ (proj₂  anti-longest-ev-part1 ))) =  proj₂ (flat {l} u₁) 
          
    
    ... | no ¬len|v₁|<len|u₁| with (¬m>n→n≡m⊎n>m ¬len|v₁|<len|u₁|)
    ...                        | inj₂ len|v₁|>len|u₁| = seq₁ (len-> len|v₁|>len|u₁|)
    ...                        | inj₁ len|v₁|≡len|u₁| with l ⊢ v₁ ≟ u₁
    ...                                                | no ¬v₁≡u₁ = seq₁ (⇒→>-max  w₁,l→v₁ u₁ ¬v₁≡u₁ (proj₁ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |pair-v₁v₂|≡|pair-u₁u₂| len|v₁|≡len|u₁|)))
    ...                                                | yes v₁≡u₁ = seq₂ v₁≡u₁ (⇒→>-max w₂,r→v₂ u₂  ¬v₂≡u₂ (proj₂ (w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ |pair-v₁v₂|≡|pair-u₁u₂| len|v₁|≡len|u₁|)) )
                                                             where
                                                               ¬v₂≡u₂ : ¬ v₂ ≡ u₂
                                                               ¬v₂≡u₂ v₂≡u₂ = ¬pair-v₁v₂≡pair-u₁u₂ (Eq.cong₂ (λ x y → (PairU {l} {r} {loc} x y)) v₁≡u₁ v₂≡u₂) 

```


Lemma : the max value in the posix ordering > must be a posix parse tree.



```agda

intersect-memberʳ : ∀ { l r : RE } { v : U r } 
    → proj₁ (flat {r} v) ∈⟦ l ⟧
    → ∃[ u ] ( proj₁ (flat {l} u) ∈⟦ l ⟧ )  × (proj₁ (flat {r} v) ≡  proj₁ (flat {l} u)  )
intersect-memberʳ {l} {r} {v} |v|∈⟦l⟧ = u , |u|∈⟦l⟧ , sym |u|≡|v| 
  where
    u : U l
    u = unflat |v|∈⟦l⟧
    |u|≡|v| : proj₁ (flat u) ≡ proj₁ (flat v)
    |u|≡|v| rewrite flat∘unflat {l} |v|∈⟦l⟧ = refl 
    |u|∈⟦l⟧ : proj₁ (flat u) ∈⟦ l ⟧
    |u|∈⟦l⟧ rewrite |u|≡|v| = |v|∈⟦l⟧
  


>-anti-sym : ∀ { r : RE } { v u : U r }
    → r ⊢ v > u
    → r ⊢ u > v
    ------------
    → v ≡ u

>→¬< : ∀ { r : RE } { v u : U r }
  → r ⊢ v > u
  -------------
  → ¬ r ⊢ u > v
  
>-anti-sym  {ε}           {EmptyU}        {EmptyU}      (len-> 0>0) = Nullary.contradiction 0>0 (<-irrefl refl)
>-anti-sym  {ε}           {EmptyU}        {EmptyU}      (len-≡ refl ())  (len-≡ refl ()) 
>-anti-sym  {$ c ` loc}   {LetterU .c}    {LetterU .c}  (len-> 1>1) = Nullary.contradiction 1>1 (<-irrefl refl)
>-anti-sym  {$ c ` loc}   {LetterU .c}    {LetterU .c}  (len-≡ refl ())  (len-≡ refl ())
>-anti-sym  {r} {v}   {u} (len-> len|v|>len|u|)               (len-> len|u|>len|v|)   = Nullary.contradiction len|v|>len|u| (<⇒≯ len|u|>len|v|)
>-anti-sym  {r} {v}   {u} (len-> len|v|>len|u|)               (len-≡ len|u|≡len|v| _) = Nullary.contradiction len|v|>len|u| (<-irrefl len|u|≡len|v|)
>-anti-sym  {r} {v}   {u} (len-≡ len|v|≡len|u| _)             (len-> len|u|>len|v|)   = Nullary.contradiction len|u|>len|v| (<-irrefl len|v|≡len|u|)

>-anti-sym  {l ● r ` loc} {PairU v₁ v₂}   {PairU u₁ u₂} (len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| (seq₁ v₁>u₁))        (len-≡ len|pair-u₁u₂|≡len|pair-v₁v₂| (seq₁ u₁>v₁))       = Nullary.contradiction v₁>u₁ (>→¬< u₁>v₁)
>-anti-sym  {l ● r ` loc} {PairU v₁ v₂}   {PairU u₁ u₂} (len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| (seq₂ v₁≡u₁ v₂>u₂))  (len-≡ len|pair-u₁u₂|≡len|pair-v₁v₂| (seq₂ u₁≡v₁ u₂>v₂)) = Nullary.contradiction v₂>u₂ (>→¬< u₂>v₂)
>-anti-sym  {l ● r ` loc} {PairU v₁ v₂}   {PairU u₁ u₂} (len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| (seq₂ v₁≡u₁ v₂>u₂))  (len-≡ len|pair-u₁u₂|≡len|pair-v₁v₂| (seq₁ u₁>v₁))       = Nullary.contradiction (sym v₁≡u₁) (>→¬≡ u₁>v₁)
>-anti-sym  {l ● r ` loc} {PairU v₁ v₂}   {PairU u₁ u₂} (len-≡ len|pair-v₁v₂|≡len|pair-u₁u₂| (seq₁ v₁>u₁))        (len-≡ len|pair-u₁u₂|≡len|pair-v₁v₂| (seq₂ u₁≡v₁ u₂>v₂)) = Nullary.contradiction (sym u₁≡v₁) (>→¬≡ v₁>u₁)

>-anti-sym  {l + r ` loc}   {LeftU v}     {LeftU u}           (len-≡ len|left-v|≡len|left-u|   (choice-ll v>u))  (len-≡ len|left-u|≡len|left-v| (choice-ll u>v)) = Nullary.contradiction v>u (>→¬< u>v)
>-anti-sym  {l + r ` loc}   {LeftU v}     {RightU u}          (len-≡ len|left-v|≡len|right-u|  (choice-lr len|v|≥len|u|))  (len-≡ len|right-u|≡len|left-v| (choice-rl len|u|>len|v|)) = Nullary.contradiction len|v|≥len|u| (<⇒≱  len|u|>len|v|)
>-anti-sym  {l + r ` loc}   {RightU v}    {LeftU u}           (len-≡ len|right-v|≡len|left-u|  (choice-rl len|v|>len|u|))  (len-≡ len|left-u|≡len|right-v| (choice-lr len|u|≥len|v|)) = Nullary.contradiction len|u|≥len|v| (<⇒≱  len|v|>len|u|)
>-anti-sym  {l + r ` loc}   {RightU v}    {RightU u}          (len-≡ len|right-v|≡len|right-u|  (choice-rr v>u))  (len-≡ len|right-u|≡len|right-v| (choice-rr u>v)) = Nullary.contradiction v>u (>→¬< u>v)
>-anti-sym  {r * ε∉r ` loc} {ListU []}    {ListU []}          (len-≡ refl ())  (len-≡ refl ())
>-anti-sym  {r * ε∉r ` loc} {ListU (v ∷ vs)} {ListU (u ∷ us)} (len-≡ len|list-v∷vs|≡len|list-u∷us| (star-head v>u)) (len-≡ len|list-u∷us|≡len|list-v∷vs| (star-head u>v)) = Nullary.contradiction v>u (>→¬< u>v)
>-anti-sym  {r * ε∉r ` loc} {ListU (v ∷ vs)} {ListU (u ∷ us)} (len-≡ len|list-v∷vs|≡len|list-u∷us| (star-head v>u)) (len-≡ len|list-u∷us|≡len|list-v∷vs| (star-tail u≡v _)) = Nullary.contradiction (sym u≡v) (>→¬≡ v>u)
>-anti-sym  {r * ε∉r ` loc} {ListU (v ∷ vs)} {ListU (u ∷ us)} (len-≡ len|list-v∷vs|≡len|list-u∷us| (star-tail v≡u _)) (len-≡ len|list-u∷us|≡len|list-v∷vs| (star-head u>v)) = Nullary.contradiction (sym v≡u) (>→¬≡ u>v)
>-anti-sym  {r * ε∉r ` loc} {ListU (v ∷ vs)} {ListU (u ∷ us)} (len-≡ len|list-v∷vs|≡len|list-u∷us| (star-tail v≡u vs>us)) (len-≡ len|list-u∷us|≡len|list-v∷vs| (star-tail u≡v us>vs)) =  Nullary.contradiction vs>us (>→¬< us>vs) 



>→¬< {r} {v} {u} v>u u>v = (>→¬≡ v>u) (>-anti-sym v>u u>v)


-- this can be moved to Utils
++-¬[]→> : ∀ { A : Set } { xs ys : List A }
  → ¬ ys ≡ []
  --------------------------------
  → length (xs ++ ys) > length xs
++-¬[]→> {A} {xs} {[]}     ¬ys≡[]  = Nullary.contradiction refl ¬ys≡[]   
++-¬[]→> {A} {[]} {y ∷ ys} ¬yys≡[] = Nat.s≤s Nat.z≤n
++-¬[]→> {A} {x ∷ xs } {y ∷ ys} ¬yys≡[] = Nat.s≤s ind-hyp
  where
    ind-hyp : length (xs ++ (y ∷ ys)) > length xs
    ind-hyp = ++-¬[]→> {A} {xs} {y ∷ ys} ¬yys≡[]

  

{-# TERMINATING #-}
>-max→⇒ :  ∀ { r : RE } { v : U r } 
  → ( ∀ ( u : U r )
      → proj₁ ( flat {r} v ) ≡ proj₁ (flat {r} u )
      →  r ⊢ v > u )
  -----------------------------------
  → proj₁ (flat {r} v) , r ⇒ v

>-max→⇒ {ε}           {EmptyU}      max-ev = p₁
>-max→⇒ {$ c ` loc}   {LetterU .c}  max-ev = pc
>-max→⇒ {l + r ` loc} {LeftU v}     max-ev = p+l |v|,l⇒v
  where
    ∀u→|v|≡|u|→v>u : ( u : U l ) → proj₁ (flat {l} v) ≡ proj₁ (flat {l} u)  → l ⊢ v > u
    ∀u→|v|≡|u|→v>u u |v|≡|u| with max-ev (LeftU u) |v|≡|u|
    ... | len-≡ len|left-v|≡len|left-u| (choice-ll v>u) = v>u
    ... | len-> len|left-v|>len|left-u|                 = Nullary.contradiction len|left-v|>len|left-u|  (<-irrefl (sym len|left-v|≣len|left-u|))
        where
          len|left-v|≣len|left-u| : length (proj₁ (flat {l} v)) ≡ length (proj₁ (flat {l} u))
          len|left-v|≣len|left-u| rewrite  |v|≡|u| = refl 
    |v|,l⇒v : proj₁ (flat {l} v) , l ⇒ v
    |v|,l⇒v = >-max→⇒  {l} {v} ∀u→|v|≡|u|→v>u

>-max→⇒ {l + r ` loc} {RightU v}     max-ev = p+r |v|,r⇒v ¬|v|∈⟦l⟧ 
  where
    ∀u→|v|≡|u|→v>u : ( u : U r ) →  proj₁ (flat {r} v) ≡ proj₁ (flat {r} u)  → r ⊢ v > u
    ∀u→|v|≡|u|→v>u u |v|≡|u| with max-ev (RightU u) |v|≡|u|
    ... | len-≡ len|right-v|≡len|right-u| (choice-rr v>u) = v>u
    ... | len-> len|right-v|>len|right-u|                 =  Nullary.contradiction len|right-v|>len|right-u|  (<-irrefl (sym len|right-v|≣len|right-u|)) 
        where
          len|right-v|≣len|right-u| : length (proj₁ (flat {r} v)) ≡ length (proj₁ (flat {r} u))
          len|right-v|≣len|right-u| rewrite  |v|≡|u| = refl 
    
  
    |v|,r⇒v : proj₁ (flat {r} v) , r ⇒ v
    |v|,r⇒v = >-max→⇒  {r} {v} ∀u→|v|≡|u|→v>u 
    
    ¬|v|∈⟦l⟧ : ¬ proj₁ (flat {r} v) ∈⟦ l ⟧
    ¬|v|∈⟦l⟧ |v|∈⟦l⟧ with intersect-memberʳ {l} {r} {v} |v|∈⟦l⟧
    ... |  u , |u|∈⟦l⟧ , |v|≡|u| = >→¬< ( max-ev (LeftU {l} {r} {loc} u) |v|≡|u| ) left-u>right-v 
      where
        len|v|≡len|u| : length (proj₁ (flat {r} v)) ≡ length (proj₁ (flat {l} u))
        len|v|≡len|u| rewrite |v|≡|u| = refl 
        len|right-v|≡len|left-u| : length (proj₁ (flat {l + r ` loc} (RightU v))) ≡ length (proj₁ (flat {l + r ` loc} (LeftU u)))
        len|right-v|≡len|left-u| rewrite |v|≡|u| = refl 
        left-u>right-v : l + r ` loc ⊢ LeftU {l} {r} {loc} u > RightU {l} {r} {loc} v
        left-u>right-v = len-≡ ( sym len|right-v|≡len|left-u|) (choice-lr (≤-reflexive (len|right-v|≡len|left-u|)) )

>-max→⇒ {l ● r ` loc} {PairU v₁ v₂} max-ev  = ps {proj₁ (flat v₁)} {proj₁ (flat v₂)} {(proj₁ (flat v₁)) ++ (proj₁ (flat v₂))} {l} {r} {loc} {v₁} {v₂} refl |v₁|,l⇒v₁ |v₂|,r⇒v₂ longest-ev
  where
    ∀u₁→|v₁|≡|u₁|→v₁>u₁ : ( u₁ : U l ) → proj₁ (flat {l} v₁) ≡ proj₁ (flat {l} u₁)  → l ⊢ v₁ > u₁
    ∀u₁→|v₁|≡|u₁|→v₁>u₁ u₁ |v₁|≡|u₁| with max-ev (PairU u₁ v₂) (cong (λ x → x ++ (proj₁ (flat {r} v₂) )) |v₁|≡|u₁|)
    ... | len-> len|pair-v₁v₂|>len|pair-u₁v₂| =  Nullary.contradiction  len|v₁|>len|u₁| (<-irrefl (sym len|v₁|≡len|u₁|))
      -- len->  len|v₁|>len|u₁| -- why this also works? because eventually it leads to contradiciton? 
      where
        len|v₁|≡len|u₁| : length (proj₁ (flat v₁)) ≡ length (proj₁ (flat u₁))
        len|v₁|≡len|u₁| rewrite |v₁|≡|u₁| = refl 
        len|v₁|>len|u₁| : length (proj₁ (flat v₁)) > length (proj₁ (flat u₁))
        len|v₁|>len|u₁| = len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ { (proj₁ (flat v₁)) } { (proj₁ (flat u₁)) } {  (proj₁ (flat v₂))}  len|pair-v₁v₂|>len|pair-u₁v₂|
        
    ... | len-≡ len|pair-v₁v₂|≡len|pair-u₁v₂| (seq₂ v₁≡u₁ v₂>v₂ )  = Nullary.contradiction refl (>→¬≡ v₂>v₂ )
    ... | len-≡ len|pair-v₁v₂|≡len|pair-u₁v₂| (seq₁ v₁>u₁)  = v₁>u₁
    
    |v₁|,l⇒v₁ :  proj₁ (flat {l} v₁) , l ⇒ v₁
    |v₁|,l⇒v₁ =  >-max→⇒  {l} {v₁} ∀u₁→|v₁|≡|u₁|→v₁>u₁ 

    ∀u₂→|v₂|≡|u₂|→v₂>u₂ : ( u₂ : U r ) → proj₁ (flat {r} v₂) ≡ proj₁ (flat {r} u₂) → r ⊢ v₂ > u₂
    ∀u₂→|v₂|≡|u₂|→v₂>u₂ u₂ |v₂|≡|u₂|  with max-ev (PairU v₁ u₂) (cong (λ x → (proj₁ (flat {l} v₁) ++ x ) ) |v₂|≡|u₂| ) 
    ... | len-> len|pair-v₁v₂|>len|pair-v₁u₂| = Nullary.contradiction len|v₂|>len|u₂| (<-irrefl (sym (cong length  |v₂|≡|u₂| )))
      where

        len|pair-v₁u₂|≡len|v₁|+len|u₂| :  length (proj₁ (flat {l ● r ` loc} (PairU v₁ u₂))) ≡ length (proj₁ (flat {l} v₁)) + length (proj₁ (flat {r} u₂))
        len|pair-v₁u₂|≡len|v₁|+len|u₂| =  length-++ (proj₁ (flat {l} v₁)) 

        len|pair-v₁v₂|≡len|v₁|+len|v₂| :  length (proj₁ (flat {l ● r ` loc} (PairU v₁ v₂))) ≡ length (proj₁ (flat {l} v₁)) + length (proj₁ (flat {r} v₂))
        len|pair-v₁v₂|≡len|v₁|+len|v₂| =  length-++ (proj₁ (flat {l} v₁)) 


        len|v₂|>len|u₂| : length (proj₁ (flat v₂)) > length (proj₁ (flat u₂))
        len|v₂|>len|u₂| rewrite len|pair-v₁v₂|≡len|v₁|+len|v₂| | len|pair-v₁u₂|≡len|v₁|+len|u₂|  = +-cancelˡ-< (length (proj₁ (flat {l} v₁)))  (length (proj₁ (flat {r} u₂)))  (length (proj₁ (flat {r} v₂))) len|pair-v₁v₂|>len|pair-v₁u₂| 
    ... | len-≡ len|pair-v₁v₂|≡len|pair-v₁u₂| (seq₂ refl v₂>u₂)  = v₂>u₂ 
    ... | len-≡ len|pair-v₁v₂|≡len|pair-v₁u₂| (seq₁ v₁>v₁) =  Nullary.contradiction refl (>→¬≡ v₁>v₁ )

    |v₂|,r⇒v₂ :  proj₁ (flat {r} v₂) , r ⇒ v₂
    |v₂|,r⇒v₂ =  >-max→⇒  {r} {v₂} ∀u₂→|v₂|≡|u₂|→v₂>u₂

    longest-ev :  ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) ×
                      ( w₃ ++ w₄ ≡ proj₁ (flat v₂)) ×
                      ((proj₁ (flat {l} v₁) ++ w₃) ∈⟦ l ⟧) ×
                      (w₄ ∈⟦ r ⟧))
    longest-ev ( w₃ , w₄ , ¬w₃≡[] , w₃++w₄≡|v₂| , |v₁|++w₃∈⟦l⟧ , w₄∈⟦r⟧) = (>→¬<  pair-v₁v₂>pair-u₁u₂) pair-u₁u₂>pair-v₁v₂ 

      {-
      the gist of the contradiction 
       w₃++w₄≡|v₂| hence |v₁| ++ w₃ ++ w₄ ≡ |v₁| ++ |v₂|
       find u₁ u₂ such that |u₁| ≡ |v₁| ++ w₃ , since |v₁|++w₃∈⟦l⟧ ;
            |u₂| ≡ w₄.
            Hence 
       apply max-ev (PairU u₁ u₂)  (|u₁| ++ |u₂| ≡ |v₁| ++ |v₂|)
       we have (PairU v₁ v₂) > (PairU u₁ u₂)
       However, we can also show that (PairU u₁ u₂) > (PairU v₁ v₂) via seq₁ (len-> len-|u₁|>len-|v₁|) 
      -} 
      where
        u₁ : U l
        u₁ = unflat |v₁|++w₃∈⟦l⟧
        u₂ : U r
        u₂ = unflat w₄∈⟦r⟧
        |u₂|≡w₄ : proj₁ (flat {r} u₂) ≡ w₄
        |u₂|≡w₄ rewrite flat∘unflat {r} {w₄} w₄∈⟦r⟧ = refl
        |u₁|≡|v₁|++w₃ : proj₁ (flat {l} u₁) ≡ (proj₁ (flat {l} v₁)) ++ w₃
        |u₁|≡|v₁|++w₃ rewrite flat∘unflat {l} {(proj₁ (flat {l} v₁)) ++ w₃}  |v₁|++w₃∈⟦l⟧ = refl 
        |v₁|++|v₂|≡|u₁|++|u₂| : (proj₁ (flat v₁)) ++ (proj₁ (flat v₂)) ≡ (proj₁ (flat u₁)) ++ (proj₁ (flat u₂))
        |v₁|++|v₂|≡|u₁|++|u₂| =
          begin
            (proj₁ (flat v₁)) ++ (proj₁ (flat v₂))
          ≡⟨ cong ((proj₁ (flat v₁)) ++_ ) (sym w₃++w₄≡|v₂| ) ⟩
            (proj₁ (flat v₁)) ++ (w₃ ++ w₄)
          ≡⟨ sym (++-assoc (proj₁ (flat v₁)) w₃ w₄)  ⟩
            ((proj₁ (flat v₁)) ++ w₃ ) ++ w₄
          ≡⟨ cong ( _++ w₄ ) (sym |u₁|≡|v₁|++w₃)  ⟩ 
            (proj₁ (flat u₁)) ++ w₄ 
          ≡⟨ cong ((proj₁ (flat u₁)) ++_ ) (sym |u₂|≡w₄) ⟩ 
            (proj₁ (flat u₁)) ++ (proj₁ (flat u₂))
          ∎ 
        pair-v₁v₂>pair-u₁u₂ : l ● r ` loc ⊢ PairU v₁ v₂ > PairU u₁ u₂
        pair-v₁v₂>pair-u₁u₂ = max-ev (PairU u₁ u₂) |v₁|++|v₂|≡|u₁|++|u₂|

        pair-u₁u₂>pair-v₁v₂ : l ● r ` loc ⊢ PairU u₁ u₂ > PairU v₁ v₂
        pair-u₁u₂>pair-v₁v₂ = len-≡  len-|pair-u₁u₂|≡len-|pair-v₁v₂| (seq₁ (len-> len-|u₁|>len-|v₁| ))
          where
            len-|pair-u₁u₂|≡len-|pair-v₁v₂| : length (proj₁ (flat (PairU {l} {r} {loc} u₁ u₂))) ≡ length (proj₁ (flat (PairU {l} {r} {loc}  v₁ v₂)))
            len-|pair-u₁u₂|≡len-|pair-v₁v₂| rewrite (sym |v₁|++|v₂|≡|u₁|++|u₂|) = refl
            len-|u₁|>len-|v₁| : length (proj₁ (flat u₁)) > length (proj₁ (flat v₁))
            len-|u₁|>len-|v₁| rewrite |u₁|≡|v₁|++w₃ = ++-¬[]→> {Char} {proj₁ (flat v₁)} {w₃} ¬w₃≡[]


>-max→⇒ {r * ε∉r ` loc} {ListU []} max-ev = p[]
{-
  where
    ex : ∃[ u ] ( ParseTree.ParseTreeOf r u ) × ¬ ( proj₁ (flat {r} u)) ≡ []
    ex with ParseTree.r-∃u r
    ... | u , ParseTree.parseTreeOf .{r} .{u} = u , ( ParseTree.parseTreeOf {r} {u} , ¬|u|≡[])
      where
        ¬|u|≡[] : ¬ ( proj₁ (flat {r} u)) ≡ []
        ¬|u|≡[] |u|≡[] = ([]∈⟦r⟧→¬ε∉r []∈⟦r⟧) ε∉r
          where
            []∈⟦r⟧ : [] ∈⟦ r ⟧
            []∈⟦r⟧ rewrite (sym |u|≡[] ) =  proj₂ (flat {r} u)
-} 
    
>-max→⇒ {r * ε∉r ` loc} {ListU (v ∷ vs)} max-ev =
  p* {proj₁ (flat v)} {proj₁ (flat (ListU {r} {ε∉r} {loc} vs))} {proj₁ (flat v) ++ proj₁ (flat (ListU {r} {ε∉r} {loc} vs)) } refl |v|,r⇒v |list-vs|,r*⇒list-vs  ¬|v|≡[] longest-ev
  where
    ¬|v|≡[] : ¬ proj₁ (flat v) ≡ []
    ¬|v|≡[] |v|≡[] = ([]∈⟦r⟧→¬ε∉r []∈⟦r⟧) ε∉r 
      where
        []∈⟦r⟧ : [] ∈⟦ r ⟧
        []∈⟦r⟧ rewrite (sym |v|≡[] ) =  proj₂ (flat {r} v)


    ∀u→|v|≡|u|→v>u : ( u : U r ) → proj₁ (flat {r} v) ≡ proj₁ (flat {r} u)  → r ⊢ v > u
    ∀u→|v|≡|u|→v>u u |v|≡|u| with max-ev (ListU (u ∷ vs)) (cong (λ x → x ++ (proj₁ (flat {r * ε∉r ` loc } (ListU vs)))) |v|≡|u|)
    ... | len-> len|list-v∷vs|>len|list-u∷vs| = Nullary.contradiction len|list-v∷vs|>len|list-u∷vs| (<-irrefl (sym len|list-v∷vs|≡len|list-u∷vs|)) 
      where
        |list-v∷vs|≡|list-u∷vs| : (proj₁ (flat (ListU   {r} {ε∉r} {loc}  (v ∷ vs)))) ≡ (proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ vs))))
        |list-v∷vs|≡|list-u∷vs| rewrite  |v|≡|u| = refl 

        len|list-v∷vs|≡len|list-u∷vs| : length (proj₁ (flat (ListU   {r} {ε∉r} {loc}  (v ∷ vs)))) ≡ length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ vs))))
        len|list-v∷vs|≡len|list-u∷vs| rewrite |list-v∷vs|≡|list-u∷vs|  = refl
    ... | len-≡ len|list-v∷vs|≡len|list-u∷vs| (star-tail v≡u vs>vs) =  Nullary.contradiction refl (>→¬≡ vs>vs )
    ... | len-≡ len|list-v∷vs|≡len|list-u∷vs| (star-head v>u) = v>u

    |v|,r⇒v : proj₁ (flat {r} v) , r ⇒ v
    |v|,r⇒v =  >-max→⇒  {r} {v} ∀u→|v|≡|u|→v>u 


    ∀list-us→|list-vs|≡|list-us|→list-vs>list-us : ( list-us : U ( r * ε∉r ` loc ) )
      → proj₁ (flat {r * ε∉r ` loc} (ListU vs) ) ≡ proj₁ (flat {r * ε∉r ` loc} list-us)
      → (r * ε∉r ` loc) ⊢ (ListU vs) > list-us
    ∀list-us→|list-vs|≡|list-us|→list-vs>list-us (ListU us) |list-vs|≡|list-us| with max-ev (ListU (v ∷ us)) (cong (λ x → (proj₁ (flat {r} v)) ++ x ) |list-vs|≡|list-us|)
    ... | len-> len|list-v∷vs|>len|list-v∷us| = Nullary.contradiction len|list-v∷vs|>len|list-v∷us| (<-irrefl (sym len|list-v∷vs|≡len|list-v∷us|)) 
      where
        |list-v∷vs|≡|list-v∷us| : (proj₁ (flat (ListU   {r} {ε∉r} {loc}  (v ∷ vs)))) ≡ (proj₁ (flat (ListU  {r} {ε∉r} {loc} (v ∷ us))))
        |list-v∷vs|≡|list-v∷us| rewrite  |list-vs|≡|list-us| = refl
        
        len|list-v∷vs|≡len|list-v∷us| : length (proj₁ (flat (ListU   {r} {ε∉r} {loc}  (v ∷ vs)))) ≡ length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (v ∷ us))))
        len|list-v∷vs|≡len|list-v∷us| rewrite  |list-v∷vs|≡|list-v∷us| = refl
    ... | len-≡ len|list-v∷vs|≡len|list-v∷us| (star-head v>v) = Nullary.contradiction refl (>→¬≡ v>v)
    ... | len-≡ len|list-v∷vs|≡len|list-v∷us| (star-tail v≡v list-vs>list-us) = list-vs>list-us


    |list-vs|,r*⇒list-vs : proj₁ (flat {r * ε∉r ` loc} (ListU vs)) , (r * ε∉r ` loc) ⇒ (ListU {r} {ε∉r} {loc} vs)
    |list-vs|,r*⇒list-vs =  >-max→⇒  {r * ε∉r ` loc} {ListU vs} ∀list-us→|list-vs|≡|list-us|→list-vs>list-us

    longest-ev : ¬ ( ∃[ w₃ ] ∃[ w₄ ] ( ¬ w₃ ≡ [] ) ×
                     ( w₃ ++ w₄ ≡ proj₁ (flat (ListU  {r} {ε∉r} {loc} vs)) ) ×
                     ( ((proj₁ (flat {r} v)) ++ w₃) ∈⟦ r ⟧ ) ×
                     ( w₄ ∈⟦  r * ε∉r ` loc ⟧ ) )
    longest-ev ( w₃ , w₄ , ¬w₃≡[] , w₃++w₄≡|list-vs| , |v|++w₃∈⟦r⟧ , w₄∈⟦r*⟧ ) = (>→¬<  list-v∷vs>list-u∷us )  list-u∷us>list-v∷vs
      where
        u : U r
        u = unflat |v|++w₃∈⟦r⟧

        list-us : U ( r * ε∉r ` loc )
        list-us = unflat  w₄∈⟦r*⟧

        |list-us|≡w₄ : proj₁ (flat {r * ε∉r ` loc} list-us ) ≡ w₄
        |list-us|≡w₄ rewrite flat∘unflat {r * ε∉r ` loc} {w₄}  w₄∈⟦r*⟧ = refl

        |u|≡|v|++w₃ : proj₁ (flat {r} u) ≡ (proj₁ (flat {r} v)) ++ w₃
        |u|≡|v|++w₃ rewrite flat∘unflat {r} {(proj₁ (flat {r} v)) ++ w₃}  |v|++w₃∈⟦r⟧ = refl

        |v|++|list-vs|≡|u|++|list-us| : (proj₁ (flat v)) ++ (proj₁ (flat (ListU vs))) ≡ (proj₁ (flat u)) ++ (proj₁ (flat list-us))
        |v|++|list-vs|≡|u|++|list-us| =
          begin
            (proj₁ (flat v)) ++ (proj₁ (flat (ListU vs)))
          ≡⟨  cong ((proj₁ (flat v)) ++_ ) (sym w₃++w₄≡|list-vs| ) ⟩
            (proj₁ (flat v)) ++ (w₃ ++ w₄)
          ≡⟨ sym (++-assoc (proj₁ (flat v)) w₃ w₄)  ⟩
            ((proj₁ (flat v)) ++ w₃) ++ w₄
          ≡⟨ cong ( _++ w₄ ) (sym |u|≡|v|++w₃)  ⟩
            (proj₁ (flat u)) ++ w₄
          ≡⟨ cong ((proj₁ (flat u)) ++_ ) (sym |list-us|≡w₄) ⟩ 
            (proj₁ (flat u)) ++ (proj₁ (flat list-us))
          ∎

        |list-v∷vs|≡|list-u∷us| : proj₁ (flat (ListU  {r} {ε∉r} {loc} (v ∷ vs))) ≡ proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ (unListU list-us))))
        |list-v∷vs|≡|list-u∷us| rewrite  |v|++|list-vs|≡|u|++|list-us| |  sym (listU∘unListU {r} {ε∉r} {loc} {unflat w₄∈⟦r*⟧})  = refl 
        list-v∷vs>list-u∷us : r * ε∉r ` loc ⊢ ListU  {r} {ε∉r} {loc} ( v ∷ vs) > ListU  {r} {ε∉r} {loc} (u ∷ (unListU list-us))
        list-v∷vs>list-u∷us = max-ev (ListU (u ∷ (unListU list-us)) ) |list-v∷vs|≡|list-u∷us|

        list-u∷us>list-v∷vs : r * ε∉r ` loc ⊢ ListU  {r} {ε∉r} {loc} ( u ∷ (unListU list-us)) > ListU  {r} {ε∉r} {loc} (v ∷ vs)
        list-u∷us>list-v∷vs = len-≡ (sym len-|list-v∷vs|≡len-|list-u∷us|) (star-head (len-> len-|u|>len-|v|) )
          where
            len-|list-v∷vs|≡len-|list-u∷us| : length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (v ∷ vs)))) ≡ length (proj₁ (flat (ListU  {r} {ε∉r} {loc} (u ∷ (unListU list-us)))))
            len-|list-v∷vs|≡len-|list-u∷us| rewrite (sym |list-v∷vs|≡|list-u∷us|)   = refl 
            len-|u|>len-|v| :  length (proj₁ (flat u)) > length (proj₁ (flat v))
            len-|u|>len-|v| rewrite |u|≡|v|++w₃ = ++-¬[]→> {Char} {proj₁ (flat v)} {w₃}  ¬w₃≡[]           
```
