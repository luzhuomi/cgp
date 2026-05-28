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
open import Data.Nat using (_<_ ; _≤_ ; zero ; suc ; _+_ ; _∸_ ; s<s)
open import Data.Empty using (⊥ ; ⊥-elim)
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; <-cmp ; +-suc ; +-identityʳ )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ;
  length-++ ; ++-assoc ; ∷-injective
  -- ; length-++-sucʳ -- this is only available after v2.3
  )

open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst; inspect)
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

open import Relation.Binary.Definitions using (Tri ; tri< ; tri≈ ; tri>)

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




Okui and Suzuki's POSIX order


pos extracts the set of positions in a parse tree. 

```agda

mutual
  pos : ∀ { r : RE } → U r → List (List ℕ)
  pos {ε} EmptyU = [] ∷ []
  pos {$ c ` loc} (LetterU .c) = [] ∷ []
  pos {l + r ` loc} (LeftU u) = [] ∷ (List.map (λ ps → 0 ∷ ps ) (pos u))
  pos {l + r ` loc} (RightU u) = [] ∷ (List.map (λ ps → 1 ∷ ps ) (pos u))
  pos {l ● r ` loc} (PairU u v) = [] ∷ (List.map (λ ps → 0 ∷ ps ) (pos u)) ++ (List.map (λ ps → 1 ∷ ps ) (pos v))
  pos {r * ε∉r ` loc } (ListU vs) = [] ∷ (go-pos 0 vs)

  go-pos : ∀ { r : RE } → ℕ → List (U r) → List (List ℕ)
  go-pos id [] = []
  go-pos id (u ∷ us) = (List.map (λ ps → id ∷ ps ) (pos u)) ++ go-pos (suc id) us

```

```agda
-- test_e : U ( ($  *
a*+a*●a* : RE
a*+a*●a* = ( ( ( $ 'a' ` 1 ) * ε∉$ ` 2 ) + ( ( $ 'a' ` 3 ) * ε∉$ ` 4) ` 5 ) ● ( ( $ 'a' ` 6 ) * ε∉$ ` 7 ) ` 8
a*+a*●a*●a* : RE
a*+a*●a*●a* = a*+a*●a* ● ( ( $ 'a' ` 10 ) * ε∉$ ` 11 ) ` 12

test_e : U a*+a*●a*●a*
test_e = PairU (PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ LetterU 'a' ∷  [])))       (ListU []))    (ListU [])  
test_pos : List (List ℕ )
test_pos = pos test_e 
```

```agda
subre : RE → List ℕ → Maybe RE
subre r           [] = just r
subre (l + r ` loc) (0 ∷ xs) = subre l xs
subre (l + r ` loc) (1 ∷ xs) = subre r xs
subre (l + r ` loc) (_ ∷ xs) = nothing
subre (l ● r ` loc) (0 ∷ xs) = subre l xs
subre (l ● r ` loc) (1 ∷ xs) = subre r xs
subre (l ● r ` loc) (_ ∷ xs) = nothing 
subre (r * ε∉r ` loc) (n ∷ xs) = subre r xs
subre ε           (_ ∷ _) = nothing
subre ($ c ` loc) (_ ∷ _) = nothing

```

Defining a function with a  maybe return type is a bit tricky

shall we consider a relation?

```agda

data IsSubAt : RE → List ℕ → RE → Set where
  sub-ε : IsSubAt ε [] ε 
  sub-$ : { c : Char } { loc : ℕ } → IsSubAt ($ c ` loc) [] ($ c ` loc)
  sub-● : { l r : RE } { loc : ℕ }
    → IsSubAt (l ● r ` loc) [] (l ● r ` loc)
  sub-●-0 : { l r s : RE } { loc : ℕ }
    { xs : List ℕ }
    → IsSubAt l xs s
    --------------------
    → IsSubAt (l ● r ` loc) (0 ∷ xs) s 
  sub-●-1 : { l r s : RE } { loc : ℕ }
    { xs : List ℕ }
    → IsSubAt r xs s
    --------------------
    → IsSubAt (l ● r ` loc) (1 ∷ xs) s 
  sub-+ : { l r : RE } { loc : ℕ }
    → IsSubAt (l + r ` loc) [] (l + r ` loc)
  sub-+-0 : { l r s : RE } { loc : ℕ }
    { xs : List ℕ }
    → IsSubAt l xs s
    --------------------
    → IsSubAt (l + r ` loc) (0 ∷ xs) s 
  sub-+-1 : { l r s : RE } { loc : ℕ }
    { xs : List ℕ }
    → IsSubAt r xs s
    --------------------
    → IsSubAt (l + r ` loc) (1 ∷ xs) s 
  sub-* : { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → IsSubAt (r * ε∉r ` loc) [] (r * ε∉r ` loc)
  sub-*-n : { r s : RE } { ε∉r : ε∉ r } { loc : ℕ }
    { n : ℕ } 
    { xs : List ℕ }
    → IsSubAt r xs s
    --------------------
    → IsSubAt (r * ε∉r  ` loc) (n ∷ xs) s 

```



subval takes a parse tree and a position, extracts the sub parse tree 

v ↓ []              = v

LeftU v ↓ 0∷ps      = v ↓ ps

RightU v ↓ 1∷ps     = v ↓ ps

PairU v₁ v₂ ↓ 0∷ps  = v₁ ↓ ps

PairU v₁ v₂ ↓ 1∷ps  = v₂ ↓ ps

ListU vs ↓ n∷ps     = vs[n] ↓ ps  
```agda

drop : ∀ {A : Set} → ℕ → List A → List A
drop zero xs = xs
drop (suc n) [] = []
drop (suc n) (_ ∷ xs) = drop n xs

{-# TERMINATING #-}
subval : ∀ {r s : RE } → (pos : List ℕ) → (IsSubAt r pos s)  → U r → U s
subval {ε} {ε} [] sub-ε u = u
subval {$ c ` loc} {$ c ` loc} [] sub-$ u = u
subval {l ● r ` loc} {l ● r ` loc} [] sub-● u = u
subval {l ● r ` loc} {s} (0 ∷ xs) (sub-●-0 p) (PairU u _) = subval xs p u
subval {l ● r ` loc} {s} (1 ∷ xs) (sub-●-1 p) (PairU _ v) = subval xs p v
subval {l + r ` loc} {l + r ` loc} [] sub-+ u = u
subval {l + r ` loc} {s} (0 ∷ xs) (sub-+-0 p) (LeftU u) = subval xs p u
subval {l + r ` loc} {s} (0 ∷ xs) (sub-+-0 p) (RightU v) = subval (0 ∷ xs) (sub-+-0 p) (RightU {l} {r} {loc} v) 
subval {l + r ` loc} {s} (1 ∷ xs) (sub-+-1 p) (RightU u) = subval xs p u
subval {l + r ` loc} {s} (1 ∷ xs) (sub-+-1 p) (LeftU v) = subval (1 ∷ xs) (sub-+-1 p) (LeftU {l} {r} {loc} v)
subval {r * ε∉r ` loc} {r * ε∉r ` loc} [] sub-* u = u
subval {r * ε∉r ` loc} {s} (n ∷ xs) (sub-*-n p) (ListU us) with drop n us
subval {r * ε∉r ` loc} {s} (n ∷ xs) (sub-*-n p) (ListU us) | x ∷ _ = subval xs p x
subval {r * ε∉r ` loc} {s} (n ∷ xs) (sub-*-n p) (ListU us) | [] = subval (n ∷ xs) (sub-*-n p) (ListU {r} {ε∉r} {loc} us)

subval-maybe : ∀ {r s : RE } → (pos : List ℕ) → (IsSubAt r pos s)  → U r → Maybe (U s)
subval-maybe {ε} {ε} [] sub-ε u = just u
subval-maybe {$ c ` loc} {$ c ` loc} [] sub-$ u = just u
subval-maybe {l ● r ` loc} {l ● r ` loc} [] sub-● u = just u
subval-maybe {l ● r ` loc} {s} (0 ∷ xs) (sub-●-0 p) (PairU u _) = subval-maybe xs p u
subval-maybe {l ● r ` loc} {s} (1 ∷ xs) (sub-●-1 p) (PairU _ v) = subval-maybe xs p v
subval-maybe {l + r ` loc} {l + r ` loc} [] sub-+ u = just u
subval-maybe {l + r ` loc} {s} (0 ∷ xs) (sub-+-0 p) (LeftU u) = subval-maybe xs p u
subval-maybe {l + r ` loc} {s} (0 ∷ xs) (sub-+-0 p) (RightU {l} {r} {loc} _) = nothing
subval-maybe {l + r ` loc} {s} (1 ∷ xs) (sub-+-1 p) (RightU u) = subval-maybe xs p u
subval-maybe {l + r ` loc} {s} (1 ∷ xs) (sub-+-1 p) (LeftU {l} {r} {loc} _) = nothing
subval-maybe {r * ε∉r ` loc} {r * ε∉r ` loc} [] sub-* u = just u
subval-maybe {r * ε∉r ` loc} {s} (n ∷ xs) (sub-*-n p) (ListU us) with drop n us
subval-maybe {r * ε∉r ` loc} {s} (n ∷ xs) (sub-*-n p) (ListU us) | x ∷ _ = subval-maybe xs p x
subval-maybe {r * ε∉r ` loc} {s} (n ∷ xs) (sub-*-n p) (ListU {r} {ε∉r} {loc} us) | [] = nothing

```

Definition:

length (norm) of value v at position p.

The original definition 
∥ v ∥p = if p ∈ pos v then length |v ↓ p |  else -1


We want to avoid using negative value -1, hence adjust the aboe  definition 

Let
v : U r 

∥ v ∥p = just (length |v ↓ p |)  if subre r p == just s
∥ v ∥p = nothing otherwise 


```agda
sublen : ∀ {r : RE } → U r → List ℕ → Maybe ℕ
sublen {ε} EmptyU [] = just 0
sublen {ε} EmptyU (_ ∷ _) = nothing
sublen {$ c ` loc} (LetterU .c) [] = just 1
sublen {$ c ` loc} (LetterU .c) (_ ∷ _) = nothing
sublen {l ● r ` loc} (PairU u v) [] with length (proj₁ (flat (PairU {l} {r} {loc} u v)))
... | n = just n
sublen {l ● r ` loc} (PairU u _) (0 ∷ xs) = sublen u xs
sublen {l ● r ` loc} (PairU _ v) (1 ∷ xs) = sublen v xs
sublen {l ● r ` loc} (PairU _ _) (suc (suc _) ∷ _) = nothing
sublen {l + r ` loc} (LeftU u) [] with length (proj₁ (flat (LeftU {l} {r} {loc} u)))
... | n = just n
sublen {l + r ` loc} (RightU u) [] with length (proj₁ (flat (RightU {l} {r} {loc} u)))
... | n = just n
sublen {l + r ` loc} (LeftU u) (0 ∷ xs) = sublen u xs
sublen {l + r ` loc} (RightU u) (1 ∷ xs) = sublen u xs
sublen {l + r ` loc} (LeftU _) (1 ∷ _) = nothing
sublen {l + r ` loc} (RightU _) (0 ∷ _) = nothing
sublen {l + r ` loc} (LeftU _) (suc (suc _) ∷ _) = nothing
sublen {l + r ` loc} (RightU _) (suc (suc _) ∷ _) = nothing
sublen {r * ε∉r ` loc} (ListU us) [] with length (proj₁ (flat (ListU {r} {ε∉r} {loc} us)))
... | n = just n
sublen {r * ε∉r ` loc} (ListU us) (n ∷ xs) with drop n us
sublen {r * ε∉r ` loc} (ListU us) (n ∷ xs) | x ∷ _ = sublen x xs
sublen {r * ε∉r ` loc} (ListU us) (n ∷ xs) | [] = nothing

```






Definition:

lexical ordering among positions



--------------- 
[] ≺lex p ∷ ps


p₁ < p₂
----------------------
p₁ ∷ ps₁ ≺lex p₂ ∷ ps₂



ps₁ ≺lex ps₂
----------------------
p ∷ ps₁ ≺lex p ∷ ps₂



```agda

infix 4 _≺Lex_

data _≺Lex_ :  List ℕ  →  List ℕ → Set where
  ≺lex-[] : { p : ℕ } { ps : List ℕ }
    → [] ≺Lex  (p ∷ ps)
  ≺lex-head : { p₁ p₂ : ℕ } { ps₁ ps₂ : List ℕ }
    → p₁ Nat.< p₂
    → p₁ ∷ ps₁ ≺Lex p₂ ∷ ps₂
  ≺lex-tail : { p : ℕ } { ps₁ ps₂ : List ℕ }
    → ps₁ ≺Lex ps₂
    → p ∷ ps₁ ≺Lex p ∷ ps₂


```




Definition: 
a value v₁ is smaller at position p than v₂


v₁ ≺p v₂ iff
i) ∥ v₂ ∥p < ∥ v₁ ∥p and 
ii) ∀ q ∈ Pos v₁ ∪ Pos v₂. q ≺lex p implies ∥ v1 ∥ q = ∥ v2 ∥ q


```agda

data MaybeNat< : Maybe ℕ → Maybe ℕ   → Set where
  maybenat-nothing-just : ∀ {  y : ℕ }
    --------------------------------
    → MaybeNat< nothing (just y)
    
  maybenat-just-just : ∀ { x y  : ℕ  }
    → x Nat.< y
    --------------------------------
    → MaybeNat< (just x) (just y)

data SubLen< : { r : RE } → List ℕ → U r → U r → Set  where
  sublen< : ∀ { r : RE } ( u v : U r )
    → ( pos : List ℕ )
    →  MaybeNat< (sublen u pos) (sublen v pos)
    → SubLen< pos u v

infix 4  _,_⊢_≺_


data _,_⊢_≺_ : ( r : RE ) → (List ℕ) → U r → U r → Set where
  ≺p : ∀ { r : RE } ( u v : U r )
    → ( p : List ℕ )
    → SubLen< {r} p u v
    → ( ( q : List ℕ )
      → q ∈ (pos {r} u) ++ (pos {r} v)
      → q ≺Lex p
      → sublen u q ≡ sublen v q
      )
    → r , p ⊢ u ≺ v 



infix 4  _⊢_≺_

data _⊢_≺_ : ( r : RE ) →  U r → U r → Set where
  ≺ : ∀ { r : RE } ( u v : U r )
    → ∃[ p ] ( r , p ⊢ u ≺ v )
    →  _⊢_≺_ r u v

-- type alias 

_⊢_≼_ : ( r : RE ) →  U r → U r → Set
_⊢_≼_ r u v = (_⊢_≺_ r u v) ⊎ (u ≡ v )

```


Lemma:  _≺Lex_ is total

```agda
≺Lex-cong-∷ : ∀ {m n : ℕ} {ms ns : List ℕ}
  → m ≡ n
  → ms ≺Lex ns ⊎ ns ≺Lex ms ⊎ ms ≡ ns
  → m ∷ ms ≺Lex n ∷ ns ⊎ n ∷ ns ≺Lex m ∷ ms ⊎ m ∷ ms ≡ n ∷ ns
≺Lex-cong-∷ refl (inj₁ p<q)     = inj₁ (≺lex-tail p<q)
≺Lex-cong-∷ refl (inj₂ (inj₁ q<p)) = inj₂ (inj₁ (≺lex-tail q<p))
≺Lex-cong-∷ refl (inj₂ (inj₂ refl)) = inj₂ (inj₂ refl)

≺Lex-trichotomous : ∀ ( p q : List ℕ )
  → p ≺Lex q ⊎ q ≺Lex p ⊎ p ≡ q
≺Lex-trichotomous []          []          = inj₂ (inj₂ refl)
≺Lex-trichotomous []          (_ ∷ _)     = inj₁ ≺lex-[]
≺Lex-trichotomous (_ ∷ _)     []          = inj₂ (inj₁ ≺lex-[])
≺Lex-trichotomous (m ∷ ms)    (n ∷ ns)    with <-cmp m n | ≺Lex-trichotomous ms ns
... | tri< m<n _ _ | _ = inj₁ (≺lex-head m<n)
... | tri> _ _ n<m | _ = inj₂ (inj₁ (≺lex-head n<m))
... | tri≈ _ m≡n _ | tri = ≺Lex-cong-∷ m≡n tri

```



Lemma:  _≺Lex_ is transitive

```agda


≺Lex-trans : ∀ (p q r : List ℕ) → p ≺Lex q → q ≺Lex r → p ≺Lex r
≺Lex-trans [] q (rh ∷ rt) ≺lex-[] (≺lex-head qr′) = ≺lex-[]
≺Lex-trans [] (qh ∷ qt) (qh ∷ rt) ≺lex-[] (≺lex-tail qr′) = ≺lex-[]
≺Lex-trans (ph ∷ pt) (qh ∷ qt) (rh ∷ rt) (≺lex-head pq′) (≺lex-head qr′) = ≺lex-head (<-trans pq′ qr′)
≺Lex-trans (ph ∷ pt) (qh ∷ qt) (rh ∷ rt) (≺lex-head pq′) (≺lex-tail qr′) = ≺lex-head pq′
≺Lex-trans (ph ∷ pt) (qh ∷ qt) (rh ∷ rt) (≺lex-tail pq′) (≺lex-head qr′) = ≺lex-head qr′
≺Lex-trans (ph ∷ pt) (qh ∷ qt) (rh ∷ rt) (≺lex-tail pq′) (≺lex-tail qr′) = ≺lex-tail (≺Lex-trans pt qt rt pq′ qr′)

```


Lemma: transitivity of  _⊢_≺_


Proof sketch as follows
 From the assumption we obtain two positions p and q, where the values v₁ and v₂
(respectively v₂ and v₃) are ‘distinct’. Since _≺Lex_ is trichotomous, we need to consider
three cases, namely p = q, p ≺Lex q and q ≺Lex p. Let us look at the first case. Clearly
∥ v₂ ∥ p < ∥ v₁ ∥ p (note that ∥ v₂ ∥ p is the SubLen operation) and ∥ v₃ ∥ p < ∥ v₂ ∥ p imply ∥ v₃ ∥ p < ∥ v₁ ∥ p.
It remains to show that for a
p' ∈ Pos v1 ∪ Pos v3 with p' ≺lex p that ∥ v₁ ∥ p' = ∥ v₃ ∥ p'  holds. Suppose p' ∈ Pos v₁1, then
we can infer from the first assumption that ∥ v₁ ∥ p' = ∥ v₂ ∥ p'. But this means that p'
must be in Pos v₂ too (the sublen cannot be nothing ) given p' ∈ Pos v₁).
Hence we can use the second assumption and infer ∥ v₂ ∥ p' = ∥ v₃ ∥ p', which concludes this case with v₁ ≺ v₃. The reasoning in the
other cases is similar.

```agda

-- Transitivity of the MaybeNat< ordering.
-- Used in ≺-trans (p≡q case) to compose sublen inequalities.
≺Nat<-trans : ∀ { x y z : Maybe ℕ }
  → MaybeNat< x y
  → MaybeNat< y z
  → MaybeNat< x z
≺Nat<-trans maybenat-nothing-just (maybenat-just-just _) = maybenat-nothing-just
≺Nat<-trans (maybenat-just-just x<y) (maybenat-just-just y<z) = maybenat-just-just (<-trans x<y y<z)

-- just x is never equal to nothing. Used in MaybeNat< case analysis.
¬just≡nothing : ∀ {x : ℕ} → ¬ just x ≡ nothing
¬just≡nothing {x} ()

-- nothing is never equal to just x. Used in MaybeNat< case analysis.
¬nothing≡just : ∀ {x : ℕ} → ¬ nothing ≡ just x
¬nothing≡just {x} ()

-- Map membership: if xs ∈ ys, then n ∷ xs ∈ map (n ∷_) ys.
-- Used in sublen-just-∈-pos to lift inner positions to mapped lists.
map-member : ∀ {n : ℕ} {xs : List ℕ} (ys : List (List ℕ)) → xs ∈ ys → (n ∷ xs) ∈ List.map (n ∷_) ys
map-member [] ()
map-member (y ∷ ys) (here refl) = here refl
map-member (y ∷ ys) (there x∈) = there (map-member ys x∈)

-- Convert a proof that sublen returns just to a membership proof in pos.
-- Used throughout ≺-trans to bridge between sublen equality and position membership.
sublen-just-∈-pos : ∀ { r : RE } { u : U r } { q : List ℕ }
  → ∃[ n ] sublen u q ≡ just n
  → q ∈ pos u
sublen-just-∈-pos {ε} {EmptyU} {[]} pr = here refl
sublen-just-∈-pos {$ c ` loc} {LetterU _} {[]} pr = here refl
sublen-just-∈-pos {l ● r ` loc} {PairU _ _} {[]} pr = here refl
sublen-just-∈-pos {l ● r ` loc} {PairU u v} {0 ∷ xs} pr =
  there (∈-++⁺ˡ (map-member (pos u) (sublen-just-∈-pos {l} {u} {xs} pr)))
sublen-just-∈-pos {l ● r ` loc} {PairU u v} {1 ∷ xs} pr =
  there (∈-++⁺ʳ _ (map-member (pos v) (sublen-just-∈-pos {r} {v} {xs} pr)))
sublen-just-∈-pos {l ● r ` loc} {PairU u v} {suc (suc x) ∷ xs} pr =
  ⊥-elim (¬just≡nothing (sym (proj₂ pr)))
sublen-just-∈-pos {l + r ` loc} {LeftU u} {[]} pr = here refl
sublen-just-∈-pos {l + r ` loc} {LeftU u} {0 ∷ xs} pr =
  there (map-member (pos u) (sublen-just-∈-pos {l} {u} {xs} pr))
sublen-just-∈-pos {l + r ` loc} {LeftU u} {1 ∷ xs} pr =
  ⊥-elim (¬just≡nothing (sym (proj₂ pr)))
sublen-just-∈-pos {l + r ` loc} {LeftU u} {suc (suc x) ∷ xs} pr =
  ⊥-elim (¬just≡nothing (sym (proj₂ pr)))
sublen-just-∈-pos {l + r ` loc} {RightU u} {[]} pr = here refl
sublen-just-∈-pos {l + r ` loc} {RightU u} {1 ∷ xs} pr =
  there (map-member (pos u) (sublen-just-∈-pos {r} {u} {xs} pr))
sublen-just-∈-pos {l + r ` loc} {RightU u} {0 ∷ xs} pr =
  ⊥-elim (¬just≡nothing (sym (proj₂ pr)))
sublen-just-∈-pos {l + r ` loc} {RightU u} {suc (suc x) ∷ xs} pr =
  ⊥-elim (¬just≡nothing (sym (proj₂ pr)))
sublen-just-∈-pos {sr * se ` loc} {ListU us} {[]} pr = here refl
sublen-just-∈-pos {sr * se ` loc} {ListU us} {n ∷ xs} pr = there (go 0 n us pr)
  where
    go : ∀ k n (us : List (U sr)) → ∃[ m ] sublen (ListU {sr} {se} {loc} us) (n ∷ xs) ≡ just m → (k + n) ∷ xs ∈ go-pos k us
    go k zero (y ∷ us) pr =
      subst (λ m → m ∷ xs ∈ go-pos k (y ∷ us)) (sym (+-identityʳ k))
        (∈-++⁺ˡ (map-member (pos y) (sublen-just-∈-pos {sr} {y} {xs} pr)))
    go k (suc n) (w ∷ us) pr =
      subst (λ m → m ∷ xs ∈ go-pos k (w ∷ us)) (sym (+-suc k n))
        (∈-++⁺ʳ _ (go (suc k) n us pr))
    go k (suc n) [] pr = ⊥-elim (¬just≡nothing (sym (proj₂ pr)))

-- Invert membership in a mapped list: if n∷xs is in map (n∷_) ys, then xs is in ys.
-- Used in sublen-∈-just to strip the prefix from position paths.
map-inv : ∀ { n : ℕ } { xs : List ℕ } ( ys : List (List ℕ) ) → (n ∷ xs) ∈ List.map (n ∷_) ys → xs ∈ ys
map-inv (y ∷ ys') (here p) rewrite proj₂ (∷-injective p) = here refl
map-inv (y ∷ ys') (there x∈xs) = there (map-inv ys' x∈xs)

-- Extract prefix equality from mapped list membership.
-- If suc n ∷ xs' is in map (_∷_ k) ys, then suc n ≡ k.
-- Used in sublen-∈-just to eliminate impossible prefix mismatches.
map-prefix≡ : ∀ {k n : ℕ} {xs' : List ℕ} {ys : List (List ℕ)} → (suc n ∷ xs') ∈ List.map (_∷_ k) ys → suc n ≡ k
map-prefix≡ {ys = _ ∷ _} (here p) = proj₁ (∷-injective p)
map-prefix≡ {ys = _ ∷ _} (there y∈ys) = map-prefix≡ y∈ys
map-prefix≡ {ys = []} ()

-- Shift mapped list indices: if suc n ∷ xs ∈ map (suc k ∷_) qs, then n ∷ xs ∈ map (k ∷_) qs.
go-pos-shift-map : (k n : ℕ) (xs : List ℕ) (qs : List (List ℕ)) → (suc n ∷ xs) ∈ List.map (suc k ∷_) qs → (n ∷ xs) ∈ List.map (k ∷_) qs
go-pos-shift-map k n xs [] ()
go-pos-shift-map k n xs (q ∷ qs) (here p) =
  subst (λ n' → n' ∷ xs ∈ List.map (k ∷_) (q ∷ qs)) (sym (suc-injective (proj₁ (∷-injective p)))) (subst (λ xs' → k ∷ xs' ∈ List.map (k ∷_) (q ∷ qs)) (sym (proj₂ (∷-injective p))) (here refl))
go-pos-shift-map k n xs (q ∷ qs) (there y∈) = there (go-pos-shift-map k n xs qs y∈)

-- Shift go-pos indices: membership in go-pos (suc k) implies membership in go-pos k
-- after decrementing the path prefix. Used in sublen-∈-just for ListU positions.
go-pos-shift : ∀ { r : RE } (k : ℕ) (vs : List (U r)) { n : ℕ } { xs : List ℕ }
  → (suc n ∷ xs) ∈ go-pos (suc k) vs
  → (n ∷ xs) ∈ go-pos k vs
go-pos-shift k [] ()
go-pos-shift {r} k (v ∷ vs) {n} {xs} y∈ = helper y∈
  where
    helper : (suc n ∷ xs) ∈ go-pos (suc k) (v ∷ vs) → (n ∷ xs) ∈ go-pos k (v ∷ vs)
    helper y∈ with ∈-++⁻ {v = suc n ∷ xs} (List.map (suc k ∷_) (pos v)) {ys = go-pos (suc (suc k)) vs} y∈
    ... | inj₁ y∈map = ∈-++⁺ˡ (go-pos-shift-map k n xs (pos v) y∈map)
    ... | inj₂ y∈tail = ∈-++⁺ʳ _ (go-pos-shift (suc k) vs y∈tail)

-- The empty list cannot be a member of a mapped list (all elements have prefix n).
-- Used in sublen-∈-just to eliminate impossible membership proofs.
¬[]∈map∷ : ∀ {n : ℕ} {ys : List (List ℕ)} → ¬ ([] ∈ List.map (n ∷_) ys)
¬[]∈map∷ {ys = []} ()
¬[]∈map∷ {ys = y ∷ ys} (here ())
¬[]∈map∷ {ys = y ∷ ys} (there x∈) = ¬[]∈map∷ x∈

-- Prefix mismatch implies non-membership: if m ≢ n, then m∷xs cannot be in map (n∷_) ys.
-- Used in sublen-∈-just to eliminate impossible prefix mismatches.
¬prefix∈map : ∀ {m n : ℕ} {xs : List ℕ} {ys : List (List ℕ)} → ¬ (m ≡ n) → ¬ (m ∷ xs ∈ List.map (n ∷_) ys)
¬prefix∈map {ys = []} m≢n ()
¬prefix∈map {ys = y ∷ ys} m≢n (here p) = m≢n (proj₁ (∷-injective p))
¬prefix∈map {ys = y ∷ ys} m≢n (there x∈) = ¬prefix∈map m≢n x∈

-- The empty list cannot be a member of go-pos (all elements have a numeric prefix).
-- Used in sublen-∈-just for ListU to eliminate impossible membership proofs.
¬[]∈go-pos : ∀ {r : RE} {n : ℕ} (us : List (U r)) → ¬ ([] ∈ go-pos n us)
¬[]∈go-pos [] ()
¬[]∈go-pos (u ∷ us) x∈ with ∈-++⁻ _ x∈
... | inj₁ x∈map = ¬[]∈map∷ x∈map
... | inj₂ x∈tail = ¬[]∈go-pos us x∈tail

-- 0 ∷ xs cannot be in go-pos (suc k) us (all elements have prefix ≥ suc k ≥ 1).
¬0∈go-pos-suc : ∀ {r : RE} (k : ℕ) (us : List (U r)) {xs : List ℕ} → ¬ (0 ∷ xs ∈ go-pos (suc k) us)
¬0∈go-pos-suc k [] ()
¬0∈go-pos-suc k (u ∷ us) x∈ with ∈-++⁻ _ x∈
... | inj₁ x∈map = ¬prefix∈map ¬0≡suc x∈map
  where ¬0≡suc : ¬ (0 ≡ suc k)
        ¬0≡suc ()
... | inj₂ x∈tail = ¬0∈go-pos-suc (suc k) us x∈tail

-- 0 is not equal to 1. Used in prefix mismatch eliminations.
¬0≡1 : ¬ (0 ≡ 1)
¬0≡1 ()

-- 1 is not equal to 0. Used in prefix mismatch eliminations.
¬1≡0 : ¬ (1 ≡ 0)
¬1≡0 ()

-- suc n is never equal to 0. Used in prefix mismatch eliminations.
¬suc≡0 : ∀ {n : ℕ} → ¬ (suc n ≡ 0)
¬suc≡0 ()

-- suc (suc n) is never equal to 1. Used in prefix mismatch eliminations.
¬suc-suc≡1 : ∀ {n : ℕ} → ¬ (suc (suc n) ≡ 1)
¬suc-suc≡1 {n} eq = ¬suc≡0 (suc-injective eq)

-- Extract the 'just' witness from the right side of a MaybeNat< proof.
-- Used in ≺-trans to extract sublen equality from the ordering witness.
MaybeNat<-just-r : ∀ (x y : Maybe ℕ) → MaybeNat< x y → ∃[ z ] y ≡ just z
MaybeNat<-just-r nothing (just z) maybenat-nothing-just = z , refl
MaybeNat<-just-r (just x') (just y') (maybenat-just-just _<_) = y' , refl
MaybeNat<-just-r nothing nothing ()
MaybeNat<-just-r (just _) nothing ()

-- Transitivity helper for sublen existential equalities.
-- Given sublen u₁ q ≡ sublen u₂ q and a proof that sublen u₂ q ≡ just n,
-- produces a proof that sublen u₁ q ≡ just n (packaged as ∃).
trans-SublenEq : ∀ {r} {u₁ u₂ : U r} (q : List ℕ)
  → sublen u₁ q ≡ sublen u₂ q
  → ∃[ n ] sublen u₂ q ≡ just n
  → ∃[ n ] sublen u₁ q ≡ just n
trans-SublenEq q eq (n , eq₂) = n , trans eq eq₂

-- Proof that sublen u [] ≡ just (length (proj₁ (flat u))).
sublen-nil-∈ : ∀ {r : RE} (u : U r) → ∃[ n ] sublen u [] ≡ just n
sublen-nil-∈ {ε} EmptyU = 0 , refl
sublen-nil-∈ {$ c ` loc} (LetterU c) = 1 , refl
sublen-nil-∈ {l ● r ` loc} (PairU u v) with length (proj₁ (flat (PairU {l} {r} {loc} u v)))
... | k = k , refl
sublen-nil-∈ {l + r ` loc} (LeftU u) with length (proj₁ (flat (LeftU {l} {r} {loc} u)))
... | k = k , refl
sublen-nil-∈ {l + r ` loc} (RightU u) with length (proj₁ (flat (RightU {l} {r} {loc} u)))
... | k = k , refl
sublen-nil-∈ {r * ε∉r ` loc} (ListU us) with length (proj₁ (flat (ListU {r} {ε∉r} {loc} us)))
... | k = k , refl

-- Convert position membership to a proof that sublen returns just.
-- Used throughout ≺-trans to bridge between membership and sublen equality.
sublen-∈-just : ∀ { r : RE } { u : U r } ( q' : List ℕ )
  → q' ∈ pos u
  → ∃[ n ] sublen u q' ≡ just n
sublen-∈-just {ε} {EmptyU} [] (here p) rewrite p = 0 , refl
sublen-∈-just {$ c ` loc} {LetterU _} [] (here p) rewrite p = 1 , refl
sublen-∈-just {l ● r ` loc} {PairU u v} [] (here p) with length (proj₁ (flat (PairU {l} {r} {loc} u v)))
... | k = k , refl
sublen-∈-just {l ● r ` loc} {PairU u v} (0 ∷ xs) (there x∈xs++) with ∈-++⁻ _ x∈xs++
... | inj₁ y∈ys = sublen-∈-just {l} {u} xs (map-inv (pos u) y∈ys)
... | inj₂ x∈ = ⊥-elim (¬prefix∈map ¬0≡1 x∈)
sublen-∈-just {l ● r ` loc} {PairU u v} (1 ∷ xs) (there x∈xs++) with ∈-++⁻ _ x∈xs++
... | inj₁ x∈ = ⊥-elim (¬prefix∈map ¬1≡0 x∈)
... | inj₂ y∈ys = sublen-∈-just {r} {v} xs (map-inv (pos v) y∈ys)
sublen-∈-just {l + r ` loc} {LeftU u} [] (here p) with length (proj₁ (flat (LeftU {l} {r} {loc} u)))
... | k = k , refl
sublen-∈-just {l + r ` loc} {LeftU u} [] (there x∈) = ⊥-elim (¬[]∈map∷ x∈)
sublen-∈-just {l + r ` loc} {LeftU u} (0 ∷ xs) (there x∈xs) = sublen-∈-just {l} {u} xs (map-inv (pos u) x∈xs)
sublen-∈-just {l + r ` loc} {LeftU u} (suc x ∷ q') (there x∈) = ⊥-elim (¬prefix∈map ¬suc≡0 x∈)
sublen-∈-just {l + r ` loc} {RightU u} [] (here p) with length (proj₁ (flat (RightU {l} {r} {loc} u)))
... | k = k , refl
sublen-∈-just {l + r ` loc} {RightU u} [] (there x∈) = ⊥-elim (¬[]∈map∷ x∈)
sublen-∈-just {l + r ` loc} {RightU u} (0 ∷ q') (there x∈) = ⊥-elim (¬prefix∈map ¬0≡1 x∈)
sublen-∈-just {l + r ` loc} {RightU u} (1 ∷ xs) (there x∈xs) = sublen-∈-just {r} {u} xs (map-inv (pos u) x∈xs)
sublen-∈-just {l + r ` loc} {RightU u} (suc (suc x) ∷ q') (there x∈) = ⊥-elim (¬prefix∈map ¬suc-suc≡1 x∈)
sublen-∈-just {sr * se ` loc} {ListU us} [] (here p) with length (proj₁ (flat (ListU {sr} {se} {loc} us)))
... | k = k , refl
sublen-∈-just {sr * se ` loc} {ListU us} [] (there x∈) = ⊥-elim (¬[]∈go-pos us x∈)
sublen-∈-just {r₂} {ListU {r₁} (u ∷ us)} (0 ∷ xs) (there x∈xs++) = go⁰ (∈-++⁻ _ x∈xs++)
  where go⁰ : _ ⊎ _ → _
        go⁰ (inj₁ y∈ys₁) = sublen-∈-just {r₁} {u} xs (map-inv (pos u) y∈ys₁)
        go⁰ (inj₂ x∈) = ⊥-elim (¬0∈go-pos-suc 0 us x∈)
sublen-∈-just {sr * se ` loc} {ListU {r₁} (u ∷ us)} (suc n ∷ xs) (there x∈xs++) with ∈-++⁻ _ x∈xs++
... | inj₁ y∈ = ⊥-elim (¬suc-n≡0 (map-prefix≡ {k = 0} y∈))
  where ¬suc-n≡0 : ¬ (suc n ≡ 0)
        ¬suc-n≡0 ()
... | inj₂ y∈ = helper n us y∈
  where
    helper : ∀ n (vs : List (U r₁)) → (suc n ∷ xs) ∈ go-pos 1 vs → ∃ λ m → sublen (ListU {r₁} {se} {loc} (u ∷ vs)) (suc n ∷ xs) ≡ just m
    helper zero (v ∷ vs) y∈ with ∈-++⁻ _ y∈
    ... | inj₁ y∈map = sublen-∈-just {r₁} {v} xs (map-inv (pos v) y∈map)
    ... | inj₂ y∈tail = ⊥-elim (¬1∈go-pos-suc1 0 vs y∈tail)
      where
        ¬1≡sk : ∀ {k : ℕ} → ¬ (1 ≡ suc (suc k))
        ¬1≡sk ()
        ¬1∈go-pos-suc1 : ∀ (k : ℕ) (ws : List (U r₁)) → (1 ∷ xs) ∈ go-pos (suc (suc k)) ws → ⊥
        ¬1∈go-pos-suc1 k [] ()
        ¬1∈go-pos-suc1 k (w ∷ ws) y∈ with ∈-++⁻ _ y∈
        ... | inj₁ y∈map = ⊥-elim (¬1≡sk (map-prefix≡ {k = suc (suc k)} y∈map))
        ... | inj₂ y∈tail = ¬1∈go-pos-suc1 (suc k) ws y∈tail
    helper (suc n) (v ∷ vs) y∈ with ∈-++⁻ _ y∈
    ... | inj₁ y∈map = ⊥-elim (¬suc-suc-n≡1 (map-prefix≡ {k = 1} y∈map))
      where ¬suc-suc-n≡1 : ¬ (suc (suc n) ≡ 1)
            ¬suc-suc-n≡1 ()
    ... | inj₂ y∈tail = helper n vs (go-pos-shift 1 vs y∈tail)

sublen-∈-just {sr * se ` loc} {ListU []} (n ∷ xs) (there ())
sublen-∈-just {l ● r ` loc} {u = PairU u v} [] (there x∈) = ⊥-elim (¬[]∈ x∈)
  where
    ¬[]∈ : ¬ ([] ∈ List.map (0 ∷_) (pos u) ++ List.map (1 ∷_) (pos v))
    ¬[]∈ x∈ with ∈-++⁻ {v = []} (List.map (0 ∷_) (pos u)) x∈
    ... | inj₁ x∈map = ¬[]∈map∷ x∈map
    ... | inj₂ x∈map = ¬[]∈map∷ x∈map
sublen-∈-just {l ● r ` loc} {u = PairU u v} (suc (suc x) ∷ q') (there x∈) = ⊥-elim (¬suc2∈ x∈)
  where
    ¬suc2∈ : ¬ (suc (suc x) ∷ q' ∈ List.map (0 ∷_) (pos u) ++ List.map (1 ∷_) (pos v))
    ¬suc2∈ x∈ with ∈-++⁻ {v = suc (suc x) ∷ q'} (List.map (0 ∷_) (pos u)) x∈
    ... | inj₁ x∈map = ¬prefix∈map ¬suc≡0 x∈map
    ... | inj₂ x∈map = ¬prefix∈map ¬suc-suc≡1 x∈map

-- Extract the underlying < proof from a suc-lifted inequality.
-- Used in ≺-trans to deconstruct ≺lex-head proofs.
<-injective : ∀ {m n} (p : suc m < suc n) → ∃ λ (q : m < n) → s<s q ≡ p
<-injective (s<s q) = q , refl

-- Helper for the ≺-trans q≺p case: prove the condition field of ≺p.
-- For any q' in pos u₁ ++ pos u₃ with q' ≺Lex q, we show sublen u₁ q' ≡ sublen u₃ q'.
-- This is used in all three branches of the mb₂ case analysis.
eq-cond-q-helper : ∀ { r : RE } (u₁ u₂ u₃ : U r) (p q : List ℕ)
  → (cond₁ : ∀ (x : List ℕ) → x ∈ pos u₁ ++ pos u₂ → x ≺Lex p → sublen u₁ x ≡ sublen u₂ x)
  → (cond₂ : ∀ (x : List ℕ) → x ∈ pos u₂ ++ pos u₃ → x ≺Lex q → sublen u₂ x ≡ sublen u₃ x)
  → q ≺Lex p
  → ∀ (q' : List ℕ) → q' ∈ pos u₁ ++ pos u₃ → q' ≺Lex q → sublen u₁ q' ≡ sublen u₃ q'
eq-cond-q-helper {r} u₁ u₂ u₃ p q cond₁ cond₂ q≺p q' q'∈ q'≺q = helper (∈-++⁻ {v = q'} (pos u₁) q'∈)
  where
    helper : q' ∈ pos u₁ ⊎ q' ∈ pos u₃ → sublen u₁ q' ≡ sublen u₃ q'
    helper (inj₁ q'∈u₁) =
      begin
        sublen u₁ q'
      ≡⟨ cond₁ q' (∈-++⁺ˡ q'∈u₁) (≺Lex-trans q' q p q'≺q q≺p) ⟩
        sublen u₂ q'
      ≡⟨ cond₂ q' (∈-++⁺ˡ q'∈u₂) q'≺q ⟩
        sublen u₃ q'
      ∎
      where
        q'∈u₂-just : ∃ λ n → sublen u₂ q' ≡ just n
        q'∈u₂-just = trans-SublenEq {r} q' (sym (cond₁ q' (∈-++⁺ˡ q'∈u₁) (≺Lex-trans q' q p q'≺q q≺p))) (sublen-∈-just {u = u₁} q' q'∈u₁)

        q'∈u₂ : q' ∈ pos u₂
        q'∈u₂ = sublen-just-∈-pos {u = u₂} q'∈u₂-just

    helper (inj₂ q'∈u₃) =
      trans (cond₁ q' (∈-++⁺ʳ _ q'∈u₂) (≺Lex-trans q' q p q'≺q q≺p))
            (cond₂ q' (∈-++⁺ʳ _ q'∈u₃) q'≺q)
      where
        q'∈u₂-just : ∃ λ n → sublen u₂ q' ≡ just n
        q'∈u₂-just = trans-SublenEq {r} q' (cond₂ q' (∈-++⁺ʳ _ q'∈u₃) q'≺q) (sublen-∈-just {u = u₃} q' q'∈u₃)

        q'∈u₂ : q' ∈ pos u₂
        q'∈u₂ = sublen-just-∈-pos {u = u₂} q'∈u₂-just

-- Given u₁ ≺ u₂ with witness p and u₂ ≺ u₃ with witness q,
-- we case-analyse on the trichotomy of p and q (using ≺Lex-trichotomous)
-- to build a witness for u₁ ≺ u₃.
≺-trans : ∀ { r : RE } { u₁ u₂ u₃ : U r }
  → r ⊢ u₁ ≺ u₂
  → r ⊢ u₂ ≺ u₃
  --------------
  → r ⊢ u₁ ≺ u₃
≺-trans {r} {u₁} {u₂} {u₃} (≺ _ _ (p , ≺p _ _ p (sublen< _ _ p mb₁) cond₁)) (≺ _ _ (q , ≺p _ _ q (sublen< _ _ q mb₂) cond₂))
   with ≺Lex-trichotomous p q
... | inj₁ p≺q = ≺ u₁ u₃ (p , ≺p u₁ u₃ p (sublen< u₁ u₃ p mb) eq-cond)
   where
    p∈u₂-just : ∃ λ n → sublen u₂ p ≡ just n
    p∈u₂-just = MaybeNat<-just-r (sublen u₁ p) (sublen u₂ p) mb₁

    p∈u₂-pos : p ∈ pos u₂
    p∈u₂-pos = sublen-just-∈-pos p∈u₂-just

    sublen-u₂-p≡u₃-p : sublen u₂ p ≡ sublen u₃ p
    sublen-u₂-p≡u₃-p = cond₂ p (∈-++⁺ˡ p∈u₂-pos) p≺q

    mb : MaybeNat< (sublen u₁ p) (sublen u₃ p)
    mb = subst (λ y → MaybeNat< (sublen u₁ p) y) sublen-u₂-p≡u₃-p mb₁

    eq-cond : ∀ (q' : List ℕ) → q' ∈ pos u₁ ++ pos u₃ → q' ≺Lex p → sublen u₁ q' ≡ sublen u₃ q'
    eq-cond q' q'∈ q'≺p with ∈-++⁻ {v = q'} (pos u₁) q'∈
    ... | inj₁ q'∈u₁ =
      begin
      sublen u₁ q'
      ≡⟨ cond₁ q' (∈-++⁺ˡ q'∈u₁) q'≺p ⟩
      sublen u₂ q'
      ≡⟨ cond₂ q' (∈-++⁺ˡ q'∈u₂) (≺Lex-trans q' p q q'≺p p≺q) ⟩
      sublen u₃ q'
      ∎
      where
        q'∈u₂-just : ∃ λ n → sublen u₂ q' ≡ just n
        q'∈u₂-just = trans-SublenEq {r} q' (sym (cond₁ q' (∈-++⁺ˡ q'∈u₁) q'≺p)) (sublen-∈-just q' q'∈u₁)

        q'∈u₂ : q' ∈ pos u₂
        q'∈u₂ = sublen-just-∈-pos q'∈u₂-just

    ... | inj₂ q'∈u₃ =
      begin
        sublen u₁ q'
      ≡⟨ cond₁ q' (∈-++⁺ˡ q'∈u₁) q'≺p ⟩
        sublen u₂ q'
      ≡⟨ cond₂ q' (∈-++⁺ˡ q'∈u₂) (≺Lex-trans q' p q q'≺p p≺q) ⟩
        sublen u₃ q'
      ∎
      where
        q'∈u₃-just : ∃ λ n → sublen u₃ q' ≡ just n
        q'∈u₃-just = sublen-∈-just q' q'∈u₃

        q'∈u₂-just : ∃ λ n → sublen u₂ q' ≡ just n
        q'∈u₂-just = trans-SublenEq {r} q' (cond₂ q' (∈-++⁺ʳ _ q'∈u₃) (≺Lex-trans q' p q q'≺p p≺q)) q'∈u₃-just

        q'∈u₂ : q' ∈ pos u₂
        q'∈u₂ = sublen-just-∈-pos q'∈u₂-just

        q'∈u₁-just : ∃ λ n → sublen u₁ q' ≡ just n
        q'∈u₁-just = trans-SublenEq {r} q' (cond₁ q' (∈-++⁺ʳ _ q'∈u₂) q'≺p) q'∈u₂-just

        q'∈u₁ : q' ∈ pos u₁
        q'∈u₁ = sublen-just-∈-pos q'∈u₁-just

... | inj₂ (inj₁ q≺p) = helper₂ (sublen u₂ q) refl
  where
    helper₂ : (x : Maybe ℕ) → sublen u₂ q ≡ x → r ⊢ u₁ ≺ u₃
    helper₂ (just x) eq = ≺ u₁ u₃ (q , ≺p u₁ u₃ q (sublen< u₁ u₃ q mb-q) eq-cond-q)
      where
        q∈u₂ : q ∈ pos u₂
        q∈u₂ = sublen-just-∈-pos (x , eq)

        sublen-u₁-q≡u₂-q : sublen u₁ q ≡ sublen u₂ q
        sublen-u₁-q≡u₂-q = cond₁ q (∈-++⁺ʳ _ q∈u₂) q≺p

        mb-q : MaybeNat< (sublen u₁ q) (sublen u₃ q)
        mb-q = subst (λ z → MaybeNat< z (sublen u₃ q)) (sym sublen-u₁-q≡u₂-q) mb₂

        eq-cond-q = eq-cond-q-helper u₁ u₂ u₃ p q cond₁ cond₂ q≺p

    helper₂ nothing eq = ≺ u₁ u₃ (q , ≺p u₁ u₃ q (sublen< u₁ u₃ q mb-q) eq-cond-q)
      where
        sublen-u₁-q≡nothing : sublen u₁ q ≡ nothing
        sublen-u₁-q≡nothing = lemma (sublen u₁ q) refl
          where
            lemma : ∀ (x : Maybe ℕ) → sublen u₁ q ≡ x → sublen u₁ q ≡ nothing
            lemma nothing eq' = eq'
            lemma (just x) eq' = ⊥-elim (¬nothing≡just (trans (sym eq) (trans (sym (cond₁ q (∈-++⁺ˡ (sublen-just-∈-pos {r} {u₁} (x , eq'))) q≺p)) eq')))

        mb-q : MaybeNat< (sublen u₁ q) (sublen u₃ q)
        mb-q = subst (λ z → MaybeNat< z (sublen u₃ q)) (trans eq (sym sublen-u₁-q≡nothing)) mb₂

        eq-cond-q = eq-cond-q-helper u₁ u₂ u₃ p q cond₁ cond₂ q≺p

... | inj₂ (inj₂ p≡q) = ≺ u₁ u₃ (p , ≺p u₁ u₃ p (sublen< u₁ u₃ p mb-eq) eq-cond-eq)
   where
    mb-eq : MaybeNat< (sublen u₁ p) (sublen u₃ p)
    mb-eq rewrite p≡q = ≺Nat<-trans mb₁ mb₂

    eq-cond-eq : ∀ (q' : List ℕ) → q' ∈ pos u₁ ++ pos u₃ → q' ≺Lex p → sublen u₁ q' ≡ sublen u₃ q'
    eq-cond-eq q' q'∈ q'≺p with ∈-++⁻ {v = q'} (pos u₁) q'∈
    ... | inj₁ q'∈u₁ =
      begin
        sublen u₁ q'
      ≡⟨ cond₁ q' (∈-++⁺ˡ q'∈u₁) q'≺p ⟩
        sublen u₂ q'
      ≡⟨ cond₂ q' (∈-++⁺ˡ q'∈u₂) (subst (λ x → q' ≺Lex x) p≡q q'≺p) ⟩
        sublen u₃ q'
      ∎
      where
        q'∈u₂-just : ∃ λ n → sublen u₂ q' ≡ just n
        q'∈u₂-just = trans-SublenEq {r} q' (sym (cond₁ q' (∈-++⁺ˡ q'∈u₁) q'≺p)) (sublen-∈-just q' q'∈u₁)

        q'∈u₂ : q' ∈ pos u₂
        q'∈u₂ = sublen-just-∈-pos q'∈u₂-just

    ... | inj₂ q'∈u₃ =
      begin
        sublen u₁ q'
      ≡⟨ cond₁ q' (∈-++⁺ʳ _ q'∈u₂) q'≺p ⟩
        sublen u₂ q'
      ≡⟨ cond₂ q' (∈-++⁺ʳ _ q'∈u₃) (subst (λ x → q' ≺Lex x) p≡q q'≺p) ⟩
        sublen u₃ q'
      ∎
      where
        q'∈u₂-just : ∃ λ n → sublen u₂ q' ≡ just n
        q'∈u₂-just = trans-SublenEq {r} q' (cond₂ q' (∈-++⁺ʳ _ q'∈u₃) (subst (λ x → q' ≺Lex x) p≡q q'≺p)) (sublen-∈-just q' q'∈u₃)

        q'∈u₂ : q' ∈ pos u₂
        q'∈u₂ = sublen-just-∈-pos q'∈u₂-just
```

Lemma: _ ⊢ _ ≺ _ is asymmetric

```agda
just-inj : {x y : ℕ} → just x ≡ just y → x ≡ y
just-inj refl = refl

maybeNatAsym : (x : Maybe ℕ) → (y : Maybe ℕ) → MaybeNat< x y → x ≡ y → ⊥
maybeNatAsym nothing (just n) maybenat-nothing-just x≡y = ¬nothing≡just x≡y
maybeNatAsym (just m) (just n) (maybenat-just-just m<nat) x≡y = <-irrefl (just-inj x≡y) m<nat

maybeNat<-asym : ∀ {x y : Maybe ℕ} → MaybeNat< x y → MaybeNat< y x → ⊥
maybeNat<-asym maybenat-nothing-just ()
maybeNat<-asym {just mx} {just my} (maybenat-just-just mn) (maybenat-just-just nm) = <-irrefl refl mm
  where
    mm : mx < mx
    mm = <-trans mn nm

open-exist : ∀ {r : RE} {u v : U r} → r ⊢ u ≺ v → Σ (List ℕ) (λ p → r , p ⊢ u ≺ v)
open-exist (≺ u v e) = e

≺-asym : ∀ {r : RE } { u₁ u₂ : U r }
  → r ⊢ u₁ ≺ u₂
  -------------
  → ¬ ( r ⊢ u₂ ≺ u₁)
≺-asym {r} {u₁} {u₂} u₁≺u₂ u₂≺u₁ with open-exist u₁≺u₂
... | pw₁ , ≺p _ _ pw₁ (sublen< _ _ pw₁ mb₁) cond₁ = go u₂≺u₁
  where
    go : r ⊢ u₂ ≺ u₁ → ⊥
    go (≺ _ _ (pw₂ , ≺p _ _ pw₂ (sublen< _ _ pw₂ mb₂) cond₂))
      with ≺Lex-trichotomous pw₁ pw₂
    ... | inj₁ pw₁≺pw₂ = maybeNatAsym (sublen u₁ pw₁) (sublen u₂ pw₁) mb₁ (sym (cond₂ pw₁ (∈-++⁺ˡ pw₁∈u₂) pw₁≺pw₂))
      where
        pw₁∈u₂-just : ∃ λ n → sublen u₂ pw₁ ≡ just n
        pw₁∈u₂-just = MaybeNat<-just-r (sublen u₁ pw₁) (sublen u₂ pw₁) mb₁

        pw₁∈u₂ : pw₁ ∈ pos u₂
        pw₁∈u₂ = sublen-just-∈-pos {r} {u₂} pw₁∈u₂-just

    ... | inj₂ (inj₁ pw₂≺pw₁) = maybeNatAsym (sublen u₂ pw₂) (sublen u₁ pw₂) mb₂ (sym (cond₁ pw₂ (∈-++⁺ˡ pw₂∈u₁) pw₂≺pw₁))
      where
        pw₂∈u₁-just : ∃ λ n → sublen u₁ pw₂ ≡ just n
        pw₂∈u₁-just = MaybeNat<-just-r (sublen u₂ pw₂) (sublen u₁ pw₂) mb₂

        pw₂∈u₁ : pw₂ ∈ pos u₁
        pw₂∈u₁ = sublen-just-∈-pos {r} {u₁} pw₂∈u₁-just

    ... | inj₂ (inj₂ pw₁≡pw₂) = maybeNat<-asym {sublen u₁ pw₁} {sublen u₂ pw₁} mb₁ (subst (λ y → MaybeNat< (sublen u₂ y) (sublen u₁ y)) (sym pw₁≡pw₂) mb₂)

```

Lemma: _ ⊢ _ ≺ _ is irreflexive

```agda
≺-irrefl : ∀ { r : RE } { u₁ u₂ : U r }
  → u₁ ≡ u₂
  ------------------
  → ¬ (r ⊢ u₁ ≺ u₂)
≺-irrefl u₁≡u₂ u₁≺u₂ rewrite u₁≡u₂ = ≺-asym u₁≺u₂ u₁≺u₂
```


Lemma: _ ⊢ _ ≼ _ is transitive 


```agda
≼-trans : ∀ { r : RE } { u₁ u₂ u₃ : U r }
  → r ⊢ u₁ ≼ u₂
  → r ⊢ u₂ ≼ u₃
  --------------
  → r ⊢ u₁ ≼ u₃
≼-trans (inj₁ u₁≺u₂) (inj₁ u₂≺u₃) = inj₁ (≺-trans u₁≺u₂  u₂≺u₃)
≼-trans (inj₂ u₁≡u₂) (inj₁ u₂≺u₃) rewrite u₁≡u₂ = inj₁ u₂≺u₃
≼-trans (inj₁ u₁≺u₂) (inj₂ u₂≡u₃) rewrite sym u₂≡u₃ = inj₁ u₁≺u₂
≼-trans (inj₂ u₁≡u₂) (inj₂ u₂≡u₃) rewrite sym u₂≡u₃ = inj₂ u₁≡u₂


```





Lemma: _ ⊢ _ ≼ _ is reflexive

```agda
≼-refl : ∀ { r : RE } { u : U r }
  → r ⊢ u ≼ u
≼-refl {r} {u} = inj₂ refl 
```


Lemma: _ ⊢ _ ≼ _ is anti symmetric

```agda
≼-antisym : ∀ { r : RE } { u₁ u₂ : U r }
  → r ⊢ u₁ ≼ u₂
  → r ⊢ u₂ ≼ u₁
  --------------
  → u₁ ≡ u₂ 
≼-antisym (inj₂ u₁≡u₂) _ = u₁≡u₂
≼-antisym _ (inj₂ u₂≡u₁) = sym u₂≡u₁
≼-antisym (inj₁ u₁≺u₂) (inj₁ u₂≺u₁) = Nullary.contradiction u₁≺u₂ (≺-asym u₂≺u₁)  

```

Lemma: ≼ is wellfounded given a fix flatten word.

```agda
≼-wellfounded : ∀ { r : RE } { w : List Char }
  → w ∈⟦ r ⟧ 
  → ∃[ u ] ( ( proj₁ (flat u) ≡ w ) → ( v : U r ) → (proj₁ (flat v) ≡ w) →  r ⊢ u ≼ v )
≼-wellfounded = {!!} 
```
