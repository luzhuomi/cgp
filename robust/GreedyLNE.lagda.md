```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.GreedyLNE where

import cgp.RE as RE
open RE using (RE;  ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;   ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ; first ; ε∉r→¬first-r≡[] )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU;  unListU ; listU∘unListU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU )


import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; Flat-[] ; flat-[] ;  mkAllEmptyU≢[] ; proj₁flat-v≡[]→ε∈r )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ) 



import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming ( _⊢_>_  to  _⊢_>ᵍ_ )

import cgp.greedy.PartialDerivative as GreedyPD
open GreedyPD renaming ( parseAll[_,_] to parseAllᵍ[_,_] ) 

import cgp.lne.Order as LNEOrder
open LNEOrder renaming ( _⊢_>_  to  _⊢_>ˡ_ )

import cgp.lne.PartialDerivative as LNEPD
open LNEPD renaming ( parseAll[_,_] to parseAllˡ[_,_] ) 


import cgp.Utils as Utils
open Utils using (any-right-concat; any-left-concat ; all-concat ;  ∷-inj  ; ¬∷≡[]  ; inv-map-[]  )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_  )

import Data.List.Properties
open Data.List.Properties using (  ++-assoc ;  ++-identityʳ ; ++-identityˡ ; {-  unfold-reverse ; -} ∷ʳ-++ ; ++-cancelˡ ;  ++-conicalʳ ;  ++-conicalˡ  )


import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)

import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map)
open import Data.List.Relation.Unary.Any using (Any; here; there ; map)

import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )

import Data.List.Membership.Propositional
open Data.List.Membership.Propositional using (_∈_)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)

import Relation.Nullary as Nullary 
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

open import Function using (_∘_ ; flip)

open import Level using (Level)

```

### Robustness definition 

```agda

data Robust : RE → Set where
  robust : ∀ { r : RE } 
             → ( ∀ ( v₁ : U r ) → ( v₂ : U r ) 
               → ( r ⊢ v₁ >ᵍ v₂ → r ⊢ v₁ >ˡ v₂ ) × ( r ⊢ v₁ >ˡ v₂ → r ⊢ v₁ >ᵍ v₂ )
               )
           -----------------------------------------
           → Robust r  
```


### ParseAll r w  means Robust?

step 1. We need to show that the sets of partial derivatives produced by Greedy.parseAll and LNE.parseAll are the equal

```agda


private
  variable
    a b c p ℓ : Level
    A : Set a
    B : Set b
    C : Set c


data SetEq { A : Set a } : ( xs ys : List A ) → Set a where
  setEq : { xs ys : List A }
    → All ( λ x → x ∈ ys ) xs 
    → All ( λ y → y ∈ xs ) ys 
    -------------------
    → SetEq xs ys


postulate
  greedy-lne-parseall : ∀ { r : RE } { w : List Char }
    → SetEq parseAllᵍ[ r , w ] parseAllˡ[ r , w ] 


```

step 2. if the multisets (lists) are in the same order, it implies robust?


```agda


```



### "Stable" Partial Derivative Descendant


step 3. if all pdi* of a r (regardless of greedy or lne ; since from step 1 we've proven they are the same set), are stable,
then r is having the same parseAll results for all w, i.e. it is lne-greedy robust.

```agda

data RightMostNull : RE → Set where
  rmn-+ε : ∀ { l : RE } { loc : ℕ } { ε∉l : ε∉ l }
    → RightMostNull ( l + ε ` loc )

  rmn-+* : ∀ { l r : RE } { ε∉r : ε∉ r } { loc₁ loc₂ : ℕ } { ε∉l : ε∉ l }
    → RightMostNull ( l + (r * ε∉r ` loc₁) ` loc₂)

  rmn-+● : ∀ { l s r : RE } { loc₁ loc₂ : ℕ } { ε∉l : ε∉ l } { ε∈s : ε∈ s } { ε∈r : ε∈ r }
    → RightMostNull ( l + ( s ● r ` loc₁ ) ` loc₂ )

  rmn-++ : ∀ { l s r : RE } { loc₁ loc₂ : ℕ } { ε∉l : ε∉ l } 
    → RightMostNull (s + r ` loc₁)
    ------------------------------------------------
    → RightMostNull ( l + ( s + r ` loc₁ ) ` loc₂ )


-- data StablePDI : RE → Set where
--   stable-pdd

```


### To show that the set of partial derivative descendants for 



```agda

data LNE : RE → Set where
  lne-ε  : LNE ε
  lne-$  : ∀ { c : Char } { loc : ℕ } → LNE ($ c ` loc)
  lne-●  : ∀ { l r : RE } { loc : ℕ }
    → LNE l
    → LNE r
    ----------------------------------
    → LNE ( l ● r ` loc )
  lne-+  : ∀ { l r : RE } { loc : ℕ }
    → ε∉ l -- this is not strong enough
    → LNE l  
    → LNE r
    ---------------------------------
    → LNE ( l + r ` loc )
  lne-*  : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → LNE r
    --------------------------------
    → LNE ( r * ε∉r ` loc )



postulate 
  ¬proj₁flat-cons≡[] : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { u : U r } { us : List (U r) }
    → ¬ ( proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us))) ≡ [] )
  proj₁flat-nil≡[] : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → proj₁ (flat (ListU {r} {ε∉r} {loc} [] )) ≡ [] 

{-
u>ᵍv→¬v>ᵍu : ∀ { r : RE } {u : U r} {v : U r}
  → r ⊢ u >ᵍ v
  --------------
  → ¬ r ⊢ v >ᵍ u
u>ᵍv→¬v>ᵍu {ε}             {EmptyU}          {EmptyU} = λ ()  
u>ᵍv→¬v>ᵍu {$ c ` loc}     {LetterU _}       {LetterU _} = λ ()
u>ᵍv→¬v>ᵍu {r * ε∉r ` loc} {ListU []}        {ListU []} = λ ()
u>ᵍv→¬v>ᵍu {r * ε∉r ` loc} {ListU []}        {ListU (v ∷ vs)} = λ () 
u>ᵍv→¬v>ᵍu {r * ε∉r ` loc} {ListU (u ∷ us)}  {ListU []} star-cons-nil = λ()
-- u>ᵍv→¬v>ᵍu {r * ε∉r ` loc} {ListU (u ∷ us)}  {ListU (v ∷ vs)} with u ≡? v
-- ... | yes u≡v = ?
-}





-- u≡v→¬u>ᵍv ?

lne-proj₁flat≡[]→refl : ∀ { r : RE } { ε∈r : ε∈ r } { u v : U r }
    → LNE r 
    → proj₁ (flat u) ≡ []
    → proj₁ (flat v) ≡ []
    ------------------------
    → u ≡ v
lne-proj₁flat≡[]→refl {ε}              {ε∈ε} {EmptyU} {EmptyU} lne-ε refl refl = refl
lne-proj₁flat≡[]→refl {r * ε∉r ` loc}  {ε∈*} {ListU []}       {ListU []} (lne-* lne-r) refl refl = refl 
lne-proj₁flat≡[]→refl {r * ε∉r ` loc}  {ε∈*} {ListU (u ∷ us)} {_}        (lne-* lne-r) proj₁flat-list-uus≡[] _ = Nullary.contradiction   proj₁flat-list-uus≡[] (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us})
lne-proj₁flat≡[]→refl {r * ε∉r ` loc}  {ε∈*} {_} {ListU (u ∷ us)}        (lne-* lne-r) _ proj₁flat-list-uus≡[] = Nullary.contradiction   proj₁flat-list-uus≡[] (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us})
lne-proj₁flat≡[]→refl {l ● r ` loc}  {ε∈ ε∈l ● ε∈r } {PairU u₁ u₂}  {PairU v₁ v₂} (lne-● lne-l lne-r) proj₁flat-pair-u₁u₂≡[] proj₁flat-pair-v₁v₂≡[] = prf  
  where 
    proj₁flat-v₁≡[] : proj₁ (flat v₁) ≡ []
    proj₁flat-v₁≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) proj₁flat-pair-v₁v₂≡[]
    proj₁flat-v₂≡[] : proj₁ (flat v₂) ≡ []
    proj₁flat-v₂≡[] = ++-conicalʳ (proj₁ (flat v₁)) (proj₁ (flat v₂)) proj₁flat-pair-v₁v₂≡[]
    proj₁flat-u₁≡[] : proj₁ (flat u₁) ≡ []
    proj₁flat-u₁≡[] = ++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat u₂)) proj₁flat-pair-u₁u₂≡[]
    proj₁flat-u₂≡[] : proj₁ (flat u₂) ≡ []
    proj₁flat-u₂≡[] = ++-conicalʳ (proj₁ (flat u₁)) (proj₁ (flat u₂)) proj₁flat-pair-u₁u₂≡[]
    u₁≡v₁ : u₁ ≡ v₁
    u₁≡v₁ = lne-proj₁flat≡[]→refl {l} {ε∈l} {u₁} {v₁} lne-l proj₁flat-u₁≡[] proj₁flat-v₁≡[]
    u₂≡v₂ : u₂ ≡ v₂
    u₂≡v₂ = lne-proj₁flat≡[]→refl {r} {ε∈r} {u₂} {v₂} lne-r proj₁flat-u₂≡[] proj₁flat-v₂≡[]

    prf : PairU {l} {r} {loc} u₁ u₂ ≡ PairU {l} {r} {loc}  v₁ v₂
    prf rewrite u₁≡v₁ | u₂≡v₂ = refl 
lne-proj₁flat≡[]→refl {l + r ` loc}  {ε∈ ε∈l + ε∈r } {_}  {_}  (lne-+ ε∉l lne-l lne-r) _ _ = Nullary.contradiction  ε∈l (ε∉r→¬ε∈r ε∉l)
lne-proj₁flat≡[]→refl {l + r ` loc}  {ε∈ ε∈l <+ ε∉r } {_}  {_}  (lne-+ ε∉l lne-l lne-r) _ _ = Nullary.contradiction  ε∈l (ε∉r→¬ε∈r ε∉l)
lne-proj₁flat≡[]→refl {l + r ` loc}  {ε∈ ε∉l +> ε∈r } {LeftU v}  {_}  (lne-+ ε∉l' lne-l lne-r) proj₁flat-left-v≡[] _ =  Nullary.contradiction (proj₁flat-v≡[]→ε∈r  proj₁flat-left-v≡[]) (ε∉r→¬ε∈r ε∉l)
lne-proj₁flat≡[]→refl {l + r ` loc}  {ε∈ ε∉l +> ε∈r } {_} {LeftU v}  (lne-+ ε∉l' lne-l lne-r) _  proj₁flat-left-v≡[] =   Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-left-v≡[]) (ε∉r→¬ε∈r ε∉l)
lne-proj₁flat≡[]→refl {l + r ` loc}  {ε∈ ε∉l +> ε∈r } {RightU u} {RightU v}  (lne-+ ε∉l' lne-l lne-r) proj₁flat-right-u≡[]  proj₁flat-right-v≡[] = right-u≡right-v
  where
    u≡v : u ≡ v
    u≡v =  lne-proj₁flat≡[]→refl {r} {ε∈r} {u} {v} lne-r proj₁flat-right-u≡[]  proj₁flat-right-v≡[]
    right-u≡right-v : RightU {l} {r} {loc} u ≡ RightU {l} {r} {loc} v
    right-u≡right-v rewrite u≡v = refl 


lne→¬[]>ᵍ∷ : ∀ { r : RE } 
    → LNE r
    → ( u₁ : U r )
    → ( u₂ : U r )
    → proj₁ (flat u₁) ≡ []
    → ¬ proj₁ (flat u₂) ≡ []
    -------------------------
    → ¬ r ⊢ u₁ >ᵍ u₂
lne→¬[]>ᵍ∷ {ε} lne-ε          EmptyU      EmptyU      proj₁flat-empty≡[] ¬proj₁flat-empty≡[]               = Nullary.contradiction proj₁flat-empty≡[] ¬proj₁flat-empty≡[]
lne→¬[]>ᵍ∷ {$ c ` loc} lne-$  (LetterU _) (LetterU _) proj₁flat-letter≡[] ¬proj₁flat-letter≡[]             = Nullary.contradiction proj₁flat-letter≡[] ¬proj₁flat-letter≡[]
lne→¬[]>ᵍ∷ {r * ε∉r ` loc} (lne-* lne-r) (ListU []) (ListU []) proj₁flat-nil≡[] ¬proj₁flat-nil≡[]          = Nullary.contradiction proj₁flat-nil≡[] ¬proj₁flat-nil≡[]
lne→¬[]>ᵍ∷ {r * ε∉r ` loc} (lne-* lne-r) (ListU []) (ListU ( u ∷ us )) proj₁flat-nil≡[] ¬proj₁flat-cons≡[] = λ ()
lne→¬[]>ᵍ∷ {r * ε∉r ` loc} (lne-* lne-r) (ListU ( v ∷ vs )) _  proj₁flat-cons-v-vs≡[] _  = Nullary.contradiction proj₁flat-cons-v-vs≡[] (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs})
lne→¬[]>ᵍ∷ {l + r   ` loc} (lne-+ ε∉l lne-l lne-r) (LeftU u) _ proj₁flat-left-u≡[] _     =  Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-left-u≡[]) (ε∉r→¬ε∈r ε∉l)
lne→¬[]>ᵍ∷ {l + r   ` loc} (lne-+ ε∉l lne-l lne-r) (RightU u) (LeftU v) proj₁flat-left-u≡[] ¬proj₁flat-right-v≡[] =  λ()
lne→¬[]>ᵍ∷ {l + r   ` loc} (lne-+ ε∉l lne-l lne-r) (RightU u) (RightU v) proj₁flat-right-u≡[] ¬proj₁flat-right-v≡[] (choice-rr u>ᵍv) = Nullary.contradiction u>ᵍv (lne→¬[]>ᵍ∷  {r} lne-r u v proj₁flat-right-u≡[] ¬proj₁flat-right-v≡[] )
lne→¬[]>ᵍ∷ {l ● r   ` loc} (lne-● lne-l lne-r) (PairU u₁ u₂) (PairU v₁ v₂)  proj₁flat-pair-u₁u₂≡[] ¬proj₁flat-pair-v₁v₂≡[] = prf  -- how ? can't be proven?
  where
    proj₁flat-u₁≡[] : proj₁ (flat u₁) ≡ []
    proj₁flat-u₁≡[] = ++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat u₂)) proj₁flat-pair-u₁u₂≡[]
    proj₁flat-u₂≡[] : proj₁ (flat u₂) ≡ []
    proj₁flat-u₂≡[] = ++-conicalʳ (proj₁ (flat u₁)) (proj₁ (flat u₂)) proj₁flat-pair-u₁u₂≡[]
    prf :  ¬ (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂
    prf with proj₁ (flat v₁) in proj₁flat-v₁-eq | proj₁ (flat v₂) in proj₁flat-v₂-eq
    ... |  []       |  []    = λ z → ¬proj₁flat-pair-v₁v₂≡[] refl
    ... |  []       | c ∷ cs = {!!} -- λ pair-u₁u₂>pair-v₁v₂ → seq₂ u₁≡v₁ {!!}
      where
        u₁≡v₁ : u₁ ≡ v₁
        u₁≡v₁ = lne-proj₁flat≡[]→refl {l} {proj₁flat-v≡[]→ε∈r proj₁flat-v₁-eq} {u₁} {v₁} lne-l proj₁flat-u₁≡[]  proj₁flat-v₁-eq 
        ev : ¬ (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂
        ev rewrite u₁≡v₁ = λ pair-u₁u₂>pair-v₁v₂ → {!!} 
  -- we can use lne-proj₁flat≡[]→refl 
  -- we replace this lemma by u>ᵍv→¬v>ᵍu and lne→∷>ᵍ[]


lne-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[]  : ∀ { r : RE }
    → LNE r
    → ( u : U r )
    → ( v : U r )
    → r ⊢ u >ᵍ v
    -------------------------
    → ( proj₁ (flat u) ≡ [] × proj₁ (flat v) ≡ [] ) ⊎
      ( ( ¬ proj₁ (flat u) ≡ [] × ¬ proj₁ (flat v) ≡ [] ) ⊎
        ( ¬ proj₁ (flat u) ≡ [] × proj₁ (flat v) ≡ [] ) )
lne-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {ε}             lne-ε EmptyU EmptyU = λ()
lne-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {$ c ` loc}     lne-$ (LetterU _) (LetterU _) = λ()
lne-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (lne-* lne-r) (ListU []) (ListU []) = λ()
lne-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (lne-* lne-r) (ListU []) (ListU ( v ∷ vs) ) = λ()
lne-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (lne-* lne-r) (ListU (u ∷ us )) (ListU []) star-cons-nil = inj₂ (inj₂ (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us} , proj₁flat-nil≡[] {r} {ε∉r} {loc} ) )
lne-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (lne-* lne-r) (ListU (u ∷ us )) (ListU (v ∷ vs)) _       = inj₂ (inj₁ (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us} , ¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs} ) )
lne-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {l ● r ` loc}   (lne-● lne-l lne-r) (PairU u₁ u₂) (PairU v₁ v₂)
  with proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat v₁) in proj₁flat-v₁-eq
... | []        |  []  = prf 
  where
    u₁≡v₁ : u₁ ≡ v₁ 
    u₁≡v₁ = lne-proj₁flat≡[]→refl {l} {proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq} {u₁} {v₁} lne-l proj₁flat-u₁-eq proj₁flat-v₁-eq
    prf : (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂ →
      ( proj₁ (flat u₂) ≡ [] × proj₁ (flat v₂) ≡ [] ) ⊎
      ( ( ¬ proj₁ (flat u₂) ≡ [] × ¬ proj₁ (flat v₂) ≡ [] ) ⊎
        ( ¬ proj₁ (flat u₂) ≡ [] × proj₁ (flat v₂) ≡ [] ) )
    prf rewrite u₁≡v₁ = λ { (seq₂ refl u₂>ᵍv₂ ) → {!!}  } 


lne-u>ᵍv→¬u≡[]×u≢[] : ∀ { r : RE }
    → LNE r
    → ( u : U r )
    → ( v : U r )
    → r ⊢ u >ᵍ v
    ----------------------------------------------------
    → ¬ ( proj₁ (flat u) ≡ [] × ¬ proj₁ (flat v) ≡ [] )
lne-u>ᵍv→¬u≡[]×u≢[] {r} lne-r u v u>ᵍv  (proj₁flat-u≡[] , ¬proj₁flat-v≡[])  with lne-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r} lne-r u v u>ᵍv
... | inj₁ (proj₁flat-u≡[] ,  proj₁-flat-v≡[] ) =  ¬proj₁flat-v≡[] proj₁-flat-v≡[]
... | inj₂ (inj₁ (¬proj₁flat-u≡[] ,  ¬proj₁-flat-v≡[] ) ) = ¬proj₁flat-u≡[] proj₁flat-u≡[]
... | inj₂ (inj₂ (¬proj₁flat-u≡[] ,  proj₁-flat-v≡[] ) )  = ¬proj₁flat-v≡[] proj₁-flat-v≡[] 



lne→∷>ᵍ[] : ∀ { r : RE }
    → LNE r
    → ( u₁ : U r )
    → ( u₂ : U r )
    → ¬ proj₁ (flat u₁) ≡ []
    → proj₁ (flat u₂) ≡ []
    ------------------------
    → r ⊢ u₁ >ᵍ u₂
lne→∷>ᵍ[] {ε} lne-ε          EmptyU      EmptyU      ¬proj₁flat-empty≡[]  proj₁flat-empty≡[]              = Nullary.contradiction proj₁flat-empty≡[] ¬proj₁flat-empty≡[]
lne→∷>ᵍ[] {$ c ` loc} lne-$  (LetterU _) (LetterU _) ¬proj₁flat-letter≡[] proj₁flat-letter≡[]             = Nullary.contradiction proj₁flat-letter≡[] ¬proj₁flat-letter≡[]
lne→∷>ᵍ[] {r * ε∉r ` loc} (lne-* lne-r) (ListU [])  _                       ¬proj₁flat-nil≡[] _           = Nullary.contradiction (proj₁flat-nil≡[]  {r} {ε∉r} {loc})  ¬proj₁flat-nil≡[]
lne→∷>ᵍ[] {r * ε∉r ` loc} (lne-* lne-r) (ListU ( u ∷ us )) (ListU ( v ∷ vs))  ¬proj₁flat-cons-uus≡[] proj₁flat-cons-vvs≡[] =  Nullary.contradiction proj₁flat-cons-vvs≡[] (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs})
lne→∷>ᵍ[] {r * ε∉r ` loc} (lne-* lne-r) (ListU ( u ∷ us )) (ListU [])  ¬proj₁flat-cons-uus≡[] proj₁flat-nil≡[]     = star-cons-nil
lne→∷>ᵍ[] {l + r   ` loc} (lne-+ ε∉l lne-l lne-r) (LeftU u) (LeftU v) ¬proj₁flat-left-u≡[] proj₁flat-left-v≡[]     = choice-ll (lne→∷>ᵍ[] {l} lne-l u v ¬proj₁flat-left-u≡[] proj₁flat-left-v≡[])
lne→∷>ᵍ[] {l + r   ` loc} (lne-+ ε∉l lne-l lne-r) (RightU u) (RightU v) ¬proj₁flat-right-u≡[] proj₁flat-right-v≡[] = choice-rr (lne→∷>ᵍ[] {r} lne-r u v ¬proj₁flat-right-u≡[] proj₁flat-right-v≡[])
lne→∷>ᵍ[] {l + r   ` loc} (lne-+ ε∉l lne-l lne-r) (LeftU u) (RightU v) ¬proj₁flat-left-u≡[] proj₁flat-right-v≡[] = choice-lr 
lne→∷>ᵍ[] {l + r   ` loc} (lne-+ ε∉l lne-l lne-r) (RightU u) (LeftU v) ¬proj₁flat-right-u≡[] proj₁flat-left-v≡[] = Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-left-v≡[]) (ε∉r→¬ε∈r ε∉l)
lne→∷>ᵍ[] {l ● r   ` loc} (lne-● lne-l lne-r) (PairU u₁ u₂) (PairU v₁ v₂)  ¬proj₁flat-pair-u₁u₂≡[] proj₁flat-v₁v₂≡[] = prf 
  where
    proj₁flat-v₁≡[] : proj₁ (flat v₁) ≡ []
    proj₁flat-v₁≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) proj₁flat-v₁v₂≡[]
    proj₁flat-v₂≡[] : proj₁ (flat v₂) ≡ []
    proj₁flat-v₂≡[] = ++-conicalʳ (proj₁ (flat v₁)) (proj₁ (flat v₂)) proj₁flat-v₁v₂≡[]

    prf : (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂
    prf with proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat u₂) in proj₁flat-u₂-eq 
    ... | []     |  []       = Nullary.contradiction refl ¬proj₁flat-pair-u₁u₂≡[] 
    ... | []     |  c' ∷ cs' = seq₂ u₁≡v₁ u₂>ᵍv₂ -- how? we need to show u₁≡v₁ lne-proj₁flat≡[]→refl?
      where
        u₁≡v₁ : u₁ ≡ v₁
        u₁≡v₁ = lne-proj₁flat≡[]→refl {l} {proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq} {u₁} {v₁} lne-l  proj₁flat-u₁-eq proj₁flat-v₁≡[]
        ¬proj₁flat-u₂≡[] : ¬ proj₁ (flat u₂) ≡ []
        ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq = λ proj₁flat-u₂≡[] →  ¬∷≡[] proj₁flat-u₂≡[] 
        u₂>ᵍv₂ : r  ⊢ u₂ >ᵍ v₂
        u₂>ᵍv₂ = lne→∷>ᵍ[] {r} lne-r u₂ v₂  ¬proj₁flat-u₂≡[] proj₁flat-v₂≡[] 
    ... | c ∷ cs |  cs' = seq₁ u₁>ᵍv₁
      where 
        ¬proj₁flat-u₁≡[] : ¬ proj₁ (flat u₁) ≡ []
        ¬proj₁flat-u₁≡[] rewrite proj₁flat-u₁-eq = λ proj₁flat-u₁≡[] →  ¬∷≡[] proj₁flat-u₁≡[] 
        u₁>ᵍv₁ : l  ⊢ u₁ >ᵍ v₁
        u₁>ᵍv₁ = lne→∷>ᵍ[] {l} lne-l u₁ v₁ ¬proj₁flat-u₁≡[] proj₁flat-v₁≡[] 


{-# TERMINATING #-}
lne→robust : ∀ { r : RE }
  → LNE r
  → Robust r 
lne→robust {ε}           lne-ε = robust λ v₁ v₂ → ( ( λ() ) , (λ ()) )
lne→robust {$ c ` loc}   lne-$ = robust λ v₁ v₂ → ( ( λ() ) , (λ ()) ) 
lne→robust {l ● r ` loc} (lne-● lne-l lne-r) = robust {l ● r ` loc} λ { (PairU u₁ v₁) (PairU u₂ v₂) → to-ev u₁ u₂ v₁ v₂ , from-ev  u₁ u₂ v₁ v₂ }
  where
    robust-r : Robust r
    robust-r = lne→robust {r} lne-r
    
    robust-l : Robust l
    robust-l = lne→robust {l} lne-l
    
    to-ev : ( u₁ u₂ : U l ) → ( v₁ v₂ : U r ) → (l ● r ` loc) ⊢ PairU u₁ v₁ >ᵍ PairU u₂ v₂ → (l ● r ` loc) ⊢ PairU u₁ v₁ >ˡ PairU u₂ v₂
    to-ev u₁ u₂ v₁ v₂ (seq₁ u₁>ᵍu₂) with robust-l
    ... | robust rob-l-ev = seq₁ (proj₁ (rob-l-ev u₁ u₂) u₁>ᵍu₂)
    to-ev u₁ u₂ v₁ v₂ (seq₂ u₁≡u₂ v₁>ᵍv₂) with robust-r
    ... | robust rob-r-ev = seq₂ u₁≡u₂ (proj₁ (rob-r-ev v₁ v₂) v₁>ᵍv₂ )

    from-ev : ( u₁ u₂ : U l ) → ( v₁ v₂ : U r ) → (l ● r ` loc) ⊢ PairU u₁ v₁ >ˡ PairU u₂ v₂ → (l ● r ` loc) ⊢ PairU u₁ v₁ >ᵍ PairU u₂ v₂ 
    from-ev u₁ u₂ v₁ v₂ (seq₁ u₁>ˡu₂) with robust-l
    ... | robust rob-l-ev = seq₁ (proj₂ (rob-l-ev u₁ u₂) u₁>ˡu₂) 
    from-ev u₁ u₂ v₁ v₂ (seq₂ u₁≡u₂ v₁>ˡv₂) with robust-r
    ... | robust rob-r-ev = seq₂ u₁≡u₂ (proj₂ (rob-r-ev v₁ v₂) v₁>ˡv₂ )
lne→robust {l + r ` loc} (lne-+ ε∉l lne-l lne-r) =  robust {l + r ` loc} prf
  where
    robust-l : Robust l
    robust-l = lne→robust {l} lne-l

    robust-r : Robust r
    robust-r = lne→robust {r} lne-r

    prf : (v₁ v₂ : U (l + r ` loc)) →
      ((l + r ` loc) ⊢ v₁ >ᵍ v₂ → (l + r ` loc) ⊢ v₁ >ˡ v₂) ×
      ((l + r ` loc) ⊢ v₁ >ˡ v₂ → (l + r ` loc) ⊢ v₁ >ᵍ v₂)
    prf (LeftU u₁) (LeftU u₂) = to-ev , from-ev
      where
        ¬proj₁flat-u₁≡[] : ¬ proj₁ ( flat u₁ ) ≡ []
        ¬proj₁flat-u₁≡[] proj₁flat-u₁≡[] = (ε∉r→¬ε∈r ε∉l) (proj₁flat-v≡[]→ε∈r proj₁flat-u₁≡[])
        to-ev : (l + r ` loc) ⊢ LeftU u₁ >ᵍ LeftU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ˡ LeftU u₂
        to-ev (choice-ll u₁>ᵍu₂) with robust-l | proj₁ (flat u₂) in proj₁flat-u₂-eq 
        ... | robust rob-l-ev  | [] = Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-u₂-eq) (ε∉r→¬ε∈r ε∉l) 
        ... | robust rob-l-ev  | c ∷ cs = choice-ll-notempty ¬proj₁flat-u₁≡[]  ¬proj₁flat-u₂≡[]  (proj₁ (rob-l-ev u₁ u₂) u₁>ᵍu₂ )
          where 
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[] 
        from-ev :  (l + r ` loc) ⊢ LeftU u₁ >ˡ LeftU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ᵍ LeftU u₂
        from-ev (choice-ll-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) = Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-u₂≡[]) (ε∉r→¬ε∈r ε∉l)
        from-ev (choice-ll-bothempty proj₁flat-u₁≡[] proj₁flat-u₂≡[] _ ) = Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-u₁≡[]) (ε∉r→¬ε∈r ε∉l)
        from-ev (choice-ll-notempty ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[] u₁>ˡu₂ ) with robust-l
        ... | robust rob-l-ev = choice-ll ((proj₂ (rob-l-ev u₁ u₂) u₁>ˡu₂ ))
    prf (LeftU u₁) (RightU u₂) = to-ev , from-ev
      where
        to-ev : (l + r ` loc) ⊢ LeftU u₁ >ᵍ RightU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ˡ RightU u₂
        to-ev choice-lr with proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat u₂) in proj₁flat-u₂-eq
        ... | []     | _   = Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq) (ε∉r→¬ε∈r ε∉l)  
        ... | c ∷ cs | []  = choice-lr-empty  ¬proj₁flat-u₁≡[] proj₁flat-u₂-eq
          where 
            ¬proj₁flat-u₁≡[] : ¬ proj₁ ( flat u₁ ) ≡ []
            ¬proj₁flat-u₁≡[] rewrite proj₁flat-u₁-eq  = λ proj₁flat-u₁≡[] → ¬∷≡[] proj₁flat-u₁≡[]
        ... | c ∷ cs | c' ∷ cs'  = choice-lr-notempty  ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[]
          where 
            ¬proj₁flat-u₁≡[] : ¬ proj₁ ( flat u₁ ) ≡ []
            ¬proj₁flat-u₁≡[] rewrite proj₁flat-u₁-eq  = λ proj₁flat-u₁≡[] → ¬∷≡[] proj₁flat-u₁≡[]
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[] 
        from-ev : (l + r ` loc) ⊢ LeftU u₁ >ˡ RightU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ᵍ RightU u₂
        from-ev = λ z → choice-lr  
    prf (RightU u₁) (LeftU u₂) = to-ev , from-ev
      where
        to-ev : (l + r ` loc) ⊢ RightU u₁ >ᵍ LeftU u₂ → (l + r ` loc) ⊢ RightU u₁ >ˡ LeftU u₂
        to-ev = λ () 
        from-ev : (l + r ` loc) ⊢ RightU u₁ >ˡ LeftU u₂ → (l + r ` loc) ⊢ RightU u₁ >ᵍ LeftU u₂
        from-ev (choice-rl-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) =  Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-u₂≡[]) (ε∉r→¬ε∈r ε∉l)    
    prf (RightU u₁) (RightU u₂) = to-ev , from-ev
      where 
        to-ev : (l + r ` loc) ⊢ RightU u₁ >ᵍ RightU u₂ → (l + r ` loc) ⊢ RightU u₁ >ˡ RightU u₂
        to-ev (choice-rr u₁>ᵍu₂) with robust-r | proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat u₂) in proj₁flat-u₂-eq
        ... | robust rob-r-ev | []     |     []    = choice-rr-bothempty proj₁flat-u₁-eq proj₁flat-u₂-eq (proj₁ (rob-r-ev u₁ u₂) u₁>ᵍu₂ )
        ... | robust rob-r-ev | c ∷ cs | c' ∷ cs'  = choice-rr-notempty ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[] (proj₁ (rob-r-ev u₁ u₂) u₁>ᵍu₂ )
          where
            ¬proj₁flat-u₁≡[] : ¬ proj₁ ( flat u₁ ) ≡ []
            ¬proj₁flat-u₁≡[] rewrite proj₁flat-u₁-eq  = λ proj₁flat-u₁≡[] → ¬∷≡[] proj₁flat-u₁≡[]
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[]           
        ... | robust rob-r-ev | c ∷ cs |     []    = choice-rr-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂-eq  
          where
            ¬proj₁flat-u₁≡[] : ¬ proj₁ ( flat u₁ ) ≡ []
            ¬proj₁flat-u₁≡[] rewrite proj₁flat-u₁-eq  = λ proj₁flat-u₁≡[] → ¬∷≡[] proj₁flat-u₁≡[]
        ... | robust rob-r-ev | []     | c' ∷ cs'  = Nullary.contradiction u₁>ᵍu₂ (lne→¬[]>ᵍ∷ lne-r u₁ u₂  proj₁flat-u₁-eq  ¬proj₁flat-u₂≡[]) -- can't be proven, we replace this lemma by u>ᵍv→¬v>ᵍu and lne→∷>ᵍ[]
          where 
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[]           

        from-ev : (l + r ` loc) ⊢ RightU u₁ >ˡ RightU u₂ → (l + r ` loc) ⊢ RightU u₁ >ᵍ RightU u₂
        from-ev (choice-rr-bothempty  proj₁flat-u₁≡[] proj₁flat-u₂≡[] u₁>ˡu₂)  with robust-r
        ... | robust rob-r-ev = choice-rr (proj₂ (rob-r-ev u₁ u₂) u₁>ˡu₂ ) 
        from-ev (choice-rr-notempty  ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[] u₁>ˡu₂)  with robust-r
        ... | robust rob-r-ev = choice-rr (proj₂ (rob-r-ev u₁ u₂) u₁>ˡu₂ ) 
        from-ev (choice-rr-empty  ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[])  with robust-r
        ... | robust rob-r-ev = choice-rr (lne→∷>ᵍ[] lne-r u₁ u₂ ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[])  -- how ? 
lne→robust {r * ε∉r ` loc} (lne-* lne-r) =  robust {r * ε∉r ` loc} prf
  where
    robust-r : Robust r
    robust-r = lne→robust {r} lne-r


    prf : (v₁ v₂ : U (r * ε∉r ` loc)) →
      ((r * ε∉r ` loc) ⊢ v₁ >ᵍ v₂ → (r * ε∉r ` loc) ⊢ v₁ >ˡ v₂) ×
      ((r * ε∉r ` loc) ⊢ v₁ >ˡ v₂ → (r * ε∉r ` loc) ⊢ v₁ >ᵍ v₂)
    prf (ListU []) (ListU []) = (λ ()) , λ () 
    prf (ListU []) (ListU (u ∷ us)) = (λ ()) , λ ()
    prf (ListU (v ∷ vs)) (ListU []) = (λ z → star-cons-nil) , λ z → star-cons-nil
    prf (ListU (v ∷ vs)) (ListU (u ∷ us)) = to-ev , from-ev
      where
        to-ev : (r * ε∉r ` loc) ⊢ ListU (v ∷ vs) >ᵍ ListU (u ∷ us) →
                (r * ε∉r ` loc) ⊢ ListU (v ∷ vs) >ˡ ListU (u ∷ us)
        to-ev (star-head v>ᵍu) with robust-r
        ... | robust rob-r-ev = star-head (proj₁ (rob-r-ev v u) v>ᵍu)
        to-ev (star-tail v≡u list-vs>ᵍlist-us)  = star-tail v≡u (proj₁ (prf (ListU vs) (ListU us)) list-vs>ᵍlist-us) 
        
        from-ev : (r * ε∉r ` loc) ⊢ ListU (v ∷ vs) >ˡ ListU (u ∷ us) → 
                  (r * ε∉r ` loc) ⊢ ListU (v ∷ vs) >ᵍ ListU (u ∷ us)
        from-ev (star-head v>ˡu) with robust-r
        ... | robust rob-r-ev = star-head (proj₂ (rob-r-ev v u) v>ˡu)
        from-ev (star-tail v≡u list-vs>ˡlist-us)  = star-tail v≡u (proj₂ (prf (ListU vs) (ListU us)) list-vs>ˡlist-us) 
        
```
