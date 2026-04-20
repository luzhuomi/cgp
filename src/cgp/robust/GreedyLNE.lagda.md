```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.GreedyLNE where

import cgp.RE as RE
open RE using (RE;  ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;   ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ; first ; ε∉r→¬first-r≡[] )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU;  unListU ; listU∘unListU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU ; r-∃u)


import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; Flat-[] ; flat-[] ;  mkAllEmptyU≢[] ; proj₁flat-v≡[]→ε∈r )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ) 



import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming ( _⊢_>_  to  _⊢_>ᵍ_
  ; >→¬≡ to >ᵍ→¬≡
  ; u>v→¬v>u to u>ᵍv→¬v>ᵍu
  )

import cgp.greedy.PartialDerivative as GreedyPD
open GreedyPD renaming ( parseAll[_,_] to parseAllᵍ[_,_] ; parseAll-sound to parseAllᵍ-sound ; parseAll-complete to parseAllᵍ-complete ) 

import cgp.lne.Order as LNEOrder
open LNEOrder renaming ( _⊢_>_  to  _⊢_>ˡ_
  ; >→¬≡ to >ˡ→¬≡
  )

import cgp.lne.PartialDerivative as LNEPD
open LNEPD renaming ( parseAll[_,_] to parseAllˡ[_,_]
  ; parseAll-sound to parseAllˡ-sound
  ; parseAll-complete to parseAllˡ-complete
--   ; parseAll-r-w≡[]→¬w∈⟦r⟧ to parseAllˡ-r-w≡[]→¬w∈⟦r⟧ 
     ) 


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



### A sufficient condition, Left-not-nullable form






```agda

data LNN : RE → Set where
  lnn-ε  : LNN ε
  lnn-$  : ∀ { c : Char } { loc : ℕ } → LNN ($ c ` loc)
  lnn-●  : ∀ { l r : RE } { loc : ℕ }
    → LNN l
    → LNN r
    ----------------------------------
    → LNN ( l ● r ` loc )
  lnn-+  : ∀ { l r : RE } { loc : ℕ }
    → ε∉ l 
    → LNN l  
    → LNN r
    ---------------------------------
    → LNN ( l + r ` loc )
  lnn-*  : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → LNN r
    --------------------------------
    → LNN ( r * ε∉r ` loc )



-- the follwoing two sub lemmas should be moved to ParseTree.lagda.md 
¬proj₁flat-cons≡[] : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { u : U r } { us : List (U r) }
    → ¬ ( proj₁ (flat (ListU {r} {ε∉r} {loc} (u ∷ us))) ≡ [] )
¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us} proj₁flat-list-u∷us≡[] = (ε∉r→¬ε∈r ε∉r) (proj₁flat-v≡[]→ε∈r proj₁flat-u≡[])
  where
    proj₁flat-u++proj₁flat-list-us≡[] : proj₁ (flat u) ++ proj₁ (flat (ListU {r} {ε∉r} {loc} us)) ≡ []
    proj₁flat-u++proj₁flat-list-us≡[] rewrite  proj₁flat-list-u∷us≡[]  = refl
    proj₁flat-u≡[] :  proj₁ (flat u) ≡ []
    proj₁flat-u≡[] = ++-conicalˡ ( proj₁ (flat u) ) (proj₁ (flat (ListU {r} {ε∉r} {loc} us))) proj₁flat-u++proj₁flat-list-us≡[]

proj₁flat-nil≡[] : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → proj₁ (flat (ListU {r} {ε∉r} {loc} [] )) ≡ []
proj₁flat-nil≡[] {r} {ε∉r} {loc} = refl 
    

{-
can't be proven 
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






lnn-proj₁flat≡[]→refl : ∀ { r : RE } { ε∈r : ε∈ r } { u v : U r }
    → LNN r 
    → proj₁ (flat u) ≡ []
    → proj₁ (flat v) ≡ []
    ------------------------
    → u ≡ v
lnn-proj₁flat≡[]→refl {ε}              {ε∈ε} {EmptyU} {EmptyU} lnn-ε refl refl = refl
lnn-proj₁flat≡[]→refl {r * ε∉r ` loc}  {ε∈*} {ListU []}       {ListU []} (lnn-* lnn-r) refl refl = refl 
lnn-proj₁flat≡[]→refl {r * ε∉r ` loc}  {ε∈*} {ListU (u ∷ us)} {_}        (lnn-* lnn-r) proj₁flat-list-uus≡[] _ = Nullary.contradiction   proj₁flat-list-uus≡[] (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us})
lnn-proj₁flat≡[]→refl {r * ε∉r ` loc}  {ε∈*} {_} {ListU (u ∷ us)}        (lnn-* lnn-r) _ proj₁flat-list-uus≡[] = Nullary.contradiction   proj₁flat-list-uus≡[] (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us})
lnn-proj₁flat≡[]→refl {l ● r ` loc}  {ε∈ ε∈l ● ε∈r } {PairU u₁ u₂}  {PairU v₁ v₂} (lnn-● lnn-l lnn-r) proj₁flat-pair-u₁u₂≡[] proj₁flat-pair-v₁v₂≡[] = prf  
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
    u₁≡v₁ = lnn-proj₁flat≡[]→refl {l} {ε∈l} {u₁} {v₁} lnn-l proj₁flat-u₁≡[] proj₁flat-v₁≡[]
    u₂≡v₂ : u₂ ≡ v₂
    u₂≡v₂ = lnn-proj₁flat≡[]→refl {r} {ε∈r} {u₂} {v₂} lnn-r proj₁flat-u₂≡[] proj₁flat-v₂≡[]

    prf : PairU {l} {r} {loc} u₁ u₂ ≡ PairU {l} {r} {loc}  v₁ v₂
    prf rewrite u₁≡v₁ | u₂≡v₂ = refl 
lnn-proj₁flat≡[]→refl {l + r ` loc}  {ε∈ ε∈l + ε∈r } {_}  {_}  (lnn-+ ε∉l lnn-l lnn-r) _ _ = Nullary.contradiction  ε∈l (ε∉r→¬ε∈r ε∉l)
lnn-proj₁flat≡[]→refl {l + r ` loc}  {ε∈ ε∈l <+ ε∉r } {_}  {_}  (lnn-+ ε∉l lnn-l lnn-r) _ _ = Nullary.contradiction  ε∈l (ε∉r→¬ε∈r ε∉l)
lnn-proj₁flat≡[]→refl {l + r ` loc}  {ε∈ ε∉l +> ε∈r } {LeftU v}  {_}  (lnn-+ ε∉l' lnn-l lnn-r) proj₁flat-left-v≡[] _ =  Nullary.contradiction (proj₁flat-v≡[]→ε∈r  proj₁flat-left-v≡[]) (ε∉r→¬ε∈r ε∉l)
lnn-proj₁flat≡[]→refl {l + r ` loc}  {ε∈ ε∉l +> ε∈r } {_} {LeftU v}  (lnn-+ ε∉l' lnn-l lnn-r) _  proj₁flat-left-v≡[] =   Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-left-v≡[]) (ε∉r→¬ε∈r ε∉l)
lnn-proj₁flat≡[]→refl {l + r ` loc}  {ε∈ ε∉l +> ε∈r } {RightU u} {RightU v}  (lnn-+ ε∉l' lnn-l lnn-r) proj₁flat-right-u≡[]  proj₁flat-right-v≡[] = right-u≡right-v
  where
    u≡v : u ≡ v
    u≡v =  lnn-proj₁flat≡[]→refl {r} {ε∈r} {u} {v} lnn-r proj₁flat-right-u≡[]  proj₁flat-right-v≡[]
    right-u≡right-v : RightU {l} {r} {loc} u ≡ RightU {l} {r} {loc} v
    right-u≡right-v rewrite u≡v = refl 


{-
-- can't be proven
lnn→¬[]>ᵍ∷ : ∀ { r : RE } 
    → LNN r
    → ( u₁ : U r )
    → ( u₂ : U r )
    → proj₁ (flat u₁) ≡ []
    → ¬ proj₁ (flat u₂) ≡ []
    -------------------------
    → ¬ r ⊢ u₁ >ᵍ u₂
lnn→¬[]>ᵍ∷ {ε} lnn-ε          EmptyU      EmptyU      proj₁flat-empty≡[] ¬proj₁flat-empty≡[]               = Nullary.contradiction proj₁flat-empty≡[] ¬proj₁flat-empty≡[]
lnn→¬[]>ᵍ∷ {$ c ` loc} lnn-$  (LetterU _) (LetterU _) proj₁flat-letter≡[] ¬proj₁flat-letter≡[]             = Nullary.contradiction proj₁flat-letter≡[] ¬proj₁flat-letter≡[]
lnn→¬[]>ᵍ∷ {r * ε∉r ` loc} (lnn-* lnn-r) (ListU []) (ListU []) proj₁flat-nil≡[] ¬proj₁flat-nil≡[]          = Nullary.contradiction proj₁flat-nil≡[] ¬proj₁flat-nil≡[]
lnn→¬[]>ᵍ∷ {r * ε∉r ` loc} (lnn-* lnn-r) (ListU []) (ListU ( u ∷ us )) proj₁flat-nil≡[] ¬proj₁flat-cons≡[] = λ ()
lnn→¬[]>ᵍ∷ {r * ε∉r ` loc} (lnn-* lnn-r) (ListU ( v ∷ vs )) _  proj₁flat-cons-v-vs≡[] _  = Nullary.contradiction proj₁flat-cons-v-vs≡[] (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs})
lnn→¬[]>ᵍ∷ {l + r   ` loc} (lnn-+ ε∉l lnn-l lnn-r) (LeftU u) _ proj₁flat-left-u≡[] _     =  Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-left-u≡[]) (ε∉r→¬ε∈r ε∉l)
lnn→¬[]>ᵍ∷ {l + r   ` loc} (lnn-+ ε∉l lnn-l lnn-r) (RightU u) (LeftU v) proj₁flat-left-u≡[] ¬proj₁flat-right-v≡[] =  λ()
lnn→¬[]>ᵍ∷ {l + r   ` loc} (lnn-+ ε∉l lnn-l lnn-r) (RightU u) (RightU v) proj₁flat-right-u≡[] ¬proj₁flat-right-v≡[] (choice-rr u>ᵍv) = Nullary.contradiction u>ᵍv (lnn→¬[]>ᵍ∷  {r} lnn-r u v proj₁flat-right-u≡[] ¬proj₁flat-right-v≡[] )
lnn→¬[]>ᵍ∷ {l ● r   ` loc} (lnn-● lnn-l lnn-r) (PairU u₁ u₂) (PairU v₁ v₂)  proj₁flat-pair-u₁u₂≡[] ¬proj₁flat-pair-v₁v₂≡[] = prf  -- how ? can't be proven?
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
        u₁≡v₁ = lnn-proj₁flat≡[]→refl {l} {proj₁flat-v≡[]→ε∈r proj₁flat-v₁-eq} {u₁} {v₁} lnn-l proj₁flat-u₁≡[]  proj₁flat-v₁-eq 
        ev : ¬ (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂
        ev rewrite u₁≡v₁ = λ pair-u₁u₂>pair-v₁v₂ → {!!} 
  -- we can use lnn-proj₁flat≡[]→refl 
  -- we replace this lemma by u>ᵍv→¬v>ᵍu and lnn→∷>ᵍ[]

-}


lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[]  : ∀ { r : RE }
    → LNN r
    → ( u : U r )
    → ( v : U r )
    → r ⊢ u >ᵍ v
    -------------------------
    → ( proj₁ (flat u) ≡ [] × proj₁ (flat v) ≡ [] ) ⊎
      ( ( ¬ proj₁ (flat u) ≡ [] × ¬ proj₁ (flat v) ≡ [] ) ⊎
        ( ¬ proj₁ (flat u) ≡ [] × proj₁ (flat v) ≡ [] ) )
lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {ε}             lnn-ε EmptyU EmptyU = λ()
lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {$ c ` loc}     lnn-$ (LetterU _) (LetterU _) = λ()
lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (lnn-* lnn-r) (ListU []) (ListU []) = λ()
lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (lnn-* lnn-r) (ListU []) (ListU ( v ∷ vs) ) = λ()
lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (lnn-* lnn-r) (ListU (u ∷ us )) (ListU []) star-cons-nil = inj₂ (inj₂ (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us} , proj₁flat-nil≡[] {r} {ε∉r} {loc} ) )
lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (lnn-* lnn-r) (ListU (u ∷ us )) (ListU (v ∷ vs)) _       = inj₂ (inj₁ (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us} , ¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs} ) )
lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {l ● r ` loc}   (lnn-● lnn-l lnn-r) (PairU u₁ u₂) (PairU v₁ v₂)
  with proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat v₁) in proj₁flat-v₁-eq
... | []        |  []  = prf 
  where
    u₁≡v₁ : u₁ ≡ v₁ 
    u₁≡v₁ = lnn-proj₁flat≡[]→refl {l} {proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq} {u₁} {v₁} lnn-l proj₁flat-u₁-eq proj₁flat-v₁-eq
    prf : (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂ →
      ( proj₁ (flat u₂) ≡ [] × proj₁ (flat v₂) ≡ [] ) ⊎
      ( ( ¬ proj₁ (flat u₂) ≡ [] × ¬ proj₁ (flat v₂) ≡ [] ) ⊎
        ( ¬ proj₁ (flat u₂) ≡ [] × proj₁ (flat v₂) ≡ [] ) )
    prf (seq₂ refl u₂>ᵍv₂ ) with lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r} lnn-r u₂ v₂ u₂>ᵍv₂
    ... | inj₁ ( proj₁flat-u₂≡[] , proj₁flat-v₂≡[] ) = inj₁ (proj₁flat-u₂≡[] , proj₁flat-v₂≡[])
    ... | inj₂ ( inj₁ ( ¬proj₁flat-u₂≡[] , ¬proj₁flat-v₂≡[] ) ) = inj₂ (inj₁ (¬proj₁flat-u₂≡[] , ¬proj₁flat-v₂≡[]))
    ... | inj₂ ( inj₂ ( ¬proj₁flat-u₂≡[] , proj₁flat-v₂≡[] ) ) = inj₂ (inj₂ (¬proj₁flat-u₂≡[] , proj₁flat-v₂≡[])) 
    prf (seq₁ u₁>ᵍv₁) =  Nullary.contradiction u₁≡v₁ (>ᵍ→¬≡ {l} {u₁} {v₁} u₁>ᵍv₁) 
... | []        |  (c ∷ cs)  = prf 
  where
    prf : (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂ →
      ( proj₁ (flat u₂) ≡ [] × ( (c ∷ cs) ++ proj₁ (flat v₂) ≡ [] ) ) ⊎
      ( ( ¬ proj₁ (flat u₂) ≡ [] × ¬ ( (c ∷ cs) ++ proj₁ (flat v₂)) ≡ [] ) ⊎
        ( ¬ proj₁ (flat u₂) ≡ [] × ( (c ∷ cs) ++ proj₁ (flat v₂)) ≡ [] ) )
    prf (seq₂ u₁≡v₁ u₂>ᵍv₂)  = Nullary.contradiction proj₁flatu₁≡proj₁flatv₁ ¬proj₁flatu₁≡proj₁flatv₁
      where
        proj₁flatu₁≡proj₁flatv₁ : proj₁ (flat u₁) ≡ proj₁ (flat v₁)
        proj₁flatu₁≡proj₁flatv₁ rewrite u₁≡v₁ = refl
        ¬proj₁flatu₁≡proj₁flatv₁ : ¬ proj₁ (flat u₁) ≡ proj₁ (flat v₁)
        ¬proj₁flatu₁≡proj₁flatv₁ rewrite  proj₁flat-u₁-eq |  proj₁flat-v₁-eq = λ ()
    prf (seq₁ u₁>ᵍv₁) with lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {l} lnn-l u₁ v₁ u₁>ᵍv₁
    ... | inj₁ ( proj₁flat-u₁≡[] , proj₁flat-v₁≡[] ) = Nullary.contradiction proj₁flat-v₁≡[] ¬proj₁flat-v₁≡[]
      where
        ¬proj₁flat-v₁≡[] : ¬ proj₁ (flat v₁) ≡ [] 
        ¬proj₁flat-v₁≡[] rewrite  proj₁flat-v₁-eq = λ x → ¬∷≡[] x
    ... | inj₂ ( inj₁ ( ¬proj₁flat-u₁≡[] , ¬proj₁flat-v₁≡[] ) ) =  Nullary.contradiction  proj₁flat-u₁-eq  ¬proj₁flat-u₁≡[]
    ... | inj₂ ( inj₂ ( ¬proj₁flat-u₁≡[] , proj₁flat-v₁≡[] ) )  =  Nullary.contradiction  proj₁flat-u₁-eq  ¬proj₁flat-u₁≡[]
... | (c ∷ cs)  | [] = prf
  where 
    prf : (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂ →
      ( ((c ∷ cs) ++ proj₁  (flat u₂) ) ≡ [] × ( proj₁ (flat v₂) ≡ [] ) ) ⊎
      ( ( ¬ ((c ∷ cs) ++ proj₁ (flat u₂) ≡ [] ) × ¬ proj₁ (flat v₂) ≡ [] ) ⊎
        ( ¬ ((c ∷ cs) ++ proj₁ (flat u₂) ≡ [] ) × proj₁ (flat v₂) ≡ [] ) )
    prf (seq₂ u₁≡v₁ u₂>ᵍv₂)  = Nullary.contradiction proj₁flatu₁≡proj₁flatv₁ ¬proj₁flatu₁≡proj₁flatv₁ 
      where
        proj₁flatu₁≡proj₁flatv₁ : proj₁ (flat u₁) ≡ proj₁ (flat v₁)
        proj₁flatu₁≡proj₁flatv₁ rewrite u₁≡v₁ = refl
        ¬proj₁flatu₁≡proj₁flatv₁ : ¬ proj₁ (flat u₁) ≡ proj₁ (flat v₁)
        ¬proj₁flatu₁≡proj₁flatv₁ rewrite  proj₁flat-u₁-eq |  proj₁flat-v₁-eq = λ ()
    prf  (seq₁ u₁>ᵍv₁) with lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {l} lnn-l u₁ v₁ u₁>ᵍv₁
    ... | inj₁ ( proj₁flat-u₁≡[] , proj₁flat-v₁≡[] ) =  Nullary.contradiction proj₁flat-u₁≡[]  ¬proj₁flat-u₁≡[]  
      where
        ¬proj₁flat-u₁≡[] : ¬ proj₁ (flat u₁) ≡ [] 
        ¬proj₁flat-u₁≡[] rewrite  proj₁flat-u₁-eq = λ x → ¬∷≡[] x
    ... | inj₂ ( inj₁ (  ¬proj₁flat-u₁≡[] , ¬proj₁flat-v₁≡[] ) ) =  Nullary.contradiction  proj₁flat-v₁-eq  ¬proj₁flat-v₁≡[]
    ... | inj₂ ( inj₂ (  ¬proj₁flat-u₁≡[] , proj₁flat-v₁≡[] ) ) with proj₁ (flat v₂) in proj₁flat-v₂-eq 
    ...                                                         |  [] =  inj₂ (inj₂ ( ¬c∷cs++proj₁flatu₂≡[] , refl ))
                                                                where
                                                                  ¬c∷cs++proj₁flatu₂≡[] : ¬ (c ∷ cs) ++ proj₁ (flat u₂) ≡ []
                                                                  ¬c∷cs++proj₁flatu₂≡[] = λ x → ¬∷≡[] x
    ...                                                         | c' ∷ cs' = inj₂ (inj₁  ( ¬c∷cs++proj₁flatu₂≡[] , λ () ) )                                                                
                                                                where
                                                                  ¬c∷cs++proj₁flatu₂≡[] : ¬ (c ∷ cs) ++ proj₁ (flat u₂) ≡ []
                                                                  ¬c∷cs++proj₁flatu₂≡[] = λ x → ¬∷≡[] x
... | (c ∷ cs)  | (c' ∷ cs') = prf                                                                  
  where 
    prf : (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂ →
      ( ((c ∷ cs) ++ proj₁  (flat u₂) ) ≡ [] × ((c' ∷ cs') ++  proj₁ (flat v₂) ≡ [] ) )  ⊎
      ( ( ¬ ((c ∷ cs) ++ proj₁ (flat u₂) ≡ [] ) × ¬ ((c' ∷ cs') ++ proj₁ (flat v₂) ≡ [] ) ) ⊎
        ( ¬ ((c ∷ cs) ++ proj₁ (flat u₂) ≡ [] ) × ((c' ∷ cs') ++ proj₁ (flat v₂) ≡ [] ) ) )
    prf _ = inj₂ (inj₁ ( (λ ())  ,  λ () ) )

lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {l + r ` loc}   (lnn-+ ε∉l lnn-l lnn-r) (LeftU u) (LeftU v) (choice-ll u>ᵍv) =  lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] lnn-l u v u>ᵍv
lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {l + r ` loc}   (lnn-+ ε∉l lnn-l lnn-r) (RightU u) (RightU v) (choice-rr u>ᵍv) = lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] lnn-r u v u>ᵍv
lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {l + r ` loc}   (lnn-+ ε∉l lnn-l lnn-r) (RightU u) (LeftU v) = λ () 
lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {l + r ` loc}   (lnn-+ ε∉l lnn-l lnn-r) (LeftU u) (RightU v) choice-lr
  with proj₁ (flat u) in proj₁flat-u-eq | proj₁ (flat v) in proj₁flat-v-eq
... | []       | _          = Nullary.contradiction (proj₁flat-v≡[]→ε∈r  proj₁flat-u-eq)  (ε∉r→¬ε∈r ε∉l)
... | (c ∷ cs) | []         = inj₂ (inj₂ ( (λ ()) , refl ) )
... | (c ∷ cs) | (c' ∷ cs') = inj₂ (inj₁ ( (λ ()) , λ () ) ) 


lnn-u>ᵍv→¬u≡[]×v≢[] : ∀ { r : RE }
    → LNN r
    → ( u : U r )
    → ( v : U r )
    → r ⊢ u >ᵍ v
    ----------------------------------------------------
    → ¬ ( proj₁ (flat u) ≡ [] × ¬ proj₁ (flat v) ≡ [] )

lnn-u>ᵍv→¬u≡[]×v≢[] {r} lnn-r u v u>ᵍv  (proj₁flat-u≡[] , ¬proj₁flat-v≡[])  with lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r} lnn-r u v u>ᵍv
... | inj₁ (proj₁flat-u≡[] ,  proj₁-flat-v≡[] ) =  ¬proj₁flat-v≡[] proj₁-flat-v≡[]
... | inj₂ (inj₁ (¬proj₁flat-u≡[] ,  ¬proj₁-flat-v≡[] ) ) = ¬proj₁flat-u≡[] proj₁flat-u≡[]
... | inj₂ (inj₂ (¬proj₁flat-u≡[] ,  proj₁-flat-v≡[] ) )  = ¬proj₁flat-v≡[] proj₁-flat-v≡[] 



lnn→∷>ᵍ[] : ∀ { r : RE }
    → LNN r
    → ( u₁ : U r )
    → ( u₂ : U r )
    → ¬ proj₁ (flat u₁) ≡ []
    → proj₁ (flat u₂) ≡ []
    ------------------------
    → r ⊢ u₁ >ᵍ u₂
lnn→∷>ᵍ[] {ε} lnn-ε          EmptyU      EmptyU      ¬proj₁flat-empty≡[]  proj₁flat-empty≡[]              = Nullary.contradiction proj₁flat-empty≡[] ¬proj₁flat-empty≡[]
lnn→∷>ᵍ[] {$ c ` loc} lnn-$  (LetterU _) (LetterU _) ¬proj₁flat-letter≡[] proj₁flat-letter≡[]             = Nullary.contradiction proj₁flat-letter≡[] ¬proj₁flat-letter≡[]
lnn→∷>ᵍ[] {r * ε∉r ` loc} (lnn-* lnn-r) (ListU [])  _                       ¬proj₁flat-nil≡[] _           = Nullary.contradiction (proj₁flat-nil≡[]  {r} {ε∉r} {loc})  ¬proj₁flat-nil≡[]
lnn→∷>ᵍ[] {r * ε∉r ` loc} (lnn-* lnn-r) (ListU ( u ∷ us )) (ListU ( v ∷ vs))  ¬proj₁flat-cons-uus≡[] proj₁flat-cons-vvs≡[] =  Nullary.contradiction proj₁flat-cons-vvs≡[] (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs})
lnn→∷>ᵍ[] {r * ε∉r ` loc} (lnn-* lnn-r) (ListU ( u ∷ us )) (ListU [])  ¬proj₁flat-cons-uus≡[] proj₁flat-nil≡[]     = star-cons-nil
lnn→∷>ᵍ[] {l + r   ` loc} (lnn-+ ε∉l lnn-l lnn-r) (LeftU u) (LeftU v) ¬proj₁flat-left-u≡[] proj₁flat-left-v≡[]     = choice-ll (lnn→∷>ᵍ[] {l} lnn-l u v ¬proj₁flat-left-u≡[] proj₁flat-left-v≡[])
lnn→∷>ᵍ[] {l + r   ` loc} (lnn-+ ε∉l lnn-l lnn-r) (RightU u) (RightU v) ¬proj₁flat-right-u≡[] proj₁flat-right-v≡[] = choice-rr (lnn→∷>ᵍ[] {r} lnn-r u v ¬proj₁flat-right-u≡[] proj₁flat-right-v≡[])
lnn→∷>ᵍ[] {l + r   ` loc} (lnn-+ ε∉l lnn-l lnn-r) (LeftU u) (RightU v) ¬proj₁flat-left-u≡[] proj₁flat-right-v≡[] = choice-lr 
lnn→∷>ᵍ[] {l + r   ` loc} (lnn-+ ε∉l lnn-l lnn-r) (RightU u) (LeftU v) ¬proj₁flat-right-u≡[] proj₁flat-left-v≡[] = Nullary.contradiction (proj₁flat-v≡[]→ε∈r proj₁flat-left-v≡[]) (ε∉r→¬ε∈r ε∉l)
lnn→∷>ᵍ[] {l ● r   ` loc} (lnn-● lnn-l lnn-r) (PairU u₁ u₂) (PairU v₁ v₂)  ¬proj₁flat-pair-u₁u₂≡[] proj₁flat-v₁v₂≡[] = prf 
  where
    proj₁flat-v₁≡[] : proj₁ (flat v₁) ≡ []
    proj₁flat-v₁≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) proj₁flat-v₁v₂≡[]
    proj₁flat-v₂≡[] : proj₁ (flat v₂) ≡ []
    proj₁flat-v₂≡[] = ++-conicalʳ (proj₁ (flat v₁)) (proj₁ (flat v₂)) proj₁flat-v₁v₂≡[]

    prf : (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂
    prf with proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat u₂) in proj₁flat-u₂-eq 
    ... | []     |  []       = Nullary.contradiction refl ¬proj₁flat-pair-u₁u₂≡[] 
    ... | []     |  c' ∷ cs' = seq₂ u₁≡v₁ u₂>ᵍv₂ 
      where
        u₁≡v₁ : u₁ ≡ v₁
        u₁≡v₁ = lnn-proj₁flat≡[]→refl {l} {proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq} {u₁} {v₁} lnn-l  proj₁flat-u₁-eq proj₁flat-v₁≡[]
        ¬proj₁flat-u₂≡[] : ¬ proj₁ (flat u₂) ≡ []
        ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq = λ proj₁flat-u₂≡[] →  ¬∷≡[] proj₁flat-u₂≡[] 
        u₂>ᵍv₂ : r  ⊢ u₂ >ᵍ v₂
        u₂>ᵍv₂ = lnn→∷>ᵍ[] {r} lnn-r u₂ v₂  ¬proj₁flat-u₂≡[] proj₁flat-v₂≡[] 
    ... | c ∷ cs |  cs' = seq₁ u₁>ᵍv₁
      where 
        ¬proj₁flat-u₁≡[] : ¬ proj₁ (flat u₁) ≡ []
        ¬proj₁flat-u₁≡[] rewrite proj₁flat-u₁-eq = λ proj₁flat-u₁≡[] →  ¬∷≡[] proj₁flat-u₁≡[] 
        u₁>ᵍv₁ : l  ⊢ u₁ >ᵍ v₁
        u₁>ᵍv₁ = lnn→∷>ᵍ[] {l} lnn-l u₁ v₁ ¬proj₁flat-u₁≡[] proj₁flat-v₁≡[] 


{-# TERMINATING #-}
lnn→robust : ∀ { r : RE }
  → LNN r
  → Robust r 
lnn→robust {ε}           lnn-ε = robust λ v₁ v₂ → ( ( λ() ) , (λ ()) )
lnn→robust {$ c ` loc}   lnn-$ = robust λ v₁ v₂ → ( ( λ() ) , (λ ()) ) 
lnn→robust {l ● r ` loc} (lnn-● lnn-l lnn-r) = robust {l ● r ` loc} λ { (PairU u₁ v₁) (PairU u₂ v₂) → to-ev u₁ u₂ v₁ v₂ , from-ev  u₁ u₂ v₁ v₂ }
  where
    robust-r : Robust r
    robust-r = lnn→robust {r} lnn-r
    
    robust-l : Robust l
    robust-l = lnn→robust {l} lnn-l
    
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
lnn→robust {l + r ` loc} (lnn-+ ε∉l lnn-l lnn-r) =  robust {l + r ` loc} prf
  where
    robust-l : Robust l
    robust-l = lnn→robust {l} lnn-l

    robust-r : Robust r
    robust-r = lnn→robust {r} lnn-r

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
        ... | robust rob-r-ev | []     | c' ∷ cs'  =  Nullary.contradiction ( proj₁flat-u₁-eq ,  ¬proj₁flat-u₂≡[] ) (lnn-u>ᵍv→¬u≡[]×v≢[] {r} lnn-r u₁ u₂  u₁>ᵍu₂)
          -- TODO: this can be simplified using lnn-u>ᵍv→u≡[]→v≡[]; then we can skip lnn-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[],  refer to rlnn-u>ᵍv→u≡[]→v≡[]
          where 
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[]           

        from-ev : (l + r ` loc) ⊢ RightU u₁ >ˡ RightU u₂ → (l + r ` loc) ⊢ RightU u₁ >ᵍ RightU u₂
        from-ev (choice-rr-bothempty  proj₁flat-u₁≡[] proj₁flat-u₂≡[] u₁>ˡu₂)  with robust-r
        ... | robust rob-r-ev = choice-rr (proj₂ (rob-r-ev u₁ u₂) u₁>ˡu₂ ) 
        from-ev (choice-rr-notempty  ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[] u₁>ˡu₂)  with robust-r
        ... | robust rob-r-ev = choice-rr (proj₂ (rob-r-ev u₁ u₂) u₁>ˡu₂ ) 
        from-ev (choice-rr-empty  ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[])  with robust-r
        ... | robust rob-r-ev = choice-rr (lnn→∷>ᵍ[] lnn-r u₁ u₂ ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[])  
lnn→robust {r * ε∉r ` loc} (lnn-* lnn-r) =  robust {r * ε∉r ` loc} prf
  where
    robust-r : Robust r
    robust-r = lnn→robust {r} lnn-r


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





### Is LNN necessary?

No. A counter example, ε + ε is robust but not in LNN.



```agda
-- does not hold
            
{-         
robust→lnn : ∀ { r : RE }
  → Robust r 
  → LNN r
robust→lnn {ε}           (robust {ε} robust-ev)             = lnn-ε
robust→lnn {$ c ` loc}   (robust {$ _ ` _ } robust-ev)      = lnn-$ {c} {loc}
robust→lnn {l ● r ` loc} (robust {_ ● _ ` _} robust-l●r-ev) = lnn-● lnn-l lnn-r
  where
    u : U r
    u = proj₁ (r-∃u r) 
    robust-l-ev : ∀ ( v₁ : U l ) → ( v₂ : U l )
      → ( l ⊢ v₁ >ᵍ v₂ → l ⊢ v₁ >ˡ v₂ ) × ( l ⊢ v₁ >ˡ v₂ → l ⊢ v₁ >ᵍ v₂ )
    robust-l-ev v₁ v₂ with robust-l●r-ev (PairU v₁ u) (PairU v₂ u)
    ... | v₁u>ᵍv₂u→v₁u>ˡv₂u , v₁u>ˡv₂u→v₁u>ᵍv₂u = v₁>ᵍv₂→v₁>ˡv₂ , v₁>ˡv₂→v₁>ᵍv₂   
      where
        v₁>ᵍv₂→v₁>ˡv₂ : l ⊢ v₁ >ᵍ v₂ → l ⊢ v₁ >ˡ v₂
        v₁>ᵍv₂→v₁>ˡv₂ v₁>ᵍv₂ with v₁u>ᵍv₂u→v₁u>ˡv₂u (GreedyOrder.seq₁ v₁>ᵍv₂)
        ... | LNEOrder.seq₁ v₁>ˡv₂ = v₁>ˡv₂
        ... | LNEOrder.seq₂ v₁≡v₂ u>ˡu = Nullary.contradiction v₁≡v₂ (>ᵍ→¬≡  v₁>ᵍv₂)
        v₁>ˡv₂→v₁>ᵍv₂ : l ⊢ v₁ >ˡ v₂ → l ⊢ v₁ >ᵍ v₂
        v₁>ˡv₂→v₁>ᵍv₂ v₁>ˡv₂ with v₁u>ˡv₂u→v₁u>ᵍv₂u (LNEOrder.seq₁ v₁>ˡv₂)
        ... | GreedyOrder.seq₁ v₁>ᵍv₂ = v₁>ᵍv₂
        ... | GreedyOrder.seq₂ v₁≡v₂ u>ᵍu = Nullary.contradiction v₁≡v₂ (>ˡ→¬≡ v₁>ˡv₂)         
    robust-l : Robust l
    robust-l = robust {l} robust-l-ev 
    lnn-l : LNN l
    lnn-l = robust→lnn {l} robust-l
    v : U l
    v = proj₁ (r-∃u l)
    robust-r-ev : ∀ ( u₁ : U r ) → ( u₂ : U r )
      → ( r ⊢ u₁ >ᵍ u₂ → r ⊢ u₁ >ˡ u₂ ) × ( r ⊢ u₁ >ˡ u₂ → r ⊢ u₁ >ᵍ u₂ )
    robust-r-ev u₁ u₂ with robust-l●r-ev (PairU v u₁) (PairU v u₂)
    ... | vu₁>ᵍvu₂→vu₁>ˡvu₂ , vu₁>ˡvu₂→vu₁>ᵍvu₂ = u₁>ᵍu₂→u₁>ˡu₂ , u₁>ˡu₂→u₁>ᵍu₂
      where
        u₁>ᵍu₂→u₁>ˡu₂ : r ⊢ u₁ >ᵍ u₂ → r ⊢ u₁ >ˡ u₂
        u₁>ᵍu₂→u₁>ˡu₂ u₁>ᵍu₂ with vu₁>ᵍvu₂→vu₁>ˡvu₂ (GreedyOrder.seq₂ refl u₁>ᵍu₂)
        ... | LNEOrder.seq₁ v>ˡv = Nullary.contradiction refl (>ˡ→¬≡ v>ˡv)
        ... | LNEOrder.seq₂ refl u₁>ˡu₂ = u₁>ˡu₂
        u₁>ˡu₂→u₁>ᵍu₂ : r ⊢ u₁ >ˡ u₂ → r ⊢ u₁ >ᵍ u₂ 
        u₁>ˡu₂→u₁>ᵍu₂ u₁>ˡu₂ with vu₁>ˡvu₂→vu₁>ᵍvu₂ (LNEOrder.seq₂ refl u₁>ˡu₂)
        ... | GreedyOrder.seq₁ v>ᵍv = Nullary.contradiction refl (>ᵍ→¬≡ v>ᵍv)
        ... | GreedyOrder.seq₂ refl u₁>ᵍu₂ = u₁>ᵍu₂
    robust-r : Robust r
    robust-r = robust {r} robust-r-ev 
    lnn-r : LNN r
    lnn-r = robust→lnn {r} robust-r

robust→lnn {l + r ` loc} (robust {_ + _ ` _} robust-l+r-ev) = lnn-+ ε∉l lnn-l lnn-r
  where
    ¬ε∈l : ¬ ε∈ l
    ¬ε∈l = {!!}  -- how? we need u>ᵍv→¬v>ᵍu ?
    -- hm it seems ¬ε∈l is not necessary, counter example, ε + ε is robust but not in LNN. we need 
    ε∉l : ε∉ l
    ε∉l = ¬ε∈r→ε∉r ¬ε∈l
    lnn-l : LNN l
    lnn-l = {!!} -- can be proven similarly to the ● case above 
    lnn-r : LNN r
    lnn-r = {!!}
-}

```


Definition: is-epsilon


```agda

data ε≅ : RE → Set where
  ε≅ε : ε≅ ε
  ε≅● :  ∀ { l r : RE } { loc : ℕ }
    → ε≅ l
    → ε≅ r
    ---------------------
    → ε≅ ( l ● r ` loc )
  ε≅+ :  ∀ { l r : RE } { loc : ℕ }
    → ε≅ l
    → ε≅ r
    --------------------
    → ε≅ ( l + r ` loc )


postulate
  ε≅r→flat-[] : ∀ {r : RE} { ε≅r : ε≅ r }
    → ( u : U r )
    -------------------
    → Flat-[] r u 

```


Definition: A relaxed form of LNN, restricted left-nullability form (not sufficient)

But it is not sufficient to ensure robustness 

```agda
    

data RLN : RE → Set where
  rln-ε : RLN ε
  rln-$ : ∀ { c : Char } { loc : ℕ } → RLN ($ c ` loc)
  rln-●  : ∀ { l r : RE } { loc : ℕ }
    → RLN l
    → RLN r
    ----------------------------------
    → RLN ( l ● r ` loc )
  rln-+  : ∀ { l r : RE } { loc : ℕ }
    → ( ε∈ l → ε≅ r ) -- ε∉ l ⊎ ε≅ r 
    → RLN l  
    → RLN r
    ---------------------------------
    → RLN ( l + r ` loc )
  rln-* : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → RLN r
    --------------------------------
    → RLN ( r * ε∉r ` loc )


```


rln is sufficient to ensure robustness ?



hm.. is this valid? no, a counter example

proj₁ (flat (PairU (LeftU EmptyU) NilU)) ≡ [] 

proj₁ (flat (PairU (RightU EmptyU) (ConsU a []))) ≡ [a]

But

(ε + ε) ● a* ⊢ PairU (LeftU EmptyU) NilU > PairU (RightU EmptyU) (ConsU a [])

hence

¬ ( (ε + ε) ● a* ⊢ PairU (RightU EmptyU) (ConsU a []) >  PairU (LeftU EmptyU) NilU  ) 



rln→∷>ᵍ[] : ∀ { r : RE }
    → RLN r
    → ( u₁ : U r )
    → ( u₂ : U r )
    → ¬ proj₁ (flat u₁) ≡ []
    → proj₁ (flat u₂) ≡ []
    ------------------------
    → r ⊢ u₁ >ᵍ u₂
rln→∷>ᵍ[] {ε} rln-ε          EmptyU      EmptyU      ¬proj₁flat-empty≡[]  proj₁flat-empty≡[]              = Nullary.contradiction proj₁flat-empty≡[] ¬proj₁flat-empty≡[]
rln→∷>ᵍ[] {$ c ` loc} rln-$  (LetterU _) (LetterU _) ¬proj₁flat-letter≡[] proj₁flat-letter≡[]             = Nullary.contradiction proj₁flat-letter≡[] ¬proj₁flat-letter≡[]
rln→∷>ᵍ[] {r * ε∉r ` loc} (rln-* rln-r) (ListU [])  _                       ¬proj₁flat-nil≡[] _           = Nullary.contradiction (proj₁flat-nil≡[]  {r} {ε∉r} {loc})  ¬proj₁flat-nil≡[]
rln→∷>ᵍ[] {r * ε∉r ` loc} (rln-* rln-r) (ListU ( u ∷ us )) (ListU ( v ∷ vs))  ¬proj₁flat-cons-uus≡[] proj₁flat-cons-vvs≡[] =  Nullary.contradiction proj₁flat-cons-vvs≡[] (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs})
rln→∷>ᵍ[] {r * ε∉r ` loc} (rln-* rln-r) (ListU ( u ∷ us )) (ListU [])  ¬proj₁flat-cons-uus≡[] proj₁flat-nil≡[]     = star-cons-nil
rln→∷>ᵍ[] {l + r   ` loc} (rln-+ ε∈l→ε≅r rln-l rln-r) (LeftU u) (LeftU v) ¬proj₁flat-left-u≡[] proj₁flat-left-v≡[]     = choice-ll (rln→∷>ᵍ[] {l} rln-l u v ¬proj₁flat-left-u≡[] proj₁flat-left-v≡[])
rln→∷>ᵍ[] {l + r   ` loc} (rln-+ ε∈l→ε≅r rln-l rln-r) (RightU u) (RightU v) ¬proj₁flat-right-u≡[] proj₁flat-right-v≡[] = choice-rr (rln→∷>ᵍ[] {r} rln-r u v ¬proj₁flat-right-u≡[] proj₁flat-right-v≡[])
rln→∷>ᵍ[] {l + r   ` loc} (rln-+ ε∈l→ε≅r rln-l rln-r) (LeftU u) (RightU v) ¬proj₁flat-left-u≡[] proj₁flat-right-v≡[] = choice-lr
rln→∷>ᵍ[] {l + r   ` loc} (rln-+ ε∈l→ε≅r rln-l rln-r) (RightU u) (LeftU v) ¬proj₁flat-right-u≡[] proj₁flat-left-v≡[] = Nullary.contradiction proj₁flat-u≡[] ¬proj₁flat-right-u≡[]
  where
    ε∈l : ε∈ l
    ε∈l = proj₁flat-v≡[]→ε∈r proj₁flat-left-v≡[]
    ε≅r : ε≅ r
    ε≅r = ε∈l→ε≅r ε∈l
    proj₁flat-u≡[] : proj₁ (flat u) ≡ []
    proj₁flat-u≡[] with  ε≅r→flat-[] {r} {ε≅r} u
    ... | flat-[] _ eq = eq
rln→∷>ᵍ[] {l ● r   ` loc} (rln-● rln-l rln-r) (PairU u₁ u₂) (PairU v₁ v₂)  ¬proj₁flat-pair-u₁u₂≡[] proj₁flat-v₁v₂≡[] = prf 
  where
    proj₁flat-v₁≡[] : proj₁ (flat v₁) ≡ []
    proj₁flat-v₁≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) proj₁flat-v₁v₂≡[]
    proj₁flat-v₂≡[] : proj₁ (flat v₂) ≡ []
    proj₁flat-v₂≡[] = ++-conicalʳ (proj₁ (flat v₁)) (proj₁ (flat v₂)) proj₁flat-v₁v₂≡[]

    prf : (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂
    prf with proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat u₂) in proj₁flat-u₂-eq 
    ... | []     |  []       = Nullary.contradiction refl ¬proj₁flat-pair-u₁u₂≡[] 
    ... | []     |  c' ∷ cs' = seq₂ u₁≡v₁ u₂>ᵍv₂ 
      where
        u₁≡v₁ : u₁ ≡ v₁
        u₁≡v₁ = lnn-proj₁flat≡[]→refl {l} {proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq} {u₁} {v₁} rln-l  proj₁flat-u₁-eq proj₁flat-v₁≡[]
        ¬proj₁flat-u₂≡[] : ¬ proj₁ (flat u₂) ≡ []
        ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq = λ proj₁flat-u₂≡[] →  ¬∷≡[] proj₁flat-u₂≡[] 
        u₂>ᵍv₂ : r  ⊢ u₂ >ᵍ v₂
        u₂>ᵍv₂ = lnn→∷>ᵍ[] {r} rln-r u₂ v₂  ¬proj₁flat-u₂≡[] proj₁flat-v₂≡[] 
    ... | c ∷ cs |  cs' = seq₁ u₁>ᵍv₁
      where 
        ¬proj₁flat-u₁≡[] : ¬ proj₁ (flat u₁) ≡ []
        ¬proj₁flat-u₁≡[] rewrite proj₁flat-u₁-eq = λ proj₁flat-u₁≡[] →  ¬∷≡[] proj₁flat-u₁≡[] 
        u₁>ᵍv₁ : l  ⊢ u₁ >ᵍ v₁
        u₁>ᵍv₁ = lnn→∷>ᵍ[] {l} rln-l u₁ v₁ ¬proj₁flat-u₁≡[] proj₁flat-v₁≡[] 
    


hm.. is this valid? no, a counter example

(ε + ε) ● a* ⊢ PairU (LeftU EmptyU) NilU > PairU (RightU EmptyU) (ConsU a [])

proj₁ (flat (PairU (LeftU EmptyU) NilU)) ≡ [] 

proj₁ (flat (PairU (RightU EmptyU) (ConsU a []))) ≡ [a]


rln-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[]  : ∀ { r : RE }
    → RLN r
    → ( u : U r )
    → ( v : U r )
    → r ⊢ u >ᵍ v
    -------------------------
    → ( proj₁ (flat u) ≡ [] × proj₁ (flat v) ≡ [] ) ⊎
      ( ( ¬ proj₁ (flat u) ≡ [] × ¬ proj₁ (flat v) ≡ [] ) ⊎
        ( ¬ proj₁ (flat u) ≡ [] × proj₁ (flat v) ≡ [] ) )
rln-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {ε}             rln-ε EmptyU EmptyU = λ()
rln-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {$ c ` loc}     rln-$ (LetterU _) (LetterU _) = λ()
rln-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (rln-* rln-r) (ListU []) (ListU []) = λ()
rln-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (rln-* rln-r) (ListU []) (ListU ( v ∷ vs) ) = λ()

rln-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (rln-* rln-r) (ListU (u ∷ us )) (ListU []) star-cons-nil = inj₂ (inj₂ (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us} , proj₁flat-nil≡[] {r} {ε∉r} {loc} ) )
rln-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r * ε∉r ` loc} (rln-* rln-r) (ListU (u ∷ us )) (ListU (v ∷ vs)) _       = inj₂ (inj₁ (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {u} {us} , ¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs} ) )
rln-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {l ● r ` loc}   (rln-● rln-l rln-r) (PairU u₁ u₂) (PairU v₁ v₂)
  with proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat v₁) in proj₁flat-v₁-eq
... | []        |  []  = prf 
  where
    prf : (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂ →
      ( proj₁ (flat u₂) ≡ [] × proj₁ (flat v₂) ≡ [] ) ⊎
      ( ( ¬ proj₁ (flat u₂) ≡ [] × ¬ proj₁ (flat v₂) ≡ [] ) ⊎
        ( ¬ proj₁ (flat u₂) ≡ [] × proj₁ (flat v₂) ≡ [] ) )
    prf (seq₂ refl u₂>ᵍv₂ ) with rln-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r} rln-r u₂ v₂ u₂>ᵍv₂
    ... | inj₁ ( proj₁flat-u₂≡[] , proj₁flat-v₂≡[] ) = inj₁ (proj₁flat-u₂≡[] , proj₁flat-v₂≡[])
    ... | inj₂ ( inj₁ ( ¬proj₁flat-u₂≡[] , ¬proj₁flat-v₂≡[] ) ) = inj₂ (inj₁ (¬proj₁flat-u₂≡[] , ¬proj₁flat-v₂≡[]))
    ... | inj₂ ( inj₂ ( ¬proj₁flat-u₂≡[] , proj₁flat-v₂≡[] ) ) = inj₂ (inj₂ (¬proj₁flat-u₂≡[] , proj₁flat-v₂≡[]))
    prf (seq₁ u₁>ᵍv₁) = {!!}  -- can we use  rln→∷>ᵍ[] to contradiction the case where u₂ is [] and v₂ is not?

rln-u>ᵍv→¬u≡[]×v≢[] : ∀ { r : RE }
    → RLN r
    → ( u : U r )
    → ( v : U r )
    → r ⊢ u >ᵍ v
    ----------------------------------------------------
    → ¬ ( proj₁ (flat u) ≡ [] × ¬ proj₁ (flat v) ≡ [] )
rln-u>ᵍv→¬u≡[]×v≢[] {r} rln-r u v u>ᵍv  (proj₁flat-u≡[] , ¬proj₁flat-v≡[])  with rln-u>ᵍv→u≡[]×v≡[]⊎u≢[]×v≢[]×u≢[]×v≡[] {r} rln-r u v u>ᵍv
... | inj₁ (proj₁flat-u≡[] ,  proj₁-flat-v≡[] ) =  ¬proj₁flat-v≡[] proj₁-flat-v≡[]
... | inj₂ (inj₁ (¬proj₁flat-u≡[] ,  ¬proj₁-flat-v≡[] ) ) = ¬proj₁flat-u≡[] proj₁flat-u≡[]
... | inj₂ (inj₂ (¬proj₁flat-u≡[] ,  proj₁-flat-v≡[] ) )  = ¬proj₁flat-v≡[] proj₁-flat-v≡[] 



hm.. is this valid? no, a counter example

(ε + ε) ● a* ⊢ PairU (LeftU EmptyU) NilU >ᵍ PairU (RightU EmptyU) (ConsU a []) 

can we show

(ε + ε) ● a* ⊢ PairU (LeftU EmptyU) NilU >ˡ PairU (RightU EmptyU) (ConsU a [])  ?



rln-u>ᵍv→u≡[]→v≡[] : ∀ { r : RE}
    → RLN r
    → ( u : U r )
    → ( v : U r )
    → r ⊢ u >ᵍ v
    → proj₁ (flat u) ≡ []
    ----------------------------------------------------
    → proj₁ (flat v) ≡ []
rln-u>ᵍv→u≡[]→v≡[] {r} rln-r u v u>ᵍv proj₁flat-u≡[] = prf
  where
    prf : proj₁ (flat v) ≡ []
    prf with proj₁ (flat v) in proj₁flat-v-eq  
    ... | []     = refl
    ... | c ∷ cs = Nullary.contradiction (  proj₁flat-u≡[] , ¬proj₁flat-v≡[]) (rln-u>ᵍv→¬u≡[]×v≢[] rln-r u v u>ᵍv)
      where
        ¬proj₁flat-v≡[] : ¬ proj₁ (flat v) ≡ []
        ¬proj₁flat-v≡[] rewrite proj₁flat-v-eq = λ proj₁flat-v≡[] → ¬∷≡[] proj₁flat-v≡[]



== Not a counter example

Given

(ε + ε) ● a* ⊢ PairU (LeftU EmptyU) NilU >ᵍ PairU (RightU EmptyU) (ConsU a [])

proof : seq₁ choice-lr 

can we prove? 

(ε + ε) ● a* ⊢ PairU (LeftU EmptyU) NilU >ˡ PairU (RightU EmptyU) (ConsU a [])  ?

proof : seq: choice-lr-bothempty

== A counter example

((ε + ε) ● a*) + ε is RLN?, yes


can we prove

((ε + ε) ● a*) + ε ⊢ LeftU (PairU (LeftU EmptyU) NilU) >ᵍ LeftU (PairU (RightU EmptyU) (ConsU a []))

proof:  choice-ll (seq₁ choice-lr)

can we prove

((ε + ε) ● a*) + ε ⊢ LeftU (PairU (LeftU EmptyU) NilU) >ˡ LeftU (PairU (RightU EmptyU) (ConsU a []))

?

No, none of  choice-ll-bothempty, choice-ll-notempty , choice-ll-empty can be applied. 


the current RLN is not sufficient to guarantee robustness



{-# TERMINATING #-}
rln→robust : ∀ { r : RE }
  → RLN r
  → Robust r
rln→robust {ε}           rln-ε = robust λ v₁ v₂ → ( ( λ() ) , (λ ()) )
rln→robust {$ c ` loc}   rln-$ = robust λ v₁ v₂ → ( ( λ() ) , (λ ()) ) 
rln→robust {l ● r ` loc} (rln-● rln-l rln-r) = robust {l ● r ` loc} λ { (PairU u₁ v₁) (PairU u₂ v₂) → to-ev u₁ u₂ v₁ v₂ , from-ev  u₁ u₂ v₁ v₂ }
  where
    robust-r : Robust r
    robust-r = rln→robust {r} rln-r
    
    robust-l : Robust l
    robust-l = rln→robust {l} rln-l
  
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
rln→robust {l + r ` loc} (rln-+ ε∈l→ε≅r rln-l rln-r) =  robust {l + r ` loc} prf
  where
    robust-l : Robust l
    robust-l = rln→robust {l} rln-l

    robust-r : Robust r
    robust-r = rln→robust {r} rln-r

    prf : (v₁ v₂ : U (l + r ` loc)) →
      ((l + r ` loc) ⊢ v₁ >ᵍ v₂ → (l + r ` loc) ⊢ v₁ >ˡ v₂) ×
      ((l + r ` loc) ⊢ v₁ >ˡ v₂ → (l + r ` loc) ⊢ v₁ >ᵍ v₂)
    prf (LeftU u₁) (LeftU u₂) with proj₁ (flat u₁) in proj₁flat-u₁-eq
    ... | []     = to-ev , from-ev
      where
        εεl : ε∈ l
        εεl = proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq
        to-ev : (l + r ` loc) ⊢ LeftU u₁ >ᵍ LeftU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ˡ LeftU u₂
        to-ev (choice-ll u₁>ᵍu₂) with robust-l | proj₁ (flat u₂) in proj₁flat-u₂-eq
        ... | robust rob-l-ev | [] = choice-ll-bothempty proj₁flat-u₁-eq proj₁flat-u₂-eq ((proj₁ (rob-l-ev u₁ u₂) u₁>ᵍu₂ ))
        ... | robust rob-l-ev | c ∷ cs = Nullary.contradiction u₂>ᵍu₁ (u>ᵍv→¬v>ᵍu u₁>ᵍu₂)  -- we don't need a contradiction here. It is possible to get u₁>ˡu₂?
        -- note ε∈ l does not mean ε≅ l.  ¬proj₁flat-u₂≡[]  is possible
        -- for lne, we have choice-ll-bothempty, choice-ll-notempty, choice-ll-empty
                              
          where
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[]                     
            u₂>ᵍu₁ : l ⊢ u₂ >ᵍ u₁
            u₂>ᵍu₁ = {!!} -- rln→∷>ᵍ[] rln-l u₂ u₁ ¬proj₁flat-u₂≡[] proj₁flat-u₁-eq -- shall we specialize it to l + r only? 
        from-ev :  (l + r ` loc) ⊢ LeftU u₁ >ˡ LeftU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ᵍ LeftU u₂
        from-ev (choice-ll-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) =  choice-ll {!!} -- (rln→∷>ᵍ[] rln-l u₁ u₂ ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[])
        from-ev (choice-ll-bothempty proj₁flat-u₁≡[] proj₁flat-u₂≡[] u₁>ˡu₂ ) with robust-l
        ... | robust rob-l-ev = choice-ll ((proj₂ (rob-l-ev u₁ u₂) u₁>ˡu₂ ))
        from-ev (choice-ll-notempty ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[] u₁>ˡu₂ ) with robust-l
        ... | robust rob-l-ev = choice-ll ((proj₂ (rob-l-ev u₁ u₂) u₁>ˡu₂ ))
    ... | c ∷ cs = to-ev , from-ev 
      where
        ¬proj₁flat-u₁≡[] : ¬ proj₁ ( flat u₁ ) ≡ []
        ¬proj₁flat-u₁≡[] rewrite proj₁flat-u₁-eq  = λ proj₁flat-u₁≡[] → ¬∷≡[] proj₁flat-u₁≡[]                     
        to-ev : (l + r ` loc) ⊢ LeftU u₁ >ᵍ LeftU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ˡ LeftU u₂
        to-ev (choice-ll u₁>ᵍu₂) with robust-l | proj₁ (flat u₂) in proj₁flat-u₂-eq 
        ... | robust rob-l-ev  | [] = choice-ll-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂-eq 
        ... | robust rob-l-ev  | c ∷ cs = choice-ll-notempty ¬proj₁flat-u₁≡[]  ¬proj₁flat-u₂≡[]  (proj₁ (rob-l-ev u₁ u₂) u₁>ᵍu₂ )
          where
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[]         
        from-ev :  (l + r ` loc) ⊢ LeftU u₁ >ˡ LeftU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ᵍ LeftU u₂
        from-ev (choice-ll-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) = choice-ll {!!} -- (rln→∷>ᵍ[] rln-l u₁ u₂ ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) 
        from-ev (choice-ll-bothempty proj₁flat-u₁≡[] proj₁flat-u₂≡[] u₁>ˡu₂ ) with robust-l
        ... | robust rob-l-ev = choice-ll ((proj₂ (rob-l-ev u₁ u₂) u₁>ˡu₂ ))

        from-ev (choice-ll-notempty ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[] u₁>ˡu₂ ) with robust-l
        ... | robust rob-l-ev = choice-ll ((proj₂ (rob-l-ev u₁ u₂) u₁>ˡu₂ ))
    prf (LeftU u₁) (RightU u₂) = to-ev , from-ev
      where
        to-ev : (l + r ` loc) ⊢ LeftU u₁ >ᵍ RightU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ˡ RightU u₂
        to-ev choice-lr with proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat u₂) in proj₁flat-u₂-eq
        ... | []     | _   = choice-lr-bothempty proj₁flat-u₁-eq proj₁flat-u₂≡[]
          where
            εεl : ε∈ l
            εεl = proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq
  
            ε≅r : ε≅ r
            ε≅r = ε∈l→ε≅r εεl
            proj₁flat-u₂≡[] : proj₁ (flat u₂) ≡ []
            proj₁flat-u₂≡[] with  ε≅r→flat-[] {r} {ε≅r} u₂
            ... | flat-[] _ eq = eq
        ... | c ∷ cs | [] = choice-lr-empty  ¬proj₁flat-u₁≡[] proj₁flat-u₂-eq
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
        from-ev =  λ z → choice-lr
    prf (RightU u₁) (LeftU u₂) = to-ev , from-ev
      where
        to-ev : (l + r ` loc) ⊢ RightU u₁ >ᵍ LeftU u₂ → (l + r ` loc) ⊢ RightU u₁ >ˡ LeftU u₂
        to-ev = λ () 
        from-ev : (l + r ` loc) ⊢ RightU u₁ >ˡ LeftU u₂ → (l + r ` loc) ⊢ RightU u₁ >ᵍ LeftU u₂
        from-ev (choice-rl-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) = Nullary.contradiction proj₁flat-u₁≡[] ¬proj₁flat-u₁≡[]   
          where
            ε∈l : ε∈ l
            ε∈l = proj₁flat-v≡[]→ε∈r proj₁flat-u₂≡[]
            ε≅r : ε≅ r 
            ε≅r = ε∈l→ε≅r ε∈l
            proj₁flat-u₁≡[] : proj₁ (flat u₁) ≡ []
            proj₁flat-u₁≡[] with ε≅r→flat-[] {r} {ε≅r} u₁
            ... | flat-[] _ x = x 
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
        ... | robust rob-r-ev | []     | c' ∷ cs'  =  {!!} -- Nullary.contradiction (rln-u>ᵍv→u≡[]→v≡[] {r} rln-r u₁ u₂ u₁>ᵍu₂ proj₁flat-u₁-eq) ¬proj₁flat-u₂≡[]
          where 
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[]           

        from-ev : (l + r ` loc) ⊢ RightU u₁ >ˡ RightU u₂ → (l + r ` loc) ⊢ RightU u₁ >ᵍ RightU u₂
        from-ev (choice-rr-bothempty  proj₁flat-u₁≡[] proj₁flat-u₂≡[] u₁>ˡu₂)  with robust-r
        ... | robust rob-r-ev = choice-rr (proj₂ (rob-r-ev u₁ u₂) u₁>ˡu₂ ) 
        from-ev (choice-rr-notempty  ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[] u₁>ˡu₂)  with robust-r
        ... | robust rob-r-ev = choice-rr (proj₂ (rob-r-ev u₁ u₂) u₁>ˡu₂ ) 
        from-ev (choice-rr-empty  ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[])  with robust-r
        ... | robust rob-r-ev = choice-rr {!!} -- (rln→∷>ᵍ[] rln-r u₁ u₂ ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[])  
rln→robust {r * ε∉r ` loc} (rln-* rln-r) =  robust {r * ε∉r ` loc} prf
  where
    robust-r : Robust r
    robust-r = rln→robust {r} rln-r


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


### Definition RLNN 

RLN is not sufficient, let's a "in-between" of RLN and LNN 
-- relaxed LNN ? 

```agda
data RLNN : RE → Set where
  rlnn-ε : RLNN ε
  rlnn-$ : ∀ { c : Char } { loc : ℕ } → RLNN ($ c ` loc)
  rlnn-●  : ∀ { l r : RE } { loc : ℕ }
    → RLNN l
    → RLNN r
    ----------------------------------
    → RLNN ( l ● r ` loc )
  rlnn-+  : ∀ { l r : RE } { loc : ℕ }
    → ( ε∈ l → ε≅ r ) -- ε∉ l ⊎ ε≅ r 
    → LNN l  
    → RLNN r
    ---------------------------------
    → RLNN ( l + r ` loc )
  rlnn-* : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ }
    → RLNN r
    --------------------------------
    → RLNN ( r * ε∉r ` loc )


```
is rlnn sufficiently guaranteeing robustness?


### sub lemma 

```agda
-- not true, counter example ε + ε 
postulate
  rlnn-proj₁flat≡[]→refl : ∀ { r : RE } { ε∈r : ε∈ r } { u v : U r }
    → RLNN r 
    → proj₁ (flat u) ≡ []
    → proj₁ (flat v) ≡ []
    ------------------------
    → u ≡ v


-- not true? counter example
-- (ε + ε ) ● a* ⊢ PairU ( LeftU EmptyU ) NilU >ᵍ PairU ( RightU EmptyU ) (ConsU a [])
-- proof: seq₁ choice-lr
-- which implies 
-- ¬ (ε + ε ) ● a* ⊢ PairU ( RightU EmptyU ) (ConsU a []) >ᵍ PairU ( LeftU EmptyU ) NilU 
rlnn→∷>ᵍ[] : ∀ { r : RE }
    → RLNN r
    → ( u₁ : U r )
    → ( u₂ : U r )
    → ¬ proj₁ (flat u₁) ≡ []
    → proj₁ (flat u₂) ≡ []
    ------------------------
    → r ⊢ u₁ >ᵍ u₂
rlnn→∷>ᵍ[] {ε} rlnn-ε          EmptyU      EmptyU      ¬proj₁flat-empty≡[]  proj₁flat-empty≡[]              = Nullary.contradiction proj₁flat-empty≡[] ¬proj₁flat-empty≡[]
rlnn→∷>ᵍ[] {$ c ` loc} rlnn-$  (LetterU _) (LetterU _) ¬proj₁flat-letter≡[] proj₁flat-letter≡[]             = Nullary.contradiction proj₁flat-letter≡[] ¬proj₁flat-letter≡[]
rlnn→∷>ᵍ[] {r * ε∉r ` loc} (rlnn-* rlnn-r) (ListU [])  _                       ¬proj₁flat-nil≡[] _           = Nullary.contradiction (proj₁flat-nil≡[]  {r} {ε∉r} {loc})  ¬proj₁flat-nil≡[]
rlnn→∷>ᵍ[] {r * ε∉r ` loc} (rlnn-* rlnn-r) (ListU ( u ∷ us )) (ListU ( v ∷ vs))  ¬proj₁flat-cons-uus≡[] proj₁flat-cons-vvs≡[] =  Nullary.contradiction proj₁flat-cons-vvs≡[] (¬proj₁flat-cons≡[] {r} {ε∉r} {loc} {v} {vs})
rlnn→∷>ᵍ[] {r * ε∉r ` loc} (rlnn-* rlnn-r) (ListU ( u ∷ us )) (ListU [])  ¬proj₁flat-cons-uus≡[] proj₁flat-nil≡[]     = star-cons-nil
rlnn→∷>ᵍ[] {l + r   ` loc} (rlnn-+ ε∈l→ε≅r lnn-l rlnn-r) (LeftU u) (LeftU v) ¬proj₁flat-left-u≡[] proj₁flat-left-v≡[]     = choice-ll (lnn→∷>ᵍ[] {l} lnn-l u v ¬proj₁flat-left-u≡[] proj₁flat-left-v≡[])
rlnn→∷>ᵍ[] {l + r   ` loc} (rlnn-+ ε∈l→ε≅r rlnn-l rlnn-r) (RightU u) (RightU v) ¬proj₁flat-right-u≡[] proj₁flat-right-v≡[] = choice-rr (rlnn→∷>ᵍ[] {r} rlnn-r u v ¬proj₁flat-right-u≡[] proj₁flat-right-v≡[])
rlnn→∷>ᵍ[] {l + r   ` loc} (rlnn-+ ε∈l→ε≅r rlnn-l rlnn-r) (LeftU u) (RightU v) ¬proj₁flat-left-u≡[] proj₁flat-right-v≡[] = choice-lr
rlnn→∷>ᵍ[] {l + r   ` loc} (rlnn-+ ε∈l→ε≅r rlnn-l rlnn-r) (RightU u) (LeftU v) ¬proj₁flat-right-u≡[] proj₁flat-left-v≡[] = Nullary.contradiction proj₁flat-u≡[] ¬proj₁flat-right-u≡[]
  where
    ε∈l : ε∈ l
    ε∈l = proj₁flat-v≡[]→ε∈r proj₁flat-left-v≡[]
    ε≅r : ε≅ r
    ε≅r = ε∈l→ε≅r ε∈l
    proj₁flat-u≡[] : proj₁ (flat u) ≡ []
    proj₁flat-u≡[] with  ε≅r→flat-[] {r} {ε≅r} u
    ... | flat-[] _ eq = eq
rlnn→∷>ᵍ[] {l ● r   ` loc} (rlnn-● rlnn-l rlnn-r) (PairU u₁ u₂) (PairU v₁ v₂)  ¬proj₁flat-pair-u₁u₂≡[] proj₁flat-v₁v₂≡[] = prf 
  where
    proj₁flat-v₁≡[] : proj₁ (flat v₁) ≡ []
    proj₁flat-v₁≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) proj₁flat-v₁v₂≡[]
    proj₁flat-v₂≡[] : proj₁ (flat v₂) ≡ []
    proj₁flat-v₂≡[] = ++-conicalʳ (proj₁ (flat v₁)) (proj₁ (flat v₂)) proj₁flat-v₁v₂≡[]

    prf : (l ● r ` loc) ⊢ PairU u₁ u₂ >ᵍ PairU v₁ v₂
    prf with proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat u₂) in proj₁flat-u₂-eq 
    ... | []     |  []       = Nullary.contradiction refl ¬proj₁flat-pair-u₁u₂≡[] 
    ... | []     |  c' ∷ cs' = seq₂ u₁≡v₁ u₂>ᵍv₂ 
      where
        u₁≡v₁ : u₁ ≡ v₁
        u₁≡v₁ = rlnn-proj₁flat≡[]→refl {l} {proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq} {u₁} {v₁} rlnn-l  proj₁flat-u₁-eq proj₁flat-v₁≡[] -- not true because rlnn-proj₁flat≡[]→refl does not hold
        ¬proj₁flat-u₂≡[] : ¬ proj₁ (flat u₂) ≡ []
        ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq = λ proj₁flat-u₂≡[] →  ¬∷≡[] proj₁flat-u₂≡[] 
        u₂>ᵍv₂ : r  ⊢ u₂ >ᵍ v₂
        u₂>ᵍv₂ = rlnn→∷>ᵍ[] {r} rlnn-r u₂ v₂  ¬proj₁flat-u₂≡[] proj₁flat-v₂≡[] 
    ... | c ∷ cs |  cs' = seq₁ u₁>ᵍv₁
      where 
        ¬proj₁flat-u₁≡[] : ¬ proj₁ (flat u₁) ≡ []
        ¬proj₁flat-u₁≡[] rewrite proj₁flat-u₁-eq = λ proj₁flat-u₁≡[] →  ¬∷≡[] proj₁flat-u₁≡[] 
        u₁>ᵍv₁ : l  ⊢ u₁ >ᵍ v₁
        u₁>ᵍv₁ = rlnn→∷>ᵍ[] {l} rlnn-l u₁ v₁ ¬proj₁flat-u₁≡[] proj₁flat-v₁≡[] 



-- not true? counter example
-- (ε + ε ) ● a* ⊢ PairU ( LeftU EmptyU ) NilU >ᵍ PairU ( RightU EmptyU ) (ConsU a [])
-- does not hold as result of rlnn→∷>ᵍ[] not holding
rlnn-u>ᵍv→u≡[]→v≡[] : ∀ { r : RE}
    → RLNN r
    → ( u : U r )
    → ( v : U r )
    → r ⊢ u >ᵍ v
    → proj₁ (flat u) ≡ []
    ----------------------------------------------------
    → proj₁ (flat v) ≡ []
rlnn-u>ᵍv→u≡[]→v≡[] {r} rlnn-r u v u>ᵍv proj₁flat-u≡[] = prf
  where
    prf : proj₁ (flat v) ≡ []
    prf with proj₁ (flat v) in proj₁flat-v-eq  
    ... | []     = refl
    ... | c ∷ cs = Nullary.contradiction (rlnn→∷>ᵍ[] rlnn-r v u ¬proj₁flat-v≡[] proj₁flat-u≡[])  (u>ᵍv→¬v>ᵍu u>ᵍv)
      where
        ¬proj₁flat-v≡[] : ¬ proj₁ (flat v) ≡ []
        ¬proj₁flat-v≡[] rewrite proj₁flat-v-eq = λ proj₁flat-v≡[] → ¬∷≡[] proj₁flat-v≡[]
```



this sufficient proof is incomplete, it depends on some on the invalid sub lemmas above.

the necessary proof is still a myth, the main issue is that robust definition is not inductive 


```agda

{-# TERMINATING #-}
rlnn→robust : ∀ { r : RE }
  → RLNN r
  → Robust r
rlnn→robust {ε}           rlnn-ε = robust λ v₁ v₂ → ( ( λ() ) , (λ ()) )
rlnn→robust {$ c ` loc}   rlnn-$ = robust λ v₁ v₂ → ( ( λ() ) , (λ ()) ) 
rlnn→robust {l ● r ` loc} (rlnn-● rlnn-l rlnn-r) = robust {l ● r ` loc} λ { (PairU u₁ v₁) (PairU u₂ v₂) → to-ev u₁ u₂ v₁ v₂ , from-ev  u₁ u₂ v₁ v₂ }
  where
    robust-r : Robust r
    robust-r = rlnn→robust {r} rlnn-r
    
    robust-l : Robust l
    robust-l = rlnn→robust {l} rlnn-l
  
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
rlnn→robust {l + r ` loc} (rlnn-+ ε∈l→ε≅r lnn-l rlnn-r) =  robust {l + r ` loc} prf
  where
    robust-l : Robust l
    robust-l = lnn→robust {l} lnn-l

    robust-r : Robust r
    robust-r = rlnn→robust {r} rlnn-r

    prf : (v₁ v₂ : U (l + r ` loc)) →
      ((l + r ` loc) ⊢ v₁ >ᵍ v₂ → (l + r ` loc) ⊢ v₁ >ˡ v₂) ×
      ((l + r ` loc) ⊢ v₁ >ˡ v₂ → (l + r ` loc) ⊢ v₁ >ᵍ v₂)
    prf (LeftU u₁) (LeftU u₂) with proj₁ (flat u₁) in proj₁flat-u₁-eq
    ... | []     = to-ev , from-ev
      where
        εεl : ε∈ l
        εεl = proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq
        to-ev : (l + r ` loc) ⊢ LeftU u₁ >ᵍ LeftU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ˡ LeftU u₂
        to-ev (choice-ll u₁>ᵍu₂) with robust-l | proj₁ (flat u₂) in proj₁flat-u₂-eq
        ... | robust rob-l-ev | [] = choice-ll-bothempty proj₁flat-u₁-eq proj₁flat-u₂-eq ((proj₁ (rob-l-ev u₁ u₂) u₁>ᵍu₂ ))
        ... | robust rob-l-ev | c ∷ cs = Nullary.contradiction u₂>ᵍu₁ (u>ᵍv→¬v>ᵍu u₁>ᵍu₂)  -- we don't need a contradiction here. It is possible to get u₁>ˡu₂?
        -- note ε∈ l does not mean ε≅ l.  ¬proj₁flat-u₂≡[]  is possible
        -- for lne, we have choice-ll-bothempty, choice-ll-notempty, choice-ll-empty
                              
          where
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[]                     
            u₂>ᵍu₁ : l ⊢ u₂ >ᵍ u₁
            u₂>ᵍu₁ =  lnn→∷>ᵍ[] lnn-l u₂ u₁ ¬proj₁flat-u₂≡[] proj₁flat-u₁-eq
        from-ev :  (l + r ` loc) ⊢ LeftU u₁ >ˡ LeftU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ᵍ LeftU u₂
        from-ev (choice-ll-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) =  choice-ll (lnn→∷>ᵍ[] lnn-l u₁ u₂ ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) 
        from-ev (choice-ll-bothempty proj₁flat-u₁≡[] proj₁flat-u₂≡[] u₁>ˡu₂ ) with robust-l
        ... | robust rob-l-ev = choice-ll ((proj₂ (rob-l-ev u₁ u₂) u₁>ˡu₂ ))
        from-ev (choice-ll-notempty ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[] u₁>ˡu₂ ) with robust-l
        ... | robust rob-l-ev = choice-ll ((proj₂ (rob-l-ev u₁ u₂) u₁>ˡu₂ ))
    ... | c ∷ cs = to-ev , from-ev 
      where
        ¬proj₁flat-u₁≡[] : ¬ proj₁ ( flat u₁ ) ≡ []
        ¬proj₁flat-u₁≡[] rewrite proj₁flat-u₁-eq  = λ proj₁flat-u₁≡[] → ¬∷≡[] proj₁flat-u₁≡[]                     
        to-ev : (l + r ` loc) ⊢ LeftU u₁ >ᵍ LeftU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ˡ LeftU u₂
        to-ev (choice-ll u₁>ᵍu₂) with robust-l | proj₁ (flat u₂) in proj₁flat-u₂-eq 
        ... | robust rob-l-ev  | [] = choice-ll-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂-eq 
        ... | robust rob-l-ev  | c ∷ cs = choice-ll-notempty ¬proj₁flat-u₁≡[]  ¬proj₁flat-u₂≡[]  (proj₁ (rob-l-ev u₁ u₂) u₁>ᵍu₂ )
          where
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[]         
        from-ev :  (l + r ` loc) ⊢ LeftU u₁ >ˡ LeftU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ᵍ LeftU u₂
        from-ev (choice-ll-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) = choice-ll (lnn→∷>ᵍ[] lnn-l u₁ u₂ ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) 
        from-ev (choice-ll-bothempty proj₁flat-u₁≡[] proj₁flat-u₂≡[] u₁>ˡu₂ ) with robust-l
        ... | robust rob-l-ev = choice-ll ((proj₂ (rob-l-ev u₁ u₂) u₁>ˡu₂ ))

        from-ev (choice-ll-notempty ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[] u₁>ˡu₂ ) with robust-l
        ... | robust rob-l-ev = choice-ll ((proj₂ (rob-l-ev u₁ u₂) u₁>ˡu₂ ))
    prf (LeftU u₁) (RightU u₂) = to-ev , from-ev
      where
        to-ev : (l + r ` loc) ⊢ LeftU u₁ >ᵍ RightU u₂ → (l + r ` loc) ⊢ LeftU u₁ >ˡ RightU u₂
        to-ev choice-lr with proj₁ (flat u₁) in proj₁flat-u₁-eq | proj₁ (flat u₂) in proj₁flat-u₂-eq
        ... | []     | _   = choice-lr-bothempty proj₁flat-u₁-eq proj₁flat-u₂≡[]
          where
            εεl : ε∈ l
            εεl = proj₁flat-v≡[]→ε∈r proj₁flat-u₁-eq
  
            ε≅r : ε≅ r
            ε≅r = ε∈l→ε≅r εεl
            proj₁flat-u₂≡[] : proj₁ (flat u₂) ≡ []
            proj₁flat-u₂≡[] with  ε≅r→flat-[] {r} {ε≅r} u₂
            ... | flat-[] _ eq = eq
        ... | c ∷ cs | [] = choice-lr-empty  ¬proj₁flat-u₁≡[] proj₁flat-u₂-eq
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
        from-ev =  λ z → choice-lr
    prf (RightU u₁) (LeftU u₂) = to-ev , from-ev
      where
        to-ev : (l + r ` loc) ⊢ RightU u₁ >ᵍ LeftU u₂ → (l + r ` loc) ⊢ RightU u₁ >ˡ LeftU u₂
        to-ev = λ () 
        from-ev : (l + r ` loc) ⊢ RightU u₁ >ˡ LeftU u₂ → (l + r ` loc) ⊢ RightU u₁ >ᵍ LeftU u₂
        from-ev (choice-rl-empty ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[]) = Nullary.contradiction proj₁flat-u₁≡[] ¬proj₁flat-u₁≡[]   
          where
            ε∈l : ε∈ l
            ε∈l = proj₁flat-v≡[]→ε∈r proj₁flat-u₂≡[]
            ε≅r : ε≅ r 
            ε≅r = ε∈l→ε≅r ε∈l
            proj₁flat-u₁≡[] : proj₁ (flat u₁) ≡ []
            proj₁flat-u₁≡[] with ε≅r→flat-[] {r} {ε≅r} u₁
            ... | flat-[] _ x = x 
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
        ... | robust rob-r-ev | []     | c' ∷ cs'  =  Nullary.contradiction (rlnn-u>ᵍv→u≡[]→v≡[] {r} rlnn-r u₁ u₂ u₁>ᵍu₂ proj₁flat-u₁-eq) ¬proj₁flat-u₂≡[] -- does not hold -- does it implies, r must be lnn-r too? 
          where 
            ¬proj₁flat-u₂≡[] : ¬ proj₁ ( flat u₂ ) ≡ []
            ¬proj₁flat-u₂≡[] rewrite proj₁flat-u₂-eq  = λ proj₁flat-u₂≡[] → ¬∷≡[] proj₁flat-u₂≡[]           

        from-ev : (l + r ` loc) ⊢ RightU u₁ >ˡ RightU u₂ → (l + r ` loc) ⊢ RightU u₁ >ᵍ RightU u₂
        from-ev (choice-rr-bothempty  proj₁flat-u₁≡[] proj₁flat-u₂≡[] u₁>ˡu₂)  with robust-r
        ... | robust rob-r-ev = choice-rr (proj₂ (rob-r-ev u₁ u₂) u₁>ˡu₂ ) 
        from-ev (choice-rr-notempty  ¬proj₁flat-u₁≡[] ¬proj₁flat-u₂≡[] u₁>ˡu₂)  with robust-r
        ... | robust rob-r-ev = choice-rr (proj₂ (rob-r-ev u₁ u₂) u₁>ˡu₂ ) 
        from-ev (choice-rr-empty  ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[])  with robust-r
        ... | robust rob-r-ev = choice-rr  (rlnn→∷>ᵍ[] rlnn-r u₁ u₂ ¬proj₁flat-u₁≡[] proj₁flat-u₂≡[])  
rlnn→robust {r * ε∉r ` loc} (rlnn-* rlnn-r) =  robust {r * ε∉r ` loc} prf
  where
    robust-r : Robust r
    robust-r = rlnn→robust {r} rlnn-r


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



### Is RLNN necessary?


is this true?

no. counter example

(ε + ε) ● a* ⊢ PairU (LeftU EmptyU) NilU >ˡ PairU (RightU EmptyU) (ConsU a [])

seq₁ (choice-lr-bothempty refl refl)



postulate
  ∷>ˡ[] : ∀ { r : RE } { u v : U r } 
    → ¬ proj₁ (flat u) ≡ []
    → proj₁ (flat v) ≡ []
    ------------------------
    → r ⊢ u >ˡ v 



```agda

robust→rlnn : ∀ { r : RE }
  → Robust r 
  → RLNN r
robust→rlnn {ε}           (robust {ε} robust-ev)             = rlnn-ε
robust→rlnn {$ c ` loc}   (robust {$ _ ` _ } robust-ev)      = rlnn-$ {c} {loc}
robust→rlnn {l ● r ` loc} (robust {_ ● _ ` _} robust-l●r-ev) = rlnn-● rlnn-l rlnn-r -- we need lnn-l here not rlnn-l 
  where
    u : U r
    u = proj₁ (r-∃u r) 
    robust-l-ev : ∀ ( v₁ : U l ) → ( v₂ : U l )
      → ( l ⊢ v₁ >ᵍ v₂ → l ⊢ v₁ >ˡ v₂ ) × ( l ⊢ v₁ >ˡ v₂ → l ⊢ v₁ >ᵍ v₂ )
    robust-l-ev v₁ v₂ with robust-l●r-ev (PairU v₁ u) (PairU v₂ u)
    ... | v₁u>ᵍv₂u→v₁u>ˡv₂u , v₁u>ˡv₂u→v₁u>ᵍv₂u = v₁>ᵍv₂→v₁>ˡv₂ , v₁>ˡv₂→v₁>ᵍv₂   
      where
        v₁>ᵍv₂→v₁>ˡv₂ : l ⊢ v₁ >ᵍ v₂ → l ⊢ v₁ >ˡ v₂
        v₁>ᵍv₂→v₁>ˡv₂ v₁>ᵍv₂ with v₁u>ᵍv₂u→v₁u>ˡv₂u (GreedyOrder.seq₁ v₁>ᵍv₂)
        ... | LNEOrder.seq₁ v₁>ˡv₂ = v₁>ˡv₂
        ... | LNEOrder.seq₂ v₁≡v₂ u>ˡu = Nullary.contradiction v₁≡v₂ (>ᵍ→¬≡  v₁>ᵍv₂)
        v₁>ˡv₂→v₁>ᵍv₂ : l ⊢ v₁ >ˡ v₂ → l ⊢ v₁ >ᵍ v₂
        v₁>ˡv₂→v₁>ᵍv₂ v₁>ˡv₂ with v₁u>ˡv₂u→v₁u>ᵍv₂u (LNEOrder.seq₁ v₁>ˡv₂)
        ... | GreedyOrder.seq₁ v₁>ᵍv₂ = v₁>ᵍv₂
        ... | GreedyOrder.seq₂ v₁≡v₂ u>ᵍu = Nullary.contradiction v₁≡v₂ (>ˡ→¬≡ v₁>ˡv₂)         
    robust-l : Robust l
    robust-l = robust {l} robust-l-ev 
    rlnn-l : RLNN l
    rlnn-l = robust→rlnn {l} robust-l
    v : U l
    v = proj₁ (r-∃u l)
    robust-r-ev : ∀ ( u₁ : U r ) → ( u₂ : U r )
      → ( r ⊢ u₁ >ᵍ u₂ → r ⊢ u₁ >ˡ u₂ ) × ( r ⊢ u₁ >ˡ u₂ → r ⊢ u₁ >ᵍ u₂ )
    robust-r-ev u₁ u₂ with robust-l●r-ev (PairU v u₁) (PairU v u₂)
    ... | vu₁>ᵍvu₂→vu₁>ˡvu₂ , vu₁>ˡvu₂→vu₁>ᵍvu₂ = u₁>ᵍu₂→u₁>ˡu₂ , u₁>ˡu₂→u₁>ᵍu₂
      where
        u₁>ᵍu₂→u₁>ˡu₂ : r ⊢ u₁ >ᵍ u₂ → r ⊢ u₁ >ˡ u₂
        u₁>ᵍu₂→u₁>ˡu₂ u₁>ᵍu₂ with vu₁>ᵍvu₂→vu₁>ˡvu₂ (GreedyOrder.seq₂ refl u₁>ᵍu₂)
        ... | LNEOrder.seq₁ v>ˡv = Nullary.contradiction refl (>ˡ→¬≡ v>ˡv)
        ... | LNEOrder.seq₂ refl u₁>ˡu₂ = u₁>ˡu₂
        u₁>ˡu₂→u₁>ᵍu₂ : r ⊢ u₁ >ˡ u₂ → r ⊢ u₁ >ᵍ u₂ 
        u₁>ˡu₂→u₁>ᵍu₂ u₁>ˡu₂ with vu₁>ˡvu₂→vu₁>ᵍvu₂ (LNEOrder.seq₂ refl u₁>ˡu₂)
        ... | GreedyOrder.seq₁ v>ᵍv = Nullary.contradiction refl (>ᵍ→¬≡ v>ᵍv)
        ... | GreedyOrder.seq₂ refl u₁>ᵍu₂ = u₁>ᵍu₂
    robust-r : Robust r
    robust-r = robust {r} robust-r-ev 
    rlnn-r : RLNN r
    rlnn-r = robust→rlnn {r} robust-r

robust→rlnn {l + r ` loc} (robust {_ + _ ` _} robust-l+r-ev) = rlnn-+ ε∈l→ε≅r lnn-l rlnn-r
  where
    ε∈l→ε≅r : ε∈ l → ε≅ r
    ε∈l→ε≅r = {!!}
    robust-l-ev : ∀ ( v₁ : U l ) → ( v₂ : U l )
      → ( l ⊢ v₁ >ᵍ v₂ → l ⊢ v₁ >ˡ v₂ ) × ( l ⊢ v₁ >ˡ v₂ → l ⊢ v₁ >ᵍ v₂ )
    robust-l-ev v₁ v₂ with robust-l+r-ev (LeftU v₁) (LeftU v₂)
    ... | left-v₁>ᵍleft-v₂→left-v₁>ˡleft-v₂ , left-v₁>ˡleft-v₂→left-v₁>ᵍleft-v₂ =  v₁>ᵍv₂→v₁>ˡv₂ , v₁>ˡv₂→v₁>ᵍv₂
      where
        v₁>ᵍv₂→v₁>ˡv₂ : l ⊢ v₁ >ᵍ v₂ → l ⊢ v₁ >ˡ v₂
        v₁>ᵍv₂→v₁>ˡv₂ v₁>ᵍv₂ with left-v₁>ᵍleft-v₂→left-v₁>ˡleft-v₂ (choice-ll v₁>ᵍv₂)
        ... | choice-ll-bothempty proj₁flat-v₁≡[] proj₁flat-v₂≡[] v₁>ˡv₂ = v₁>ˡv₂
        ... | choice-ll-notempty ¬proj₁flat-v₁≡[] ¬proj₁flat-v₂≡[] v₁>ˡv₂ = v₁>ˡv₂
        ... | choice-ll-empty ¬proj₁flat-v₁≡[] proj₁flat-v₂≡[] = {!!}  --  ∷>ˡ[]  ¬proj₁flat-v₁≡[] proj₁flat-v₂≡[]  -- this is not true! -- this means (l + r) is robust does not implies l is robust!!!? 
        v₁>ˡv₂→v₁>ᵍv₂ : l ⊢ v₁ >ˡ v₂ → l ⊢ v₁ >ᵍ v₂
        v₁>ˡv₂→v₁>ᵍv₂ = {!!}
    robust-l : Robust l
    robust-l = robust {l} robust-l-ev         
    lnn-l : LNN l
    lnn-l = {!!} -- can be proven similarly to the ● case above 
    rlnn-r : RLNN r
    rlnn-r = {!!}


```
