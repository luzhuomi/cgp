```agda
{-# OPTIONS --rewriting  #-}
-- {-# OPTIONS --rewriting --allow-unsolved-metas #-}
module cgp.lnegen.Max where

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
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ; mkinjFstSoundEv ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ;
  concatmap-pdinstance-snd ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with 
  ) 


import cgp.lnegen.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; 
  advance-pdi*-with-c ; 
  pdUMany[_,_]; pdUMany-aux ;
  mkinjLetter ; mkinjLetterSound 
  ) 

import cgp.lnegen.Order as Order
open Order -- TODO: we should only whitelist those are used here 

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; _≟_ )



import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; trans; sym; cong; cong₂; cong-app; subst)
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

import Data.Empty using (⊥ ; ⊥-elim)
open Data.Empty

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; ⌊_⌋; True; toWitness; fromWitness; _×-dec_; _⊎-dec_; ¬?)

open import Function using (_∘_ ; flip ; case_of_)


```


#### ParseAll is not sorted


The following is defined in lnegen/PartialDerivative
  -- ((a●(ε+ε))●(ε+b))●(ε+b)
  a●ε+ε●ε+b●ε+b = ( ( (($ 'a' ` 1) ● ( ε + ε ` 2) ` 3) ● ( ε + ($ 'b' ` 4) ` 5) ` 6) ● (ε + ($ 'b' ` 7) ` 8) ` 9 )
  ex_sss : List (U a●ε+ε●ε+b●ε+b)
  ex_sss = parseAll[ a●ε+ε●ε+b●ε+b ,  'a' ∷ 'b' ∷  [] ]

ExampleParseAll.ex_sss

should yield

~~~~~~~

PairU (PairU (PairU (LetterU 'a') (LeftU EmptyU))   (RightU (LetterU 'b'))) (LeftU EmptyU) -- (a)
∷
PairU (PairU (PairU (LetterU 'a') (RightU EmptyU))  (RightU (LetterU 'b'))) (LeftU EmptyU) -- (b)
∷
PairU (PairU (PairU (LetterU 'a') (LeftU EmptyU)) (LeftU EmptyU)) (RightU (LetterU 'b'))   -- (c)
∷
PairU (PairU (PairU (LetterU 'a') (RightU EmptyU)) (LeftU EmptyU)) (RightU (LetterU 'b'))  -- (d)
∷ []


```agda
a●ε+ε●ε+b●ε+b : RE 
a●ε+ε●ε+b●ε+b = ( ( (($ 'a' ` 1) ● ( ε + ε ` 2) ` 3) ● ( ε + ($ 'b' ` 4) ` 5) ` 6) ● (ε + ($ 'b' ` 7) ` 8) ` 9 )
t_a t_b t_c t_d : U a●ε+ε●ε+b●ε+b
t_a = PairU (PairU (PairU (LetterU 'a') (LeftU EmptyU))   (RightU (LetterU 'b'))) (LeftU EmptyU) -- (a)
t_b = PairU (PairU (PairU (LetterU 'a') (RightU EmptyU))  (RightU (LetterU 'b'))) (LeftU EmptyU) -- (b)
t_c = PairU (PairU (PairU (LetterU 'a') (LeftU EmptyU)) (LeftU EmptyU)) (RightU (LetterU 'b'))   -- (c)
t_d = PairU (PairU (PairU (LetterU 'a') (RightU EmptyU)) (LeftU EmptyU)) (RightU (LetterU 'b'))  -- (d)

t_a>t_b : a●ε+ε●ε+b●ε+b ⊢ t_a > t_b
t_a>t_b = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₁
                                                           (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                            (seq₂ refl (be refl refl choice-lr))))) )

t_c>t_d : a●ε+ε●ε+b●ε+b ⊢ t_c > t_d
t_c>t_d = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₁
                                                           (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                            (seq₂ refl (be refl refl choice-lr))))) )

t_a>t_d : a●ε+ε●ε+b●ε+b ⊢ t_a > t_d
t_a>t_d = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₁
                                                           (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                            (seq₂ refl (be refl refl choice-lr))))))

t_a>t_c : a●ε+ε●ε+b●ε+b ⊢ t_a > t_c
t_a>t_c = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₂ refl (lne (Nat.s≤s Nat.z≤n) refl))) )


t_b>t_d : a●ε+ε●ε+b●ε+b ⊢ t_b > t_d
t_b>t_d = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₂ refl (lne (Nat.s≤s Nat.z≤n) refl))) )


-- however instead of t_b>t_c, we have

t_c>t_b : a●ε+ε●ε+b●ε+b ⊢ t_c > t_b
t_c>t_b = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₁
                                                           (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                            (seq₂ refl (be refl refl choice-lr))))))


```

The breakdown of parseAll[ a●ε+ε●ε+b●ε+b ,  'a' ∷ 'b' ∷  [] ]

We omit the number annotation

( (a ● (ε + ε ) ) ● ( ε + b ) ) ● ( ε + b)
               | a in₁
  ( (ε ● (ε + ε ) ) ● ( ε + b ) ) ● ( ε + b)
             /b in₂      \ b in₃
 ε ● (ε + b)                  ε
 PairU EmptyU (LeftU EmptyU)  EmptyU

in₂ (PairU EmptyU (Left EmptyU)) =
  [ PairU (PairU (PairU EmptyU (LeftU EmptyU)) (RightU (LetterU 'b'))) (LeftU EmptyU)    --(a')
  , PairU (PairU (PairU EmptyU (RightU EmptyU)) (RightU (LetterU 'b'))) (LeftU EmptyU)   --(b')
  ]

in₃ EmptyU =
  [ PairU (PairU (PairU EmptyU (LeftU EmptyU)) (LeftU EmptyU)) (RightU (LetterU 'b'))    --(c')
  , PairU (PairU (PairU EmptyU (RightU EmptyU)) (LeftU EmptyU)) (RightU (LetterU 'b'))   --(d')
  ] 



```agda
ε●ε+ε●ε+b●ε+b : RE 
ε●ε+ε●ε+b●ε+b = ( ( (ε ● ( ε + ε ` 2) ` 3) ● ( ε + ($ 'b' ` 4) ` 5) ` 6) ● (ε + ($ 'b' ` 7) ` 8) ` 9 )

t_a' t_b' t_c' t_d' : U ε●ε+ε●ε+b●ε+b
t_a' = PairU (PairU (PairU EmptyU (LeftU EmptyU))  (RightU (LetterU 'b'))) (LeftU EmptyU)
t_b' = PairU (PairU (PairU EmptyU (RightU EmptyU)) (RightU (LetterU 'b'))) (LeftU EmptyU)
t_c' = PairU (PairU (PairU EmptyU (LeftU EmptyU))  (LeftU EmptyU))         (RightU (LetterU 'b'))
t_d' = PairU (PairU (PairU EmptyU (RightU EmptyU)) (LeftU EmptyU))         (RightU (LetterU 'b'))

-- the > order is total, hence the following is good enough
t_a'>t_b' : ε●ε+ε●ε+b●ε+b ⊢ t_a' > t_b'
t_a'>t_b' = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                            (seq₁ (be refl refl (seq₂ refl (be refl refl choice-lr))))) )
t_b'>t_c' : ε●ε+ε●ε+b●ε+b ⊢ t_b' > t_c'
t_b'>t_c' = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (lne (Nat.s≤s Nat.z≤n) refl) )

t_c'>t_d' : ε●ε+ε●ε+b●ε+b ⊢ t_c' > t_d'
t_c'>t_d' = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (be refl refl
                                                            (seq₁ (be refl refl (seq₂ refl (be refl refl choice-lr))))) )


-- my_in₁' : U ((ε●(ε+ε))●(ε+b)) → U  ((a●(ε+ε))●(ε+b))
my_in₁' : U  ( (ε ● ( ε + ε ` 2) ` 3) ● ( ε + ($ 'b' ` 4) ` 5) ` 6)  → U  ( (($ 'a' ` 1) ● ( ε + ε ` 2) ` 3) ● ( ε + ($ 'b' ` 4) ` 5) ` 6)
my_in₁' (PairU (PairU EmptyU lr-emp) l-empty-r-b) =
        PairU (PairU (LetterU 'a') lr-emp) l-empty-r-b
-- my_in₁ : U ((ε●(ε+ε))●(ε+b))●(ε+b) → U  ((a●(ε+ε))●(ε+b))●(ε+b)
my_in₁ : U ( ( (ε ● ( ε + ε ` 2) ` 3) ● ( ε + ($ 'b' ` 4) ` 5) ` 6) ● (ε + ($ 'b' ` 7) ` 8) ` 9 ) → U ( ( (($ 'a' ` 1) ● ( ε + ε ` 2) ` 3) ● ( ε + ($ 'b' ` 4) ` 5) ` 6) ● (ε + ($ 'b' ` 7) ` 8) ` 9 )
-- my_in₁ (PairU (PairU (PairU EmptyU lr-emp) l-empty-r-b) l-empty-r-b') =
  -- (PairU (PairU (PairU (LetterU 'a') lr-emp) l-empty-r-b) l-empty-r-b')
my_in₁ = mkinjFst my_in₁' 

_ : my_in₁ t_a' ≡ t_a
_ = refl

_ : my_in₁ t_b' ≡ t_b
_ = refl

_ : my_in₁ t_c' ≡ t_c
_ = refl


_ : my_in₁ t_d' ≡ t_d
_ = refl
```

Hence the order > is not preserved by injection, because injection is not monotonic.

ParseAll should maintain the property that the first element is the maximal.

Maximality must be bounded by the flatten word, otherwise, it might not exist.

```agda

a* : RE
a* = ($ 'a' ` 1) * ε∉$ ` 2

aa aaa : U a*
aa = ListU ((LetterU 'a') ∷ (LetterU 'a') ∷ [])

aaa = ListU ((LetterU 'a') ∷ (LetterU 'a') ∷ (LetterU 'a') ∷ [])

aaa>aa : a* ⊢ aaa > aa
aaa>aa = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (star-tail refl (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                                   (star-tail refl (lne (Nat.s≤s Nat.z≤n) refl)))) 
```

we have aaaa > aaa , aaaaa > aaaa, ... 


```agda
data ≥-Max : ∀ { r : RE } → U r → Set where 
  ≥-max : ∀ { r : RE }
        → ( u : U r )
        → ( ( v : U r )
          → ( proj₁ (flat u ) ≡ proj₁ (flat v))
          → r ⊢ u ≥ v )
        → ≥-Max {r} u

-- each partial derivative p is unique

data ≥-Max-Preserve : ∀ { r : RE } { c : Char } → PDInstance r c → Set where
  ≥-max-pres : ∀ { p r : RE } { c : Char } { inj : U p →  U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ≥-Max u -- ∀ (v : U p) →  |u|≡|v| → p ⊢ u ≥ v
      → ( v : U p )
      → ( proj₁ (flat u ) ≡ proj₁ (flat v)) -- too weak? , t_b' > t_c', but t_c > t_b, but t_b is not max. t_a is max. t_b' is not max, t_a' is max. 
      → r ⊢ inj u ≥ inj v ) -- local max w.r.t to the inj
    → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
    -- shouldn't the above be
    {- ( ( u : U p)
      → ≥-Max u
      → ≥-Max (inj u) ) -- this is too strong, requiring inj having all other parts are max too, e.g. mkSndInj inj e. e must be max, e is max is ok, because it is []
    -} 


      
  {- this leads to negative data type definition
  ≥-max-pres-●-f : ∀ { p l r : RE } { loc : ℕ }  { c : Char }  { inj : U p →  U l }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {l} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u : U p )
      → ≥-Max u
      → ( v : U r )
      → ≥-Max v
      → ( y : U p )
      →  proj₁ (flat u ) ≡ proj₁ (flat y) 
      → ≥-Max-Preserve {l} {c} (pdinstance inj sound-ev)
      → ( l ● r ` loc ) ⊢ mkinjFst inj (PairU u v) ≥ mkinjFst inj (PairU y v ) )
    → ≥-Max-Preserve {l ● r ` loc} {c} (pdinstance-fst (pdinstance inj sound-ev))
  -} 

≥-max-pair-inv : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( u : U l )
  → ( v : U r )
  → ≥-Max (PairU {l} {r} {loc} u v)
  → ≥-Max u × ≥-Max v
≥-max-pair-inv {l} {r} {loc} {c} u v (≥-max (PairU .u .v) pair-u'-v'→|uv|≡|u'v'|→uv≥u'v')  =
   ≥-max u ev₁  , ≥-max v ev₂
   where
     extract-≥-fst : ∀ {u₁ u₂ : U l} {v₁ : U r}
       → proj₁ (flat u₁) ≡ proj₁ (flat u₂)
       → (l ● r ` loc) ⊢ PairU u₁ v₁ ≥ PairU u₂ v₁
       → l ⊢ u₁ ≥ u₂
     extract-≥-fst _ (inj₁ (be _ _ (seq₁ u₁>u₂))) = inj₁ u₁>u₂
     extract-≥-fst _ (inj₁ (be _ _ (seq₂ refl v₁>v₁))) = ⊥-elim (>→¬≡ v₁>v₁ refl)
     extract-≥-fst _ (inj₁ (bne _ _ (seq₁ u₁>u₂))) = inj₁ u₁>u₂
     extract-≥-fst _ (inj₁ (bne _ _ (seq₂ refl v₁>v₁))) = ⊥-elim (>→¬≡ v₁>v₁ refl)
     extract-≥-fst {u₁} {u₂} {v₁} flat-u₁≡flat-u₂ (inj₁ (lne len>0 len≡0)) =
       ⊥-elim (n≡0→¬n>0 len-u₁v₁≡0 len>0)
       where
         len-u₁v₁≡len-u₂v₁ : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ length (proj₁ (flat (PairU {l} {r} {loc} u₂ v₁)))
         len-u₁v₁≡len-u₂v₁ = cong length (cong (λ w → w List.++ proj₁ (flat v₁)) flat-u₁≡flat-u₂)
         len-u₁v₁≡0 : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ 0
         len-u₁v₁≡0 = trans len-u₁v₁≡len-u₂v₁ len≡0
     extract-≥-fst _ (inj₂ refl) = inj₂ refl

     ev₁ : (u₁ : U l) → proj₁ (flat u) ≡ proj₁ (flat u₁) → l ⊢ u ≥ u₁
     ev₁ u₁ flat-u≡flat-u₁ =
       extract-≥-fst flat-u≡flat-u₁
         (pair-u'-v'→|uv|≡|u'v'|→uv≥u'v' (PairU u₁ v)
           (cong (λ w → w List.++ proj₁ (flat v)) flat-u≡flat-u₁))

     extract-≥-snd : ∀ {u₁ : U l} {v₁ v₂ : U r}
       → proj₁ (flat v₁) ≡ proj₁ (flat v₂)
       → (l ● r ` loc) ⊢ PairU u₁ v₁ ≥ PairU u₁ v₂
       → r ⊢ v₁ ≥ v₂
     extract-≥-snd _ (inj₁ (be _ _ (seq₂ refl v₁>v₂))) = inj₁ v₁>v₂
     extract-≥-snd _ (inj₁ (be _ _ (seq₁ u₁>u₁))) = ⊥-elim (>→¬≡ u₁>u₁ refl)
     extract-≥-snd _ (inj₁ (bne _ _ (seq₂ refl v₁>v₂))) = inj₁ v₁>v₂
     extract-≥-snd _ (inj₁ (bne _ _ (seq₁ u₁>u₁))) = ⊥-elim (>→¬≡ u₁>u₁ refl)
     extract-≥-snd {u₁} {v₁} {v₂} flat-v₁≡flat-v₂ (inj₁ (lne len>0 len≡0)) =
        ⊥-elim (n≡0→¬n>0 len-u₁v₁≡0 len>0)
        where
          len-u₁v₁≡len-u₁v₂ : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₂)))
          len-u₁v₁≡len-u₁v₂ = cong length (cong (proj₁ (flat u₁) List.++_) flat-v₁≡flat-v₂)
          len-u₁v₁≡0 : length (proj₁ (flat (PairU {l} {r} {loc} u₁ v₁))) ≡ 0
          len-u₁v₁≡0 = trans len-u₁v₁≡len-u₁v₂ len≡0
     extract-≥-snd _ (inj₂ refl) = inj₂ refl

     ev₂ : (v₂ : U r) → proj₁ (flat v) ≡ proj₁ (flat v₂) → r ⊢ v ≥ v₂
     ev₂ v₂ flat-v≡flat-v₂ =
       extract-≥-snd flat-v≡flat-v₂
         (pair-u'-v'→|uv|≡|u'v'|→uv≥u'v' (PairU u v₂)
           (cong (proj₁ (flat u) List.++_) flat-v≡flat-v₂)) 
       

-- do we have some thing like ≥-Max-Preserve but for the first of a pair parse tree?
       
≥-max-pres-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-left pdi)
≥-max-pres-left {l} {r} {loc} {c} (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres u→max-u→v→|u|≡|v|→inj-u≥inj-v) =
  ≥-max-pres (λ u max-u v |u|≡|v| → left-mono-≥ (u→max-u→v→|u|≡|v|→inj-u≥inj-v u max-u v |u|≡|v|))


≥-max-pres-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance r c )
  → ≥-Max-Preserve {r} {c} pdi
  → ≥-Max-Preserve {l + r ` loc} {c} (pdinstance-right pdi)
≥-max-pres-right {l} {r} {loc} {c} (pdinstance {p} .{r} .{c} inj s-ev) (≥-max-pres u→max-u→v→|u|≡|v|→inj-u≥inj-v) =
  ≥-max-pres (λ u max-u v |u|≡|v| → right-mono-≥ (u→max-u→v→|u|≡|v|→inj-u≥inj-v u max-u v |u|≡|v|))        

-- is this useful?
≥-max-pres-●-fst :  ∀ { p l r : RE } { loc : ℕ }  { c : Char }  { inj : U p →  U l }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {l} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ≥-Max-Preserve {l} {c} (pdinstance inj sound-ev)
    → ( u : U p )
    → ≥-Max u
    → ( v : U r )
    → ≥-Max v
    → ( y : U p )
    →  proj₁ (flat u ) ≡ proj₁ (flat y) 
    → ( l ● r ` loc ) ⊢ mkinjFst inj (PairU u v) ≥ mkinjFst inj (PairU y v )
≥-max-pres-●-fst {p} {l} {r} {loc} {c} {inj} {s-ev} (≥-max-pres u→maxu→v→|u|≡|v|→u≥v)
  u (≥-max .(u) v→|u|≡|v|→u≥v) v ≥-max-v y |u|≡|y|
  with u→maxu→v→|u|≡|v|→u≥v u (≥-max u v→|u|≡|v|→u≥v) y |u|≡|y|
... | inj₁ inj-u>inj-y = inj₁ (bne len>0 len>0 (seq₁ inj-u>inj-y))
  where
    len>0 : ∀ {w} → length (proj₁ (flat (PairU {l} {r} {loc} (inj w) v))) Nat.> 0
    len>0 {w} rewrite s-ev w = Nat.s≤s Nat.z≤n
... | inj₂ inj-u≡inj-y rewrite inj-u≡inj-y = inj₂ refl


-- is this useful?
-- the following is a "monomorphized" version of the ≥-Max-Preserve 
data ≥-Max-Fst : ∀ { l r : RE } { loc : ℕ } { c : Char } → ( PDInstance ( l ● r ` loc ) c ) → Set where
  ≥-max-fst : ∀ { p l r : RE } { loc : ℕ } { c : Char } { inj : U p → U l }
    { sound-ev : ∀ ( x : U p ) → (proj₁ (flat {l} (inj x))) ≡ c ∷ ( proj₁ (flat {p} x )) }
    → ( ( u : U p )
      → ( v : U r )
      → ≥-Max (PairU {p} {r} {loc} u v)
      → ( u' : U p )
      → ( v' : U r ) 
      → ( proj₁ (flat (PairU {p} {r} {loc} u v)) ≡ proj₁ (flat (PairU {p} {r} {loc} u' v')) )
      → l ● r ` loc ⊢ mkinjFst inj (PairU u v) ≥ mkinjFst inj (PairU u' v') )
    → ≥-Max-Fst {l} {r} {loc} {c} (pdinstance-fst (pdinstance inj sound-ev))

-- this data type looks similar to ≥-max-pres-●-fst except that v ≡ v'.
-- if ≥-max-pres-●-fst is provable why ≥-pres0-fst is not?

-- this is what we want but hard.
-- this leads us to MaxPre.lagda.md
≥-max-pres-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {c} pdi
  → ≥-Max-Preserve {l ● r ` loc} {c} (pdinstance-fst pdi)
≥-max-pres-fst {l} {r} {loc} {c}  (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres u→maxu→v→|u|≡|v|→inju≥injv) =
  ≥-max-pres prf
  where
    prf : (u : U (p ● r ` loc))
        → ≥-Max u
        → (v : U (p ● r ` loc))
        → proj₁ (flat u) ≡ proj₁ (flat v)
        → (l ● r ` loc) ⊢ mkinjFst inj u ≥ mkinjFst inj v
    prf (PairU v₁ v₂)
        ≥-max-v₁v₂@(≥-max (PairU .v₁ .v₂) pair-v₁'v₂'→|v₁v₂|≡|v₁'v₂'|→pair-v₁v₂>pair-v₁'v₂')
        (PairU v₁' v₂')
        |v₁v₂|≡|v₁'v₂'|
        with pair-v₁'v₂'→|v₁v₂|≡|v₁'v₂'|→pair-v₁v₂>pair-v₁'v₂' (PairU v₁' v₂') |v₁v₂|≡|v₁'v₂'|
    ... | inj₁ (be len|v₁v₂|≡len|v₁'v₂'| len|v₁v₂|≡0 pairv₁v₂>ⁱpairv₁'v₂') = {!!}
          -- from len|v₁v₂|≡len|v₁'v₂'| len|v₁v₂|≡0 we have len|v₁'v₂'|≡0, hence
          -- len|v₁|≡len|v₁'|≡0 hence |v₁|≡|v₁'|≡[]
          -- we apply u→maxu→v→|u|≡|v|→inju≥injv to v₁ max-v₁ v₁' |v₁|≡|v₁'|to get inj v₁ ≥ inj v₂
          -- if inj v₁ > inj v₂, we prove it with bne _ _ (seq₁ ...)
          -- if inj v₁ ≡ inj v₂, we know pairv₁v₂>ⁱpairv₁'v₂' must be seq₂ v₂>v₂'
          --                     we prove it with bne _ _ (seq₂ ...) 
    ... | inj₁ (lne len|v₁v₂|>0 len|v₁'v₂'|≡0) = {!!} -- ? 
    ... | inj₁ (bne len|v₁v₂|>0 len|v₁'v₂'|>0 pairv₁v₂>ⁱpairv₁'v₂') = {!!}
          -- from ≥-max-pair-inv, we have ≥-max v₁ and ≥-max v₂
          -- how to get |v₁|≡|v₁'| ?? which is needed to apply  u→maxu→v→|u|≡|v|→inju≥inj to get inj v₁ ≥ inj v₁' 
    ... | inj₂ pair-v₁v₂≡pair-v₁'v₂' rewrite sym pair-v₁v₂≡pair-v₁'v₂' = inj₂ {!!}  -- using pair-inv we have v₁≡v₁' and v₂≡v₂' 
      -- the length diff betwen v₁ and v₁' and v₂ and v₂' are 0 or 1?
      -- let say inj is my_in₁'
      -- mkinjFst inj is my_in₁ 
      -- issue: we don't have |v₁|≡|v₁'| and |v₂|≡|v₂'|
      -- what if we enforce the same constraint as ≅ in PrefEq?
      -- it should work but
      -- what aboit the concatmap-advance-pdi-with-c in ExtenedOrder? 
  



≥-max-pres-●-snd : ∀ { p l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( u : U p )
    → ≥-Max u
    → ( e : U l )
    → Flat-[] l e
    → ≥-Max e
    → ( y : U p )
    → proj₁ (flat u) ≡ proj₁ (flat y)
    → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
    → ( l ● r ` loc ) ⊢ mkinjSnd inj e u ≥  mkinjSnd inj e y
≥-max-pres-●-snd {p} {l} {r} {ε∈l} {loc} {c} {inj} {s-ev} u max-u e (flat-[] .e flat-e≡[]) max-e y flat-u≡flat-y (≥-max-pres f) =
  aux (f u max-u y flat-u≡flat-y)
  where
    len>0-inj : (w : U p) → length (proj₁ (flat (inj w))) Nat.> 0
    len>0-inj w rewrite s-ev w = Nat.s≤s Nat.z≤n

    len>0-pair : (w : U p) → length (proj₁ (flat (PairU {l} {r} {loc} e (inj w)))) Nat.> 0
    len>0-pair w rewrite flat-e≡[] | s-ev w = Nat.s≤s Nat.z≤n

    aux : r ⊢ inj u ≥ inj y → (l ● r ` loc) ⊢ mkinjSnd inj e u ≥ mkinjSnd inj e y
    aux (inj₁ (be _ len0 _)) = ⊥-elim (n≡0→¬n>0 len0 (len>0-inj y))
    aux (inj₁ (bne _ _ inj-u>ⁱinj-y)) =
      inj₁ (bne {l ● r ` loc} {PairU {l} {r} {loc} e (inj u)} {PairU {l} {r} {loc} e (inj y)}
        (len>0-pair u) (len>0-pair y)
        (seq₂ {l} {r} {loc} {e} {e} {inj u} {inj y} refl
          (bne {r} {inj u} {inj y} (len>0-inj u) (len>0-inj y) inj-u>ⁱinj-y)))
    aux (inj₁ (lne _ len0)) = ⊥-elim (n≡0→¬n>0 len0 (len>0-inj y))
    aux (inj₂ eq) = inj₂ (cong (PairU {l} {r} {loc} e) eq) 





≥-max-pres-* : ∀ { p r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( u : U p )
    → ≥-Max u
    → ( vs : U (r * ε∉r ` loc )  )
    → ≥-Max vs
    → ( y : U p )
    → ( proj₁ (flat u ) ≡ proj₁ (flat y) )
    → ≥-Max-Preserve {r} {c} (pdinstance inj sound-ev)
    → ( r * ε∉r ` loc ) ⊢ mkinjList inj (PairU u vs) ≥ mkinjList inj (PairU y vs )
≥-max-pres-*  {p} {r} {ε∉r} {loc} {c} {inj} {s-ev} u (≥-max .(u) v→|u|≡|v|→u≥v) (ListU vs) ≥-max-list-vs y |u|≡|y|
  (≥-max-pres u→maxu→v→|u|≡|v|→u≥v)
  with  u→maxu→v→|u|≡|v|→u≥v u (≥-max u v→|u|≡|v|→u≥v) y |u|≡|y|
... | inj₁ inj-u>inj-y = inj₁ (bne len>0 len>0 (star-head inj-u>inj-y))
  where
    len>0 : ∀ {w} → length (proj₁ (flat (ListU {r} {ε∉r}  {loc} ((inj w) ∷ vs )))) Nat.> 0
    len>0 {w} rewrite s-ev w = Nat.s≤s Nat.z≤n
... | inj₂ inj-u≡inj-y rewrite inj-u≡inj-y = inj₂ refl 




-- pdU-≥-max-pres : ∀ {r : RE } { c : Char }
--   → 
  
{-

-- fst
-- not provable 
≥-max-pres-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≥-Max-Preserve {l} {c} pdi
  → ≥-Max-Preserve {l ● r ` loc} {c} (pdinstance-fst pdi)
≥-max-pres-fst {l} {r} {loc} {c}  (pdinstance {p} .{l} .{c} inj s-ev) (≥-max-pres f) =
  ≥-max-pres (λ { (PairU u₁ u₂) max-u'@(≥-max .(PairU u₁ u₂) h) (PairU v₁ v₂) flat-eq →
    let max₁ = max-u₁ max-u'
        max₂ = max-u₂ max-u'
    in case h (PairU v₁ v₂) flat-eq of λ {
      (inj₁ (be len≡ len0 seq)) →
        case seq of λ {
          (seq₁ u₁>v₁) →
            let flat-u₁≡[] = ++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat u₂)) (length≡0→[] (trans len≡ len0))
                flat-v₁≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) (length≡0→[] len0)
            in case-flat-eq max₁ max₂ flat-eq (trans flat-u₁≡[] (sym flat-v₁≡[]))
        ; (seq₂ u₁≡v₁ _) →
            case-flat-eq max₁ max₂ flat-eq (cong proj₁ (cong flat u₁≡v₁))
        }
    ; (inj₁ (bne len>0 len>0' (seq₂ u₁≡v₁ u₂>v₂))) →
        case-flat-eq max₁ max₂ flat-eq (cong proj₁ (cong flat u₁≡v₁))
    ; (inj₁ (bne len>0 len>0' (seq₁ u₁>v₁))) →
        case u₁>v₁ of λ {
          (be len≡' len0' _) →
            let flat-u₁≡[] = length≡0→[] (trans len≡' len0')
                flat-v₁≡[] = length≡0→[] len0'
            in case-flat-eq max₁ max₂ flat-eq (trans flat-u₁≡[] (sym flat-v₁≡[]))
        ; (bne lenu₁>0 lenv₁>0 u₁>ⁱv₁) →
            {!!}
            -- COUNTEREXAMPLE: when p = ε ● ($ a + ε), r = $ a + ε,
            -- u₁ = PairU EmptyU (LeftU (LetterU 'a')), u₂ = RightU EmptyU,
            -- v₁ = PairU EmptyU (RightU EmptyU), v₂ = LeftU (LetterU 'a'),
            -- the goal is unprovable because l ⊢ inj u₁ > inj v₁ is impossible
            -- (lengths differ: 2 vs 1) and inj u₁ ≢ inj v₁.
        ; (lne lenu₁>0 lenv₁≡0) →
            {!!}
            -- Similarly unprovable: flat v₁ ≡ [] but flat u₁ is non-empty,
            -- so l ⊢ inj u₁ > inj v₁ is impossible (no applicable > constructor).
        }
    ; (inj₁ (lne len>0 len0)) →
        let flat-v₁v₂≡[] = length≡0→[] len0
            flat-v₁≡[] = ++-conicalˡ (proj₁ (flat v₁)) (proj₁ (flat v₂)) flat-v₁v₂≡[]
            flat-v₂≡[] = ++-conicalʳ (proj₁ (flat v₁)) (proj₁ (flat v₂)) flat-v₁v₂≡[]
            flat-u₁u₂≡[] = trans flat-eq (cong₂ _++_ flat-v₁≡[] flat-v₂≡[])
            len-pair≡0 = cong length flat-u₁u₂≡[]
        in ⊥-elim (n≡0→¬n>0 len-pair≡0 len>0)
    ; (inj₂ u≡v) →
        let u₁≡v₁ = proj₁ (ParseTree.inv-pairU u₁ u₂ v₁ v₂ u≡v)
            u₂≡v₂ = proj₂ (ParseTree.inv-pairU u₁ u₂ v₁ v₂ u≡v)
        in inj₂ (cong₂ (PairU {l} {r} {loc}) (cong inj u₁≡v₁) u₂≡v₂)
    }
  })
  where
    len>0 : ∀ {u v} → length (proj₁ (flat (PairU {l} {r} {loc} (inj u) v))) Nat.> 0
    len>0 {u} rewrite s-ev u = Nat.s≤s Nat.z≤n

    extract-≥-fst : ∀ {x₁ w₁ : U p} {x₂ : U r}
      → proj₁ (flat x₁) ≡ proj₁ (flat w₁)
      → (p ● r ` loc) ⊢ PairU x₁ x₂ ≥ PairU w₁ x₂
      → p ⊢ x₁ ≥ w₁
    extract-≥-fst _ (inj₁ (be _ _ (seq₁ x₁>w₁))) = inj₁ x₁>w₁
    extract-≥-fst _ (inj₁ (be _ _ (seq₂ refl x₂>x₂))) = ⊥-elim (>→¬≡ x₂>x₂ refl)
    extract-≥-fst _ (inj₁ (bne _ _ (seq₁ x₁>w₁))) = inj₁ x₁>w₁
    extract-≥-fst _ (inj₁ (bne _ _ (seq₂ refl x₂>x₂))) = ⊥-elim (>→¬≡ x₂>x₂ refl)
    extract-≥-fst {x₁} {w₁} {x₂} flat-x₁≡flat-w₁ (inj₁ (lne len-x₁x₂>0 len-w₁x₂≡0)) =
      ⊥-elim (n≡0→¬n>0 len-x₁x₂≡0 len-x₁x₂>0)
      where
        flat-w₁x₂≡[] = length≡0→[] len-w₁x₂≡0
        flat-w₁≡[] = ++-conicalˡ (proj₁ (flat w₁)) (proj₁ (flat x₂)) flat-w₁x₂≡[]
        flat-x₂≡[] = ++-conicalʳ (proj₁ (flat w₁)) (proj₁ (flat x₂)) flat-w₁x₂≡[]
        flat-x₁≡[] = trans flat-x₁≡flat-w₁ flat-w₁≡[]
        flat-x₁x₂≡[] : proj₁ (flat (PairU {p} {r} {loc} x₁ x₂)) ≡ []
        flat-x₁x₂≡[] = subst (λ w → w List.++ proj₁ (flat x₂) ≡ []) (sym flat-x₁≡[]) (trans (++-identityˡ (proj₁ (flat x₂))) flat-x₂≡[])
        len-x₁x₂≡0 = cong length flat-x₁x₂≡[]
    extract-≥-fst _ (inj₂ refl) = inj₂ refl

    max-u₁ : ∀ {x₁ x₂} → ≥-Max {p ● r ` loc} (PairU x₁ x₂) → ≥-Max {p} x₁
    max-u₁ (≥-max (PairU x₁ x₂) h) = ≥-max x₁ (λ w₁ flat-x₁≡flat-w₁ →
      extract-≥-fst flat-x₁≡flat-w₁ (h (PairU w₁ x₂) (cong (_++ proj₁ (flat x₂)) flat-x₁≡flat-w₁)))

    extract-≥-snd : ∀ {x₁ : U p} {x₂ w₂ : U r}
      → proj₁ (flat x₂) ≡ proj₁ (flat w₂)
      → (p ● r ` loc) ⊢ PairU x₁ x₂ ≥ PairU x₁ w₂
      → r ⊢ x₂ ≥ w₂
    extract-≥-snd _ (inj₁ (be _ _ (seq₂ refl x₂>w₂))) = inj₁ x₂>w₂
    extract-≥-snd _ (inj₁ (be _ _ (seq₁ x₁>x₁))) = ⊥-elim (>→¬≡ x₁>x₁ refl)
    extract-≥-snd _ (inj₁ (bne _ _ (seq₂ refl x₂>w₂))) = inj₁ x₂>w₂
    extract-≥-snd _ (inj₁ (bne _ _ (seq₁ x₁>x₁))) = ⊥-elim (>→¬≡ x₁>x₁ refl)
    extract-≥-snd {x₁} flat-x₂≡flat-w₂ (inj₁ (lne len-x₁x₂>0 len-x₁w₂≡0)) =
      ⊥-elim (n≡0→¬n>0 (trans (cong length flat-x₁x₂≡flat-x₁w₂) len-x₁w₂≡0) len-x₁x₂>0)
      where
        flat-x₁x₂≡flat-x₁w₂ = cong (proj₁ (flat x₁) ++_) flat-x₂≡flat-w₂
    extract-≥-snd _ (inj₂ refl) = inj₂ refl

    max-u₂ : ∀ {x₁ x₂} → ≥-Max {p ● r ` loc} (PairU x₁ x₂) → ≥-Max {r} x₂
    max-u₂ (≥-max (PairU x₁ x₂) h) = ≥-max x₂ (λ w₂ flat-x₂≡flat-w₂ →
      extract-≥-snd flat-x₂≡flat-w₂ (h (PairU x₁ w₂) (cong (proj₁ (flat x₁) ++_) flat-x₂≡flat-w₂)))

    case-flat-eq : ∀ {u₁ v₁ : U p} {u₂ v₂ : U r}
      → ≥-Max {p} u₁
      → ≥-Max {r} u₂
      → proj₁ (flat (PairU {p} {r} {loc} u₁ u₂)) ≡ proj₁ (flat (PairU {p} {r} {loc} v₁ v₂))
      → proj₁ (flat u₁) ≡ proj₁ (flat v₁)
      → (l ● r ` loc) ⊢ mkinjFst inj (PairU {p} {r} {loc} u₁ u₂) ≥ mkinjFst inj (PairU {p} {r} {loc} v₁ v₂)
    case-flat-eq {u₁} {v₁} {u₂} {v₂} max₁ (≥-max .u₂ max₂f) flat-eq flat-u₁≡flat-v₁ =
      let flat-u₂≡flat-v₂ : proj₁ (flat u₂) ≡ proj₁ (flat v₂)
          flat-u₂≡flat-v₂ = ++-cancelˡ (proj₁ (flat u₁)) (proj₁ (flat u₂)) (proj₁ (flat v₂))
                              (trans flat-eq (cong (λ w → w List.++ proj₁ (flat v₂)) (sym flat-u₁≡flat-v₁)))
          pair≥ : (l ● r ` loc) ⊢ mkinjFst inj (PairU {p} {r} {loc} u₁ u₂) ≥ mkinjFst inj (PairU {p} {r} {loc} v₁ u₂)
          pair≥ = ≥-max-pres-● {p} {l} {r} {loc} {c} {inj} {s-ev} u₁ max₁ u₂ (≥-max u₂ max₂f) v₁ flat-u₁≡flat-v₁ (≥-max-pres f)
      in combine pair≥ (max₂f v₂ flat-u₂≡flat-v₂)
      where
        combine : (l ● r ` loc) ⊢ mkinjFst inj (PairU u₁ u₂) ≥ mkinjFst inj (PairU v₁ u₂) → r ⊢ u₂ ≥ v₂ → (l ● r ` loc) ⊢ mkinjFst inj (PairU u₁ u₂) ≥ mkinjFst inj (PairU v₁ v₂)
        combine (inj₁ (be _ len0 _)) _ = ⊥-elim (n≡0→¬n>0 len0 len>0)
        combine (inj₁ (lne _ len0)) _ = ⊥-elim (n≡0→¬n>0 len0 len>0)
        combine (inj₁ (bne _ _ (seq₁ inj-u>inj-v))) _ = inj₁ (bne len>0 len>0 (seq₁ inj-u>inj-v))
        combine (inj₁ (bne _ _ (seq₂ _ u₂>u₂))) _ = ⊥-elim (>→¬≡ u₂>u₂ refl)
        combine (inj₂ eq) (inj₁ u₂>v₂) =
          let inj-u₁≡inj-v₁ = proj₁ (ParseTree.inv-pairU (inj u₁) u₂ (inj v₁) u₂ eq)
          in inj₁ (bne len>0 len>0 (seq₂ inj-u₁≡inj-v₁ u₂>v₂))
        combine (inj₂ eq) (inj₂ u₂≡v₂) =
          let inj-u₁≡inj-v₁ = proj₁ (ParseTree.inv-pairU (inj u₁) u₂ (inj v₁) u₂ eq)
          in inj₂ (trans eq (cong (PairU (inj v₁)) u₂≡v₂)) 
-} 
```
