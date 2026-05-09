This module contains the attempt of proving PD Injection monotonicity over lnegen ordering by restricting to Prefix equivalence form.

It all worked without the   ●⊢lne case

however without   ●⊢lne  case we can't proceed with proof in ExtendedOrder as it is too restrictive

```agda
{-# OPTIONS --rewriting  #-}
-- {-# OPTIONS --rewriting --allow-unsolved-metas #-}
module cgp.lnegen.PrefEq where

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
open Order

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

### Definition (Prefix Structural equivalance) this is too strong, we got stuck in ExtendedOrder.lagda.md 

```agda

infix 4 _⊢_≅_

-- structural sub-word equivalance

data _⊢_≅_ : ∀ ( r : RE ) → ( u : U r  ) →  ( v : U r  ) → Set where
  ε⊢≅ : ε ⊢ EmptyU ≅ EmptyU
  $⊢≅ : { c : Char } { loc : ℕ } → ($ c ` loc ) ⊢ (LetterU c) ≅ ( LetterU c )
  ●⊢≅ : { l r : RE  } { loc : ℕ } { u u' : U l } { v v'  : U r } 
    → l ⊢ u ≅ u' 
    → proj₁ (flat u) ++ proj₁ (flat v) ≡ proj₁ (flat u') ++ proj₁ (flat v')
    ----------------------------------------------------------------------
    → l ● r ` loc ⊢ (PairU {l} {r} {loc} u v) ≅ (PairU {l} {r} {loc} u' v')
  ●⊢lne : { l r : RE  } { ε∈l : ε∈ l }  { loc : ℕ } { u u' : U l } { v v'  : U r }
    → ¬ (proj₁ (flat u) ≡ []) 
    → proj₁ (flat u') ≡ [] 
    → proj₁ (flat u) ++ proj₁ (flat v) ≡ proj₁ (flat v')
    ----------------------------------------------------------------------
    → l ● r ` loc ⊢ (PairU {l} {r} {loc} u v) ≅ (PairU {l} {r} {loc} u' v')
    
  +⊢≅ : { l r : RE  } { loc : ℕ } { u u' : U ( l + r ` loc ) }
    → proj₁ (flat u) ≡ proj₁ (flat u')
    ------------------------------------------------
    → l + r ` loc ⊢ u ≅ u' 
  *⊢≅ : { r : RE } { loc : ℕ } { ε∉r : ε∉ r } { u u' : U ( r * ε∉r ` loc ) }
    → proj₁ (flat u) ≡ proj₁ (flat u')
    ------------------------------------------------
    → r * ε∉r ` loc ⊢ u ≅ u' 
```

Lemma :

Prefix structural equivalence implies flatten word equivalence. 

```agda

≅→||≡|| : ∀ { r : RE } { u v : U r }
  →  r ⊢ u ≅ v
  → proj₁ (flat u) ≡ proj₁ (flat v)
≅→||≡|| {ε} {EmptyU} {EmptyU} ε⊢≅ = refl
≅→||≡|| {$ c ` loc} {LetterU c} {LetterU .c} $⊢≅ = refl
≅→||≡|| {l ● r ` loc} {PairU u v} {PairU u' v'} (●⊢≅ u≅u' |u|++|v|≅|u'|++|v'|) = |u|++|v|≅|u'|++|v'|
≅→||≡|| {l ● r ` loc} {PairU u v} {PairU u' v'} (●⊢lne _ |u'|≡[] |u|++|v|≡|v'|) =
  subst (λ w → proj₁ (flat u) ++ proj₁ (flat v) ≡ w ++ proj₁ (flat v')) (sym |u'|≡[]) |u|++|v|≡|v'|
≅→||≡|| {l + r ` loc} {u} {u'} (+⊢≅ |u|≡|u'|) = |u|≡|u'|
≅→||≡|| {r * ε∉r ` loc} {u} {u'} (*⊢≅ |u|≡|u'|) = |u|≡|u'|
```


```agda

-- ≅ relation is preserved by PDI
data ≅-Preserve : ∀ { r : RE } { c : Char } → PDInstance r c → Set where
  ≅-pres : ∀ { p r : RE } { c : Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( u₁ u₂  : U p )
      → p ⊢ u₁ ≅ u₂
      → r ⊢ inj u₁ ≅ inj u₂ )
    → ≅-Preserve {r} {c} (pdinstance {p} {r} {c} inj sound-ev)
```

Lemma: all the pdinstances from pdU is ≅-preserving 

```agda

≅-refl : ∀ { r : RE } { u : U r } → r ⊢ u ≅ u
≅-refl {ε} {EmptyU} = ε⊢≅
≅-refl {$ c ` loc} {LetterU c} = $⊢≅
≅-refl {l ● r ` loc} {PairU u v} = ●⊢≅ (≅-refl {l} {u}) refl
≅-refl {l + r ` loc} {u} = +⊢≅ refl
≅-refl {r * ε∉r ` loc} {u} = *⊢≅ refl

≅-pres-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≅-Preserve {l} {c} pdi
  → ≅-Preserve {l + r ` loc} {c} (pdinstance-left pdi)
≅-pres-left {l} {r} {loc} {c} (pdinstance {p} inj s-ev) (≅-pres ev) = ≅-pres prf
  where
    prf : (u₁ u₂ : U p) → p ⊢ u₁ ≅ u₂ → (l + r ` loc) ⊢ LeftU (inj u₁) ≅ LeftU (inj u₂)
    prf u₁ u₂ u₁≅u₂ = +⊢≅ (trans (s-ev u₁) (trans (cong (c ∷_) (≅→||≡|| u₁≅u₂)) (sym (s-ev u₂))))

≅-pres-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance r c )
  → ≅-Preserve {r} {c} pdi
  → ≅-Preserve {l + r ` loc} {c} (pdinstance-right pdi)
≅-pres-right {l} {r} {loc} {c} (pdinstance {p} inj s-ev) (≅-pres ev) = ≅-pres prf
  where
    prf : (u₁ u₂ : U p) → p ⊢ u₁ ≅ u₂ → (l + r ` loc) ⊢ RightU (inj u₁) ≅ RightU (inj u₂)
    prf u₁ u₂ u₁≅u₂ = +⊢≅ (trans (s-ev u₁) (trans (cong (c ∷_) (≅→||≡|| u₁≅u₂)) (sym (s-ev u₂))))

≅-pres-map-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdis : List ( PDInstance l c ) )
  → All (≅-Preserve {l} {c}) pdis
  → All (≅-Preserve {l + r ` loc} {c}) (List.map pdinstance-left pdis)
≅-pres-map-left {l} {r} {loc} {c} [] [] = []
≅-pres-map-left {l} {r} {loc} {c} (pdi ∷ pdis) (≅-pres-pdi ∷ ≅-pres-pdis ) = ≅-pres-left pdi ≅-pres-pdi  ∷ ≅-pres-map-left pdis ≅-pres-pdis 


≅-pres-map-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdis : List ( PDInstance r c ) )
  → All (≅-Preserve {r} {c}) pdis
  → All (≅-Preserve {l + r ` loc} {c}) (List.map pdinstance-right pdis)
≅-pres-map-right {l} {r} {loc} {c} [] [] = [] 
≅-pres-map-right {l} {r} {loc} {c} (pdi ∷ pdis) (≅-pres-pdi ∷ ≅-pres-pdis ) = ≅-pres-right pdi ≅-pres-pdi  ∷ ≅-pres-map-right pdis ≅-pres-pdis 

≅-pres-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → ≅-Preserve {l} {c} pdi
  → ≅-Preserve {l ● r ` loc} {c} (pdinstance-fst pdi)
≅-pres-fst {l} {r} {loc} {c} (pdinstance inj s-ev) (≅-pres ev) = ≅-pres (λ where
  (PairU u₁ v₁) (PairU u₂ v₂) (●⊢≅ u₁≅u₂ |uv₁|≅|uv₂|) → ●⊢≅ (ev u₁ u₂ u₁≅u₂)
    (trans (cong (λ w → w List.++ proj₁ (flat v₁)) (s-ev u₁))
      (trans (cong (c ∷_) |uv₁|≅|uv₂|)
        (cong (λ w → w List.++ proj₁ (flat v₂)) (sym (s-ev u₂)))))
  (PairU u₁ v₁) (PairU u₂ v₂) (●⊢lne _ _ _) → {!!} )

≅-pres-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance r c )
  → ≅-Preserve {r} {c} pdi
  → ≅-Preserve {r * ε∉r ` loc} {c} (pdinstance-star pdi)
≅-pres-star {r} {ε∉r} {loc} {c} (pdinstance {p} inj s-ev) (≅-pres ev) = ≅-pres prf
  where
    prf : (u₁ u₂ : U (p ● (r * ε∉r ` loc) ` loc)) → _ ⊢ u₁ ≅ u₂ → _ ⊢ PDI.mkinjList inj u₁ ≅ PDI.mkinjList inj u₂
    prf (PairU u₁ (ListU vs₁)) (PairU u₂ (ListU vs₂)) (●⊢≅ u₁≅u₂ flat-u₁vs₁≡flat-u₁vs₂) = *⊢≅ (begin
        proj₁ (flat (PDI.mkinjList inj (PairU u₁ (ListU vs₁))))
      ≡⟨ PDI.mkinjListSoundEv inj s-ev (PairU u₁ (ListU vs₁)) ⟩
        c ∷ (proj₁ (flat u₁) ++ proj₁ (flat (ListU vs₁)))
      ≡⟨ cong (λ x → c ∷ x) flat-u₁vs₁≡flat-u₁vs₂ ⟩
        c ∷ (proj₁ (flat u₂) ++ proj₁ (flat (ListU vs₂)))
      ≡⟨ sym (PDI.mkinjListSoundEv inj s-ev (PairU u₂ (ListU vs₂))) ⟩
        proj₁ (flat (PDI.mkinjList inj (PairU u₂ (ListU vs₂))))
      ∎)
    prf (PairU u₁ (ListU vs₁)) (PairU u₂ (ListU vs₂)) (●⊢lne _ _ _) = {!!}

≅-pres-map-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  → ( pdis : List ( PDInstance r c ) )
  → All (≅-Preserve {r} {c}) pdis
  → All (≅-Preserve {r * ε∉r ` loc} {c}) (List.map pdinstance-star pdis)
≅-pres-map-star {r} {ε∉r} {loc} {c} [] [] = []
≅-pres-map-star {r} {ε∉r} {loc} {c} (pdi ∷ pdis) (≅-pres-pdi ∷ ≅-pres-pdis ) = ≅-pres-star pdi ≅-pres-pdi  ∷ ≅-pres-map-star pdis ≅-pres-pdis 


≅-pres-snd : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → (e : U l) → (flat-[]-e : Flat-[] l e)
  → ( pdi : PDInstance r c )
  → ≅-Preserve {r} {c} pdi
  → ≅-Preserve {l ● r ` loc} {c} (mk-snd-pdi (e , flat-[]-e) pdi)
≅-pres-snd {l} {r} {loc} {c} e (flat-[] .(e) ev) (pdinstance {p} inj s-ev) (≅-pres prf) = ≅-pres (λ u₁ u₂ u₁≅u₂ → ●⊢≅ (≅-refl {l} {e})
    (trans (cong (_++ proj₁ (flat (inj u₁))) ev)
      (trans (++-identityˡ (proj₁ (flat (inj u₁))))
        (trans (s-ev u₁)
          (trans (cong (c ∷_) (≅→||≡|| u₁≅u₂))
            (trans (sym (s-ev u₂))
              (trans (sym (++-identityˡ (proj₁ (flat (inj u₂)))))
                (cong (_++ proj₁ (flat (inj u₂))) (sym ev)))))))) )

≅-pres-map-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdis : List ( PDInstance l c ) )
  → All (≅-Preserve {l} {c}) pdis
  → All (≅-Preserve {l ● r ` loc} {c}) (List.map pdinstance-fst pdis)
≅-pres-map-fst [] [] = []
≅-pres-map-fst (pdi ∷ pdis) (≅-pres-pdi ∷ ≅-pres-pdis) = ≅-pres-fst pdi ≅-pres-pdi ∷ ≅-pres-map-fst pdis ≅-pres-pdis

≅-pres-map-snd : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → (e : U l) → (flat-[]-e : Flat-[] l e)
  → ( pdis : List ( PDInstance r c ) )
  → All (≅-Preserve {r} {c}) pdis
  → All (≅-Preserve {l ● r ` loc} {c}) (List.map (mk-snd-pdi (e , flat-[]-e)) pdis)
≅-pres-map-snd e flat-[]-e [] [] = []
≅-pres-map-snd e flat-[]-e (pdi ∷ pdis) (≅-pres-pdi ∷ ≅-pres-pdis) = ≅-pres-snd e flat-[]-e pdi ≅-pres-pdi ∷ ≅-pres-map-snd e flat-[]-e pdis ≅-pres-pdis

all-concatMap : ∀ {A B : Set} {P : B → Set} (f : A → List B) (xs : List A)
  → All (λ x → All P (f x)) xs
  → All P (concatMap f xs)
all-concatMap f [] [] = []
all-concatMap f (x ∷ xs) (px ∷ pxs) = all-concat px (all-concatMap f xs pxs)

pdU-≅-preserve : ∀ { r : RE } { c : Char }
  → All (≅-Preserve {r} {c}) pdU[ r , c ]
pdU-≅-preserve {ε} {c} = []
pdU-≅-preserve {$ c ` loc} {c'} with c Char.≟ c'
... | yes refl =  ≅-pres {ε} {$ c ` loc} {c}  {mkinjLetter} {mkinjLetterSound}  ev  ∷ []
    where
      ev :  (u₁ u₂ : U ε) →  ε ⊢ u₁ ≅ u₂ → ($ c ` loc) ⊢ mkinjLetter u₁ ≅ mkinjLetter u₂
      ev EmptyU EmptyU ε⊢≅ = ≅-refl  
... | no ¬c≡c = [] 

pdU-≅-preserve {l + r ` loc} {c} = all-concat map-ind-hyp-l map-ind-hyp-r
  where
    ind-hyp-l : All (≅-Preserve {l} {c}) pdU[ l , c ]
    ind-hyp-l = pdU-≅-preserve {l} {c}
    
    ind-hyp-r : All (≅-Preserve {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU-≅-preserve {r} {c}

    map-ind-hyp-l : All (≅-Preserve {l + r ` loc} {c}) (List.map pdinstance-left pdU[ l , c ])
    map-ind-hyp-l = ≅-pres-map-left pdU[ l , c ]  ind-hyp-l

    map-ind-hyp-r : All (≅-Preserve {l + r ` loc} {c}) (List.map pdinstance-right pdU[ r , c ])
    map-ind-hyp-r = ≅-pres-map-right pdU[ r , c ]  ind-hyp-r

pdU-≅-preserve {r * ε∉r ` loc} {c} = map-ind-hyp-r
  where
    ind-hyp-r : All (≅-Preserve {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU-≅-preserve {r} {c}

    map-ind-hyp-r : All ≅-Preserve pdU[ r * ε∉r ` loc , c ]
    map-ind-hyp-r = ≅-pres-map-star pdU[ r , c ] ind-hyp-r 
pdU-≅-preserve {l ● r ` loc} {c} with ε∈? l
... | no ¬ε∈l = ≅-pres-map-fst pdU[ l , c ] (pdU-≅-preserve {l} {c})
... | yes ε∈l = all-concat (≅-pres-map-fst pdU[ l , c ] (pdU-≅-preserve {l} {c}))
                            (all-snd-pdis (pdU-≅-preserve {r} {c}))
  where
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l
    e-flats = zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es
    all-snd-pdis : All (≅-Preserve {r} {c}) pdU[ r , c ]
      → All (≅-Preserve {l ● r ` loc} {c}) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdU[ r , c ])
    all-snd-pdis all-preserve-r = all-concatMap (λ e-flat → List.map (mk-snd-pdi e-flat) pdU[ r , c ]) e-flats all-for-each-e
      where
        all-for-each-e : All (λ e-flat → All (≅-Preserve {l ● r ` loc} {c}) (List.map (mk-snd-pdi e-flat) pdU[ r , c ])) e-flats
        all-for-each-e = aux es flat-[]-es
          where
            aux : (es' : List (U l)) → (flat-[]-es' : All (Flat-[] l) es')
              → All (λ e-flat → All (≅-Preserve {l ● r ` loc} {c}) (List.map (mk-snd-pdi e-flat) pdU[ r , c ])) (zip-es-flat-[]-es {l} {ε∈l} es' flat-[]-es')
            aux [] [] = []
            aux (e ∷ es'') (flat-[] .(e) ev ∷ flat-[]-es'') =
              ≅-pres-map-snd e (flat-[] e ev) pdU[ r , c ] all-preserve-r ∷ aux es'' flat-[]-es''

```


Lemma:

parse trees generated by mkAllEmptyU are in _≅_ relation 

```agda

data All-≅ : ∀ { r : RE } ( us : List (U r) ) → Set where
  all-≅-nil : ∀ { r  : RE } → All-≅ {r} []
  all-≅-cons : ∀ { r : RE }
    → ( u : U r )
    → ( us : List (U r ) )
    → All (λ v → r ⊢ u ≅ v ) us
    ---------------------------------
    → All-≅ {r} ( u ∷ us )

All-≅→All : ∀ { r : RE } { u : U r } { us : List (U r) }
  → All-≅ (u ∷ us)
  → All (λ v → r ⊢ u ≅ v) us
All-≅→All (all-≅-cons _ _ p) = p

mkAllEmptyU-≅  : ∀ { r : RE } { ε∈r : ε∈ r }
  → All-≅ {r} (mkAllEmptyU ε∈r)
mkAllEmptyU-≅ {ε} {ε∈ε} = all-≅-cons EmptyU [] []
mkAllEmptyU-≅ {$ c ` loc} {}
mkAllEmptyU-≅ {r * nε ` loc} {ε∈*} = all-≅-cons (ListU []) [] []
mkAllEmptyU-≅ {l + r ` loc} {ε∈ ε∈l <+ ε∉r}
  = go (mkAllEmptyU ε∈l) refl (mkAllEmptyU-sound {l} ε∈l)
  where
    go : (es : List (U l)) → mkAllEmptyU ε∈l ≡ es → All (Flat-[] l) es → All-≅ (List.map LeftU es)
    go [] eq flat-[]-es = Nullary.contradiction eq (mkAllEmptyU≢[] ε∈l)
    go (u ∷ lus) eq (flat-[] .u u≡[] ∷ flat-[]-lus)
      = all-≅-cons (LeftU u) (List.map LeftU lus) (all-LeftU-≅ lus flat-[]-lus)
      where
        all-LeftU-≅ : (lus : List (U l)) → All (Flat-[] l) lus
          → All (λ v → l + r ` loc ⊢ LeftU u ≅ v) (List.map LeftU lus)
        all-LeftU-≅ [] _ = []
        all-LeftU-≅ (u' ∷ lus) (flat-[] .u' u'≡[] ∷ flat-[]-lus)
          = +⊢≅ (trans u≡[] (sym u'≡[])) ∷ all-LeftU-≅ lus flat-[]-lus
mkAllEmptyU-≅ {l + r ` loc} {ε∈ ε∉l +> ε∈r}
  = go (mkAllEmptyU ε∈r) refl (mkAllEmptyU-sound {r} ε∈r)
  where
    go : (es : List (U r)) → mkAllEmptyU ε∈r ≡ es → All (Flat-[] r) es → All-≅ (List.map RightU es)
    go [] eq flat-[]-es = Nullary.contradiction eq (mkAllEmptyU≢[] ε∈r)
    go (v ∷ rus) eq (flat-[] .v v≡[] ∷ flat-[]-rus)
      = all-≅-cons (RightU v) (List.map RightU rus) (all-RightU-≅ rus flat-[]-rus)
      where
        all-RightU-≅ : (rus : List (U r)) → All (Flat-[] r) rus
          → All (λ v' → l + r ` loc ⊢ RightU v ≅ v') (List.map RightU rus)
        all-RightU-≅ [] _ = []
        all-RightU-≅ (v' ∷ rus) (flat-[] .v' v'≡[] ∷ flat-[]-rus)
          = +⊢≅ (trans v≡[] (sym v'≡[])) ∷ all-RightU-≅ rus flat-[]-rus
mkAllEmptyU-≅ {l + r ` loc} {ε∈ ε∈l + ε∈r}
  = go (mkAllEmptyU ε∈l) (mkAllEmptyU ε∈r) refl refl (mkAllEmptyU-sound {l} ε∈l) (mkAllEmptyU-sound {r} ε∈r)
  where
    go : (lus : List (U l)) (rus : List (U r))
      → mkAllEmptyU ε∈l ≡ lus → mkAllEmptyU ε∈r ≡ rus
      → All (Flat-[] l) lus → All (Flat-[] r) rus
      → All-≅ (List.map LeftU lus ++ List.map RightU rus)
    go [] _ eq₁ _ _ _ = Nullary.contradiction eq₁ (mkAllEmptyU≢[] ε∈l)
    go _ [] _ eq₂ _ _ = Nullary.contradiction eq₂ (mkAllEmptyU≢[] ε∈r)
    go (u ∷ lus) (v ∷ rus) eq₁ eq₂ (flat-[] .u u≡[] ∷ flat-[]-lus) (flat-[] .v v≡[] ∷ flat-[]-rus)
      = all-≅-cons (LeftU u) (List.map LeftU lus ++ List.map RightU (v ∷ rus)) all-tail
      where
        all-left : All (λ v' → l + r ` loc ⊢ LeftU u ≅ v') (List.map LeftU lus)
        all-left = all-LeftU-≅ lus flat-[]-lus
          where
            all-LeftU-≅ : (lus : List (U l)) → All (Flat-[] l) lus
              → All (λ v' → l + r ` loc ⊢ LeftU u ≅ v') (List.map LeftU lus)
            all-LeftU-≅ [] _ = []
            all-LeftU-≅ (u' ∷ lus) (flat-[] .u' u'≡[] ∷ flat-[]-lus)
              = +⊢≅ (trans u≡[] (sym u'≡[])) ∷ all-LeftU-≅ lus flat-[]-lus

        all-right : All (λ v' → l + r ` loc ⊢ LeftU u ≅ v') (List.map RightU (v ∷ rus))
        all-right = +⊢≅ (trans u≡[] (sym v≡[])) ∷ all-RightU-≅ rus flat-[]-rus
          where
            all-RightU-≅ : (rus : List (U r)) → All (Flat-[] r) rus
              → All (λ v' → l + r ` loc ⊢ LeftU u ≅ v') (List.map RightU rus)
            all-RightU-≅ [] _ = []
            all-RightU-≅ (v' ∷ rus) (flat-[] .v' v'≡[] ∷ flat-[]-rus)
              = +⊢≅ (trans u≡[] (sym v'≡[])) ∷ all-RightU-≅ rus flat-[]-rus

        all-tail = all-concat all-left all-right
mkAllEmptyU-≅ {l ● r ` loc} {ε∈ ε∈l ● ε∈r}
  = go (mkAllEmptyU ε∈l) (mkAllEmptyU ε∈r) refl refl (mkAllEmptyU-sound {l} ε∈l) (mkAllEmptyU-sound {r} ε∈r) (mkAllEmptyU-≅ {l} {ε∈l})
  where
    go : (lus : List (U l)) (rus : List (U r))
      → mkAllEmptyU ε∈l ≡ lus → mkAllEmptyU ε∈r ≡ rus
      → All (Flat-[] l) lus → All (Flat-[] r) rus
      → All-≅ lus
      → All-≅ (concatMap (λ u → List.map (PairU u) rus) lus)
    go [] _ eq₁ _ _ _ _ = Nullary.contradiction eq₁ (mkAllEmptyU≢[] ε∈l)
    go _ [] _ eq₂ _ _ _ = Nullary.contradiction eq₂ (mkAllEmptyU≢[] ε∈r)
    go (u ∷ lus) (v ∷ rus) eq₁ eq₂ (flat-[] .u u≡[] ∷ flat-[]-lus) (flat-[] .v v≡[] ∷ flat-[]-rus) l-ind
      = all-≅-cons (PairU u v) tail all-tail
      where
        tail = List.map (PairU u) rus ++ concatMap (λ u' → List.map (PairU u') (v ∷ rus)) lus

        flat-eq : ∀ (u' : U l) (v' : U r)
          → proj₁ (flat u') ≡ []
          → proj₁ (flat v') ≡ []
          → proj₁ (flat u) ++ proj₁ (flat v) ≡ proj₁ (flat u') ++ proj₁ (flat v')
        flat-eq u' v' u'≡[] v'≡[] =
          trans
            (trans (cong (λ x → x ++ proj₁ (flat v)) u≡[]) v≡[])
            (sym (trans (cong (λ x → x ++ proj₁ (flat v')) u'≡[]) v'≡[]))

        all-rus : All (λ w → l ● r ` loc ⊢ PairU u v ≅ w) (List.map (PairU u) rus)
        all-rus = all-map-pairU-u rus flat-[]-rus
          where
            all-map-pairU-u : (rus : List (U r)) → All (Flat-[] r) rus
              → All (λ w → l ● r ` loc ⊢ PairU u v ≅ w) (List.map (PairU u) rus)
            all-map-pairU-u [] _ = []
            all-map-pairU-u (v' ∷ rus) (flat-[] .v' v'≡[] ∷ flat-[]-rus)
              = ●⊢≅ ≅-refl (flat-eq u v' u≡[] v'≡[]) ∷ all-map-pairU-u rus flat-[]-rus

        all-u≅lus : All (λ u' → l ⊢ u ≅ u') lus
        all-u≅lus = All-≅→All l-ind

        all-lus : All (λ w → l ● r ` loc ⊢ PairU u v ≅ w) (concatMap (λ u' → List.map (PairU u') (v ∷ rus)) lus)
        all-lus = all-concatMap-pairU lus (v ∷ rus) flat-[]-lus (flat-[] v v≡[] ∷ flat-[]-rus) all-u≅lus
          where
            all-concatMap-pairU : (lus : List (U l)) (rus : List (U r))
              → All (Flat-[] l) lus → All (Flat-[] r) rus
              → All (λ u' → l ⊢ u ≅ u') lus
              → All (λ w → l ● r ` loc ⊢ PairU u v ≅ w) (concatMap (λ u' → List.map (PairU u') rus) lus)
            all-concatMap-pairU [] _ _ _ _ = []
            all-concatMap-pairU (u' ∷ lus) rus (flat-[] .u' u'≡[] ∷ flat-[]-lus) flat-[]-rus (u≅u' ∷ all-u≅lus)
              = all-concat
                  (all-map-pairU-u' rus flat-[]-rus u≅u' u'≡[])
                  (all-concatMap-pairU lus rus flat-[]-lus flat-[]-rus all-u≅lus)
              where
                all-map-pairU-u' : (rus : List (U r)) → All (Flat-[] r) rus
                  → (u≅u' : l ⊢ u ≅ u')
                  → (u'≡[] : proj₁ (flat u') ≡ [])
                  → All (λ w → l ● r ` loc ⊢ PairU u v ≅ w) (List.map (PairU u') rus)
                all-map-pairU-u' [] _ _ _ = []
                all-map-pairU-u' (v' ∷ rus) (flat-[] .v' v'≡[] ∷ flat-[]-rus) u≅u' u'≡[]
                  = ●⊢≅ u≅u' (flat-eq u' v' u'≡[] v'≡[]) ∷ all-map-pairU-u' rus flat-[]-rus u≅u' u'≡[]

        all-tail = all-concat all-rus all-lus 
```

```agda

-- do we need this ? 
-- ≅ relation is preserved by PDInstance*
data ≅-Preserve* : ∀ { r : RE } { w : List Char } → PDInstance* r w → Set where
  ≅-pres* : ∀ { p r : RE } { w : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ w ++ ( proj₁ (flat {p} x) )) }
    → ( ( u₁ u₂  : U p )
      → p ⊢ u₁ ≅ u₂
      → r ⊢ inj u₁ ≅ inj u₂ )
    → ≅-Preserve* {r} {w} (pdinstance* {p} {r} {w} inj sound-ev)
```


-- injection is monotonic if the input parse trees are left-most align u₁ ≅ u₂ 

```agda

data >-Inc-≅ : ∀ { r : RE } { c : Char } →  PDInstance r c  → Set where
  >-inc : ∀ { p r : RE } { c : Char } { inj : U p →  U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( (u₁ : U p) → (u₂ : U p)
        → p ⊢ u₁ ≅ u₂ 
        → p ⊢ u₁ > u₂  → r ⊢ inj u₁ > inj u₂ ) -- strict increasing evidence 
    → >-Inc-≅ {r} {c} (pdinstance {p} {r} {c} inj sound-ev)

```

### Lemma 33: all pdinstances from pdU[ r , c ] are >-strict increasing .

Let r be a  non problematic regular expression.
Let c be a letter.
Then for all pdi ∈ pdU[ r , c], pdi is >-strict increasing .



#### Sub Lemma 33.1 - 33.9 : >-Inc-≅ is preserved inductively by the pdinstance operations. 

```agda


-----------------------------------------------------------------------------
-- Sub Lemma 33.1 - 33.9  BEGIN
----------------------------------------------------------------------------

>-inc-map-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( pdis : List (PDInstance l c) )
    → All (>-Inc-≅ {l} {c}) pdis
    → All (>-Inc-≅ {l + r ` loc } {c}) (List.map pdinstance-left pdis)
>-inc-map-left [] [] = []
>-inc-map-left {l} {r} {loc} {c} ((pdinstance {p} {l} {c}  inj sound-ev) ∷ pdis)
  (>-inc u₁→u₂→u₁≅u₂→u₁>u₂→inj-u₁>inj-u₂ ∷ pxs)
  = >-inc >-inc-ev   ∷ >-inc-map-left pdis pxs
  where
    >-inc-ev : ∀ (u₁ : U p)
              → (u₂ : U p)
              → p ⊢ u₁ ≅ u₂
              → p ⊢ u₁ > u₂
              --------------
              → (l + r ` loc) ⊢ LeftU (inj u₁) > LeftU (inj u₂)
    >-inc-ev u₁ u₂  u₁≅u₂ u₁>u₂ =
      let inj-u₁>inj-u₂ = u₁→u₂→u₁≅u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ u₁≅u₂ u₁>u₂
      in bne (¬≡[]→length>0 ¬proj₁flat-inj-u₁≡[]) (¬≡[]→length>0 ¬proj₁flat-inj-u₂≡[]) (choice-ll  inj-u₁>inj-u₂)
      where
        ¬proj₁flat-inj-u₁≡[] : ¬ (proj₁ (flat (inj u₁)) ≡ [])
        ¬proj₁flat-inj-u₁≡[] rewrite (sound-ev u₁) = λ proj₁flat-inj-u₁≡[] → Utils.¬∷≡[] proj₁flat-inj-u₁≡[] 
        ¬proj₁flat-inj-u₂≡[] : ¬ (proj₁ (flat (inj u₂)) ≡ [])
        ¬proj₁flat-inj-u₂≡[] rewrite (sound-ev u₂) = λ proj₁flat-inj-u₂≡[] → Utils.¬∷≡[] proj₁flat-inj-u₂≡[] 


>-inc-map-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( pdis : List (PDInstance r c) )
    → All (>-Inc-≅ {r} {c}) pdis
    → All (>-Inc-≅ {l + r ` loc } {c}) (List.map pdinstance-right pdis)
>-inc-map-right [] [] = []
>-inc-map-right {l} {r} {loc} {c} ((pdinstance {p} {r} {c} inj sound-ev) ∷ pdis)
  (>-inc  u₁→u₂→u₁≅u₂→u₁>u₂→inj-u₁>inj-u₂ ∷ pxs)
  = >-inc >-inc-ev  ∷ >-inc-map-right pdis pxs
  where
    >-inc-ev : ∀ (u₁ : U p)
              → (u₂ : U p)
              → p ⊢ u₁ ≅ u₂ 
              → p ⊢ u₁ > u₂
              --------------
              → (l + r ` loc) ⊢ RightU (inj u₁) > RightU (inj u₂)
    >-inc-ev u₁ u₂ u₁≅u₂ u₁>u₂ =
      let inj-u₁>inj-u₂ = u₁→u₂→u₁≅u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ u₁≅u₂  u₁>u₂
      in bne (¬≡[]→length>0 ¬proj₁flat-inj-u₁≡[]) (¬≡[]→length>0 ¬proj₁flat-inj-u₂≡[])  (choice-rr inj-u₁>inj-u₂)
      where
        ¬proj₁flat-inj-u₁≡[] : ¬ (proj₁ (flat (inj u₁)) ≡ [])
        ¬proj₁flat-inj-u₁≡[] rewrite (sound-ev u₁) = λ proj₁flat-inj-u₁≡[] → Utils.¬∷≡[] proj₁flat-inj-u₁≡[] 
        ¬proj₁flat-inj-u₂≡[] : ¬ (proj₁ (flat (inj u₂)) ≡ [])
        ¬proj₁flat-inj-u₂≡[] rewrite (sound-ev u₂) = λ proj₁flat-inj-u₂≡[] → Utils.¬∷≡[] proj₁flat-inj-u₂≡[] 


>-inc-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
               → ( pdi : PDInstance l c )
               → >-Inc-≅ {l} {c} pdi
               ------------------------
               → >-Inc-≅ {l ● r ` loc} {c} (pdinstance-fst {l} {r} {loc} {c} pdi)
>-inc-fst {l} {r} {loc} {c} (pdinstance {p} {l} {c}  inj sound-ev)(>-inc u₁→u₂→u₁≅u₂→u₁>u₂→inj-u₁>inj-u₂) = >-inc >-inc-ev 
  where 
    injFst : U (p ● r ` loc)   → U (l ● r ` loc ) -- the p can only be seq ε or ● 
    injFst = mkinjFst inj
    injFstSnd :  ( u : U (p ● r ` loc) )  → proj₁ (flat (injFst u))  ≡ c ∷ proj₁ (flat u)
    injFstSnd = mkinjFstSoundEv inj sound-ev
    
    >-inc-ev : ∀ (uv₁ : U ( p ● r ` loc ))
              → (uv₂ : U ( p ● r ` loc ))
              → p ● r ` loc  ⊢ uv₁ ≅ uv₂ 
              → p ● r ` loc  ⊢ uv₁ > uv₂
              ------------------------------------
              → l ● r ` loc ⊢ (injFst uv₁) > (injFst uv₂)

    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) (●⊢lne ¬|u₁|≡[] |u₂|≡[] |uv₁|≡|v₂|) (be len|pair-u₁v₁|≡len|pair-u₂v₂| len|pair-u₂v₂|≡0 pair-u₁v₁>ⁱpair-u₂v₂ ) =
      contradiction-¬|u₁|≡[]
      where
        contradiction-¬|u₁|≡[] = Nullary.contradiction |u₁|≡[] ¬|u₁|≡[]
          where
            |v₂|≡[] : proj₁ (flat v₂) ≡ []
            |v₂|≡[] = ++-conicalʳ (proj₁ (flat u₂)) (proj₁ (flat v₂)) (length≡0→[] len|pair-u₂v₂|≡0)
            |u₁|≡[] : proj₁ (flat u₁) ≡ []
            |u₁|≡[] = ++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat v₁)) (trans |uv₁|≡|v₂| |v₂|≡[])
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) (●⊢lne ¬|u₁|≡[] |u₂|≡[] |uv₁|≡|v₂|) (bne len|pair-u₁v₁|>0 len|pair-u₂v₂|>0 (seq₁ u₁>u₂) ) =
      case-u₁>u₂ u₁>u₂
      where
        |u₂|≡0 : length (proj₁ (flat u₂)) ≡ 0
        |u₂|≡0 = cong length |u₂|≡[]

        case-u₁>u₂ : p ⊢ u₁ > u₂ → (l ● r ` loc) ⊢ injFst (PairU u₁ v₁) > injFst (PairU u₂ v₂)
        case-u₁>u₂ (be len|u₁|≡len|u₂| len|u₂|≡0 _) =
          ⊥-elim (¬|u₁|≡[] (length≡0→[] (trans len|u₁|≡len|u₂| len|u₂|≡0)))
        case-u₁>u₂ (bne _ len|u₂|>0 _) =
          ⊥-elim (n≡0→¬n>0 |u₂|≡0 len|u₂|>0)
        case-u₁>u₂ (lne len|u₁|>0 len|u₂|≡0) = {!!}
          -- unprovable: need l ⊢ inj u₁ > inj u₂ but lack u₁ ≅ u₂ premise
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) (●⊢lne ¬|u₁|≡[] |u₂|≡[] |uv₁|≡|v₂|) (bne len|pair-u₁v₁|>0 len|pair-u₂v₂|>0 (seq₂ u₁≡u₂ v₁>v₂) ) =
      Nullary.contradiction (trans (cong proj₁ (cong flat u₁≡u₂)) |u₂|≡[]) ¬|u₁|≡[]
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) (●⊢lne ¬|u₁|≡[] |u₂|≡[] |uv₁|≡|v₂|) (lne len|pair-u₁v₁|>0 len|pair-u₂v₂|≡0 ) =
      contradiction-¬|u₁|≡[]
      where
        contradiction-¬|u₁|≡[] = Nullary.contradiction |u₁|≡[] ¬|u₁|≡[]
          where
            |v₂|≡[] : proj₁ (flat v₂) ≡ []
            |v₂|≡[] = ++-conicalʳ (proj₁ (flat u₂)) (proj₁ (flat v₂)) (length≡0→[] len|pair-u₂v₂|≡0)
            |u₁|≡[] : proj₁ (flat u₁) ≡ []
            |u₁|≡[] = ++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat v₁)) (trans |uv₁|≡|v₂| |v₂|≡[])
      

    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) (●⊢≅ u₁≅u₂ |uv₁|≡|uv₂|) (be len|pair-u₁v₁|≡len|pair-u₂v₂| len|pair-u₂v₂|≡0 (seq₁ u₁>u₂)) =
      let inj-u₁>inj-u₂ = u₁→u₂→u₁≅u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ u₁≅u₂ u₁>u₂
      in bne |injFst-pair-u₁-v₁|>0 |injFst-pair-u₂-v₂|>0 (seq₁ inj-u₁>inj-u₂)
        where
          |injFst-pair-u₁-v₁|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₁) v₁))) Nat.> 0
          |injFst-pair-u₁-v₁|>0 rewrite injFstSnd (PairU u₁ v₁) = Nat.s≤s Nat.z≤n 

          |injFst-pair-u₂-v₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₂) v₂))) Nat.> 0
          |injFst-pair-u₂-v₂|>0 rewrite injFstSnd (PairU u₂ v₂) = Nat.s≤s Nat.z≤n 


    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) (●⊢≅ u₁≅u₂ |uv₁|≡|uv₂|) (be len|pair-u₁v₁|≡len|pair-u₂v₂| len|pair-u₂v₂|≡0 (seq₂ u₁≡u₂ v₁>v₂)) =
      bne |injFst-pair-u₁-v₁|>0 |injFst-pair-u₂-v₂|>0 (seq₂ inj-u₁≡inj-u₂ v₁>v₂)
        where
          inj-u₁≡inj-u₂ : inj u₁ ≡ inj u₂ 
          inj-u₁≡inj-u₂ = cong inj u₁≡u₂
          |injFst-pair-u₁-v₁|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₁) v₁))) Nat.> 0
          |injFst-pair-u₁-v₁|>0 rewrite injFstSnd (PairU u₁ v₁) = Nat.s≤s Nat.z≤n 

          |injFst-pair-u₂-v₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₂) v₂))) Nat.> 0
          |injFst-pair-u₂-v₂|>0 rewrite injFstSnd (PairU u₂ v₂) = Nat.s≤s Nat.z≤n 
          

    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) (●⊢≅ u₁≅u₂ |uv₁|≡|uv₂|) (lne len|pair-u₁v₁|>0 len|pair-u₂v₂|≡0 ) = prf -- hm this case is tricky.
      where
        -- |u₁|≡|u₂| : proj₁ (flat u₁) ≡ proj₁ (flat u₂)
        -- |u₁|≡|u₂| = ≅→||≡||  u₁≅u₂ 

        len|pair-u₂v₂|>0 : length (proj₁ (flat (PairU {p} {r} {loc} u₂ v₂) )) Nat.> 0
        len|pair-u₂v₂|>0 rewrite sym |uv₁|≡|uv₂| = len|pair-u₁v₁|>0

        prf :  (l ● r ` loc) ⊢ injFst (PairU u₁ v₁) > injFst (PairU u₂ v₂)
        prf = Nullary.contradiction len|pair-u₂v₂|>0 (n≡0→¬n>0 len|pair-u₂v₂|≡0) 
        -- there was an issue here with the counter example t13 t14 above.
        -- it is addres with the additional constraint (●⊢≅ u₁≅u₂ v₁≅v₂), hence maximality is not needed .
        -- old issue
        -- t13>t14

        -- counter examples the t13 t14 above.
        -- t13>t14
        -- injFst t13 = PairU (PairU (RightU (ListU (LetterU 'a' ∷ []))         (RightU (ListU (LetterU 'a' ∷ []))))               (ListU (LetterU 'a' ∷ []))
        -- injFst t14 = PairU (PairU (LeftU (ListU (LetterU 'a' ∷ []))          (LeftU (ListU [])))                                (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
        -- injFst t14 > injFst t13


        -- the left most element should be the maximal element
        -- t_top = PairU (PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))                                        (LeftU (ListU [])))                                (ListU [])
        -- injFst t_top =  PairU (PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷  LetterU 'a' ∷ [])))                                        (LeftU (ListU [])))                                (ListU [])
        {-
          Wait do we really have issue here?
          r = ( (a* + a* ) ● (a* + a*) ) ● a*
          after pdU[ r , a ] we have 5 pdinstances
          1) ( (ε ● a*) ● (a* + a*) ) ● a*        in₁ = 
          2) ( (ε ● a*) ● (a* + a*) ) ● a*        in₂ = 
          3) ( ε ● a* ) ● a*                      in₃ = 
          4) ( ε ● a* ) ● a*                      in₄ =
          5) ε ● a*                               in₅ =
          each injection should have >-Inc
          observation: the left most inner most sub exp must be ε, followed by some r.

          let's consider another example
          t = a ● r
          t / a = ε ● r,
          let v₁ = PairU EmptyU t13
              v₂ = PairU EmptyU t14
          inj v₁ = PairU (LetterU 'a') t13
          inj v₂ = PairU (LetterU 'a') t14, it does not change the order!
          So >-Inc might hold. We need to capture this invariant in the >-Inc premise. 
        -} 

    
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂)  (●⊢≅ u₁≅u₂ |uv₁|≡|uv₂|)  (bne len|pair-u₁v₁|>0 len|pair-u₂v₂|>0 (seq₁  u₁>u₂))  =  
      let inj-u₁>inj-u₂ = u₁→u₂→u₁≅u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ u₁≅u₂  u₁>u₂
      in bne |injFst-pair-u₁-v₁|>0 |injFst-pair-u₂-v₂|>0 (seq₁ inj-u₁>inj-u₂) 

        where

          |injFst-pair-u₁-v₁|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₁) v₁))) Nat.> 0
          |injFst-pair-u₁-v₁|>0 rewrite injFstSnd (PairU u₁ v₁) = Nat.s≤s Nat.z≤n 

          |injFst-pair-u₂-v₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₂) v₂))) Nat.> 0
          |injFst-pair-u₂-v₂|>0 rewrite injFstSnd (PairU u₂ v₂) = Nat.s≤s Nat.z≤n 


    >-inc-ev (PairU u₁ v₁)  (PairU u₂ v₂)  (●⊢≅ u₁≅u₂ |uv₁|≡|uv₂|) (bne len|pair-u₁v₁|>0 len|pair-u₂v₂|>0 (seq₂  u₁≡u₂ v₁>v₂ )) =
      bne |injFst-pair-u₁-v₁|>0 |injFst-pair-u₂-v₂|>0 (seq₂ inj-u₁≡inj-u₂ v₁>v₂)  
        where
          inj-u₁≡inj-u₂ : inj u₁ ≡ inj u₂ 
          inj-u₁≡inj-u₂ = cong inj u₁≡u₂

          |injFst-pair-u₁-v₁|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₁) v₁))) Nat.> 0
          |injFst-pair-u₁-v₁|>0 rewrite injFstSnd (PairU u₁ v₁) = Nat.s≤s Nat.z≤n 

          |injFst-pair-u₂-v₂|>0 : length (proj₁ (flat (PairU {l} {r} {loc} (inj u₂) v₂))) Nat.> 0
          |injFst-pair-u₂-v₂|>0 rewrite injFstSnd (PairU u₂ v₂) = Nat.s≤s Nat.z≤n 




>-inc-map-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
               → ( pdis : List (PDInstance l c ) )
               → All (>-Inc-≅ {l} {c}) pdis
               → All (>-Inc-≅  {l ● r ` loc} {c}) (List.map (pdinstance-fst {l} {r} {loc} {c}) pdis)
>-inc-map-fst [] [] = []
>-inc-map-fst {l} {r} {loc} {c} ((pdinstance {p} {l} {c}  inj sound-ev) ∷ pdis) ((>-inc u₁→u₂→u₁≅u₂→u₁>u₂→inj-u₁>inj-u₂ ) ∷ pxs)
   = (>-inc-fst (pdinstance inj sound-ev) (>-inc u₁→u₂→u₁≅u₂→u₁>u₂→inj-u₁>inj-u₂))    ∷  >-inc-map-fst pdis pxs




-----------------------------------------------------------------------------------------
-- aux lemma to show that injSnd is >-strict increasing
>-inc-injSnd : ∀ {l r p : RE } { loc : ℕ } { c : Char } 
         → ( v : U l )
         → ( Flat-[] l v )         
         → ( inj : U p → U r )
         → ( s-ev : ( u :  U p )  → proj₁ (flat (inj u )) ≡ c ∷ proj₁ (flat u ))
         → ( u₁ : U p )
         → ( u₂ : U p )
         → r ⊢ inj u₁ > inj u₂
         --------------------------------------------------------------------------
         → ( l ● r ` loc ) ⊢  (mkinjSnd inj v u₁) > (mkinjSnd inj v u₂) 
>-inc-injSnd {l} {r} {p} {loc} {c} v (flat-[] .v |v|≡[]) inj s-ev u₁ u₂ (bne |inj-u₁|>0 |inj-u₂|>0 inj-u₁>ⁱinj-u₂) = (bne len|pair-v-inj-u₁|>0 len|pair-v-inj-u₂|>0 (seq₂ refl (bne |inj-u₁|>0 |inj-u₂|>0 inj-u₁>ⁱinj-u₂)))
  where
    ¬|pair-v-inj-u₁|≡[] : ¬ ((proj₁ (flat (PairU {l} {r} {loc} v (inj u₁)) )) ≡ [] )
    ¬|pair-v-inj-u₁|≡[] rewrite PDI.mkinjSndSoundEv {p} {l} {r} {loc} {c}  inj s-ev v (flat-[] v |v|≡[]) u₁ = Utils.¬∷≡[]
    ¬|pair-v-inj-u₂|≡[] : ¬ ((proj₁ (flat (PairU {l} {r} {loc} v (inj u₂)) )) ≡ [] )
    ¬|pair-v-inj-u₂|≡[] rewrite PDI.mkinjSndSoundEv {p} {l} {r} {loc} {c}  inj s-ev v (flat-[] v |v|≡[]) u₂ = Utils.¬∷≡[]     
    len|pair-v-inj-u₁|>0 :  length (proj₁ (flat (PairU {l} {r} {loc} v (inj u₁)) )) Nat.> 0
    len|pair-v-inj-u₁|>0 = ¬≡[]→length>0 ¬|pair-v-inj-u₁|≡[]  
    len|pair-v-inj-u₂|>0 :  length (proj₁ (flat (PairU {l} {r} {loc} v (inj u₂)) )) Nat.> 0
    len|pair-v-inj-u₂|>0 = ¬≡[]→length>0 ¬|pair-v-inj-u₂|≡[]   
>-inc-injSnd {l} {r} {p} {loc} {c} v (flat-[] .v |v|≡[]) inj s-ev u₁ u₂ (be len|inj-u₁|≡len|inj-u₂| len|inj-u₂|≡0 inj-u₁>ⁱinj-u₂) = Nullary.contradiction len|inj-u₂|>0 (n≡0→¬n>0 len|inj-u₂|≡0 ) 
  where
    ¬|inj-u₂|≡[] : ¬ ((proj₁ (flat (inj u₂)) )) ≡ []
    ¬|inj-u₂|≡[] rewrite s-ev u₂ = Utils.¬∷≡[] 
    len|inj-u₂|>0 :  length (proj₁ (flat (inj u₂)) ) Nat.> 0
    len|inj-u₂|>0 =  ¬≡[]→length>0 ¬|inj-u₂|≡[]
>-inc-injSnd {l} {r} {p} {loc} {c} v (flat-[] .v |v|≡[]) inj s-ev u₁ u₂ (lne len|inj-u₁|>0 len|inj-u₂|≡0) = Nullary.contradiction len|inj-u₂|>0 (n≡0→¬n>0 len|inj-u₂|≡0 ) 
  where
    ¬|inj-u₂|≡[] : ¬ ((proj₁ (flat (inj u₂)) )) ≡ []
    ¬|inj-u₂|≡[] rewrite s-ev u₂ = Utils.¬∷≡[] 
    len|inj-u₂|>0 :  length (proj₁ (flat (inj u₂)) ) Nat.> 0
    len|inj-u₂|>0 =  ¬≡[]→length>0 ¬|inj-u₂|≡[] 
    

-- aux lemma to show that mk-snd-pdi is >-strict increasing
>-inc-mk-snd-pdi : ∀ { l r : RE } { loc : ℕ } { c : Char }
   → ( e-flat-[]-e : (∃[ e ] Flat-[] l e)  )
   → ( pdi : PDInstance r c )
   → >-Inc-≅ {r} {c} pdi 
   -------------------------------------------------------------------
   → >-Inc-≅ (mk-snd-pdi {l} {r} {loc} {c} e-flat-[]-e pdi) 
>-inc-mk-snd-pdi {l} {r} {loc} {c} (e , flat-[] .e proj₁∘flate≡[]) (pdinstance {p} {r} {c} inj s-ev) (>-inc >-inc-inj) =
  >-inc (λ u₁ u₂ u₁≅u₂ u₁>u₂ → ( >-inc-injSnd {l} {r} {p} {loc} {c} e (flat-[] e proj₁∘flate≡[]) inj s-ev u₁ u₂  (>-inc-inj u₁ u₂ u₁≅u₂ u₁>u₂))  )
  where
    -- duplicated from mk-snd-pdi from PartialDerivativeParseTree so that the PDInstance can be inferred
    -- this is needed because p is an existential type `hidden` inside PDInstance r c 
    injSnd :  U p → U (l ● r ` loc)
    injSnd = mkinjSnd {l} {r} {p} {loc} inj e
    injSnd-s-ev =
      (λ u → 
           begin
             proj₁ (flat (PairU {l} {r} {loc} e (inj u)))
           ≡⟨⟩
             (proj₁ (flat e)) ++ (proj₁ (flat (inj u)))
           ≡⟨ cong (λ x → ( x ++  (proj₁ (flat (inj u))))) proj₁∘flate≡[] ⟩  --  e must be an empty; we do have flat v ≡ [] from mkAllEmptyU-sound
             [] ++ (proj₁ (flat (inj u)))
           ≡⟨⟩
             proj₁ (flat (inj u))
           ≡⟨ s-ev u ⟩
             c ∷ (proj₁ (flat u))
           ∎
          )    

-- aux lemma to show that concatMap pdinstance-snd  is >-strict increasing

>-inc-pdinstance-snd : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( e-flat-[]-e : ∃[ e ] Flat-[] l e )
  → ( pdis : List (PDInstance r c ) )
  → All (>-Inc-≅ {r} {c}) pdis
  ---------------------------------------------------------------------------
  → All  (>-Inc-≅ {l ● r ` loc} {c}) (List.map  (mk-snd-pdi e-flat-[]-e ) pdis )
>-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e-flat-[]-e []           [] = [] 
>-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e-flat-[]-e (pdi ∷ pdis) (>-inc-pdi ∷ all>-inc-pdis) = (>-inc-mk-snd-pdi e-flat-[]-e pdi >-inc-pdi) ∷ >-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c} e-flat-[]-e pdis all>-inc-pdis


>-inc-concatmap-pdinstance-snd-sub :  ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → ( e-flat-[]-es  : List ( ∃[ e ] Flat-[] l e ) )
  → ( pdis : List (PDInstance r c ) )
  → All (>-Inc-≅ {r} {c}) pdis
  -----------------------------------------------------------------------------------------------------
  → All (>-Inc-≅ {l ● r ` loc} {c}) (concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) e-flat-[]-es)
>-inc-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} [] _ _ = []
>-inc-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} ( e-flat-[]-e ∷ e-flat-[]-es ) pdis all>-inc-pdis =
  all-concat  (>-inc-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  e-flat-[]-e  pdis all>-inc-pdis)
              (>-inc-concatmap-pdinstance-snd-sub {l} {r} {ε∈l} {loc} {c} e-flat-[]-es pdis all>-inc-pdis)  


>-inc-concatmap-pdinstance-snd : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
               → ( pdis : List (PDInstance r c ) )
               → All (>-Inc-≅ {r} {c}) pdis
               → All (>-Inc-≅ {l ● r ` loc} {c}) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  pdis)
>-inc-concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis all>-inc-pdis = >-inc-concatmap-pdinstance-snd-sub  {l} {r} {ε∈l} {loc} {c} (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es) pdis all>-inc-pdis
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l    




>-inc-map-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
               → ( pdis : List (PDInstance r c)  )
               → All (>-Inc-≅ {r} {c}) pdis
               → All (>-Inc-≅ {r * ε∉r ` loc} {c}) (List.map (pdinstance-star {r} {ε∉r} {loc} {c}) pdis)
>-inc-map-star {r} {ε∉r} {loc} {c} [] [] = []
>-inc-map-star {r} {ε∉r} {loc} {c} (pdinstance {p} {r} {c} inj s-ev ∷ pdis) (>-inc >-ev ∷ pxs)  =
  >-inc >-inc-ev ∷ >-inc-map-star pdis pxs
  where
    injList : U (p ● (r * ε∉r ` loc ) ` loc ) → U ( r * ε∉r ` loc )
    injList = mkinjList inj   

    >-inc-ev : ∀ (uv₁ : U ( p ● (r * ε∉r ` loc ) ` loc ))
              → (uv₂ : U ( p ● (r * ε∉r ` loc ) ` loc ))
              → (p ● (r * ε∉r ` loc ) ` loc )  ⊢ uv₁ ≅ uv₂              
              → (p ● (r * ε∉r ` loc ) ` loc )  ⊢ uv₁ > uv₂
              ------------------------------------
              → (r * ε∉r ` loc) ⊢ (injList uv₁) > (injList uv₂)

    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (●⊢≅ u₁≅u₂ list-vs₁≅list-vs₂) (bne len|u₁-vs₁|>0 len|u₂-vs₂|>0 (seq₁ u₁>u₂)) = 
      let inj-u₁>inj-u₂ = >-ev u₁ u₂ u₁≅u₂ u₁>u₂
      in bne len|injList-u₁-vs₁|>0 len|injList-u₂-vs₂|>0 (star-head {r} {loc} {ε∉r} {inj u₁} {inj u₂} {vs₁} {vs₂} inj-u₁>inj-u₂)
      where
        len|injList-u₁-vs₁|>0 : length (proj₁ (flat (injList (PairU u₁ (ListU vs₁))))) Nat.> 0
        len|injList-u₁-vs₁|>0 = ¬≡[]→length>0 λ eq → ¬c∷[]≡[] (begin
          (c ∷ proj₁ (flat u₁)) ++ proj₁ (flat (ListU vs₁))
          ≡⟨ sym (PDI.mkinjListSoundEv inj s-ev (PairU u₁ (ListU vs₁))) ⟩
            proj₁ (flat (injList (PairU u₁ (ListU vs₁))))
          ≡⟨ eq ⟩
            []
          ∎)
          where
            ¬c∷[]≡[] : ¬ ((c ∷ proj₁ (flat u₁)) ++ proj₁ (flat (ListU vs₁)) ≡ [])
            ¬c∷[]≡[] ()

        len|injList-u₂-vs₂|>0 : length (proj₁ (flat (injList (PairU u₂ (ListU vs₂))))) Nat.> 0
        len|injList-u₂-vs₂|>0 = ¬≡[]→length>0 λ eq → ¬c∷[]≡[] (begin
          (c ∷ proj₁ (flat u₂)) ++ proj₁ (flat (ListU vs₂))
          ≡⟨ sym (PDI.mkinjListSoundEv inj s-ev (PairU u₂ (ListU vs₂))) ⟩
            proj₁ (flat (injList (PairU u₂ (ListU vs₂))))
          ≡⟨ eq ⟩
            []
          ∎)
          where
            ¬c∷[]≡[] : ¬ ((c ∷ proj₁ (flat u₂)) ++ proj₁ (flat (ListU vs₂)) ≡ [])
            ¬c∷[]≡[] ()
    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (●⊢≅ u₁≅u₂ list-vs₁≅list-vs₂) (be len|u₁-vs₁|≡len|u₂-vs₂| len|u₂-vs₂|≡0 (seq₁ u₁>u₂)) =
      let inj-u₁>inj-u₂ = >-ev u₁ u₂ u₁≅u₂ u₁>u₂
      in bne len|injList-u₁-vs₁|>0 len|injList-u₂-vs₂|>0 (star-head inj-u₁>inj-u₂)
      where
        len|injList-u₁-vs₁|>0 : length (proj₁ (flat (injList (PairU u₁ (ListU vs₁))))) Nat.> 0
        len|injList-u₁-vs₁|>0 = ¬≡[]→length>0 λ eq → ¬c∷[]≡[] (begin
          (c ∷ proj₁ (flat u₁)) ++ proj₁ (flat (ListU vs₁))
          ≡⟨ sym (PDI.mkinjListSoundEv inj s-ev (PairU u₁ (ListU vs₁))) ⟩
            proj₁ (flat (injList (PairU u₁ (ListU vs₁))))
          ≡⟨ eq ⟩
            []
          ∎)
          where
            ¬c∷[]≡[] : ¬ ((c ∷ proj₁ (flat u₁)) ++ proj₁ (flat (ListU vs₁)) ≡ [])
            ¬c∷[]≡[] ()

        len|injList-u₂-vs₂|>0 : length (proj₁ (flat (injList (PairU u₂ (ListU vs₂))))) Nat.> 0
        len|injList-u₂-vs₂|>0 = ¬≡[]→length>0 λ eq → ¬c∷[]≡[] (begin
          (c ∷ proj₁ (flat u₂)) ++ proj₁ (flat (ListU vs₂))
          ≡⟨ sym (PDI.mkinjListSoundEv inj s-ev (PairU u₂ (ListU vs₂))) ⟩
            proj₁ (flat (injList (PairU u₂ (ListU vs₂))))
          ≡⟨ eq ⟩
            []
          ∎)
          where
            ¬c∷[]≡[] : ¬ ((c ∷ proj₁ (flat u₂)) ++ proj₁ (flat (ListU vs₂)) ≡ [])
            ¬c∷[]≡[] ()
    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (●⊢≅ u₁≅u₂ list-vs₁≅list-vs₂) (be len|u₁-vs₁|≡len|u₂-vs₂| len|u₂-vs₂|≡0 (seq₂ u₁≡u₂ list-vs₁>list-vs₂)) =
      bne len|injList-u₁-vs₁|>0 len|injList-u₂-vs₂|>0 (star-tail inj-u₁≡inj-u₂ list-vs₁>list-vs₂)
        where
          inj-u₁≡inj-u₂ : inj u₁ ≡ inj u₂
          inj-u₁≡inj-u₂ = cong inj u₁≡u₂

          len|injList-u₁-vs₁|>0 : length (proj₁ (flat (injList (PairU u₁ (ListU vs₁))))) Nat.> 0
          len|injList-u₁-vs₁|>0 = ¬≡[]→length>0 λ eq → ¬c∷[]≡[] (begin
            (c ∷ proj₁ (flat u₁)) ++ proj₁ (flat (ListU vs₁))
            ≡⟨ sym (PDI.mkinjListSoundEv inj s-ev (PairU u₁ (ListU vs₁))) ⟩
              proj₁ (flat (injList (PairU u₁ (ListU vs₁))))
            ≡⟨ eq ⟩
              []
            ∎)
            where
              ¬c∷[]≡[] : ¬ ((c ∷ proj₁ (flat u₁)) ++ proj₁ (flat (ListU vs₁)) ≡ [])
              ¬c∷[]≡[] ()

          len|injList-u₂-vs₂|>0 : length (proj₁ (flat (injList (PairU u₂ (ListU vs₂))))) Nat.> 0
          len|injList-u₂-vs₂|>0 = ¬≡[]→length>0 λ eq → ¬c∷[]≡[] (begin
            (c ∷ proj₁ (flat u₂)) ++ proj₁ (flat (ListU vs₂))
            ≡⟨ sym (PDI.mkinjListSoundEv inj s-ev (PairU u₂ (ListU vs₂))) ⟩
              proj₁ (flat (injList (PairU u₂ (ListU vs₂))))
            ≡⟨ eq ⟩
              []
            ∎)
            where
              ¬c∷[]≡[] : ¬ ((c ∷ proj₁ (flat u₂)) ++ proj₁ (flat (ListU vs₂)) ≡ [])
              ¬c∷[]≡[] ()
    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (●⊢≅ u₁≅u₂ |u₁-vs₁|≡|u₂-vs₂|) (lne len|u₁-vs₁|>0 len|u₂-vs₂|≡0) = Nullary.contradiction len|u₁-vs₁|>0 (n≡0→¬n>0 len|u₁-vs₁|≡0)
      where
        |u₂-vs₂|≡[] : proj₁ (flat (PairU {p} {r * ε∉r ` loc } {loc} u₂ (ListU vs₂))) ≡ []
        |u₂-vs₂|≡[] = Utils.length≡0→[] len|u₂-vs₂|≡0 
        len|u₁-vs₁|≡0 : length (proj₁ (flat (PairU {p} {r * ε∉r ` loc} {loc} u₁ (ListU vs₁)))) ≡ 0
        len|u₁-vs₁|≡0 = cong length (trans |u₁-vs₁|≡|u₂-vs₂| |u₂-vs₂|≡[])
        |u₂|≡[] :  proj₁ (flat  u₂) ≡ []
        |u₂|≡[] = ++-conicalˡ (proj₁ (flat u₂))  (proj₁ (flat (ListU vs₂))) |u₂-vs₂|≡[]
    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (●⊢≅ u₁≅u₂ list-vs₁≅list-vs₂) (bne len|u₁-vs₁|>0 len|u₂-vs₂|>0 (seq₂  u₁≡u₂ list-vs₁>list-vs₂ )) =
      bne len|injList-u₁-vs₁|>0 len|injList-u₂-vs₂|>0 (star-tail inj-u₁≡inj-u₂ list-vs₁>list-vs₂)  
        where
          inj-u₁≡inj-u₂ : inj u₁ ≡ inj u₂ 
          inj-u₁≡inj-u₂ = cong inj u₁≡u₂

          len|injList-u₁-vs₁|>0 : length (proj₁ (flat (injList (PairU u₁ (ListU vs₁))))) Nat.> 0
          len|injList-u₁-vs₁|>0 = ¬≡[]→length>0 λ eq → ¬c∷[]≡[] (begin
            (c ∷ proj₁ (flat u₁)) ++ proj₁ (flat (ListU vs₁))
            ≡⟨ sym (PDI.mkinjListSoundEv inj s-ev (PairU u₁ (ListU vs₁))) ⟩
              proj₁ (flat (injList (PairU u₁ (ListU vs₁))))
            ≡⟨ eq ⟩
              []
            ∎)
            where
              ¬c∷[]≡[] : ¬ ((c ∷ proj₁ (flat u₁)) ++ proj₁ (flat (ListU vs₁)) ≡ [])
              ¬c∷[]≡[] ()

          len|injList-u₂-vs₂|>0 : length (proj₁ (flat (injList (PairU u₂ (ListU vs₂))))) Nat.> 0
          len|injList-u₂-vs₂|>0 = ¬≡[]→length>0 λ eq → ¬c∷[]≡[] (begin
            (c ∷ proj₁ (flat u₂)) ++ proj₁ (flat (ListU vs₂))
            ≡⟨ sym (PDI.mkinjListSoundEv inj s-ev (PairU u₂ (ListU vs₂))) ⟩
              proj₁ (flat (injList (PairU u₂ (ListU vs₂))))
            ≡⟨ eq ⟩
              []
            ∎)
            where
              ¬c∷[]≡[] : ¬ ((c ∷ proj₁ (flat u₂)) ++ proj₁ (flat (ListU vs₂)) ≡ [])
              ¬c∷[]≡[] ()
    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (●⊢lne _ _ _) (be _ _ (seq₁ _)) = {!!}
    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (●⊢lne _ _ _) (be _ _ (seq₂ _ _)) = {!!}
    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (●⊢lne _ _ _) (bne _ _ (seq₁ _)) = {!!}
    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (●⊢lne _ _ _) (bne _ _ (seq₂ _ _)) = {!!}
    >-inc-ev (PairU u₁ (ListU vs₁))  (PairU u₂ (ListU vs₂)) (●⊢lne _ _ _) (lne _ _) = {!!}

-----------------------------------------------------------------------------
-- Sub Lemma 33.1 - 33.9 END
----------------------------------------------------------------------------


```


#### Main proof for Lemma 33

```agda

-- main lemma proof
pdU->-inc : ∀ { r : RE } { c : Char }
  → All (>-Inc-≅ {r} {c}) pdU[ r , c ]


pdU->-inc {ε} {c} = []
pdU->-inc {$ c ` loc} {c'} with c Char.≟ c'
...  | no ¬c≡c' = []
...  | yes refl =  ( >-inc ev  ) ∷ []
  where
    ev :  (u₁ u₂ : U ε) →
      ε ⊢ u₁ ≅ u₂ →
      ε ⊢ u₁ > u₂ → ($ c ` loc) ⊢ mkinjLetter u₁ > mkinjLetter u₂
    ev EmptyU EmptyU ε⊢≅ (be refl refl ())
pdU->-inc {l + r ` loc} {c} = all-concat map-ind-hyp-l map-ind-hyp-r 
  where
    ind-hyp-l : All (>-Inc-≅ {l} {c}) pdU[ l , c ]
    ind-hyp-l = pdU->-inc {l} {c}
    
    ind-hyp-r : All (>-Inc-≅ {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU->-inc {r} {c}     

    map-ind-hyp-l : All (>-Inc-≅ {l + r ` loc} {c}) (List.map pdinstance-left pdU[ l , c ])
    map-ind-hyp-l = >-inc-map-left pdU[ l , c ]  ind-hyp-l

    map-ind-hyp-r : All (>-Inc-≅ {l + r ` loc} {c}) (List.map pdinstance-right pdU[ r , c ])
    map-ind-hyp-r = >-inc-map-right pdU[ r , c ]  ind-hyp-r
pdU->-inc {r * ε∉r ` loc } {c} = all->-inc-map-star
  where
    ind-hyp-r : All (>-Inc-≅ {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU->-inc {r} {c}

    all->-inc-map-star : All (>-Inc-≅ {r * ε∉r ` loc} {c}) (List.map (pdinstance-star {r} {ε∉r} {loc} {c})  pdU[ r , c ])
    all->-inc-map-star  = >-inc-map-star pdU[ r , c ] ind-hyp-r

pdU->-inc {l ● r ` loc} {c} with ε∈? l
...                           | no ¬ε∈l = >-inc-map-fst pdU[ l , c ] ind-hyp-l
  where 
    ind-hyp-l : All (>-Inc-≅ {l} {c}) pdU[ l , c ]
    ind-hyp-l = pdU->-inc {l} {c}
    
pdU->-inc {l ● r ` loc} {c}  | yes ε∈l = all-concat all->-inc-pdis-inj-from-l-c all->-inc-concatmap-pdinstance-snd 
  where
    ind-hyp-l : All (>-Inc-≅ {l} {c}) pdU[ l , c ]
    ind-hyp-l = pdU->-inc {l} {c}

    all->-inc-pdis-inj-from-l-c : All (>-Inc-≅ {l ● r ` loc} {c}) (List.map (pdinstance-fst {l} {r} {loc} {c}) pdU[ l , c ])
    all->-inc-pdis-inj-from-l-c =  >-inc-map-fst pdU[ l , c ] ind-hyp-l
    
    ind-hyp-r : All (>-Inc-≅ {r} {c}) pdU[ r , c ]
    ind-hyp-r = pdU->-inc {r} {c}

    all->-inc-concatmap-pdinstance-snd : All (>-Inc-≅ {l ● r ` loc} {c}) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  pdU[ r , c ])
    all->-inc-concatmap-pdinstance-snd  = >-inc-concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  pdU[ r , c ] ind-hyp-r



```



### Definition 34: >-Strict increaseing PDInstance*

Let r be a non problematic regular expression.
Let w be a word.
Let pdi be a PDInstance* w.r.t r and w.
We say pdi is >-inc (strict increasing) iff,
  1. p be the partial derivative descendant inhabited in pdi, and
  2. inj is the injection function from parse tress of p to parse tress of r.
  3. for all parse trees p, u₁ and u₂ where p ⊢ u₁ > u₂
  Then r ⊢ inj u₁ > inj u₂

```agda
{-
data *>-Inc : ∀ { r : RE } { w : List Char } → PDInstance* r w → Set where
  *>-inc : ∀ { p r : RE } { w : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → (proj₁ ( flat {r} (inj x ) ) ≡ w ++ (proj₁ (flat {p} x))) }
    → ( (u₁ : U p) → (u₂ : U p ) → p ⊢ u₁ > u₂ → r ⊢ inj u₁ > inj u₂ ) -- strict increasing evidence
    → *>-Inc {r} {w} (pdinstance* {p} {r} {w} inj sound-ev)
-}

data *>-Inc-≅ : ∀ { r : RE } { w : List Char } → PDInstance* r w → Set where
  *>-inc : ∀ { p r : RE } { w : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → (proj₁ ( flat {r} (inj x ) ) ≡ w ++ (proj₁ (flat {p} x))) }
    → ( (u₁ : U p) → (u₂ : U p )
      → p ⊢ u₁ ≅ u₂ 
      → p ⊢ u₁ > u₂
      → r ⊢ inj u₁ > inj u₂ ) -- strict increasing evidence
    → *>-Inc-≅ {r} {w} (pdinstance* {p} {r} {w} inj sound-ev)
{-    
  *>-inc-> : ∀ { p₁ p₂ r : RE } { w : List Char }
    { in₁ : U p₁ → U r }
    { s-ev₁ : ∀ ( x : U p₁ ) → (proj₁ ( (flat {r} (in₁ x ) ) ≡ w ++ (proj₁ (flat {p₁} x)))) }
    { in₂ : U p₂ → U r }
    { s-ev₂ : ∀ ( x : U p₂ ) → (proj₁ ( (flat {r} (in₂ x ) ) ≡ w ++ (proj₁ (flat {p₂} x)))) }
    → ( (u₁ : U p₁) → (u₂ : U p₂ )
      → r ⊢ in₁ u₁ > in₂ u₂ ) -- strict increasing evidence
    → *>-Inc-≅ {r} {w} (pdinstance* {p} {r} {w} inj sound-ev)
-}     

 -- if p ≡ r and w ≡ [] , inj is λ x → x, do we need a special case? no. 
```




### Lemma 35 : all pdinstance*'s from pdUMany[ r , w ] are >-strict increasing .

Let r be a non problematic regular expression.
Let w be a word.
Then for all pdi ∈ pdUMany[ r , w ], pdi is >-strict increasing. 


#### Sub Lemma 35.1 - 35.3 : *>-Inc is preserved inductively over pdinstance*'s operations

```agda

-----------------------------------------------------------------------------
-- Sub Lemma 35.1 - 35.3 BEGIN 
----------------------------------------------------------------------------
compose-pdi-with-*>-inc : { r d : RE } { pref : List Char } { c : Char }
                   → ( d→r : U d → U r )
                   → ( s-ev-d→r : ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
                   → (pdi : PDInstance d c)
                   → ≅-Preserve pdi 
                   → >-Inc-≅ pdi
                   → ( (x₁ : U d) → (x₂ : U d) →  (d ⊢ x₁ ≅ x₂) → (d ⊢ x₁ > x₂) → r ⊢ d→r x₁ > d→r x₂ )
                   ---------------------------------------------------------------
                   → *>-Inc-≅ (compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d→r pdi)
compose-pdi-with-*>-inc {r} {d} {pref} {c} d→r s-ev-d→r pdi@(pdinstance {p} {d} {c}  p→d s-ev-p→d) (≅-pres u₁→u₂→u₁≅u₂→p→du₁≅p→du₂) (>-inc u₁→u₂→u₁≅u₂→u₁>u₂→pd-u₁>pd-u₂ ) x₁→x₂→x₁≅x₂→x₁>x₂→dr-x₁>dr-x₂ = *>-inc ev-*>-inc 
  where
    ev-*>-inc : (v₁ v₂ : U p)
      → p ⊢ v₁ ≅ v₂
      → p ⊢ v₁ > v₂
      → r ⊢ d→r (p→d v₁) > d→r (p→d v₂)
    ev-*>-inc v₁ v₂ v₁≅v₂ v₁>v₂ = x₁→x₂→x₁≅x₂→x₁>x₂→dr-x₁>dr-x₂ (p→d v₁) (p→d v₂) (u₁→u₂→u₁≅u₂→p→du₁≅p→du₂  v₁ v₂ v₁≅v₂ )  (u₁→u₂→u₁≅u₂→u₁>u₂→pd-u₁>pd-u₂ v₁ v₂ v₁≅v₂ v₁>v₂)   


advance-pdi*-with-c-*>-inc : ∀ { r : RE } { pref : List Char } { c : Char}
  → (pdi : PDInstance* r pref)
  → *>-Inc-≅ pdi
  ----------------------------------------------------------
  → All *>-Inc-≅ (advance-pdi*-with-c {r} {pref} {c} pdi)
advance-pdi*-with-c-*>-inc {r} {pref} {c} pdi@(pdinstance* {d} {r} {pref} d→r s-ev-d→r) (*>-inc u₁→u₂→u₁>u₂→dr-u₁>dr-u₂)= go pdU[ d , c ] (pdU-≅-preserve {d} {c})  (pdU->-inc {d} {c}) 
  where
    go : ( pdis : List (PDInstance d c) )
       → All ≅-Preserve pdis 
       → All >-Inc-≅ pdis
       → All *>-Inc-≅ (List.map (compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d→r) pdis)
    go [] [] [] = []
    go (pdi ∷ pdis) (pdi-≅-pres ∷ all-≅-pres-pdis) (pdi->-inc ∷ all->-inc-pdis) = ( compose-pdi-with-*>-inc {r} {d} {pref} {c} d→r s-ev-d→r pdi pdi-≅-pres pdi->-inc u₁→u₂→u₁>u₂→dr-u₁>dr-u₂ ) ∷ go pdis all-≅-pres-pdis  all->-inc-pdis 


concatmap-advance-pdi*-with-c-*>inc : ∀ { r : RE } { pref : List Char } { c : Char}
  → (pdis : List (PDInstance* r pref) )
  → All *>-Inc-≅ pdis
  ----------------------------------------------------------
  → All *>-Inc-≅ (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
concatmap-advance-pdi*-with-c-*>inc {r} {pref} {c} [] [] = []
concatmap-advance-pdi*-with-c-*>inc {r} {pref} {c} (pdi ∷ pdis) (pdi-*>-inc ∷ all-*>-inc-pdis) = all-concat all-*>-inc-advance-pdi*-with-c-pdi ind-hyp 

  where
    all-*>-inc-advance-pdi*-with-c-pdi : All *>-Inc-≅ (advance-pdi*-with-c {r} {pref} {c} pdi)
    all-*>-inc-advance-pdi*-with-c-pdi = advance-pdi*-with-c-*>-inc pdi pdi-*>-inc

    ind-hyp : All *>-Inc-≅ (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    ind-hyp = concatmap-advance-pdi*-with-c-*>inc {r} {pref} {c} pdis all-*>-inc-pdis

-----------------------------------------------------------------------------
-- Sub Lemma 35.1 - 35.3 END
----------------------------------------------------------------------------


```


#### Main proof for Lemma 35

```agda

pdUMany-aux-*>-inc : ∀ { r : RE } { pref : List Char} 
  → (suff : List Char )
  → (pdis : List (PDInstance* r pref))
  → All *>-Inc-≅ pdis
  ----------------------------------------------------
  → All *>-Inc-≅ (pdUMany-aux suff pdis)
pdUMany-aux-*>-inc {r} {pref} [] pdis all-*>-inc-pdis rewrite (++-identityʳ pref) = all-*>-inc-pdis
pdUMany-aux-*>-inc {r} {pref} ( c ∷ cs) pdis all-*>-inc-pdis = pdUMany-aux-*>-inc {r} {pref ∷ʳ c} cs (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis) concatmap-advance-pdi*-with-c-pdis-all-*>inc

  where
    concatmap-advance-pdi*-with-c-pdis-all-*>inc : All *>-Inc-≅ (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
    concatmap-advance-pdi*-with-c-pdis-all-*>inc = concatmap-advance-pdi*-with-c-*>inc pdis all-*>-inc-pdis 



pdUMany-*>-inc : ∀ { r : RE } { w : List Char }
  → All (*>-Inc-≅ {r} {w}) pdUMany[ r  , w ]
pdUMany-*>-inc {r} {w} = pdUMany-aux-*>-inc w  [  ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ] (*>-inc ev-*>-inc  ∷ [] )
  where
    ev-*>-inc : (u₁ : U r)
      → (u₂ : U r)
      → r ⊢ u₁ ≅ u₂ 
      → r ⊢ u₁ > u₂
      --------------------------------
      → r ⊢ (λ u → u) u₁ > (λ u → u) u₂ 
    ev-*>-inc u₁ u₂ u₁≅u₂ u₁>u₂ = u₁>u₂ 

```



