```agda
module cgp.Utils where

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_)

import Data.List.Properties
open Data.List.Properties using (∷-injective ; ++-identityʳ ; unfold-reverse ; ∷ʳ-++ )

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using (ℕ ; _>_ ; zero ; suc ) 

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
import Data.List.Membership.Propositional
open Data.List.Membership.Propositional using (_∈_)

open import Function using (_∘_ ; flip)

import Relation.Nullary as Nullary 
open Nullary using (¬_)

```


#### Sub Lemma 0.1 ( Any concatenation )

Let P be a unary predicate with dom2ain r.
Let xs and ys be lists of r.
Then
1) Any P ys implies Any P (xs ++ ys) and 
2) Any P xs implies Any P (xs ++ ys)

```agda
any-right-concat : ∀ { r : Set } { P : r → Set } { xs ys : List r }
  → Any P ys
  ----------------
  → Any P (xs ++ ys)
any-right-concat {r} {P} {[]} {ys} any-p-ys = any-p-ys
any-right-concat {r} {P} {(x ∷ xs)} {ys} any-p-ys = there (any-right-concat {r} {P} {xs} {ys} any-p-ys)

any-left-concat : ∀ { r : Set } { P : r → Set } { xs ys : List r }
  → Any P xs
  ------------------
  → Any P (xs ++ ys)
any-left-concat (here px)   = here px
any-left-concat (there pxs) = there (any-left-concat pxs)
```

The above lemma is very general and not specific to this paper.

### Sub Lemma 0.2 ( All concatenation )
Let P be a unary predicate with domain r.
Let xs and ys be lists of r.
Then All P xs and All P ys implies All P (xs ++ ys)

```agda
all-concat : ∀ { r : Set } { P : r → Set } { xs ys : List r }
  → All P xs
  → All P ys
  -------------------
  → All P (xs ++ ys)
all-concat {r} {P} {[]} {ys} [] pys = pys
all-concat {r} {P} {x ∷ xs} {ys} (px ∷ pxs) pys = px ∷ (all-concat {r} {P} {xs} {ys} pxs pys)

```



### Sub Lemma 0.3 ( inverse ∷ for List )

```agda

∷-inj : ∀ { c₁ c₂ : Char } { cs₁ cs₂ : List Char }
        → (c₁ ∷ cs₁) ≡ (c₂ ∷ cs₂)
        --------------------------
        → (c₁ ≡ c₂) × (cs₁ ≡ cs₂)
-- ∷-inj {c₁} {c₂} {cs₁} {cs₂} refl = refl , refl
∷-inj = ∷-injective -- specialized with {A} as {Char}

```

### Sub Lmma 0.4 ( foldr _++_ ys (map (λ _ → []) xs)  is ys)

```agda

foldr++ys-map-λ_→[]-xs≡ys : ∀ { A B : Set } (xs : List A) (ys : List B) 
    -----------------------------------------------------
    → List.foldr _++_ ys (List.map (λ _ → []) xs) ≡ ys
foldr++ys-map-λ_→[]-xs≡ys []        ys = refl
foldr++ys-map-λ_→[]-xs≡ys (x ∷ xs) ys = foldr++ys-map-λ_→[]-xs≡ys xs ys 

```

```agda
¬∷≡[] : ∀ { A : Set } { x : A } { xs : List A } 
  → ¬ ( x ∷ xs ≡ [] )
¬∷≡[] = λ()  



contraposition : ∀ {A B : Set}
  → (A → B)
    -----------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)


length≡0→[] : ∀ { A : Set } { xs : List A }
  → List.length xs ≡ 0
  ----------------------
  → xs ≡ []
length≡0→[] {A} {[]} refl = refl

[]→length≡0 : ∀ { A : Set } { xs : List A }
  → xs ≡ []
  ----------------------
  → List.length xs ≡ 0
[]→length≡0 {A} {[]} refl = refl   


¬≡[]→¬length≡0 : ∀ { A : Set } { xs : List A }
  → ¬ xs ≡ []
  -----------------------
  → ¬ List.length xs ≡ 0
¬≡[]→¬length≡0 {A} {xs} = contraposition length≡0→[] 
  

¬≡0→>0 :  ∀ { n : ℕ }
  → ¬ n ≡ 0
  ----------------------------
  → n > 0
¬≡0→>0 {0} ¬0≡0 = Nullary.contradiction refl ¬0≡0
¬≡0→>0 {suc n} ¬suc-n≡0 = Nat.s≤s Nat.z≤n 



∷→length>0 : ∀ { A : Set } { x : A } { xs : List A }
  → List.length ( x ∷ xs ) > 0
∷→length>0 = Nat.s≤s Nat.z≤n   


map-[] : ∀ { A B : Set } { xs : List A } { f : A → B }
  → xs ≡ []
  --------------------
  → List.map f xs ≡ []
map-[] {A} {B} {[]} {f} refl = refl
map-[] {A} {B} {y ∷ ys} {f} y∷ys≡[] = Nullary.contradiction  y∷ys≡[] ¬∷≡[]




inv-map-[] : ∀ { A B : Set } { xs : List A } { f : A → B }
  → List.map f xs ≡ []
  --------------------
  → xs ≡ []
inv-map-[] {xs = []} eq = refl
inv-map-[] {xs = x ∷ xs} ()


inv-concatMap-map-f-[] : ∀ { A B C : Set } { xs : List A } { ys : List B} { f : A → B → C }
  → concatMap (λ x → List.map (f x) ys) xs ≡ []
  ----------------------------------------------
  → (xs ≡ []) ⊎ ( ys ≡ [] )
inv-concatMap-map-f-[] {A} {B} {C}  {[]}  {ys} {f} concatMap-map-f-ys-[]≡[] = inj₁ refl 
inv-concatMap-map-f-[] {A} {B} {C}  {xs}  {[]} {f} concatMap-map-f-[]-xs≡[] = inj₂ refl


xs-all-∈xs : { A : Set } → ( xs : List A ) → All ( _∈ xs) xs 
xs-all-∈xs xs = tabulate  (λ p → p)  


```


-- aux lemma
-- _≢_ : ∀ {A : Set} → A → A → Set
-- x ≢ y  =  ¬ (x ≡ y)

```agda 
{-

-- for these two  we'd better use the Data.List.Properties directly

++-idʳ = ++-identityʳ

unfold-rev = unfold-reverse
-}


{-
-- not in used anymore, since we simplified pdUMany and PDInstance*
-- manually by Kenny 
rev-prefix≡rev-tail++hd  : ∀ { A : Set } { x : A } { ys : List A } { zs : List A }
                        → (List.reverse ( x ∷ ys )) ++ zs ≡ (List.reverse ys) ++ ( x ∷ zs )

rev-prefix≡rev-tail++hd {A} {x} {[]} {zs}       = refl
rev-prefix≡rev-tail++hd {A} {x} {ys} {zs}       = 
  begin
    List.reverse ( x ∷ ys ) ++ zs
  ≡⟨ cong ( _++ zs ) (unfold-reverse x ys) ⟩
    (List.reverse ys) ∷ʳ x  ++ zs
  ≡⟨ ∷ʳ-++ (List.reverse ys) x zs ⟩
    (List.reverse ys) ++ ( x ∷ zs )   
  ∎

-}

{-
-- generated by GPT 5 
rev-prefix≡rev-tail++hd
  : ∀ {A : Set} {x : A} {ys zs : List A}
  → List.reverse (x ∷ ys) ++ zs ≡ List.reverse ys ++ (x ∷ zs)
rev-prefix≡rev-tail++hd {A} {x} {ys} {zs} =
  begin
    (List.reverse (x ∷ ys) ++ zs)
  ≡⟨ cong ( _++ zs) (Data.List.Properties.reverse-++ (x ∷ []) ys) ⟩
    (List.reverse ys ++ List.reverse (x ∷ [])) ++ zs
  ≡⟨⟩
    (List.reverse ys ++ (x ∷ [])) ++ zs
  ≡⟨ Data.List.Properties.++-assoc (List.reverse ys) (x ∷ []) zs ⟩
    List.reverse ys ++ ((x ∷ []) ++ zs)
  ≡⟨⟩
   List.reverse ys ++ (x ∷ zs)
  ∎
-}


{- -- does not work 
foldl-flip∷[]++ : ∀ { A : Set } { xs ys : List A }
                  → (List.foldl (flip _∷_) [] xs) ++ ys ≡ List.foldl (flip _∷_) ys xs

rev-prefix≡rev-tail++hd  : ∀ { A : Set } { x : A } { ys : List A } { zs : List A }
                        → (List.reverse ( x ∷ ys )) ++ zs ≡ (List.reverse ys) ++ ( x ∷ zs )


rev-prefix≡rev-tail++hd {A} {x} {[]} {zs}       = refl
rev-prefix≡rev-tail++hd {A} {x} {y ∷ ys} {zs}  =
  begin
    List.reverse (x ∷ y ∷ ys) ++ zs
  ≡⟨⟩
    List.foldl (flip _∷_) [] (x ∷ y ∷ ys) ++ zs
  ≡⟨ foldl-flip∷[]++ {A} {(x ∷ y ∷ ys)} {zs} ⟩
    List.foldl (flip _∷_) zs (x ∷ y ∷ ys)
  ≡⟨⟩
    List.foldl (flip _∷_) (x ∷ zs) (y ∷ ys)
  ≡⟨ sym (foldl-flip∷[]++ {A} {y ∷ ys} {x ∷ zs}) ⟩
    List.reverse (y ∷ ys) ++ x ∷ zs 
  ∎


foldl-flip∷[]++ {A} {[]} {ys}           = refl 
foldl-flip∷[]++ {A} {xs} {[]}        rewrite ++-identityʳ (List.foldl (flip _∷_) [] xs)  = refl
foldl-flip∷[]++ {A} {a ∷ as} { b ∷ bs } = -- {!!}
  begin
    List.foldl (flip _∷_) (flip _∷_ [] a) as ++ (b ∷ bs)
  ≡⟨⟩
    List.foldl (flip _∷_) (a ∷ []) as ++ (b ∷ bs)
  ≡⟨⟩ 
    List.foldl (flip _∷_) [] (a ∷ as) ++ (b ∷ bs)
  ≡⟨ sym (rev-prefix≡rev-tail++hd {A} {a} {as} {b ∷ bs}) ⟩
    List.foldl (flip _∷_) [] ( b ∷ a ∷ as ) ++ bs
  ≡⟨ foldl-flip∷[]++ {A} { b ∷ a ∷ as} {bs} ⟩
    List.foldl (flip _∷_) bs (b ∷ a ∷ as)
  ≡⟨⟩
   List.foldl (flip _∷_) (flip _∷_  (b ∷ bs) a) as
  ∎
-}
```
