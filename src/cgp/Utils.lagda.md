```agda
module cgp.Utils where

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_ ; length ; head )

import Data.List.Properties
open Data.List.Properties using (∷-injective ; ++-identityʳ ; unfold-reverse ; ∷ʳ-++ ; ++-assoc )

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using (ℕ ; _>_ ; zero ; suc ; _+_ ) 

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst ; cong₂ )
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )



import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)


import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)


import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map ; tabulate )


open import Data.List.Relation.Unary.All.Properties using (map⁺)

open import Data.List.Relation.Unary.Any using (Any; here; there ; map)
import Data.List.Membership.Propositional
open Data.List.Membership.Propositional using (_∈_)

open import Function using (_∘_ ; flip )

import Relation.Nullary as Nullary 
open Nullary using (¬_ ; contraposition)

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


¬0>0 : ¬ 0 > 0
¬0>0 = λ () 

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


n≡0→¬n>0 : ∀ {n} → n ≡ 0 → ¬ (n Nat.> 0)
n≡0→¬n>0 refl ()

nat+0→>0 : ∀ {n} → (n + 0) > 0 → n > 0
nat+0→>0 {n} p rewrite NatProperties.+-identityʳ n = p

0+nat→>0 : ∀ {n} → (0 + n) > 0 → n > 0
0+nat→>0 {n} p rewrite NatProperties.+-identityˡ n = p


¬≡0→>0 :  ∀ { n : ℕ }
  → ¬ n ≡ 0
  ----------------------------
  → n > 0
¬≡0→>0 {0} ¬0≡0 = Nullary.contradiction refl ¬0≡0
¬≡0→>0 {suc n} ¬suc-n≡0 = Nat.s≤s Nat.z≤n 

>0→¬≡0 : ∀ { n : ℕ }
  → n > 0
  --------------------------
  → ¬ n ≡ 0
>0→¬≡0 {0} ()

¬≡[]→¬length≡0 : ∀ { A : Set } { xs : List A }
  → ¬ xs ≡ []
  -----------------------
  → ¬ List.length xs ≡ 0
¬≡[]→¬length≡0 {A} {xs} = contraposition length≡0→[] 
  

¬≡[]→length>0 : ∀ { A : Set } { xs : List A }
  → ¬ xs ≡ []
  -----------------------
  → List.length xs > 0
¬≡[]→length>0 {A} {xs} ¬xs≡[] = ¬≡0→>0   (¬≡[]→¬length≡0 ¬xs≡[] ) 


length>0→¬≡[] : ∀ { A : Set } { xs : List A }
  → List.length xs > 0
  -----------------------
  → ¬ xs ≡ []
length>0→¬≡[] {A} {xs} len|xs|>0 xs≡[] = >0→¬≡0  len|xs|>0  ([]→length≡0 xs≡[])



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

```agda

w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ : ∀ { w₁ w₂ w₃ w₄ : List Char }
    → w₁ ++ w₂ ≡ w₃ ++ w₄
    → length w₁ ≡ length w₃
    ---------------------------------------------------------------- 
    → (w₁ ≡ w₃) × (w₂ ≡ w₄) 
w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ {[]}        {xs₂} {[]}       {xs₄} xs₂≡xs₄               len-[]≡len-[]         = refl , xs₂≡xs₄
w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ {x₁ ∷ xs₁ } {xs₂} {x₃ ∷ xs₃} {xs₄} x₁∷xs₁++xs₂≡x₃∷xs₃++xs₄ len-x₁∷xs₁≡len-x₃∷xs₃ =  Eq.cong₂ (_∷_) x₁≡x₃ (proj₁ ind-hyp) , proj₂ ind-hyp
  where
    x₁≡x₃ : x₁ ≡ x₃
    x₁≡x₃ = proj₁ (∷-inj x₁∷xs₁++xs₂≡x₃∷xs₃++xs₄ ) 

    xs₁++xs₂≡xs₃++xs₄ : xs₁ ++ xs₂ ≡ xs₃ ++ xs₄
    xs₁++xs₂≡xs₃++xs₄  = proj₂ (∷-inj  {x₁} {x₃} {xs₁ ++ xs₂} {xs₃ ++ xs₄} x₁∷xs₁++xs₂≡x₃∷xs₃++xs₄)

    len-xs₁≡len-xs₃ : length xs₁ ≡ length xs₃
    len-xs₁≡len-xs₃ = suc-injective len-x₁∷xs₁≡len-x₃∷xs₃ 


    ind-hyp : xs₁ ≡ xs₃ × xs₂ ≡ xs₄
    ind-hyp = w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ {xs₁} {xs₂} {xs₃} {xs₄} xs₁++xs₂≡xs₃++xs₄ len-xs₁≡len-xs₃  
    


len-w++[x]≡len-w+1 : ∀ { w : List Char } { x : Char } 
    → length (w ++ [ x ]) ≡ suc (length w)
len-w++[x]≡len-w+1 {[]} {x} = refl  
len-w++[x]≡len-w+1 { y ∷ ys } {x} =
  begin
    length ( ( y ∷ ys ) ++ [ x ])
  ≡⟨⟩
    length ( y ∷ ( ys  ++ [ x ]) )
  ≡⟨⟩
    suc ( length ( ys  ++ [ x ]) )
  ≡⟨ cong suc (len-w++[x]≡len-w+1 {ys} {x})⟩
    suc ( suc ( length ys ) )
  ≡⟨⟩
    suc (length ( y ∷ ys ) )
  ∎ 

len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ : ∀ { w₁ w₂ w₃ : List Char }
    → length ( w₁ ++ w₃ ) Nat.> length (w₂ ++ w₃)
    ---------------------------------------------------------------- 
    → length w₁ > length w₂
len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ {w₁} {w₂} {[]} len-w₁>len-w₂ rewrite ++-identityʳ w₁ | ++-identityʳ w₂  = len-w₁>len-w₂
len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ {w₁} {w₂} {x ∷ []} len-w₁++x>len-w₂++x rewrite  len-w++[x]≡len-w+1 {w₁} {x} |  len-w++[x]≡len-w+1 {w₂} {x} = Nat.s<s⁻¹  len-w₁++x>len-w₂++x 
len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ {w₁} {w₂} {x ∷ xs} len-w₁++x∷xs>len-w₂++x∷xs = len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ {w₁} {w₂} {x ∷ []} len-w₁++[x]>len-w₂++[x]
  where
    len-w₁++[x]++xs>len-w₂++[x]++xs : length ( ( w₁ ++ [ x ] ) ++ xs ) Nat.>  length ( ( w₂ ++ [ x ] ) ++ xs ) 
    len-w₁++[x]++xs>len-w₂++[x]++xs rewrite sym (++-assoc w₁ [ x ] xs ) | sym ( ++-assoc w₂ [ x ] xs ) = len-w₁++x∷xs>len-w₂++x∷xs
    len-w₁++[x]>len-w₂++[x] : length ( w₁ ++ [ x ] ) > length ( w₂ ++ [ x ] )
    len-w₁++[x]>len-w₂++[x] = len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ {w₁ ++ [ x ] } {w₂ ++ [ x ] } {xs}  len-w₁++[x]++xs>len-w₂++[x]++xs
    
  

  
w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ : ∀ {w₁ w₂ w₃ w₄ : List Char}
  → w₁ ++ w₂ ≡ w₃ ++ w₄
  → length w₁ Nat.< length w₃
  ---------------------------------------------------------------- 
  → ∃[ w₅ ] (¬ w₅ ≡ []) × (w₁ ++ w₅ ≡ w₃) × (w₂ ≡ w₅ ++ w₄)
w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ {[]}        {xs₂}    {[]}       {xs₄} []++xs₂≡[]++xs₄         len-[]<len-[]         = Nullary.contradiction len-[]<len-[] (NatProperties.n≮n 0 )
w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ {[]}        {xs₂}    {x₃ ∷ xs₃} {xs₄} []++xs₂≡x₃∷xs₃++xs₄     len-[]<len-x₃∷xs₃     = (x₃ ∷ xs₃) , (λ()) , refl , []++xs₂≡x₃∷xs₃++xs₄  
w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ {x₁ ∷ xs₁}  {xs₂}    {x₃ ∷ xs₃} {xs₄} x₁∷xs₁++xs₂≡x₃∷xs₃++xs₄ len-x₁∷xs₁<len-x₃∷xs₃ =
  proj₁ ind-hyp ,  proj₁ (proj₂ ind-hyp) , Eq.cong₂ (_∷_) x₁≡x₃  (proj₁ (proj₂ (proj₂ ind-hyp)))  , (proj₂ (proj₂ (proj₂ ind-hyp)))  
  where
    x₁≡x₃ : x₁ ≡ x₃
    x₁≡x₃ = proj₁ (∷-inj x₁∷xs₁++xs₂≡x₃∷xs₃++xs₄ ) 
    xs₁++xs₂≡xs₃++xs₄ : xs₁ ++ xs₂ ≡ xs₃ ++ xs₄
    xs₁++xs₂≡xs₃++xs₄  = proj₂ (∷-inj  {x₁} {x₃} {xs₁ ++ xs₂} {xs₃ ++ xs₄}  x₁∷xs₁++xs₂≡x₃∷xs₃++xs₄)
    len-xs₁<len-xs₃ : length xs₁ Nat.< length xs₃
    len-xs₁<len-xs₃ = Nat.s<s⁻¹ len-x₁∷xs₁<len-x₃∷xs₃ 
    ind-hyp :  ∃[ w₅ ] (¬ w₅ ≡ []) × (xs₁ ++ w₅ ≡ xs₃) × (xs₂ ≡ w₅ ++ xs₄)
    ind-hyp = w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ {xs₁} {xs₂} {xs₃} {xs₄} xs₁++xs₂≡xs₃++xs₄ len-xs₁<len-xs₃ 



-- this can be moved to Utils
import Relation.Binary.Definitions
open  Relation.Binary.Definitions using (
  Tri ; tri< ; tri≈ ; tri> ) 
¬m>n→n≡m⊎n>m : ∀ { n m : ℕ }
    → ¬ (m > n)
    → (n ≡ m) ⊎ (n > m)
¬m>n→n≡m⊎n>m {n} {m} ¬m>n with (Nat.<-cmp m n)
... | tri< m<n _    _    = inj₂ m<n          
... | tri≈ _  m≡n  _     = inj₁ (sym m≡n)   
... | tri> _   _    m>n  = Nullary.contradiction m>n ¬m>n



```


```agda
concatmap-λx→[]-xs≡[] : ∀ { A : Set } { B : Set} ( xs : List A )
  → (concatMap (λ x → [] {A = B} ) xs   ) ≡ []
concatmap-λx→[]-xs≡[] {A} {B} [] = refl
concatmap-λx→[]-xs≡[] {A} {B} (x ∷ xs) = concatmap-λx→[]-xs≡[] xs 

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


inspector pattern , not in used for now. 



data Singleton {a} {A : Set a} (x : A) : Set a where
  _with≡_ : (y : A) → x ≡ y → Singleton x

inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
inspect x = x with≡ refl



```agda
-- Purpose: nothing cannot equal just x (absurd pattern)
-- Used by: first-inhabit-++-just-left-pres, first-inhabit-++-just-right-pres, first-inhabit-++-nothing-left, head-map-LeftU-++-map-RightU
-- Proof idea: Pattern matching on impossible constructor
¬nothing≡just : ∀ {A : Set} {x : A} → ¬ nothing ≡ just x
¬nothing≡just ()

-- Purpose: Injectivity of just constructor
-- Used by: first-inhabit-yes-eq-full, first-inhabit-++-just-left-pdi, first-inhabit-++-just-right-decompose, first-inhabit-++-just-left-pres′
-- Proof idea: Pattern matching on refl
just-injective : ∀ {A : Set} {x y : A} → just x ≡ just y → x ≡ y
just-injective refl = refl

-- Purpose: head of a non-empty list is just the first element
-- Used by: (standalone helper for head reasoning)
-- Proof idea: Reflexivity
head-x∷xs≡just-x : ∀ { A : Set} {x : A } { xs : List A } → head ( x ∷ xs ) ≡ just x
head-x∷xs≡just-x {A} {x} {xs} = refl 



-- not in used
head-++-[]-right-∷ : ∀ {a b c : Set} {f : a → c} {g : b → c} {x : b} {xs : List b}
  → head (List.map f [] ++ List.map g (x ∷ xs)) ≡ just (g x)
head-++-[]-right-∷ = refl


  -- these functions can be moved to Utils
 -- Purpose: map identity function is identity
-- Used by: buildU-≡-map-inj-buildU-root, parseAll-[]-yes
-- Proof idea: Induction on xs
map-id : ∀ {A : Set} (xs : List A) → List.map (λ x → x) xs ≡ xs
map-id [] = refl
map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

 -- Purpose: Pointwise equality of functions implies map equality
-- Used by: concatMap-buildU-advance-lift-pdi*-left, advance-lift-pdi*-left-eq
-- Proof idea: Induction on xs
map-cong : ∀ {A B : Set} {f g : A → B} {xs : List A}
    → (∀ x → f x ≡ g x)
    → List.map f xs ≡ List.map g xs
map-cong {xs = []} _ = refl
map-cong {xs = x ∷ xs} h = cong₂ _∷_ (h x) (map-cong h)

 -- Purpose: map distributes over function composition
-- Used by: buildU-≡-map-inj-buildU-root, buildU-lift-pdi*-left, concatMap-buildU-pdUMany-aux-lemma-step
-- Proof idea: Induction on xs
map-∘-eq : ∀ {A B C : Set} (f : A → B) (g : B → C) (xs : List A)
    → List.map (g ∘ f) xs ≡ List.map g (List.map f xs)
map-∘-eq f g [] = refl
map-∘-eq f g (x ∷ xs) = cong₂ _∷_ refl (map-∘-eq f g xs)

 -- Purpose: concatMap distributes over function composition
-- Used by: parseAll-pdU-decomp, concatMap-buildU-advance-lift-pdi*-left
-- Proof idea: Induction on xs
concatMap-∘-eq : ∀ {A B C : Set} (f : A → B) (g : B → List C) (xs : List A)
    → List.concatMap (g ∘ f) xs ≡ List.concatMap g (List.map f xs)
concatMap-∘-eq f g []       = refl
concatMap-∘-eq f g (x ∷ xs) = cong (g (f x) ++_) (concatMap-∘-eq f g xs)

  
  -- map distributes over ++
 -- Purpose: map distributes over list concatenation
-- Used by: concatMap-++-distrib, concatMap-advance-lift-pdi*-left-eq
-- Proof idea: Induction on xs
map-++-distrib : ∀ {A B : Set} (f : A → B) (xs ys : List A)
    → List.map f (xs ++ ys) ≡ List.map f xs ++ List.map f ys
map-++-distrib f []       ys = refl
map-++-distrib f (x ∷ xs) ys = cong (f x ∷_) (map-++-distrib f xs ys)
  
 -- Purpose: map and concatMap commute: concatMap (map f ∘ g) = map f ∘ concatMap g
-- Used by: concatMap-buildU-pdUMany-aux-lemma-step, concatMap-buildU-advance-lift-pdi*-left
-- Proof idea: Induction on xs using map-++-distrib
concatMap-map-commute : ∀ {A B C : Set} (f : B → C) (g : A → List B) (xs : List A)
    → List.concatMap (List.map f ∘ g) xs ≡ List.map f (List.concatMap g xs)
concatMap-map-commute f g [] = refl
concatMap-map-commute f g (x ∷ xs) =
        -- cong₂ _++_ refl (concatMap-map-commute f g xs)
        trans (cong (List.map f (g x) ++_) (concatMap-map-commute f g xs))
          (sym (map-++-distrib f (g x) (List.concatMap g xs)))

 -- Purpose: Pointwise equality of list-valued functions implies concatMap equality
-- Used by: parseAll-pdU-decomp, concatMap-buildU-pdUMany-aux-+
-- Proof idea: Induction on xs
concatMap-cong : ∀ {A B : Set} {f g : A → List B} {xs : List A}
    → (∀ x → f x ≡ g x)
    → List.concatMap f xs ≡ List.concatMap g xs
concatMap-cong {xs = []} _ = refl
concatMap-cong {A} {B} {f} {g} {xs = x ∷ xs} h =
    cong₂ _++_ (h x) (concatMap-cong {A} {B} {f} {g} {xs = xs} h)

 -- Purpose: concat distributes over list concatenation
-- Used by: concatMap-++-distrib
-- Proof idea: Induction on xs using ++-assoc
concat-++ : ∀ {A : Set} (xs ys : List (List A))
    → List.concat (xs ++ ys) ≡ List.concat xs ++ List.concat ys
concat-++ [] ys = refl
concat-++ (x ∷ xs) ys =
    trans (cong (x ++_) (concat-++ xs ys))
          (sym (++-assoc x (List.concat xs) (List.concat ys)))

 -- Purpose: concatMap distributes over list concatenation
-- Used by: concatMap-buildU-pdUMany-aux-lemma-step, concatMap-buildU-pdUMany-aux-+
-- Proof idea: concat (map f (xs++ys)) = concat (map f xs ++ map f ys) = concat xs ++ concat ys
concatMap-++-distrib : ∀ {A B : Set} (f : A → List B) (xs ys : List A)
    → List.concatMap f (xs ++ ys) ≡ List.concatMap f xs ++ List.concatMap f ys
concatMap-++-distrib f xs ys =
    trans (cong List.concat (map-++-distrib f xs ys))
          (concat-++ (List.map f xs) (List.map f ys))


-- Purpose: Build All P (map f xs) from pointwise membership proofs
-- Used by: (utility lemma for All proofs over mapped lists)
-- Proof idea: Induction on xs, threading there constructor
all-map-∈ : ∀ { A B : Set } { P : B → Set } ( f : A → B ) ( xs : List A )
  → ( ∀ ( x : A ) → x ∈ xs → P ( f x ) )
  → All P ( List.map f xs )  
-- all-map-∈ f [] h = []
-- all-map-∈ f (x ∷ xs) h = h x (here refl) ∷ all-map-∈ f xs (λ x' x'∈xs → h x' (there x'∈xs))
all-map-∈ f xs h = map⁺ (tabulate (λ {x} x∈xs → h x x∈xs))

```
