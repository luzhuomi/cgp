This module contains the common definitions of the PDInstance and PDInstance* being used in greedy/PartialDerivative.lagda.md and lne/PartialDerivative.lagda.md


```agda

{-# OPTIONS --rewriting #-}
module cgp.PDInstance  where


import cgp.RE as RE
open RE using (RE;  ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;   ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ; first ; ε∉r→¬first-r≡[] )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU;  unListU ; listU∘unListU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU )


import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_  )



import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)




-- partial derivative (descendant?) relation and coercion function
-- the result type of pdU
data PDInstance : ∀ ( r : RE ) ( c : Char ) → Set where
  pdinstance : ∀ { p r : RE }     -- ^ partial derivative p and input re r 
                  { c : Char }     -- ^ the letter 
               → ( inj : U p → U r ) -- ^ the injection function 
               → ( ∀ ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) ) -- ^ soundness evidence of the inject function
          --------------------------------------------------------------------------------
               → PDInstance r c -- do we need to record the char c and the loc history?



data PDInstance* : ∀ ( r : RE ) ( pref : List Char ) → Set where
  pdinstance* : ∀ { p r : RE }            -- ^ partial derivative descendant p and input re r
                   { pref : List Char }   -- ^ the  prefix (has been consumed)
                → ( inj : U p → U r )     -- ^ the injection function
                → ( ∀ ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ pref ++ ( proj₁ (flat {p} u) )) ) -- ^ soundness evidence of the inject function
                ------------------------------------------------
                → PDInstance* r pref 



-- ^ applying parse tree constructors to coercion records (namely, the injection function and the soundness evidence) 
pdinstance-right : ∀ { l r : RE } { loc : ℕ } { c : Char } → PDInstance r c → PDInstance (l + r ` loc) c 
pdinstance-right {l} {r} {loc} {c} (pdinstance {p} {r} {c} f s-ev) = (pdinstance {p} { l + r ` loc } {c} (λ v → RightU (f v)) s-ev )

pdinstance-left  : ∀ { l r : RE } { loc : ℕ } { c : Char } → PDInstance l c → PDInstance (l + r ` loc) c 
pdinstance-left  {l} {r} {loc} {c} (pdinstance {p} {l} {c} f s-ev) = (pdinstance {p} { l + r ` loc } {c} ( λ u → LeftU (f u)) s-ev ) 

------------------------------------------------------------------------------------
-- pdinstance-star and its sub function
-- injection builder for list ; (lifted up from pdinstance-star's where clause to expose to the any-recons-star proof


mkinjList : ∀ {r' r : RE} { nε : ε∉ r } { loc : ℕ }
   → ( f : U r' → U r )
   → U (r' ● (r * nε ` loc ) ` loc )
   → U ( r * nε ` loc )
mkinjList {r'} {r} {nε} {loc} f  (PairU v (ListU vs)) = ListU ( (f v) ∷ vs) 

pdinstance-star : ∀ { r : RE }  { nε : ε∉ r } { loc : ℕ } { c : Char} →  PDInstance r c → PDInstance ( r * nε ` loc ) c
pdinstance-star {r} {nε} {loc} {c} (pdinstance {r'} {r} {c} f s-ev) =
                         pdinstance { r' ● (r * nε ` loc) ` loc }
                                { r * nε ` loc }
                                {c}
                                injList
                                sound-ev
                where
                  injList : U (r' ● (r * nε ` loc ) ` loc ) → U ( r * nε ` loc )
                  -- injList (PairU v (ListU vs)) = ListU ( (f v) ∷ vs) -- being lifted out as mkinjList for provability
                  injList = mkinjList f 
                  sound-ev : ∀ ( u : U (r' ● (r * nε ` loc ) ` loc ) ) → ( proj₁ (flat { r * nε ` loc } (injList u)) ≡ (c ∷ (proj₁ (flat { r' ● (r * nε ` loc ) ` loc } u ))))
                  sound-ev (PairU v (ListU vs)) =
                    begin
                      proj₁ (flat (ListU (f v ∷ vs )))
                    ≡⟨⟩
                      proj₁ (flat (f v)) ++ proj₁ (flat (ListU vs))
                    ≡⟨ cong (λ x → x ++ proj₁ (flat (ListU vs)) ) (s-ev v) ⟩
                      ( c ∷ proj₁ (flat v) ) ++ (proj₁ (flat (ListU vs)))
                    ∎ 


-- pdinstance-star and its sub function end
------------------------------------------------------------------------------------

```
