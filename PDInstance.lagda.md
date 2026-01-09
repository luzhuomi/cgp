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

import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; Flat-[] ; flat-[] ;  mkAllEmptyU≢[])


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


------------------------------------------------------------------------------------
-- pdinstance-fst and its sub function
-- injection builder for pair with the first being injected ; (lifted up from pdinstance-fst's where clause to expose to the ≤-mono-map-fst proof

mkinjFst : ∀ {l' l r : RE } { loc : ℕ } 
  → (f : U l' → U l )
  → U (l' ● r ` loc )
  → U (l ● r  ` loc )
mkinjFst {l'} {l} {r} {loc}  f (PairU {l'} {r} {loc} u v) = PairU {l} {r} {loc} (f u) v 

pdinstance-fst : ∀ { l r : RE } { loc : ℕ } { c : Char } → PDInstance l c → PDInstance (l ● r ` loc) c
pdinstance-fst {l} {r} {loc} {c} (pdinstance {l'} {l} {c} f s-ev) = 
                   pdinstance { l' ● r ` loc }
                          { l ● r ` loc }
                          {c}
                          injFst 
                          sound-ev2
           where                                           
             injFst : U (l' ● r ` loc)   → U (l ● r ` loc )
             -- injFst (PairU {l'} {r} {loc} u v) = PairU {l} {r} {loc} (f u) v -- lifted out as mkinjFst for provability
             injFst = mkinjFst f
             sound-ev2 : ∀ ( u : U ( l' ● r ` loc) ) → (proj₁ (flat { l ● r ` loc } (injFst u )) ≡ c ∷ (proj₁ (flat { l' ● r ` loc } u)))
             sound-ev2 (PairU {l'} {r} {loc} u v) =
               begin
                 proj₁ (flat (PairU {l} {r} {loc} (f u) v))
               ≡⟨⟩
                 (proj₁ (flat (f u))) ++ (proj₁ (flat v))
               ≡⟨ cong (λ x → ( x ++ (proj₁ (flat v)))) (s-ev u) ⟩
                 (c ∷ (proj₁ (flat u))) ++ (proj₁ (flat v))
               ≡⟨⟩
                 c ∷ (proj₁ (flat (PairU {l'} {r} {loc} u v)))
               ∎
-- pdinstance-fst and its sub function end
------------------------------------------------------------------------------------

------------------------------------------------------------------------------------
-- pdinstance-snd and its sub functions


mkinjSnd  : ∀ {l r r' : RE } { loc : ℕ }
          →  (f : U r' → U r)
          →  U l 
          →  U r'
          →  U (l ● r ` loc )
mkinjSnd {l} {r} {r'} {loc} f v u = PairU {l} {r} {loc} v (f u)


mk-snd-pdi : ∀ { l r : RE } { loc : ℕ } { c : Char }
           → ∃[ e ] Flat-[] l e
           → PDInstance r c 
           → PDInstance ( l ● r ` loc ) c
mk-snd-pdi {l} {r} {loc} {c} (e , (flat-[] e' proj₁∘flate≡[] )) (pdinstance {p} {r} {c}  inj s-ev) = pdinstance {p} { l ● r ` loc } {c} -- e' is e
                        -- (λ u → PairU {l} {r} {loc} e (inj u) )
                        -- injSnd
                        (mkinjSnd {l} {r} {p} {loc} inj e)
                        injSnd-s-ev
                   where
                     injSnd :  U p → U (l ● r ` loc)
                     injSnd =                     
                        (mkinjSnd {l} {r} {p} {loc} inj e)
                     injSnd-s-ev =
                       (λ u → 
                           begin
                             proj₁ (flat (PairU {l} {r} {loc} e (inj u)))
                           ≡⟨⟩
                             (proj₁ (flat e')) ++ (proj₁ (flat (inj u)))
                           ≡⟨ cong (λ x → ( x ++  (proj₁ (flat (inj u))))) proj₁∘flate≡[] ⟩  --  e must be an empty; we do have flat v ≡ [] from mkAllEmptyU-sound
                             [] ++ (proj₁ (flat (inj u)))
                           ≡⟨⟩
                             proj₁ (flat (inj u))
                           ≡⟨ s-ev u ⟩
                             c ∷ (proj₁ (flat u))
                           ∎
                        )



pdinstance-snd : ∀ { l r : RE } { loc : ℕ } { c : Char } → ∃[ e ] (Flat-[] l e ) → List (PDInstance r c )  →  List (PDInstance (l ● r ` loc) c)
pdinstance-snd {l} {r} {loc} {c} ( e , flat-[]-e )  pdis = List.map (mk-snd-pdi (e , flat-[]-e)) pdis 


-- pdinstance-snd and its sub functions end
------------------------------------------------------------------------------------


```
