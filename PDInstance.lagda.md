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

import Data.List.Properties
open Data.List.Properties using (  ++-assoc ;  ++-identityʳ ; ++-identityˡ ; {-  unfold-reverse ; -} ∷ʳ-++ ; ++-cancelˡ ;  ++-conicalʳ ;  ++-conicalˡ  )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)


import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] ; map)
open import Data.List.Relation.Unary.Any using (Any; here; there ; map)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)


open import Function using (_∘_ ; flip)




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


mkinjList : ∀ {r' r : RE} { nε : ε∉ r } { loc : ℕ } -- r' is the pd 
   → ( f : U r' → U r )
   → U (r' ● (r * nε ` loc ) ` loc )
   → U ( r * nε ` loc )
mkinjList {r'} {r} {nε} {loc} f  (PairU v (ListU vs)) = ListU ( (f v) ∷ vs)


mkinjListSoundEv : ∀ { p r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char } 
  → ( inj : U p → U r )
  → ( inj-s-ev : ( u : U p ) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u) )
  ----------------------------------------------------------------------
  → ( u : U ( p ● ( r * ε∉r ` loc ) ` loc ) )
  → proj₁ (flat (mkinjList inj u ) ) ≡ c ∷ proj₁ (flat u)
mkinjListSoundEv {p} {r} {ε∉r} {loc} {c} inj inj-s-ev (PairU v (ListU vs)) =
                    begin
                      proj₁ (flat (ListU (inj v ∷ vs )))
                    ≡⟨⟩
                      proj₁ (flat (inj v)) ++ proj₁ (flat (ListU vs))
                    ≡⟨ cong (λ x → x ++ proj₁ (flat (ListU vs)) ) (inj-s-ev v) ⟩
                      ( c ∷ proj₁ (flat v) ) ++ (proj₁ (flat (ListU vs)))
                    ∎ 
  

pdinstance-star : ∀ { r : RE }  { ε∉r : ε∉ r } { loc : ℕ } { c : Char} →  PDInstance r c → PDInstance ( r * ε∉r ` loc ) c
pdinstance-star {r} {ε∉r} {loc} {c} (pdinstance {r'} {r} {c} f s-ev) =
                         pdinstance { r' ● (r * ε∉r ` loc) ` loc }
                                { r * ε∉r ` loc }
                                {c}
                                injList
                                sound-ev
                where
                  injList : U (r' ● (r * ε∉r ` loc ) ` loc ) → U ( r * ε∉r ` loc )
                  -- injList (PairU v (ListU vs)) = ListU ( (f v) ∷ vs) -- being lifted out as mkinjList for provability
                  injList = mkinjList f 
                  sound-ev : ∀ ( u : U (r' ● (r * ε∉r ` loc ) ` loc ) ) → ( proj₁ (flat { r * ε∉r ` loc } (injList u)) ≡ (c ∷ (proj₁ (flat { r' ● (r * ε∉r ` loc ) ` loc } u ))))
                  sound-ev = mkinjListSoundEv {r'} {r} {ε∉r} {loc} {c} f s-ev
                  {-
                  sound-ev (PairU v (ListU vs)) =
                    begin
                      proj₁ (flat (ListU (f v ∷ vs )))
                    ≡⟨⟩
                      proj₁ (flat (f v)) ++ proj₁ (flat (ListU vs))
                    ≡⟨ cong (λ x → x ++ proj₁ (flat (ListU vs)) ) (s-ev v) ⟩
                      ( c ∷ proj₁ (flat v) ) ++ (proj₁ (flat (ListU vs)))
                    ∎ -} 


-- pdinstance-star and its sub function end
------------------------------------------------------------------------------------


------------------------------------------------------------------------------------
-- pdinstance-fst and its sub function
-- injection builder for pair with the first being injected ; (lifted up from pdinstance-fst's where clause to expose to the ≤-mono-map-fst proof

mkinjFst : ∀ {l' l r : RE } { loc : ℕ } -- l' is the pd
  → (f : U l' → U l )
  → U (l' ● r ` loc )
  → U (l ● r  ` loc )
mkinjFst {l'} {l} {r} {loc}  f (PairU {l'} {r} {loc} u v) = PairU {l} {r} {loc} (f u) v 


mkinjFstSoundEv : ∀ { p l r : RE } { loc : ℕ } { c : Char } 
  → ( inj : U p → U l )
  → ( s-ev-inj : ( u : U p ) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u) )
  -----------------------------------------------------------------
  → ( u : U ( p ● r ` loc ))
  → proj₁ (flat ((mkinjFst inj) u)) ≡ c ∷ proj₁ (flat u)
mkinjFstSoundEv {p} {l} {r} {loc} {c}  inj s-ev-inj (PairU {p} {r} {loc} u v) =
               begin
                 proj₁ (flat (PairU {l} {r} {loc} (inj u) v))
               ≡⟨⟩
                 (proj₁ (flat (inj u))) ++ (proj₁ (flat v))
               ≡⟨ cong (λ x → ( x ++ (proj₁ (flat v)))) (s-ev-inj u) ⟩
                 (c ∷ (proj₁ (flat u))) ++ (proj₁ (flat v))
               ≡⟨⟩
                 c ∷ (proj₁ (flat (PairU {p} {r} {loc} u v)))
               ∎
                 
  

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
             sound-ev2 = mkinjFstSoundEv f s-ev
             {-
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
             -} 
-- pdinstance-fst and its sub function end
------------------------------------------------------------------------------------

------------------------------------------------------------------------------------
-- pdinstance-snd and its sub functions


mkinjSnd  : ∀ {l r r' : RE } { loc : ℕ } -- r' is the pd
          →  (f : U r' → U r)
          →  U l 
          →  U r'
          →  U (l ● r ` loc )
mkinjSnd {l} {r} {r'} {loc} f v u = PairU {l} {r} {loc} v (f u)

mkinjSndSoundEv : ∀ { p l r : RE } { loc : ℕ } { c : Char } 
  → ( inj : U p → U r )
  → ( s-ev-inj : ( u : U p ) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u ) )
  → ( e : U l )
  → ( Flat-[] l e )
  → ( u : U p )
  → proj₁ (flat ((mkinjSnd {l} {r} {p} {loc} inj e) u)) ≡ c ∷ proj₁ (flat u )
mkinjSndSoundEv {p} {l} {r} {loc} {c}  inj s-ev-inj e (flat-[] .(e) proj₁∘flate≡[] ) u
  = 
                           begin
                             proj₁ (flat (PairU {l} {r} {loc} e (inj u)))
                           ≡⟨⟩
                             (proj₁ (flat e)) ++ (proj₁ (flat (inj u)))
                           ≡⟨ cong (λ x → ( x ++  (proj₁ (flat (inj u))))) proj₁∘flate≡[] ⟩  --  e must be an empty; we do have flat v ≡ [] from mkAllEmptyU-sound
                             [] ++ (proj₁ (flat (inj u)))
                           ≡⟨⟩
                             proj₁ (flat (inj u))
                           ≡⟨ s-ev-inj u ⟩
                             c ∷ (proj₁ (flat u))
                           ∎


mk-snd-pdi : ∀ { l r : RE } { loc : ℕ } { c : Char }
           → ∃[ e ] Flat-[] l e
           → PDInstance r c 
           → PDInstance ( l ● r ` loc ) c
mk-snd-pdi {l} {r} {loc} {c} (e , (flat-[] .(e) proj₁∘flate≡[] )) (pdinstance {p} {r} {c}  inj s-ev) = pdinstance {p} { l ● r ` loc } {c} 
                        -- (λ u → PairU {l} {r} {loc} e (inj u) )
                        -- injSnd
                        (mkinjSnd {l} {r} {p} {loc} inj e)
                        injSnd-s-ev
                   where
                     injSnd :  U p → U (l ● r ` loc)
                     injSnd =                     
                        (mkinjSnd {l} {r} {p} {loc} inj e)
                     injSnd-s-ev = mkinjSndSoundEv {p} {l} {r} {loc} {c} inj s-ev e (flat-[] e  proj₁∘flate≡[])
                     {-
                      =
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
                     -} 


pdinstance-snd : ∀ { l r : RE } { loc : ℕ } { c : Char } → ∃[ e ] (Flat-[] l e ) → List (PDInstance r c )  →  List (PDInstance (l ● r ` loc) c)
pdinstance-snd {l} {r} {loc} {c} ( e , flat-[]-e )  pdis = List.map (mk-snd-pdi (e , flat-[]-e)) pdis 


-- pdinstance-snd and its sub functions end
------------------------------------------------------------------------------------


------------------------------------------------------------------------------------
-- concatmap-pdinstance-snd


zip-es-flat-[]-es : ∀ {l : RE} {ε∈l : ε∈ l }
                    → (es : List (U l)) →  All (Flat-[] l) es →  List ( ∃[ e ] (Flat-[] l e) )
zip-es-flat-[]-es {l} {ε∈l} [] [] = []
zip-es-flat-[]-es {l} {ε∈l} (e ∷ es) (flat-[]-e ∷ flat-[]-es) = ( e , flat-[]-e ) ∷ zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es 


concatmap-pdinstance-snd : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char } → List (PDInstance r c) → List (PDInstance (l ● r ` loc) c)
concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} pdis = concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x  pdis) (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es)
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l

-- concatmap-pdinstance-snd END
------------------------------------------------------------------------------------

------------------------------------------------------------------------------------
-- pdinstance-assoc and its sub functions

inv-assoc : ∀ { l s r : RE } { loc₁ loc₂ : ℕ }
         →  U ( l ● ( s ● r ` loc₂ ) ` loc₁)
         ---------------------------------------------         
         →  U ( ( l ● s ` loc₁ ) ● r ` loc₂)
inv-assoc {l} {s} {r} {loc₁} {loc₂} (PairU  v₁ (PairU v₂ v₃ ) ) = PairU (PairU  v₁ v₂) v₃ 


inv-assoc-sound : ∀ { l s r : RE } { loc₁ loc₂ : ℕ }
         →  ( u : U ( l ● ( s ● r ` loc₂ ) ` loc₁) )
         →  proj₁ (flat (inv-assoc u)) ≡ proj₁ (flat u)
inv-assoc-sound {l} {s} {r} {loc₁} {loc₂} (PairU {l} {s ● r ` loc₂}  {loc₁} v₁ (PairU {s} {r} {loc₂} v₂ v₃ ) )
  with flat v₁      | flat v₂     | flat v₃  
... |  w₁ ,  w₁∈⟦l⟧ | w₂ , w₂∈⟦s⟧ | w₃ , w₃∈⟦r⟧ =  ++-assoc w₁ w₂ w₃


mkinjAssoc : ∀ { p l s r : RE } { loc₁ loc₂ : ℕ } 
    → ( f : U p → U (l ● ( s ● r ` loc₂ ) ` loc₁ ) )
    → U p
    → U (( l ● s ` loc₁) ● r ` loc₂ )
mkinjAssoc {p} {l} {s} {r} {loc₁} {loc₂} f u = inv-assoc (f u)


pdinstance-assoc : ∀ { l s r : RE } { loc₁ loc₂ : ℕ }  { c : Char } → PDInstance (l ● ( s ● r ` loc₂ ) ` loc₁ ) c → PDInstance (( l ● s ` loc₁) ● r ` loc₂ ) c
pdinstance-assoc {l} {s} {r} {loc₁} {loc₂} {c}
  (pdinstance {p}
               {l ● ( s ● r ` loc₂ ) ` loc₁ }
               inj
               inj-sound ) = 
  pdinstance {p} {( l ● s ` loc₁) ● r ` loc₂}
    injAssoc
    injAssoc-sound
                
  where
    injAssoc : U p → U (( l ● s ` loc₁) ● r ` loc₂)
    injAssoc = mkinjAssoc {p} {l} {s} {r} {loc₁} {loc₂} inj
    injAssoc-sound : (u : U p)                           
                   → proj₁ (flat (injAssoc u)) ≡ c ∷ (proj₁ (flat u))
    injAssoc-sound u rewrite sym (inj-sound u) = inv-assoc-sound (inj u)


-- inverse of inv-assoc 
assoc : ∀ { l s r : RE } { loc₁ loc₂ : ℕ }
        →  U ( ( l ● s ` loc₁ ) ● r ` loc₂)
        ---------------------------------------------        
        →  U ( l ● ( s ● r ` loc₂ ) ` loc₁) 
assoc {l} {s} {r} {loc₁} {loc₂} (PairU (PairU  v₁ v₂) v₃ )  = PairU  v₁ (PairU v₂ v₃ ) 

-- needed for the ExtendedGreedy ordering proof. 
assoc-inv-assoc-u≡u :  ∀ { l s r : RE } { loc₁ loc₂ : ℕ }
                    →  { u :  U ( l ● ( s ● r ` loc₂ ) ` loc₁)  }
                    ---------------------------------------------
                    → assoc ( inv-assoc u ) ≡ u
assoc-inv-assoc-u≡u {l} {s} {r} {loc₁} {loc₂} {PairU  v₁ (PairU v₂ v₃ )} =
  begin
    assoc (inv-assoc (PairU v₁ (PairU v₂ v₃ )))
  ≡⟨⟩
    assoc (PairU (PairU  v₁ v₂) v₃)
  ≡⟨⟩
    PairU v₁ (PairU v₂ v₃ )
  ∎ 


inv-assoc-assoc-u≡u :  ∀ { l s r : RE } { loc₁ loc₂ : ℕ }
                    →  { u : U ( ( l ● s ` loc₁ ) ● r ` loc₂)}  
                     ---------------------------------------------
                    → inv-assoc ( assoc u ) ≡ u
inv-assoc-assoc-u≡u {l} {s} {r} {loc₁} {loc₂} {PairU (PairU  v₁ v₂) v₃ } =
  begin
    inv-assoc (assoc (PairU (PairU  v₁ v₂) v₃))
  ≡⟨⟩
    inv-assoc (PairU v₁ (PairU v₂ v₃))
  ≡⟨⟩
    PairU (PairU  v₁ v₂) v₃
  ∎ 


-- pdinstance-assoc and its sub functions END 
------------------------------------------------------------------------------------

import cgp.Rewriting  -- import ∷ʳ-++ rewriting rule

---------------------------------------------------------------------------------------------------------
-- A helper function  for pdUMany-aux then pdUMany 
-- compose-pdi-with : copmose a PDInstance with the "downstream" PDinstance* injection and soundness evidence


compose-pdi-with : ∀ { r d : RE } { pref : List Char } { c : Char }
                   → ( d→r-inj : U d → U r )
                   → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r-inj v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
                   → PDInstance d c
                   → PDInstance* r (pref ∷ʳ c )
compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d-r (pdinstance {p} {d} {c} p→d s-ev-p-d) = 
                 pdinstance* {p} {r} {pref ∷ʳ c } ( d→r ∘ p→d ) 
                                       (
                                        λ u →
                                          begin
                                            proj₁ (flat (d→r (p→d u)))
                                          ≡⟨ s-ev-d-r (p→d u) ⟩
                                            pref ++ proj₁ (flat (p→d u))
                                          ≡⟨ cong ( pref ++_ ) (s-ev-p-d u) ⟩
                                            pref ++ ( c ∷ Product.proj₁ (flat u) )
                                          -- ≡⟨ sym ( ∷ʳ-++ pref c (Product.proj₁ (flat u)) ) ⟩  -- this becomes a refl, thanks to the REWRITE ∷ʳ-++  pragma 
                                          ≡⟨ refl ⟩                                         
                                            pref ∷ʳ c ++ proj₁ (flat u) 
                                          ∎
                                        )
                                        


```

```agda
{-
concatmap-pdinstance-snd-[]≡[] : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
  → concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} [] ≡ []
concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c} = {!!}   
-}  


concatmap-pdinstance-snd-[]≡[] : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char }
    → concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} [] ≡ []
concatmap-pdinstance-snd-[]≡[] {l} {r} {ε∈l} {loc} {c} = sub e-flat-es 
  where
    es : List (U l)
    es = mkAllEmptyU {l} ε∈l
    flat-[]-es : All (Flat-[] l) es
    flat-[]-es = mkAllEmptyU-sound {l} ε∈l
    e-flat-es :  List ( ∃[ e ] (Flat-[] l e) )
    e-flat-es = zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es
    sub : (xs :  List ( ∃[ e ] (Flat-[] l e) )) → concatMap (λ x → pdinstance-snd {l} {r} {loc} {c} x []) xs ≡ []
    sub [] = refl
    sub (x ∷ xs) = sub xs



```
