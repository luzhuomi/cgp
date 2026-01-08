This module contains the implementation of regular expression parsing algorithm using Antimriov's original partial derivative operation without applying distributivity law.

```agda
{-# OPTIONS --rewriting #-}
module cgp.lne.PartialDerivative where

import cgp.RE as RE
open RE using (RE ; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ;  ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? ; first ;  ε∉r→¬first-r≡[]  )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ; flat-Uε≡[] ;  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star ; inv-leftU ; inv-rightU ; inv-pairU ; inv-listU;  unListU ; listU∘unListU ; LeftU≢RightU ; RightU≢LeftU ; proj₁∘LeftU≢proj₁∘RightU  )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ;
  pdinstance-left; pdinstance-right ;
  pdinstance-star ; mkinjList
  ) 


import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; Flat-[] ; flat-[] ;  mkAllEmptyU≢[] )


import cgp.Utils as Utils
open Utils using (any-right-concat; any-left-concat ; all-concat ;  ∷-inj ; ¬∷≡[] ; inv-map-[] ; inv-concatMap-map-f-[]  )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_  )

import Data.List.Properties
open Data.List.Properties using ( ++-assoc  ; ++-identityʳ ; ++-identityˡ ; {-  unfold-reverse ; -} ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ )


import Data.List.Relation.Unary.Any.Properties
open Data.List.Relation.Unary.Any.Properties using ( ¬Any[] )

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

```

### Definition 15: Partial Derivative

We recall the partial derivative operaiton from [3]

pd(ϕ, ℓ) = {}   pd(ε, ℓ) = {}    pd(ℓ, ℓ) = {ε}    pd(ℓ', ℓ) = {}

pd(r₁ ● r₂ , ℓ ) = { r₁' ● r₂ ∣ r₁' ∈ pd( r₁ , ℓ ) } ∪ {  r₂' ∣ ε ∈ r₁ ∧ r₂' ∈ pd( r₂ , ℓ ) }

pd(r₁ + r₂ , ℓ ) = pd( r₁ , ℓ ) ∪ pd( r₂ , ℓ  )

pd(r* , ℓ ) = pd( r' ● r* ∣ r' ∈ pd( r , ℓ ) }

```agda

pd[_,_] : RE →  Char → List RE
pdConcat : ( l :  RE )  → ( r :  RE ) → ( ε∈l : ε∈ l ) → ( loc : ℕ ) → ( c : Char)  → List RE

pd[ ε , c ]    = []
pd[ $ c ` loc  , c' ] with c Char.≟ c'
...                      | yes refl = [ ε ]
...                      | no  _    = []
pd[ l ● r ` loc , c ] with ε∈? l
...                      | yes ε∈l =  pdConcat  l r ε∈l loc c
...                      | no ¬ε∈l =  List.map (λ l' → l' ● r ` loc ) pd[ l , c ]
pd[ l + r ` loc , c ]               = pd[ l , c ] ++ pd[ r , c ]
pd[ r * nε ` loc , c ]              = List.map (λ r' → r' ● ( r * nε ` loc ) ` loc ) pd[ r , c ]
{-# TERMINATING #-}
pdConcat ε  r  ε∈ε loc c  = pd[ r  , c ]
pdConcat (l * ε∉l ` loc₂ ) r ε∈*             loc c = (List.map (λ l' → l' ● r ` loc ) pd[ l * ε∉l ` loc₂ , c ]) ++ pd[ r , c ]
pdConcat (l ● s ` loc₂ )   r (ε∈ ε∈l ● ε∈s)  loc c = pd[ l ● ( s ● r  ` loc ) ` loc₂ , c ]
pdConcat (l + s ` loc₂ )   r (ε∈l+s)         loc c = (List.map (λ p → p ● r ` loc ) pd[ l + s ` loc₂ , c ]) ++ pd[ r , c ]

```


### Definition 16: Partial derivatives with coercion functions 

```agda
-- partial derivative (descendant?) relation and coercion function
-- the result type of pdU
-- moved to PDInstance.lagda.md
{-
data PDInstance : ∀ ( r : RE ) ( c : Char ) → Set where
  pdinstance : ∀ { p r : RE }     -- ^ partial derivative p and input re r 
                  { c : Char }     -- ^ the letter 
               → ( inj : U p → U r ) -- ^ the injection function 
               → ( ∀ ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) ) -- ^ soundness evidence of the inject function
           {-  -- soundness evidence can be embeded, because it is by construction, the result of the injection must be a valid parse tree, regardless which instance of PD we are at. 
               -- completness evidence can't be embeded here, b/c each PDInstance is just an instance of partial derivative.
               -- consider, r = c . ( a + b ); pd[ r , 'c'] = [ ε . a , ε . b ], if we are given u = (c , b) but we are at p = ε . a , we can never construct u given.
               -- completeness has to be defined over the entire list of PDInstances,
               -- it has to be a search! 
           -}               
          --------------------------------------------------------------------------------
               → PDInstance r c -- do we need to record the char c and the loc history?

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
-}
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



-- pdinstance-dist and its sub functions end
------------------------------------------------------------------------------------

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


------------------------------------------------------------------------------------
-- pdU[_,_] and pdUConcat



pdU[_,_] :  ( r : RE ) → ( c :  Char ) →  List (PDInstance r c)
pdUConcat : ( l r : RE ) → ( ε∈l : ε∈ l ) → ( loc : ℕ ) → ( c : Char ) → List (PDInstance (l ● r ` loc ) c)

pdU[ ε , c ] = []
pdU[ $ c ` loc  , c' ] with c Char.≟ c'
...                       | yes refl = [  pdinstance {ε} {$ c ` loc} {c}
                                                 (λ u → LetterU {loc} c)
                                                 (λ EmptyU →                 -- ^ soundness ev
                                                   begin
                                                     [ c ]
                                                    ≡⟨⟩
                                                     c ∷ []
                                                    ≡⟨ cong ( λ x → ( c ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                                                     c ∷ (proj₁ (flat EmptyU))
                                                    ∎)
                                                 ] 
...                       | no _     = []
           
pdU[ l + r ` loc , c ] =
  ( List.map pdinstance-left pdU[ l , c ] )
    ++
  ( List.map pdinstance-right pdU[ r , c ])
pdU[ r * nε ` loc , c ] =
  List.map pdinstance-star  pdU[ r , c ]

pdU[ l ● r ` loc , c ] with ε∈? l
...                       | no ¬ε∈l = List.map pdinstance-fst  pdU[ l , c ]
...                       | yes ε∈l = pdUConcat l r ε∈l loc c 

{-# TERMINATING #-}
pdUConcat ε r ε∈ε loc c                   = concatmap-pdinstance-snd {ε}              {r} {ε∈ε}   {loc} {c} pdU[ r , c ]
pdUConcat (l * ε∉l ` loc₁)  r ε∈*   loc₂ c =
  ( List.map pdinstance-fst pdU[ (l * ε∉l ` loc₁) , c ] )
  ++
  concatmap-pdinstance-snd {l * ε∉l ` loc₁} {r} {ε∈*}   {loc₂} {c} pdU[ r , c ]
pdUConcat (l ● s ` loc₁)    r ε∈l●s loc₂ c = List.map pdinstance-assoc pdU[ ( l ● ( s ● r ` loc₂ ) ` loc₁ ) , c ]
--  ( List.map pdinstance-fst pdU[ (l ● s ` loc₁) , c ] )
--  ++
--   concatmap-pdinstance-snd {l ● s ` loc₁}   {r} {ε∈l●s} {loc₂} {c} pdU[ r , c ]
pdUConcat (l + s ` loc₁)    r ε∈l+s loc₂ c =
  ( List.map pdinstance-fst pdU[ (l + s ` loc₁) , c ] )
  ++
   concatmap-pdinstance-snd {l + s ` loc₁}   {r} {ε∈l+s} {loc₂} {c} pdU[ r , c ]
```




### Lemma 17: pdU[_,_] is sound.

Let r be a non problematic regular expression.
Let c be a letter.
Let p be a partial derivative of r w.r.t c, i.e. p ∈ pd[r , c]
Let f be the injection function from parse tree of p to parse tree of r.
Let u be a parse tree of p, then |(f u)| = c ∷ | u |, where (f u) is a parse tree of r.
( in agda terms,  proj₁ (flat {r} (f u)) ≡ c ∷ (proj₁ (flat {p} u)) ). 


The proof is given as part of the PDInstance being computed. 

### Lemma 18(a): pdU[_,_] is complete. (Too weak, not working)


Let r be a non problematic regular expression.
Let c be a letter.
Let p be a partial derivative of r w.r.t c, i.e. p ∈ pd[r , c]               (**)
Let u be a parse tree of r such that (flat u) = c ∷ w for some word w.       (**) 
  (in agda term, ∃ [ w ] ( proj₁ (flat {r} u) ≡ c ∷ w ) )
such that w ∈ ⟦ p ⟧ 
Then there exist a parse tree v of p and a coercion function f such that
unflatten {p} w∈ ⟦ p ⟧ ) = v and f v ≡ u.

The above lemma is too weak because of (**) being too strong; we strengthened the lemma but moving the premise of p and w ∈ ⟦p⟧ into the conclusion part (w/ existentially quantification )

We rephrase the conclusion of Lemma 18(a) in the following reconstructibilty definition. 

### Definition 18 (Reconstructability):
Let r be a non problematic regular expression.
Let c be a character.
Let u be a parse tree of r.
Let pdi be a partial derivative (instance) of r w.r.t c,
such that pdi = { p , inj , sound-ev }
  where
    1. p is the partial derivative instance of p/c;
    2. inj is the injection function from parse tree of p back to parse tree of r;
    3. sound-ev is the soundness evidence pdi
Then we say pdi is u-reconstructable w.r.t c iff there exists a word w ∈ ⟦p⟧ such that inj (unflat w∈p) ≡ u.


```agda


data Recons : { r : RE } { c : Char } → ( u : U r ) → ( PDInstance r c )  → Set where
  recons : ∀ { p r : RE } { c : Char } { w : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → (u : U r)
    → ∃[ w∈⟦p⟧ ] ( (inj (unflat {p} {w}  w∈⟦p⟧)) ≡ u )    -- the completeness property.
    → Recons {r} {c} u (pdinstance {p} {r} {c} inj sound-ev) -- <- the input PDI obj

```
### Lemma 19: pdU[_,_] is complete. 

Let r be a non problematic regular expression.
Let c be a letter.
Let u be a parse tree of r such that (flat u) = c ∷ w for some word w.      
Then there exists a partial derivative instance, pdi ∈ pdU[r,c] , such that
pdi is u-reconstruable w.r.t c.



To prove Lemma 19, we need to prove some sub lemmas. 


#### Sub Lemmas 19.1 - 19.7 Reconstructability is preserved inductively over pdinstance operations. 


```agda
-----------------------------------------------------------------------------------------
-- Sub Lemmas 19.1 - 19.7 BEGIN
----------------------------------------------------------------------------------------


any-recons-left : ∀ { l r : RE } { loc : ℕ } {c : Char } { w : List Char} { u : U l }
    → ( pdis : List (PDInstance l c) )
    → Any (Recons {l} {c} u) pdis 
    ---------------------------------------------------------
    → Any (Recons {l + r ` loc } {c} (LeftU u)) (List.map pdinstance-left pdis)
any-recons-left ( pdi ∷ pdis' ) (here {pd} {pds} (recons {p} {l} {c} {w} {inj} {sound-ev} u ( w∈⟦p⟧ ,  inj∘unflat≡u ))) = here (recons (LeftU u) ( w∈⟦p⟧ ,  cong LeftU  inj∘unflat≡u )) 
any-recons-left {l} {r} {loc} {c} {w} {u} ( pdi ∷ pdis' ) (there {pd} {pds} pxs) = there (any-recons-left {l} {r} {loc} {c} {w} {u} pdis' pxs) 



any-recons-right : ∀ { l r : RE } { loc : ℕ } {c : Char } { w : List Char} { u : U r }
    → ( pdis : List (PDInstance r c) )
    → Any (Recons {r} {c} u) pdis 
    ---------------------------------------------------------
    → Any (Recons {l + r ` loc } {c} (RightU u)) (List.map pdinstance-right pdis)
any-recons-right ( pdi ∷ pdis' ) (here {pd} {pds} (recons {p} {r} {c} {w} {inj} {sound-ev} u ( w∈⟦p⟧ ,  inj∘unflat≡u ))) = here (recons (RightU u) ( w∈⟦p⟧ , cong RightU  inj∘unflat≡u)) 
any-recons-right {l} {r} {loc} {c} {w} {u} ( pdi ∷ pdis' ) (there {pd} {pds} pxs) = there (any-recons-right {l} {r} {loc} {c} {w} {u} pdis' pxs) 


any-recons-fst : ∀ { l r : RE } { loc : ℕ } { c : Char } { w : List Char } { u : U l } { v : U r }
    → ( pdis : List (PDInstance l c) )
    → Any (Recons {l} {c} u) pdis
    -----------------------------------------------------------
    → Any (Recons {l ● r ` loc } {c} (PairU u v)) (List.map pdinstance-fst pdis)
any-recons-fst {l} {r} {loc} {c} {w} {u} {v} ( pdi ∷ pdis' ) (here {pd} {pds} (recons {p} {l} {c} {w₁} {inj} {sound-ev} u' ( w₁∈⟦p⟧ ,  inj∘unflat≡u ))) = 
  here (recons (PairU u' v) ((w₁∈⟦p⟧ ● proj₂ (flat v) ⧺ refl) , Eq.cong₂ (λ x y → PairU x y) inj∘unflat≡u (unflat∘proj₂∘flat {r} {v}) ))
any-recons-fst {l} {r} {loc} {c} {w} {u} {v} ( pdi ∷ pdis' ) (there {pd} {pds} pxs)  = there (any-recons-fst {l} {r} {loc} {c} {w} {u} {v} pdis' pxs) 


any-recons-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char } { w : List Char } { u : U r } { us : List (U r) }
    → ( pdis : List (PDInstance r c ) )
    → Any (Recons {r} {c} u) pdis
    ------------------------------------------------------------
    → Any (Recons { r * ε∉r ` loc } {c} (ListU (u ∷ us))) (List.map pdinstance-star pdis)
any-recons-star {r} {ε∉r} {loc} {c} {w} {u} {us} ( pdi ∷ pdis' ) (here {pd} {pds} (recons {p} {r} {c} {w₁} {inj} {sound-ev} _ ( w₁∈⟦p⟧ , inj∘unflatw₁∈p≡u ))) =
  let
    injList = mkinjList {p} {r} {ε∉r} {loc} inj
  in here (recons {- { p ● (r * ε∉r ` loc) ` loc } {r * ε∉r ` loc} {c} {w} {injList} {_} -} -- ignoring the implict para help to simplify to use refl, just like any-recons-fst
                  (ListU (u ∷ us)) ((w₁∈⟦p⟧ ● proj₂ (flat (ListU {r} {ε∉r} {loc} us)) ⧺ refl) , (
    begin
      mkinjList inj (PairU (unflat w₁∈⟦p⟧) (unflat (Product.proj₂ (flat (ListU us)))))
    ≡⟨ cong (λ x → mkinjList inj (PairU (unflat w₁∈⟦p⟧) x )) (unflat∘proj₂∘flat {r * ε∉r ` loc} {ListU us}) ⟩
      mkinjList inj (PairU (unflat w₁∈⟦p⟧) (ListU us))
    ≡⟨⟩
      ListU (inj (unflat w₁∈⟦p⟧) ∷ us)
    ≡⟨ cong ( λ x → ListU (x ∷ us) )  inj∘unflatw₁∈p≡u ⟩ 
      ListU (u ∷ us)
    ∎) )) 
any-recons-star {r} {ε∉r} {loc} {c} {w} {u} {us} ( pdi ∷ pdis' ) (there {pd} {pds} pxs) = there (any-recons-star {r} {ε∉r} {loc} {c} {w} {u} {us} pdis' pxs) 




any-recons-pdinstance-snd : ∀ { l r : RE } { loc : ℕ } { c : Char } { w : List Char } { e : U l } { v : U r }
  → ( flat-[]-e : Flat-[] l e )
  → ( pdis : List (PDInstance r c) )
  → Any (Recons {r} {c} v) pdis  
  -------------------------------------------------------------------------------------------------------------------
  → Any (Recons {l ● r ` loc } {c} (PairU e v)) (pdinstance-snd {l} {r} {loc} {c} ( e , flat-[]-e )  pdis )
any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v} (flat-[] _ proj₁-flat-e≡[]) [] any-recons-v = Nullary.contradiction any-recons-v ¬Any[]
any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v} (flat-[] _ proj₁-flat-e≡[]) (pdi ∷ pdis) (here (recons v ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡v ))) = here (recons (PairU e v) ( w∈⟦p⟧ ,  cong (λ x → PairU e x ) inj-unflat-w∈⟦p⟧≡v ))
any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v} flat-[]-e@(flat-[] _ proj₁-flat-e≡[]) (pdi ∷ pdis) (there pxs) = -- there (any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v} (flat-[] e proj₁-flat-e≡[]) pdis pxs) 
  there next
  where
    next : Any (Recons {l ● r ` loc } {c} (PairU e v)) (pdinstance-snd {l} {r} {loc} {c} ( e , flat-[]-e )  pdis )
    next = any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v} (flat-[] e proj₁-flat-e≡[]) pdis pxs


any-recons-concatmap-pdinstance-snd : ∀ { l r : RE } { ε∈l : ε∈ l} { loc : ℕ } { c : Char } { w : List Char } { u : U l } { v : U r }
    → ( proj1-flat-u≡[] : proj₁ (flat u) ≡ [] )
    → ( pdis : List (PDInstance r c) ) 
    → Any (Recons {r} {c} v) pdis
    ----------------------------------------------------------- 
    -- → Any (Recons {l ● r ` loc } {c} (PairU u v)) (concatMap (pdinstance-snd {l} {r} {ε∈l} {loc} {c})  pdis) -- inlined to make it easier to prove
    → Any (Recons {l ● r ` loc } {c} (PairU u v)) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  pdis) 
any-recons-concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdis any-recons-v-pdis = any-Snd (mkAllEmptyU ε∈l) (mkAllEmptyU-sound ε∈l)  u∈mkAllEmptU-ε∈l pdis any-recons-v-pdis  
  where

    u∈mkAllEmptU-ε∈l : Any ( u ≡_ ) (mkAllEmptyU {l} ε∈l)
    u∈mkAllEmptU-ε∈l = mkAllEmptyU-complete ε∈l u (flat-[] u proj1-flat-u≡[])
    any-Snd :  (es : List (U l))
      → (flat-[]-es : All (Flat-[] l) es )
      → Any ( u ≡_ ) es
      → ( pdis : List (PDInstance r c) )
      → Any (Recons {r} {c} v) pdis
      --------------------------------------------------------------------------------------------------------
      -- → Any (Recons {l ● r ` loc } {c} (PairU u v)) (concatmap-pdinstance-snd {l} {r} {ε∈l} {loc} {c}  pdis)
      → Any (Recons {l ● r ` loc } {c} (PairU u v)) (concatMap (λ x →  pdinstance-snd {l} {r} {loc} {c} x pdis) (zip-es-flat-[]-es  {l} {ε∈l} es flat-[]-es))
    any-Snd []        _                         u∈[]        _    _                 = Nullary.contradiction u∈[] ¬Any[]
    any-Snd (e ∷ es) (flat-[]-e ∷ flat-[]-es) (there u∈es) pdis any-recons-v-pdis = any-right-concat (any-Snd es flat-[]-es u∈es pdis any-recons-v-pdis)
    -- the first parse tree is found, we need to search for the 2nd parse tree 
    any-Snd (e ∷ es) (flat-[]-e ∷ flat-[]-es) (here refl)  pdis any-recons-v-pdis  = any-left-concat any-recons-pair-e-v-pdinstance-snd
      where
        any-recons-pair-e-v-pdinstance-snd :  Any (Recons {l ● r ` loc } {c} (PairU e v)) (pdinstance-snd {l} {r} {loc} {c} ( e , flat-[]-e ) pdis )
        any-recons-pair-e-v-pdinstance-snd = any-recons-pdinstance-snd {l} {r} {loc} {c} {w} {e} {v}  flat-[]-e pdis  any-recons-v-pdis


-- TODO: do we need {w} in all these any-recons lemmas? 
any-recons-assoc : ∀ { l t s : RE } { loc₁ loc₂ : ℕ } { c : Char } { w : List Char } {u₁ : U l } {u₂ : U t } { v : U s }
    → ( pdis :  List (PDInstance  ( l ● ( t ● s ` loc₂) ` loc₁ )  c ) )
    → Any (Recons { l ● ( t ● s ` loc₂) ` loc₁ } {c} ( PairU u₁ (PairU u₂ v)) ) pdis
    → Any (Recons { ( l ● t ` loc₁) ● s ` loc₂ } {c} ( PairU (PairU u₁ u₂) v) ) (List.map pdinstance-assoc pdis)
any-recons-assoc {l} {t} {s} {loc₁} {loc₂} {c} {w} {u₁} {u₂} {v} [] any-recons-pdis = Nullary.contradiction any-recons-pdis ¬Any[]
any-recons-assoc {l} {t} {s} {loc₁} {loc₂} {c} {w} {u₁} {u₂} {v} (pdi ∷ pdis) (there pxs) = there (any-recons-assoc {l} {t} {s} {loc₁} {loc₂} {c} {w} {u₁} {u₂} {v} pdis pxs)
any-recons-assoc {l} {t} {s} {loc₁} {loc₂} {c} {w} {u₁} {u₂} {v} (pdi@(pdinstance inj sound-ev) ∷ pdis)
  (here (recons pair-u₁-pair-u₂v ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡PairU-u₁-PairU-u₂-v ) ))
        = here (recons (PairU (PairU u₁ u₂) v) ( w∈⟦p⟧ , complete-evidence))
        where
          complete-evidence : mkinjAssoc inj (unflat w∈⟦p⟧) ≡ PairU (PairU u₁ u₂) v
          complete-evidence =
            begin
              mkinjAssoc inj (unflat w∈⟦p⟧)
            ≡⟨⟩
              inv-assoc (inj (unflat w∈⟦p⟧))
            ≡⟨ cong (λ x → inv-assoc x ) inj-unflat-w∈⟦p⟧≡PairU-u₁-PairU-u₂-v ⟩
              PairU (PairU u₁ u₂) v             
            ∎

-----------------------------------------------------------------------------------------
-- Sub Lemmas 19.1 - 19.7 END
----------------------------------------------------------------------------------------
```

#### Main proof for Lemma 19 

```agda



pdU-complete : ∀ { r : RE  } { c : Char } { w : List Char }
  → ( u : U r )  
  → ( proj₁ (flat {r} u) ≡ c ∷ w )
  → Any (Recons {r} {c} u) pdU[ r , c ]

pdUConcat-complete : ∀ { l s : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char } { w : List Char }
    → ( u : U l )
    → ( v : U s ) 
    → ( proj₁ (flat { l ● s ` loc } (PairU u v)) ≡ c ∷ w )
    → Any (Recons { l ● s ` loc } (PairU u v)) (pdUConcat l s ε∈l loc c)


-- intuition: give a parse tree u of r, flat u = c :: w;
-- we must be able to find a PDInstance record in pdU such that u can be reconstruct from w and c.



pdU-complete {ε}           {c}  {w} EmptyU = λ()
pdU-complete {$ c ` loc}   {c'} {w} (LetterU _) with c Char.≟ c'
...                                              | yes refl with w    
...                                                           |  []  = λ proj1-flat-u≡[] →  here (recons (LetterU c) (ε , refl))
pdU-complete {$ c ` loc}   {c'} {w} (LetterU c₂) | no  ¬c≡c'  = λ c∷[]≡c'w →  Nullary.contradiction (proj₁ (∷-inj c∷[]≡c'w)) ¬c≡c' 
pdU-complete {l + s ` loc} {c}  {w} (LeftU u)  proj1-flat-leftu≡cw =   any-left-concat ys
  where
    xs : Any (Recons {l} {c} u) pdU[ l , c ]
    xs =  pdU-complete {l} {c} u proj1-flat-leftu≡cw
    ys : Any (Recons { l + s ` loc} {c} (LeftU u)) (List.map pdinstance-left pdU[ l , c ])
    ys =  any-recons-left {l} {s} {loc} {c}  {w} {u} pdU[ l , c ]  xs      
pdU-complete {l + s ` loc} {c}  {w} (RightU u)  proj1-flat-rightu≡cw = any-right-concat ys
  where
    xs : Any (Recons {s} {c} u) pdU[ s , c ]
    xs =  pdU-complete {s} {c} u proj1-flat-rightu≡cw
    ys : Any (Recons { l + s ` loc} {c} (RightU u)) (List.map pdinstance-right pdU[ s , c ])
    ys =  any-recons-right {l} {s} {loc} {c}  {w} {u} pdU[ s , c ]  xs
-- pdU-complete {( l + r ` loc₁ ) ● s ` loc₂} {c} {w} (PairU u v) proj1-flat-pair-u-v≡cw = ? 

pdU-complete {l * ε∉l ` loc} {c} {w} (ListU (u ∷ us)) proj1-flat-u∷us≡cw  = bs
  where
    e1-e2-e3 : ∃[ xs ] ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs ) × ( proj₁ (flat (ListU us)) ≡ ys ) × ( xs ++ ys ≡ w ) 
    e1-e2-e3 = inv-flat-star {l} {ε∉l} {loc} {u} {us} {c} {w} proj1-flat-u∷us≡cw   
    xs               = proj₁ e1-e2-e3
    proj1-flat-u≡cxs = proj₁ (proj₂ (proj₂ e1-e2-e3))
    as : Any (Recons {l} {c} u) pdU[ l , c ] 
    as = pdU-complete {l} {c} {xs} u proj1-flat-u≡cxs 
    bs : Any (Recons {l * ε∉l ` loc } {c} (ListU (u ∷ us))) (List.map pdinstance-star pdU[ l , c ])
    bs = any-recons-star {l} {ε∉l} {loc} {c} {w} {u} {us} pdU[ l , c ] as 

pdU-complete {l ● s ` loc} {c}  {w} (PairU u v) proj1-flat-pair-u-v≡cw with ε∈? l   
pdU-complete {l ● s ` loc} {c}  {w} (PairU u v) proj1-flat-pair-u-v≡cw    | no ¬ε∈l  =  ys
  where
    e1-e2-e3 : ∃[ cs ] ∃[ cs' ] (proj₁ (flat u) ≡ c ∷ cs) × (proj₁ (flat v) ≡ cs') × ( cs ++ cs' ≡ w )
    e1-e2-e3 = inv-flat-pair-fst {l} {s} {¬ε∈l} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw
    e1 : ∃[ cs ] (proj₁ (flat u) ≡ c ∷ cs)
    e1 = ( proj₁ e1-e2-e3 , ( proj₁ ∘ proj₂ ∘ proj₂ ) e1-e2-e3 )
    xs : Any (Recons {l} {c} u) pdU[ l , c ]
    xs  = pdU-complete {l} {c} {proj₁ e1} u (proj₂ e1)   
    ys : Any (Recons { l ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l , c ])
    ys = any-recons-fst {l} {s} {loc} {c} {w} {u} {v} pdU[ l , c ] xs 
 
pdU-complete {l ● s ` loc} {c}  {w} (PairU u v) proj1-flat-pair-u-v≡cw       | yes ε∈l  =  pdUConcat-complete {l} {s} {ε∈l} {loc} {c} {w} u v  proj1-flat-pair-u-v≡cw

{-# TERMINATING #-}    
pdUConcat-complete {ε} {s} {ε∈ε} {loc} {c} {w} u@EmptyU v proj1-flat-pair-u-v≡cw  = prove e1-e2-e3 
  where
    e1-e2-e3 :  ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) 
              ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) ) 
    e1-e2-e3 = inv-flat-pair-snd {ε} {s} {ε∈ε} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw 
    prove : ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) )
           → Any (Recons {ε ● s ` loc} {c} (PairU u v)) (List.map (pdinstance-fst {ε} {s} {loc} {c}) pdU[ ε , c ] ++ (concatmap-pdinstance-snd {ε} {s} {ε∈ε} {loc} {c} pdU[ s , c ])) 
    prove (inj₂ ( xs , ys , proj1-flat-u≡cxs , proj1-flat-v≡ys , refl ) )  = any-left-concat bs
      where 
        as : Any (Recons {ε} {c} u) pdU[ ε , c ]
        as = pdU-complete {ε} {c} {xs} u proj1-flat-u≡cxs   
        bs : Any (Recons { ε ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ ε , c ])
        bs = any-recons-fst {ε} {s} {loc} {c} {w} {u} {v} pdU[ ε , c ] as 
    prove (inj₁ ( ys , proj1-flat-u≡[] , proj1-flat-v≡cys , refl ) ) = any-right-concat {PDInstance (ε ● s ` loc) c} {(Recons { ε ● s ` loc} {c} (PairU u v))} {(List.map pdinstance-fst pdU[ ε , c ])}  bs
      where 
        as : Any (Recons {s} {c} v) pdU[ s , c ] 
        as = pdU-complete {s} {c} {ys} v proj1-flat-v≡cys
        bs : Any (Recons { ε ● s ` loc} {c} (PairU u v)) (concatmap-pdinstance-snd {ε} {s} {ε∈ε} {loc} {c} pdU[ s , c ]) 
        bs = any-recons-concatmap-pdinstance-snd {ε} {s} {ε∈ε} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdU[ s , c ] as
pdUConcat-complete {l * ε∉l ` loc₁} {s} {ε∈*} {loc} {c} {w} u@(ListU us) v proj1-flat-pair-u-v≡cw  = prove e1-e2-e3 
  where
    e1-e2-e3 :  ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) 
              ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) ) 
    e1-e2-e3 = inv-flat-pair-snd {l * ε∉l ` loc₁} {s} {ε∈*} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw 
    prove : ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) )
           → Any (Recons {(l * ε∉l ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l * ε∉l ` loc₁ , c ] ++ (concatmap-pdinstance-snd  {l * ε∉l ` loc₁} {s} {ε∈*} {loc} {c}   pdU[ s , c ])) 
    prove (inj₂ ( xs , ys , proj1-flat-u≡cxs , proj1-flat-v≡ys , refl ) )  = any-left-concat bs
      where 
        as : Any (Recons {l * ε∉l ` loc₁} {c} u) pdU[ l * ε∉l ` loc₁ , c ]
        as = pdU-complete {l * ε∉l ` loc₁} {c} {xs} u proj1-flat-u≡cxs   
        bs : Any (Recons { (l * ε∉l ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l * ε∉l ` loc₁ , c ])
        bs = any-recons-fst {l * ε∉l ` loc₁} {s} {loc} {c} {w} {u} {v} pdU[ l * ε∉l ` loc₁ , c ] as 
    prove (inj₁ ( ys , proj1-flat-u≡[] , proj1-flat-v≡cys , refl ) ) = any-right-concat  {PDInstance ( (l * ε∉l ` loc₁) ● s ` loc) c} {(Recons { (l * ε∉l ` loc₁)  ● s ` loc} {c} (PairU u v))} {(List.map pdinstance-fst pdU[ l * ε∉l ` loc₁ , c ])}  bs
      where 
        as : Any (Recons {s} {c} v) pdU[ s , c ] 
        as = pdU-complete {s} {c} {ys} v proj1-flat-v≡cys
        bs : Any (Recons { (l * ε∉l ` loc₁) ● s ` loc} {c} (PairU u v)) (concatmap-pdinstance-snd {l * ε∉l ` loc₁} {s} {ε∈*} {loc} {c} pdU[ s , c ]) 
        bs = any-recons-concatmap-pdinstance-snd {l * ε∉l ` loc₁} {s} {ε∈*} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdU[ s , c ] as

pdUConcat-complete {l ● t ` loc₁} {s} {ε∈l●t} {loc} {c} {w} u@(PairU u₁ u₂) v proj1-flat-pair-u-v≡cw  = any-recons-assoc {l} {t} {s} {loc₁} {loc} {c} {w} {u₁} {u₂} {v}  pdU[ l ● (t ● s ` loc) ` loc₁ , c ] xs  
  where
    proj₁-flat-pair-u₁-pair-u₂-v≡cw : proj₁ (flat (PairU {l} { t ● s ` loc } {loc₁} u₁ (PairU u₂ v))) ≡ c ∷ w
    proj₁-flat-pair-u₁-pair-u₂-v≡cw with flat u₁   | flat u₂     | flat v
    ... | w₁ , w₁∈⟦l⟧ | w₂ , w₂∈⟦t⟧  | w₃ , w₃∈⟦s⟧ rewrite ++-assoc w₁ w₂ w₃ = proj1-flat-pair-u-v≡cw
    
    xs : Any (Recons {l ● (t ● s ` loc) ` loc₁} {c} (PairU u₁ (PairU u₂ v))) pdU[ l ● (t ● s ` loc) ` loc₁ , c ]
    xs  = pdU-complete {l ● (t ● s ` loc) ` loc₁} {c} {w}  (PairU u₁ (PairU u₂ v)) proj₁-flat-pair-u₁-pair-u₂-v≡cw 
  
pdUConcat-complete {l + t ` loc₁} {s} {ε∈l+t} {loc} {c} {w} u v proj1-flat-pair-u-v≡cw  = prove e1-e2-e3 
  where
    e1-e2-e3 :  ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) 
              ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) ) 
    e1-e2-e3 = inv-flat-pair-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw 
    prove : ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) )
           → Any (Recons {(l + t ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l + t ` loc₁ , c ] ++ (concatmap-pdinstance-snd  {l + t ` loc₁} {s} {ε∈l+t} {loc} {c}   pdU[ s , c ])) 
    prove (inj₂ ( xs , ys , proj1-flat-u≡cxs , proj1-flat-v≡ys , refl ) )  = any-left-concat bs
      where 
        as : Any (Recons {l + t ` loc₁} {c} u) pdU[ l + t ` loc₁ , c ]
        as = pdU-complete {l + t ` loc₁} {c} {xs} u proj1-flat-u≡cxs   
        bs : Any (Recons { (l + t ` loc₁) ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l + t ` loc₁ , c ])
        bs = any-recons-fst {l + t ` loc₁} {s} {loc} {c} {w} {u} {v} pdU[ l + t ` loc₁ , c ] as 
    prove (inj₁ ( ys , proj1-flat-u≡[] , proj1-flat-v≡cys , refl ) ) = any-right-concat  {PDInstance ( (l + t ` loc₁) ● s ` loc) c} {(Recons { (l + t ` loc₁)  ● s ` loc} {c} (PairU u v))} {(List.map pdinstance-fst pdU[ l + t ` loc₁ , c ])}  bs
      where 
        as : Any (Recons {s} {c} v) pdU[ s , c ] 
        as = pdU-complete {s} {c} {ys} v proj1-flat-v≡cys
        bs : Any (Recons { (l + t ` loc₁) ● s ` loc} {c} (PairU u v)) (concatmap-pdinstance-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {c} pdU[ s , c ]) 
        bs = any-recons-concatmap-pdinstance-snd {l + t ` loc₁} {s} {ε∈l+t} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdU[ s , c ] as


```

### Definition 20: Many steps Partial deriviatves with coercion functions `pdUMany[ r , w ]`


For the ease of establishing the completeness proof of `pdUMany[ r , w ]`, we introduce
a data type `PDInstance*` (similar to `PDInstance`) to record the partial derivative descendant, the prefix of `w` which has been consumed
so far, the injection function and the soundness evidence.

As we collect the prefix, we make use of the snoc `∷ʳ` operation (which is a short hand for `λ xs x → xs ++ [ x ]`).
And the prefix is used as the index of the dependent datatype. 


One caveat of Agda is that it *does not automatically register* that ` xs ∷ʳ x ++ ys ` is equivalent to ` xs ++ ( x ∷ ys ) `. It has to be explicitly
"taught" that the equivalence holds with the library function `∷ʳ-++`.

Though this can be done manually as and when Agda complains about that the equivalence is not met, it gets trickier as the rewriting take place "implicitly".

For example, it is hard to manually prove that, which is 

pdUMany-aux≡ : ∀ {r : RE} {pref : List Char} {c : Char} {cs : Char} { pdis : List ( PDInstance* r pref ) }
  → pdUMany-aux {r} {pref} (c ∷ cs) pdis ≡  pdUMany-aux {r} {pref ∷ʳ c} cs ( concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis )


Simply because Agda can't find unify the type of the left-hand-side of the equivalence relation of type `List (PDInstance* r ( pref ++ cs ∷ cs ))` with
the right hand side `List (PDInstance* r ( pref ∷ʳ c ++ cs ) )`.

Hence using a global automatic rewriting language extension help to address this issue.




```agda 

import cgp.Rewriting  -- import ∷ʳ-++ rewriting rule


-- the result type for pdUMany, a variant of PDInstance
-- moved to PDInstance.lagda.md

{-
data PDInstance* : ∀ ( r : RE ) ( pref : List Char ) → Set where
  pdinstance* : ∀ { p r : RE }            -- ^ partial derivative descendant p and input re r
                   { pref : List Char }   -- ^ the  prefix (has been consumed)
                → ( inj : U p → U r )     -- ^ the injection function
                → ( ∀ ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ pref ++ ( proj₁ (flat {p} u) )) ) -- ^ soundness evidence of the inject function
                ------------------------------------------------
                → PDInstance* r pref
-}                
```



```agda

-- helper function  for pdUMany-aux
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
-- helper functions for pdUMany-aux                   
-- advance-pdi*-with-c : advance a PDInstance* with a character c (by consuming it with pdU) and return a list of PDInstance*
advance-pdi*-with-c : ∀ { r : RE } { pref : List Char } { c : Char }
                     → PDInstance* r pref
                     → List (PDInstance* r (pref ∷ʳ c ))
advance-pdi*-with-c {r} {pref} {c} (pdinstance* {d} {r} {pref} d→r s-ev-d-r) =
  List.map (compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d-r ) pdU[ d , c ] 

pdUMany-aux :  ∀ { r : RE }
                 {pref : List Char}
               → (suff : List Char) 
               → List (PDInstance* r pref)
               → List (PDInstance* r (pref ++ suff ) )
pdUMany-aux {r} {pref} [] pdis rewrite (++-identityʳ pref) =  pdis
pdUMany-aux {r} {pref} (c ∷ cs) pdis {- rewrite (cong (λ x → List (PDInstance* r x )) (sym (∷ʳ-++ pref c cs))) -}  =  -- the rewrite is no longer needed thanks to the REWRITE ∷ʳ-++  pragma 
                pdUMany-aux {r} {pref ∷ʳ c} cs (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)

pdUMany[_,_] : ( r : RE ) → ( cs : List Char ) → List (PDInstance* r cs )
pdUMany[ r , cs ]         =
   pdUMany-aux {r} {[]} cs [  ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ]



```

### Lemma 21 : pdUMany[ r , w ] is sound

Let r  be a non problematic regular expresion.
Let w be a word.
Let p be a partial derivative descendant of r w.r.t c, i.e. p ∈ proj₁ (proj₂ pdUMany[ r , w ] )
Let f be the injection function from parse tree of o to parse tree of r.
Let u be a parse tree of p, then |(f u)| = w ++ | u |, where (f u) is a parse tree of r.


The proof is given as part of the PDInstance* being computed. 


### Definition 22 (Prefix Reconstructability):
Let r be a non problematic regular expression.
Let pref be a word,
LEt u be a parse tree of r.
Let pdi be a partial derivative descendant (instance) of r w.r.t. prefix pref,
such that pdi = { p , inj , sound-ev }
  where
    1. p is the partial derivative descendant instance of r / pref
    2. inj is the injection function from the parse tree of p back to the parse tree of r;
    3. sound-ev is the soundness evidence pdi
Then we say pdi is prefix reconstructable w.r.t. pre iff there exists a word w ∈⟦p⟧ such that inj (unflat w∈⟦p⟧) ≡ u.


```agda

data Recons* : { r : RE } { pref : List Char } → ( u : U r ) → ( PDInstance* r pref ) → Set where
  recons* : ∀ { p r : RE } { w : List Char } { pref : List Char } { inj : U p → U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ pref ++ ( proj₁ (flat {p} x) )) }
    → ( u : U r )
    → ∃[ w∈⟦p⟧ ] ( (inj (unflat {p} {w} w∈⟦p⟧)) ≡ u ) -- the completeness property.
    → Recons* {r} {pref} u (pdinstance* {p} {r} {pref} inj sound-ev) -- <- the input PDI obj
```



### Lemma 23 (Fixed) : pdUMany[ r , w ] is complete ** this should by pdUMany-aux-complete?

Let r be a non problematic regular expression.
Let w be a word.
Let u be a parse tree of r such that (flat u) = w.
Then there exist a partial derivative descendant instance, pdi ∈ pdUMany[r, w], such that
pdi is u-reconstructable w.r.t w. 


** note : prefix is the partial input which has been consumed by pdU so far when we just started with pdUMany[ r , suff ], the prefix `pref` is []
** for each step, we take the leading letter c from suffix `suffand snoc it into `pref`.


#### Sub Lemma 23.1 - 23.3  : Reconstructibility is preserved inductively over the pdinstance*'s (and pdinstance's) operations

```agda

-------------------------------------------------------------------------------------------------------------
-- Sub Lemma 23.1 - 23.3 BEGIN 
-------------------------------------------------------------------------------------------------------------



-- TODO the following lemma can be simplified. 
compose-pdi-with-can-recons* : ∀ { r d : RE } { pref : List Char } { c : Char } 
                   → ( u : U r ) 
                   → ( v : U d ) 
                   → ( d→r : U d → U r )
                   → ( d→r-v≡u : d→r v ≡ u)  -- can we derive this w/o passing it in from the call site?
                   → ( s-ev-d-r : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
                   → ( pdi : PDInstance d c)
                   → Recons {d} {c} v pdi  -- can we get rid of this premise? 
                   → Recons* {r} {pref ∷ʳ c} u (compose-pdi-with {r} {d} {pref} {c} d→r s-ev-d-r pdi)
compose-pdi-with-can-recons* {r} {d} {pref} {c}  u v d→r d→r-v≡u s-ev-d-r pdi@(pdinstance {p} {d} {c} p→d s-ev-p-d) (recons v ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡v ) )
  = recons*  u (w∈⟦p⟧ , (begin
    d→r (p→d (unflat w∈⟦p⟧)) ≡⟨ cong (λ x → (d→r x) ) inj-unflat-w∈⟦p⟧≡v ⟩
    d→r v ≡⟨ d→r-v≡u ⟩
    u 
                         ∎ )) 


-- any-advance-pdi*-with-c : search for reconstructable pd Instance from (List.map (compose-pdi-with {r} {d}  {pref} {c} d→r-inj s-ev-d-r ) pdU [d , c]
any-advance-pdi*-with-c : ∀ { r : RE } { pref : List Char } { c : Char } { cs : List Char }
    → ( u : U r )
    → ( proj₁ (flat {r} u) ≡ pref ++ ( c ∷ cs ))
    → ( pdi : PDInstance* r pref )
    → Recons* {r} {pref} u pdi
    → Any (Recons* {r} {pref ∷ʳ c} u) (advance-pdi*-with-c {r} {pref} {c} pdi)  
any-advance-pdi*-with-c {r} {pref} {c} {cs} u proj1-flat-u≡pref++ccs (pdinstance* {d} {r} {pref} d→r s-ev-d-r) (recons* {d} {r} {ccs} {pref} {d→r} {s-ev-d-r} u' ( ccs∈⟦d⟧ , d→r-unflat-ccs∈⟦d⟧≡u )) = find pdU[ d , c ] any-recons-pdu-d-c  
  where 
      proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++c∷cs : proj₁ (flat (d→r (unflat ccs∈⟦d⟧ ))) ≡ pref ++ c ∷ cs
      proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++c∷cs =
        begin
          proj₁ (flat (d→r (unflat ccs∈⟦d⟧ )))
        ≡⟨ cong (λ x → (proj₁ (flat x))) d→r-unflat-ccs∈⟦d⟧≡u ⟩
          proj₁ (flat u)
        ≡⟨ proj1-flat-u≡pref++ccs ⟩
          pref ++ c ∷ cs
        ∎
      proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++proj1-flat-unflat=ccs∈⟦d⟧ : proj₁ (flat (d→r (unflat ccs∈⟦d⟧))) ≡ pref ++ proj₁ (flat (unflat ccs∈⟦d⟧))
      proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++proj1-flat-unflat=ccs∈⟦d⟧ = s-ev-d-r (unflat ccs∈⟦d⟧)
      pref++proj-1-flat-unflat-ccs∈⟦d⟧≡pref++ccs : pref ++ proj₁ (flat (unflat ccs∈⟦d⟧)) ≡ pref ++ c ∷ cs
      pref++proj-1-flat-unflat-ccs∈⟦d⟧≡pref++ccs = Eq.trans (sym proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++proj1-flat-unflat=ccs∈⟦d⟧)  proj1-flat-d→r-unflat-ccs∈⟦d⟧≡pref++c∷cs
      proj1-flat-unflat-ccs∈⟦d⟧≡ccs : proj₁ (flat (unflat ccs∈⟦d⟧)) ≡ c ∷ cs 
      proj1-flat-unflat-ccs∈⟦d⟧≡ccs =  ++-cancelˡ pref  (proj₁ (flat (unflat ccs∈⟦d⟧))) (c ∷ cs) pref++proj-1-flat-unflat-ccs∈⟦d⟧≡pref++ccs

      -- : U d can be reconstructed based on pdU completenes 
      any-recons-pdu-d-c : Any (Recons {d} {c} (unflat ccs∈⟦d⟧)) pdU[ d , c ]
      any-recons-pdu-d-c =  pdU-complete {d} {c} {cs} (unflat ccs∈⟦d⟧) proj1-flat-unflat-ccs∈⟦d⟧≡ccs

      find : ∀ (pdis : List (PDInstance d c)) → Any (Recons {d} {c} (unflat ccs∈⟦d⟧)) pdis →  Any (Recons* u) (List.map (compose-pdi-with d→r s-ev-d-r) pdis)
      find  [] any-recons-pdu-d-c = Nullary.contradiction any-recons-pdu-d-c ¬Any[]
      find  (pdi₁ ∷ pdis₁) = 
        λ { ( here recons-d-c-pdi₁)  →               
              here (compose-pdi-with-can-recons* {r} {d} {pref} {c} u (unflat ccs∈⟦d⟧) d→r d→r-unflat-ccs∈⟦d⟧≡u  s-ev-d-r pdi₁ recons-d-c-pdi₁ )
          ; ( there pxs) →  there (find pdis₁ pxs) }      

-- any-recons*-concatmap-advance-with-c :
--   search for the reconstructable pd instance from (concatMap advance-pdi*-with-c pdis) given that there exist some pd instance in pdis reconstructing u
any-recons*-concatmap-advance-with-c : ∀ { r : RE } { pref : List Char } { c : Char } { cs : List Char }
    → ( u : U r )
    → ( proj₁ (flat {r} u) ≡ pref ++ ( c ∷ cs ))
    → ( pdis : List (PDInstance* r pref) )
    → Any (Recons* {r} {pref} u) pdis
    → Any (Recons* {r} {pref ∷ʳ  c} u) (concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis)
any-recons*-concatmap-advance-with-c {r} {pref} {c} {cs} u proj1-flatu≡pref++ccs ( pdi@(pdinstance* {d} {r} {_pref} d→r s-ev-d-r )  ∷ pdis) any-recons*u-pdis
  with any-recons*u-pdis
... | here px@(recons* u' ( w∈⟦d⟧ , d→r-unflat-w∈⟦d⟧≡u' )) = any-left-concat (any-advance-pdi*-with-c {r} {pref} {c} {cs} u proj1-flatu≡pref++ccs pdi px)
... | there pxs = any-right-concat (any-recons*-concatmap-advance-with-c {r} {pref} {c} {cs} u proj1-flatu≡pref++ccs pdis pxs )

-------------------------------------------------------------------------------------------------------------
-- Sub Lemma 23.1 - 23.3 END 
-------------------------------------------------------------------------------------------------------------

```

#### Sub Lemma 23.4 : Reconstructibility is preserved over pdUMany-aux. 

```agda


-- completeness for pdUMany-aux function 
pdUMany-aux-complete : ∀ { r : RE } { pref : List Char } { suff : List Char }
    → ( u : U r )
    → ( proj₁ (flat {r} u) ≡ pref ++ suff )
    → ( pdis : List (PDInstance* r pref) )
    → Any (Recons* {r} {pref} u) pdis
    → Any (Recons* {r} {pref ++ suff} u) (pdUMany-aux {r} {pref} suff pdis)
pdUMany-aux-complete {r} {pref} {[]}     u proj1-flat-u≡pref      (pdi ∷ pdis) (here (recons* u' ( w∈⟦p⟧ , inj∘unflatw∈⟦p⟧≡u ))) rewrite (++-identityʳ pref) = here (recons* u (w∈⟦p⟧ , inj∘unflatw∈⟦p⟧≡u))   -- base case
pdUMany-aux-complete {r} {pref} {[]}     u proj1-flat-u≡pref      (pdi ∷ pdis) (there pxs) rewrite (++-identityʳ pref) = there pxs   -- base case
pdUMany-aux-complete {r} {pref} {c ∷ cs} u proj1-flat-u≡pref++ccs (pdi ∷ pdis) any-recons*u-pdis  = ind-hyp -- fake-goal
  where

    any-recons*u-pdis' : Any (Recons* {r} {pref ∷ʳ c } u) ( concatMap (advance-pdi*-with-c {r} {pref} {c}) (pdi ∷ pdis) )
    any-recons*u-pdis' = 
      any-recons*-concatmap-advance-with-c {r} {pref} {c} {cs} u proj1-flat-u≡pref++ccs (pdi ∷ pdis) any-recons*u-pdis

    proj1-flat-u≡prefc++cs : proj₁ (flat u) ≡ pref ∷ʳ c ++ cs 
    proj1-flat-u≡prefc++cs = proj1-flat-u≡pref++ccs -- thanks to the REWRITE ∷ʳ-++ pragma
    {-
      begin
        proj₁ (flat u)
      ≡⟨ proj1-flat-u≡pref++ccs ⟩
        pref ++ c ∷ cs
      ≡⟨ sym (∷ʳ-++ pref c cs) ⟩
        pref ∷ʳ c ++ cs
      ∎
    -}
    

    ind-hyp : Any (Recons* {r} {pref ∷ʳ c ++  cs} u) (pdUMany-aux {r} {pref ∷ʳ c} cs ( concatMap (advance-pdi*-with-c {r} {pref} {c}) (pdi ∷ pdis) ))
    ind-hyp = pdUMany-aux-complete {r} {pref ∷ʳ c} {cs} u proj1-flat-u≡prefc++cs  (concatMap (advance-pdi*-with-c {r} {pref} {c}) (pdi ∷ pdis))  any-recons*u-pdis'

```

#### Main proof for Lemma 23 

```agda



-- main lemma   
pdUMany-complete : ∀ { r : RE }
  → ( u : U r )
  → Any (Recons* {r} {proj₁ (flat u)} u) pdUMany[ r , proj₁ (flat u) ]
pdUMany-complete {r} u =
  pdUMany-aux-complete {r} {[]} {proj₁ (flat u)} u refl 
    [  ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ]
    ( here (recons* {r} {r} {proj₁ (flat u)} {[]}  u (proj₂ (flat u),  unflat∘proj₂∘flat ) ) )



```

### Definition 24: ParseAll function

```agda

buildU : ∀ {r : RE } {w : List Char } → PDInstance* r w → List (U r)
buildU {r} {w} (pdinstance* {p} {r} p→r s-ev) with ε∈? p
...                            | yes ε∈p = List.map p→r (mkAllEmptyU ε∈p)
...                            | no _     = []


parseAll[_,_] : ( r : RE ) → ( w : List Char ) → List (U r)
parseAll[ r ,  cs ] =
  let pdinstances = pdUMany[ r , cs ]
  in List.concatMap buildU pdinstances 
```

### Example ParseAll
Let's consider an example

```agda
module ExampleParseAll where 
  a*●a* : RE
  a*●a* = ( ( $ 'a' ` 1 ) * ε∉$ ` 2 ) ● ( ( $ 'a' ` 3 ) * ε∉$ ` 4 ) ` 5

  ex_ts : List ( U a*●a* )
  ex_ts = parseAll[ a*●a* , [ 'a' ] ]



  ε+a●a+ε : RE 
  ε+a●a+ε = let a₁ = $ 'a' ` 1
                a₃ = $ 'a' ` 3 
            in (ε + a₁ ` 2) ● ( a₃ + ε ` 4) ` 5
  ex_vs :  List ( U ε+a●a+ε )
  ex_vs = parseAll[ ε+a●a+ε , [ 'a' ] ]


  a*+a*●a* : RE
  a*+a*●a* = ( ( ( $ 'a' ` 1 ) * ε∉$ ` 2 ) + ( ( $ 'a' ` 3 ) * ε∉$ ` 4) ` 5 ) ● ( ( $ 'a' ` 6 ) * ε∉$ ` 7 ) ` 8

  ex_us :  List ( U a*+a*●a* )
  ex_us = parseAll[ a*+a*●a* ,  'a' ∷ 'a' ∷ []  ]
  


  pdMany-aux : List RE → List Char → List RE
  pdMany-aux rs [] = rs
  pdMany-aux rs ( c ∷ cs ) =  pdMany-aux (concatMap (λ r → pd[ r , c ] ) rs) cs 

  pdMany[_,_] : RE → List Char → List RE
  pdMany[ r , w ] = pdMany-aux [ r ] w
  
  pds1  = pdMany[ a*+a*●a* ,  'a' ∷ 'a' ∷ []  ]
  pds1'  = pdMany[ a*+a*●a* ,  'a' ∷ []  ]

  a*+a*●a*+a* : RE
  a*+a*●a*+a* = ( ( ( $ 'a' ` 1 ) * ε∉$ ` 2 ) + ( ( $ 'a' ` 3 ) * ε∉$ ` 4) ` 5 ) ● ( ( ( $ 'a' ` 6 ) * ε∉$ ` 7 ) + ( ( $ 'a' ` 8 ) * ε∉$ ` 9 ) ` 10 ) ` 11 



  ex_ws :  List ( U a*+a*●a*+a* )
  ex_ws = parseAll[ a*+a*●a*+a* ,  'a' ∷ 'a' ∷ []  ]

  pds2  = pdMany[ a*+a*●a*+a* ,  'a' ∷ 'a' ∷ []  ]


  a*+a*●a*●a* : RE
  a*+a*●a*●a* = a*+a*●a* ● ( ( $ 'a' ` 10 ) * ε∉$ ` 11 ) ` 12
  
  ex_ys : List ( U a*+a*●a*●a* )
  ex_ys = parseAll[ a*+a*●a*●a* , 'a' ∷ 'a' ∷ [] ] 



  a*+a*●a*+a*●a* : RE
  a*+a*●a*+a*●a* = a*+a*●a*+a* ● ( ( $ 'a' ` 12 ) * ε∉$ ` 13 ) ` 14

  ex_zs : List ( U a*+a*●a*+a*●a* )
  ex_zs = parseAll[ a*+a*●a*+a*●a* , 'a' ∷ 'a' ∷ [] ]



```

ExampleParseAll.ex_ts

should yield

~~~~~~~
PairU (ListU (LetterU 'a' ∷ [])) (ListU []) ∷
PairU (ListU []) (ListU (LetterU 'a' ∷ [])) ∷ []
~~~~~~~


ExampleParseAll.ex_us

should yield

~~~~~~~
PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))) (ListU []) ∷
PairU (LeftU (ListU (LetterU 'a' ∷ [])))                (ListU (LetterU 'a' ∷ []))
∷
PairU (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))) (ListU [])
∷
PairU (RightU (ListU (LetterU 'a' ∷ [])))                (ListU (LetterU 'a' ∷ []))
∷
PairU (LeftU (ListU [])) (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])) ∷
PairU (RightU (ListU [])) (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷ []
~~~~~~~


ExampleParseAll.ex_ws

should yield

~~~~~~~

PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))) (LeftU (ListU []))
∷
PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))) (RightU (ListU []))
∷
PairU (LeftU (ListU (LetterU 'a' ∷ [])))               (LeftU (ListU (LetterU 'a' ∷ [])))
∷
PairU (LeftU (ListU (LetterU 'a' ∷ [])))               (RightU (ListU (LetterU 'a' ∷ [])))
∷
PairU (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))) (LeftU (ListU []))
∷
PairU (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))) (RightU (ListU []))
∷
PairU (RightU (ListU (LetterU 'a' ∷ [])))              (LeftU (ListU (LetterU 'a' ∷ [])))
∷
PairU (RightU (ListU (LetterU 'a' ∷ [])))              (RightU (ListU (LetterU 'a' ∷ [])))
∷
PairU (LeftU (ListU []))                               (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))
∷
PairU (LeftU (ListU []))                               (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))
∷
PairU (RightU (ListU []))                              (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))
∷
PairU (RightU (ListU []))                              (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))
∷ []


~~~~~~~


ExampleParseAll.ex_ys

should yield

~~~~~~~



PairU (PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))   (ListU []))                                 (ListU [])
∷
PairU (PairU (LeftU (ListU (LetterU 'a' ∷ [])))                 (ListU (LetterU 'a' ∷ [])))                 (ListU [])
∷
PairU (PairU (LeftU (ListU (LetterU 'a' ∷ [])))                 (ListU []))                                 (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))  (ListU []))                                 (ListU [])
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ [])))                (ListU (LetterU 'a' ∷ [])))                 (ListU [])
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ [])))                (ListU []))                                 (ListU (LetterU 'a' ∷ []))   
∷
PairU (PairU (LeftU (ListU []))                                 (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))   (ListU [])
∷
PairU (PairU (LeftU (ListU []))                                 (ListU (LetterU 'a' ∷ [])))                 (ListU (LetterU 'a' ∷ [])) 
∷
PairU (PairU (RightU (ListU []))                                (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))   (ListU [])
∷
PairU (PairU (RightU (ListU []))                                (ListU (LetterU 'a' ∷ [])))                 (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (LeftU (ListU []))                                 (ListU []))                                 (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU []))                                (ListU []))                                 (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷ []

~~~~~~~


ExampleParseAll.ex_zs

should yield

PairU (PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))       (LeftU (ListU [])))                   (ListU [])
∷
PairU (PairU (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))       (RightU (ListU [])))                  (ListU [])
∷
PairU (PairU (LeftU (ListU (LetterU 'a' ∷ [])))                     (LeftU (ListU (LetterU 'a' ∷ []))))   (ListU [])
∷
PairU (PairU (LeftU (ListU (LetterU 'a' ∷ [])))                     (RightU (ListU (LetterU 'a' ∷ []))))  (ListU [])
∷
PairU (PairU (LeftU (ListU (LetterU 'a' ∷ [])))                     (LeftU (ListU [])))                   (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (LeftU (ListU (LetterU 'a' ∷ [])))                     (RightU (ListU [])))                  (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))      (LeftU (ListU [])))                   (ListU [])
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ [])))      (RightU (ListU [])))                  (ListU [])
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ [])))                    (LeftU (ListU (LetterU 'a' ∷ []))))   (ListU [])
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ [])))                    (RightU (ListU (LetterU 'a' ∷ []))))  (ListU [])
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ [])))                    (LeftU (ListU [])))                   (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU (LetterU 'a' ∷ [])))                    (RightU (ListU [])))                  (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (LeftU (ListU []))                                     (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))))    (ListU [])
∷
PairU (PairU (LeftU (ListU []))                                     (LeftU (ListU (LetterU 'a' ∷ []))))                  (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (LeftU (ListU []))                                     (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))))   (ListU [])
∷
PairU (PairU (LeftU (ListU []))                                     (RightU (ListU (LetterU 'a' ∷ []))))                 (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (LeftU (ListU []))                                     (LeftU (ListU [])))                                  (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷
PairU (PairU (LeftU (ListU []))                                     (RightU (ListU [])))                                 (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU []))                                    (LeftU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))))    (ListU [])
∷
PairU (PairU (RightU (ListU []))                                    (LeftU (ListU (LetterU 'a' ∷ []))))                  (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU []))                                    (RightU (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))))   (ListU [])
∷
PairU (PairU (RightU (ListU []))                                    (RightU (ListU (LetterU 'a' ∷ []))))                 (ListU (LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU []))                                    (LeftU (ListU [])))                                  (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷
PairU (PairU (RightU (ListU []))                                    (RightU (ListU [])))                                 (ListU (LetterU 'a' ∷ LetterU 'a' ∷ []))
∷ []




### Lemma 25 : buildU is sound
Let r be a non problemantic regular expression.
Let w be a word.
Let pdi be a partial instance* of r w.r.t w.
Then for all u ∈ buildU {r} {w} pdi, flat u ≡ w.

```agda
buildU-sound : ∀ { r : RE } {w : List Char }
  → ( pdi : PDInstance* r w )
  → All (λ u → proj₁ (flat {r} u) ≡ w ) (buildU pdi)
buildU-sound {r} {w} (pdinstance* {p} {r} {pref} p→r s-ev) with ε∈? p
... | yes ε∈p = prove-all (mkAllEmptyU ε∈p) (mkAllEmptyU-sound ε∈p)
  where 
    prove-all : ( vs : List (U p) ) → All (Flat-[] p) vs → All (λ u → proj₁ (flat {r} u) ≡ w ) (List.map p→r vs)
    prove-all [] [] = [] 
    prove-all ( e ∷ es ) ( (flat-[] {p} e proj1-flat-e≡[]) ∷ pxs ) =
      (begin
        proj₁ (flat (p→r e))
      ≡⟨ s-ev e ⟩
        w ++ proj₁ (flat e)
      ≡⟨ cong ( w ++_ ) proj1-flat-e≡[] ⟩
        w ++ []
      ≡⟨ ++-identityʳ w ⟩
        w
      ∎) ∷ prove-all es pxs 
... | no  _    = [] 


```

### Theorem 26 : ParseAll is sound 

Let r be a non problematic regular expression.
Let w be a word.
Then for all u ∈ parseAll[ r , w ] , | u | ≡ w.


```agda
parseAll-sound : ∀ {r : RE } { w : List Char }
  → All ( λ u → proj₁ (flat u) ≡ w ) parseAll[ r , w ]
parseAll-sound {r} {w} = prove-all pdUMany[ r , w ]
  where
    prove-all : ( pdis : List (PDInstance* r w) ) → All ( λ u → proj₁ (flat u) ≡ w ) (concatMap buildU pdis)
    prove-all [] = []
    prove-all ( pdi ∷ pdis ) with buildU pdi | buildU-sound pdi
    ... | []       | []         = prove-all pdis
    ... | (v ∷ vs) | (pv ∷ pvs) = all-concat (pv ∷ pvs) (prove-all pdis)  

```


### Lemma 27 : buildU is complete

Let r be a non problematic regular expression.
Let u be a parse tree of r.
Let pdi be a partial derivative descendant instance of r w.r.t to |u| such that 
pdi is u-reconstructable. 
Then u ∈ buildU pdi

```agda
buildU-complete : ∀ { r : RE } 
  → ( u : U r )
  → ( pdi : PDInstance* r (proj₁ (flat u)) )
  → Recons* u pdi
  → Any ( _≡_ u ) (buildU pdi)
buildU-complete {r} u pdi@(pdinstance* {p} {r} {proj1-flat-u} inj s-ev-p-r) (recons* {p} {r} {w} {proj1-flat-u} {inj} {s-ev-p-r} u' ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡u) ) = u∈buildU-pdi
  where
    {- Manual proof to show w ≡ []
      The main idea of the above proof to show w ≡ [] 
        1. From soundness of p→r-inj 
           we have 
             s-ev-p-r (unflat w∈⟦p⟧) : proj₁ (flat (inj (unflat w∈⟦p⟧))) ≡ proj₁ (flat u) ++ proj₁ (flat (unflat w∈⟦p⟧))    (1) 
        2. From completeness of p→r inj
          we have
            inj-unflat-w∈⟦p⟧≡u : inj (unflat w∈⟦p⟧) ≡ u   (2)

        3. substituting (2) into (1)  :
          
          proj₁ (flat u) ≡  proj₁ (flat u) ++ proj₁ (flat (unflat w∈⟦p⟧))     (3) 

        4. applying ++-identityʳ to the LHS of (3)
        
          proj₁ (flat u) ++ []  ≡  proj₁ (flat u) ++ proj₁ (flat (unflat w∈⟦p⟧))     (4)           
        5. by applying ++-cancelˡ  to (4) (which cancel the common prefix proj₁ (flat u) from both LHS and RHS of (4) 
          [] ≡ proj₁ (flat (unflat w∈⟦p⟧))
        6. by applying flat∘unflat to the above we have
          [] ≡ w 
    -}
    eq1 :  proj₁ (flat (inj (unflat w∈⟦p⟧))) ≡ proj₁ (flat u) ++ proj₁ (flat (unflat w∈⟦p⟧))
    eq1 = s-ev-p-r (unflat w∈⟦p⟧)
    
    proj1-flat-u++[]≡proj1-flat-u++proj1-flat-unflat-w∈⟦p⟧ : proj₁ (flat u) ++ [] ≡  proj₁ (flat u) ++ proj₁ (flat (unflat w∈⟦p⟧))
    proj1-flat-u++[]≡proj1-flat-u++proj1-flat-unflat-w∈⟦p⟧ =
      begin
        proj₁ (flat u) ++ []              ≡⟨ ++-identityʳ (proj₁ (flat u)) ⟩ 
        proj₁ (flat u)                    ≡⟨ cong (λ x → proj₁ (flat x)) (sym inj-unflat-w∈⟦p⟧≡u)  ⟩ 
        proj₁ (flat (inj (unflat w∈⟦p⟧))) ≡⟨ eq1 ⟩
        proj₁ (flat u) ++ proj₁ (flat (unflat w∈⟦p⟧))
      ∎

    proj1-flat-unflat-w∈⟦p⟧≡[] : proj₁ (flat (unflat w∈⟦p⟧)) ≡ []
    proj1-flat-unflat-w∈⟦p⟧≡[] =   ++-cancelˡ ( proj₁ (flat u) ) (proj₁ (flat (unflat w∈⟦p⟧))) [] (sym proj1-flat-u++[]≡proj1-flat-u++proj1-flat-unflat-w∈⟦p⟧)

    flat-unflat-w∈⟦p⟧≡w×w∈⟦p⟧ : flat (unflat w∈⟦p⟧) ≡ ( w , w∈⟦p⟧ )
    flat-unflat-w∈⟦p⟧≡w×w∈⟦p⟧ = flat∘unflat w∈⟦p⟧

    proj1-flat-unflat-w∈⟦p⟧≡w : proj₁ (flat (unflat w∈⟦p⟧)) ≡ w
    proj1-flat-unflat-w∈⟦p⟧≡w =
      begin
        proj₁ (flat (unflat w∈⟦p⟧)) ≡⟨ cong (λ x → proj₁ x ) flat-unflat-w∈⟦p⟧≡w×w∈⟦p⟧ ⟩
        w
      ∎ 

    w≡[] : w ≡ []
    w≡[] =
      begin
         w  ≡⟨ sym (proj1-flat-unflat-w∈⟦p⟧≡w) ⟩
         proj₁ (flat (unflat w∈⟦p⟧)) ≡⟨ proj1-flat-unflat-w∈⟦p⟧≡[] ⟩
         []
      ∎

    []∈⟦p⟧ : [] ∈⟦ p ⟧
    []∈⟦p⟧ = Eq.subst (λ x → x ∈⟦ p ⟧)  w≡[] w∈⟦p⟧
  
    u∈buildU-pdi  : Any (_≡_ u) (buildU pdi)
    u∈buildU-pdi  with ε∈? p
    ... | no ¬ε∈p = Nullary.contradiction (Word.[]∈⟦r⟧→ε∈r []∈⟦p⟧) ¬ε∈p  
    ... | yes ε∈p = find (mkAllEmptyU ε∈p) ( mkAllEmptyU-complete ε∈p ( unflat w∈⟦p⟧ ) (flat-[] (unflat w∈⟦p⟧)  proj1-flat-unflat-w∈⟦p⟧≡[] )   )
      where
        find : ∀ ( vs : List (U p) ) → Any ( _≡_ ( unflat w∈⟦p⟧ ) ) vs → (Any ( _≡_ u ) (List.map inj vs ))
        find (x ∷ xs) (here px) = here ev-u≡injx
           where
              ev-u≡injx : u ≡ inj x 
              ev-u≡injx  =
               begin
                 u ≡⟨ sym inj-unflat-w∈⟦p⟧≡u ⟩
                 inj (unflat w∈⟦p⟧) ≡⟨ cong (λ z → inj z ) px ⟩
                 inj x
               ∎
        find (x ∷ xs) (there pxs) = there (find xs pxs) 
        find []       any≡ =  Nullary.contradiction any≡ ¬Any[] 


```




### Theorem 28 : ParseAll is complete

Let r be a non problematic regular expression.
Let u be a parse tree of r.
Then u ∈ parseAll[ r , w ] for some w.

```agda
parseAll-complete : ∀ { r : RE }
  → ( u : U r )
  → ∃[ w ] (Any ( _≡_ u ) parseAll[ r , w ])
parseAll-complete {r} u = proj₁ (flat u) , find pdinstances any-recons*-pdinstances 
  where
    pdinstances : List (PDInstance* r (proj₁ (flat u))) 
    pdinstances = pdUMany[ r , proj₁ (flat u) ]

    any-recons*-pdinstances : Any (Recons* {r} {proj₁ (flat u)} u ) pdinstances
    any-recons*-pdinstances = pdUMany-complete {r} u


    find : ∀ ( pdis :  List (PDInstance* r (proj₁ (flat u)))  ) →  Any (Recons* {r} {proj₁ (flat u)} u ) pdis → Any ( _≡_ u ) (concatMap buildU pdis)
    find []            any-recons*           = Nullary.contradiction any-recons* ¬Any[]
    find (pdi ∷ pdis)  (here recons*-u-pdi)  = any-left-concat (buildU-complete u pdi recons*-u-pdi)
    find (pdi ∷ pdis)  (there pxs)           = any-right-concat (find pdis pxs)     
    
```



### Auxilary Lemmas needed in the ExtendedOrder.lagda.md proofs.


#### Aux Lemma: Reconstructibility can be inversedly preserved via the pdinstance's and pdinstance*'s operations.

```agda
-------------------------------------------------
-- Inversed reconstructibility Aux Lemmas BEGIN 
-------------------------------------------------

inv-recons-left : ∀ { l r : RE } { loc : ℕ } { c : Char } 
    → ( u : U l ) 
    → ( pdi : PDInstance l c )
    → Recons (LeftU {l} {r} {loc} u) (pdinstance-left pdi )
    ---------------------------------------------------------
    → Recons u pdi
inv-recons-left {l} {r} {loc} {c} u (pdinstance {p} {l} {c} inj s-ev) (recons (LeftU u') ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡LeftU-u ))
  = recons u (w∈⟦p⟧ , inv-leftU (inj (unflat w∈⟦p⟧)) u inj-unflat-w∈⟦p⟧≡LeftU-u) 


inv-recons-right : ∀ { l r : RE } { loc : ℕ } { c : Char } 
    → ( u : U r ) 
    → ( pdi : PDInstance r c )
    → Recons (RightU {l} {r} {loc} u) (pdinstance-right pdi )
    ---------------------------------------------------------
    → Recons u pdi
inv-recons-right {l} {r} {loc} {c} u (pdinstance {p} {r} {c} inj s-ev) (recons (RightU u') ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡RightU-u ))
  = recons u (w∈⟦p⟧ , inv-rightU (inj (unflat w∈⟦p⟧)) u inj-unflat-w∈⟦p⟧≡RightU-u)

inv-recons-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( u : U l )
    → ( v : U r )  
    → ( pdi : PDInstance l c )
    → Recons (PairU {l} {r} {loc} u v) (pdinstance-fst pdi )
    -------------------------------------------------------- 
    → Recons u pdi
inv-recons-fst {l} {r} {loc} {c} u v (pdinstance {p} {l} {c} inj s-ev)
  (recons {p ● r ` loc} {l ● r ` loc} {c} {w'} {inj'} {s-ev'} (PairU u' v') ( _●_⧺_  {xs} {ys} {w'} {p} {r} {loc} xs∈⟦p⟧  ys∈⟦r⟧ xs++ys≡w'  , inj-unflat-w'∈⟦p●r⟧≡PairU-u-v ))
  = recons {p} {l} {c} {xs} {inj} {s-ev}  u (xs∈⟦p⟧  , proj₁ inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r⟧≡v ) 
    where 
      inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r⟧≡v : ( inj (unflat xs∈⟦p⟧) ≡ u ) × ( unflat ys∈⟦r⟧ ≡ v )
      inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r⟧≡v = inv-pairU (inj (unflat xs∈⟦p⟧)) (unflat ys∈⟦r⟧) u v inj-unflat-w'∈⟦p●r⟧≡PairU-u-v



inv-recons-snd : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( e : U l ) -- empty parse tree from l
  → ( v : U r )
  → ( flat-[]-e :  Flat-[] l e )  
  → ( pdi : PDInstance r c )
  → Recons (PairU {l} {r} {loc} e v) (mk-snd-pdi ( e , flat-[]-e ) pdi )
  -----------------------------------------------------------------------
  → Recons v pdi
inv-recons-snd {l} {r} {loc} {c} e v ( flat-[] _ proj₁flat-e≡[]) (pdinstance inj s-ev) (recons (PairU _ _ ) ( w∈⟦p⟧ , inj∘unflat-w∈⟦p⟧≡pair-e-v ) )
  = recons v (w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡v)
    where
      e≡e×inj-unflat-w∈⟦p⟧≡v : ( e ≡ e ) × ((inj (unflat w∈⟦p⟧)) ≡ v )
      e≡e×inj-unflat-w∈⟦p⟧≡v = inv-pairU e (inj (unflat w∈⟦p⟧)) e v inj∘unflat-w∈⟦p⟧≡pair-e-v
      inj-unflat-w∈⟦p⟧≡v : inj (unflat w∈⟦p⟧) ≡ v
      inj-unflat-w∈⟦p⟧≡v = proj₂ e≡e×inj-unflat-w∈⟦p⟧≡v 


inv-recons-star : ∀ { r : RE } {ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  → ( u : U r )
  → ( us : List (U r) )
  → ( pdi : PDInstance r c )
  → Recons (ListU {r} {ε∉r} {loc} ( u ∷ us ) ) (pdinstance-star pdi )
  ---------------------------------------------------------------------
  → Recons u pdi
inv-recons-star {r} {ε∉r} {loc} {c} u us (pdinstance {p} {r} {c} inj s-ev)
  (recons {p ● ( r * ε∉r ` loc ) ` loc } { r * ε∉r ` loc } {c} {w'} {inj'} {s-ev'} (ListU {r} {ε∉r} {loc} ( u ∷ us )) (  _●_⧺_  {xs} {ys} {w'} {p} {r * ε∉r ` loc } {loc} xs∈⟦p⟧ ys∈⟦r*⟧ xs++ys≡w' , inj'-unflat-w'∈⟦p●r*⟧≡ListU-u-us )  ) = recons {p} {r} {c} {xs} {inj} {s-ev}  u (xs∈⟦p⟧  , proj₁ inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r*⟧≡list-us ) 
    where
      listu-u-us≡listu-inj-unflat-xs∈⟦p⟧-unListU-unflat-ys∈⟦r*⟧ : ListU (u ∷ us) ≡ ListU (inj (unflat xs∈⟦p⟧) ∷ unListU (unflat ys∈⟦r*⟧))
      listu-u-us≡listu-inj-unflat-xs∈⟦p⟧-unListU-unflat-ys∈⟦r*⟧ =
        begin
          ListU (u ∷ us)
        ≡⟨ sym  inj'-unflat-w'∈⟦p●r*⟧≡ListU-u-us ⟩
          mkinjList inj (PairU (unflat xs∈⟦p⟧) (unflat ys∈⟦r*⟧))
        ≡⟨ cong (λ x →  mkinjList inj (PairU (unflat xs∈⟦p⟧) x) ) ( sym listU∘unListU )  ⟩
          mkinjList inj (PairU (unflat xs∈⟦p⟧) (ListU (unListU (unflat ys∈⟦r*⟧))))
        ≡⟨⟩ 
          ListU (inj (unflat xs∈⟦p⟧) ∷ unListU (unflat ys∈⟦r*⟧))
        ∎ 
      inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r*⟧≡list-us : ( inj (unflat xs∈⟦p⟧) ≡ u ) × ( unListU (unflat ys∈⟦r*⟧) ≡ us )
      inj-unflat-xs∈⟦p⟧≡u×unflat-ys∈⟦r*⟧≡list-us = inv-listU (inj (unflat xs∈⟦p⟧)) (unListU (unflat ys∈⟦r*⟧)) u us ((sym listu-u-us≡listu-inj-unflat-xs∈⟦p⟧-unListU-unflat-ys∈⟦r*⟧)) 

inv-recons-assoc : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
  → ( v₁ : U l )
  → ( v₂ : U s )
  → ( v₃ : U r )
  → ( pdi : PDInstance (l ● (s ● r ` loc₂) ` loc₁) c )
  → Recons (PairU (PairU v₁ v₂) v₃) (pdinstance-assoc pdi )
  ----------------------------------------------------------------
  → Recons (PairU v₁ (PairU v₂ v₃)) pdi
inv-recons-assoc {l} {s} {r} {loc₁} {loc₂} {c}  v₁ v₂ v₃ pdi@(pdinstance inj s-ev)
  (recons {p} { ( l ● s  ` loc₁ ) ● r ` loc₂} {c} {w} (PairU (PairU v₁ v₂) v₃) ( w∈⟦p⟧ , mkinjAssoc-inj-unflat-w∈⟦p⟧≡pair-pair-v₁v₂v₃))
    = recons (PairU v₁ (PairU v₂ v₃)) (w∈⟦p⟧ , sym pair-v₁-pair-v₂v₃≡inj-unflat-w∈⟦p⟧)
    where
      pair-v₁-pair-v₂v₃≡inj-unflat-w∈⟦p⟧ : PairU v₁ (PairU v₂ v₃) ≡ inj (unflat w∈⟦p⟧) 
      pair-v₁-pair-v₂v₃≡inj-unflat-w∈⟦p⟧ =
        begin
          PairU v₁ (PairU v₂ v₃)
        ≡⟨⟩
          assoc (PairU (PairU v₁ v₂) v₃)
        ≡⟨ cong ( λ x → assoc x ) (sym mkinjAssoc-inj-unflat-w∈⟦p⟧≡pair-pair-v₁v₂v₃ ) ⟩
          assoc (mkinjAssoc inj (unflat w∈⟦p⟧))
        ≡⟨⟩
          assoc (inv-assoc (inj (unflat w∈⟦p⟧)))
        ≡⟨ assoc-inv-assoc-u≡u ⟩
          inj (unflat w∈⟦p⟧)  
        ∎ 


inv-recons*-compose-pdi-with : ∀ { r d : RE } {pref : List Char } { c : Char }
  → ( u : U r )
  → ( pdi : PDInstance d c )
  → ( d→r : U d → U r )
  → ( s-ev-dr : ∀ ( v : U d ) → ( proj₁ ( flat {r} (d→r v) ) ≡ pref ++ ( proj₁ (flat {d} v) )) )
  → Recons* {r} {pref ∷ʳ c}  u (compose-pdi-with d→r s-ev-dr pdi) 
  ----------------------------------------------------
  → Recons* {r} {pref} u (pdinstance* d→r s-ev-dr) 
inv-recons*-compose-pdi-with {r} {d} {pref} {c} u (pdinstance {p} {d} {c} p→d s-ev-pd) d→r s-ev-dr
  (recons* {p} {r} {w} {pref++c} u ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧ ) ) =
    recons* {- {d} {r} {c ∷ w} {pref} {d→r} {s-ev-dr} -}  u  ( proj₂ (flat (p→d (unflat w∈⟦p⟧))) , prf )
    where
      prf :  d→r (unflat (Product.proj₂ (flat (p→d (unflat w∈⟦p⟧))))) ≡ u
      prf =
        begin
          d→r (unflat (proj₂ (flat (p→d (unflat w∈⟦p⟧)))))
        ≡⟨ cong (λ x → (d→r x) ) unflat∘proj₂∘flat ⟩
          d→r (p→d (unflat w∈⟦p⟧))
        ≡⟨ inj-unflat-w∈⟦p⟧ ⟩ 
          u
        ∎

-------------------------------------------------
-- Inversed reconstructibility Aux Lemmas END
-------------------------------------------------
```


#### Aux Lemma: Impossibilities of parse tree reconstructions through pdinstance operations.

e.g. we can reconstruct a RightU from a pdinnstance-left operation. 

```agda
-------------------------------------------------
-- Impossible reconstructibility Aux Lemmas BEGIN
-------------------------------------------------

-- A RightU parse tree cannot be reconstructed from a pdinstance-left created pdisntance
¬recons-right-from-pdinstance-left : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( u : U r ) 
  → ( pdi : PDInstance l c )
    ------------------------------------------------------------
  → ¬ (Recons (RightU {l} {r} {loc} u) (pdinstance-left pdi ))
¬recons-right-from-pdinstance-left {l} {r} {loc} {c} u pdi@(pdinstance {p} {l} inj s-ev) (recons {p'} {l + r ` loc } {c} {w} {inj'} {s-ev'} (RightU u) ( w∈⟦p'⟧ , inj∘unflat≡rightu-u ) )
  = (LeftU≢RightU {l} {r} {loc} (inj (unflat w∈⟦p'⟧)) u)  inj∘unflat≡rightu-u 


-- A LeftU parse tree cannot be reconstructed from a pdinstance-right created pdisntance
¬recons-left-from-pdinstance-right : ∀ { l r : RE } { loc : ℕ } { c : Char } 
  → ( u : U l ) 
  → ( pdi : PDInstance r c )
    ------------------------------------------------------------
  → ¬ (Recons (LeftU {l} {r} {loc} u) (pdinstance-right pdi ))
¬recons-left-from-pdinstance-right {l} {r} {loc} {c} u pdi@(pdinstance {p} {r} inj s-ev) (recons {p'} {l + r ` loc } {c} {w} {inj'} {s-ev'} (LeftU u) ( w∈⟦p'⟧ , inj∘unflat≡leftu-u ) )
  = (RightU≢LeftU {l} {r} {loc} (inj (unflat w∈⟦p'⟧)) u) inj∘unflat≡leftu-u




-- An ListU [] parse tree cannot be constructed from a pdinstance-map created pdinstance
¬recons-[]-from-pdinstance-star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  -- → ( u : U r )
  → ( pdi : PDInstance r c )
  --------------------------------------------------------------
  → ¬ (Recons (ListU {r} {ε∉r} {loc} []) (pdinstance-star pdi ))
¬recons-[]-from-pdinstance-star {r} {ε∉r} {loc} {c} pdi@(pdinstance {p} {r} inj s-ev) (recons {p'} {r * ε∉r ` loc} {c} {w} {inj'} {s-ev'} (ListU []) ( w∈⟦p'⟧ , inj∘unflat≡list-[] ) )
   =  (Word.¬c∷w≡[] {c}  {proj₁ (flat (unflat w∈⟦p'⟧))})  c∷proj₁-flat-unflat-w∈⟦p'⟧≡[]  
   where
     proj₁flat-inj'-unflat-w∈⟦p'⟧≡c∷proj₁flat-unflat-w∈⟦p'⟧ : proj₁ (flat ( inj' (unflat w∈⟦p'⟧)) ) ≡ c ∷ proj₁ (flat (unflat w∈⟦p'⟧))
     proj₁flat-inj'-unflat-w∈⟦p'⟧≡c∷proj₁flat-unflat-w∈⟦p'⟧ = s-ev' (unflat w∈⟦p'⟧)
     proj₁flat-NilU≡c∷proj₁-flat-unflat-w∈⟦p'⟧ : proj₁ (flat (ListU  {r} {ε∉r} {loc} [])) ≡ c ∷ proj₁ (flat (unflat w∈⟦p'⟧))
     proj₁flat-NilU≡c∷proj₁-flat-unflat-w∈⟦p'⟧  = 
       begin
          proj₁ (flat (ListU  {r} {ε∉r} {loc} []))
       ≡⟨ cong (λ x →  proj₁ (flat x)) (sym inj∘unflat≡list-[] ) ⟩
          proj₁ (flat ( inj' (unflat w∈⟦p'⟧)) )
       ≡⟨ proj₁flat-inj'-unflat-w∈⟦p'⟧≡c∷proj₁flat-unflat-w∈⟦p'⟧ ⟩ 
          c ∷ proj₁ (flat (unflat w∈⟦p'⟧))
       ∎
     c∷proj₁-flat-unflat-w∈⟦p'⟧≡[] : c ∷ proj₁ (flat (unflat w∈⟦p'⟧)) ≡ [] 
     c∷proj₁-flat-unflat-w∈⟦p'⟧≡[] =
       begin
         c ∷ proj₁ (flat (unflat w∈⟦p'⟧))
       ≡⟨ sym proj₁flat-NilU≡c∷proj₁-flat-unflat-w∈⟦p'⟧ ⟩
         proj₁ (flat (ListU  {r} {ε∉r} {loc} []))
       ≡⟨⟩
         []
       ∎

-------------------------------------------------
-- Impossible reconstructibility Aux Lemmas END 
-------------------------------------------------       

```


#### Aux Lemma: pdUMany-aux returns an empty list of pdinstance*'s given an empty input list of pdinstance*'s .

Let r be a non problematic regular expression.
Let pref and suff be words .
Then pdUMany-aux {r} {pref} suff [] yields [] as result. 

```agda
-- sub lemma
concatMap-advance-pdi*-with-c-[]≡[] : ∀ { r : RE } {pref : List Char} { c : Char }
  → concatMap (advance-pdi*-with-c {r} {pref} {c}) [] ≡ [] 
concatMap-advance-pdi*-with-c-[]≡[] = refl 
-- main lemma
pdUMany-aux-cs-[]≡[] : ∀ { r : RE } {pref : List Char}
    → (suff : List Char)
    → pdUMany-aux {r} {pref} suff [] ≡ [] 
pdUMany-aux-cs-[]≡[] {r} {pref} [] rewrite (++-identityʳ pref) = refl 
pdUMany-aux-cs-[]≡[] {r} {pref} (c ∷ cs) rewrite (concatMap-advance-pdi*-with-c-[]≡[] {r} {pref} {c})  = pdUMany-aux-cs-[]≡[] {r} {pref ∷ʳ c } cs
```

#### Aux Lemma : first r is not empty implies pdU r is not empty for some c.

Let r be a non problematic regular expression.
Let c be a character and cs be aword.
Let first r ≡ c ∷ cs.
Then pdU[ r , c ] must not be an empty list. 

```agda
-- sub sub lemma 
zip-es-flat-[]-es≡[]→es≡[] : ∀ {l : RE} {ε∈l : ε∈ l }
    → (es : List (U l))
    → (flat-[]-es : All (Flat-[] l) es)
    → (zip-es-flat-[]-es {l} {ε∈l} es flat-[]-es  ≡ [] ) 
    -----------------------------------------------------
    → es ≡ []
zip-es-flat-[]-es≡[]→es≡[] {l} {ε∈l} [] [] refl = refl     
zip-es-flat-[]-es≡[]→es≡[] {l} {ε∈l} (e ∷ es) (flat-[]-e ∷ flat-[]-es) =  λ ()


first≢[]→¬pdU≡[] : ∀ { r : RE } { c : Char } { cs : List Char }
    → ( first r ≡ c ∷ cs )
    ------------------------
    → ¬ ( pdU[ r , c ] ≡ [] )
first≢[]→¬pdUConcat≡[] : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { c : Char } { cs : List Char } 
  → first l ++ first r ≡ c ∷ cs
  --------------------------------------------------------------------
  → ¬ ( pdUConcat l r ε∈l loc c ≡ [] ) 


first≢[]→¬pdU≡[] {ε} {c} {cs} = λ()
first≢[]→¬pdU≡[] {$ c ` loc} {c₁} {[]} first-c≡c∷[] = prf
  where
    c≡c₁ : c ≡ c₁
    c≡c₁ = proj₁ (∷-inj first-c≡c∷[])
    
    prf : ¬ ( pdU[ $ c ` loc , c₁ ] ≡ [] )
    prf pdU-r-c≡[] with c Char.≟ c₁
    ...             | no ¬c≡c₁ = ¬c≡c₁ c≡c₁ 
    ...             | yes refl with pdU[ $ c ` loc , c₁ ]  in eq 
    ...                        | pdi ∷ [] = ¬∷≡[] pdU-r-c≡[]
first≢[]→¬pdU≡[] { l + r ` loc } {c} {cs} first-l+r≡c∷cs with first l in l-eq | first r in r-eq 
... | [] | c₁ ∷ cs₁ = prf 
  where
    c₁≡c×cs₁≡cs : (c₁ ≡ c) × (cs₁ ≡ cs)
    c₁≡c×cs₁≡cs = (∷-inj first-l+r≡c∷cs)
    ind-hyp : ¬ ( pdU[ r , c₁ ] ≡ [] )
    ind-hyp =  first≢[]→¬pdU≡[] r-eq   
    prf : ¬ ( List.map (pdinstance-left {l} {r} {loc}) pdU[ l , c ] ++ List.map (pdinstance-right {l} {r} {loc})  pdU[ r , c ] ≡ [] )
    prf  map-pdinstance-left-pdu-l-c++map-pdinstance-right-pdu-r-c≡[] rewrite sym (proj₁ c₁≡c×cs₁≡cs) =  ind-hyp (inv-map-[] map-right-pdu-r-c≡[])
      where
        map-right-pdu-r-c≡[] : List.map (pdinstance-right {l} {r} {loc})  pdU[ r , c₁ ] ≡ [] 
        map-right-pdu-r-c≡[] = ++-conicalʳ (List.map (pdinstance-left {l} {r} {loc}) pdU[ l , c₁ ]) (List.map (pdinstance-right {l} {r} {loc})  pdU[ r , c₁ ] )  map-pdinstance-left-pdu-l-c++map-pdinstance-right-pdu-r-c≡[]
... | c₁ ∷ cs₁ | cs₂ =  prf
  where 
    c₁≡c×cs₁cs₂≡cs : (c₁ ≡ c) × (cs₁ ++ cs₂ ≡ cs)
    c₁≡c×cs₁cs₂≡cs  = ∷-inj first-l+r≡c∷cs 
    ind-hyp : ¬ ( pdU[ l , c₁ ] ≡ [] )
    ind-hyp =  first≢[]→¬pdU≡[] l-eq   
    prf : ¬ ( List.map (pdinstance-left {l} {r} {loc}) pdU[ l , c ] ++ List.map (pdinstance-right {l} {r} {loc})  pdU[ r , c ] ≡ [] )
    prf  map-pdinstance-left-pdu-l-c++map-pdinstance-right-pdu-r-c≡[] rewrite sym (proj₁ c₁≡c×cs₁cs₂≡cs) =  ind-hyp (inv-map-[] map-left-pdu-l-c≡[])
      where
        map-left-pdu-l-c≡[] : List.map (pdinstance-left {l} {r} {loc})  pdU[ l , c₁ ] ≡ [] 
        map-left-pdu-l-c≡[] = ++-conicalˡ (List.map (pdinstance-left {l} {r} {loc}) pdU[ l , c₁ ]) (List.map (pdinstance-right {l} {r} {loc})  pdU[ r , c₁ ] )  map-pdinstance-left-pdu-l-c++map-pdinstance-right-pdu-r-c≡[]
first≢[]→¬pdU≡[] { r * ε∉r ` loc } {c} {cs} first-r*≡c∷cs map-star-pdU-r-c≡[] = ind-hyp (inv-map-[] map-star-pdU-r-c≡[])
  where
    ind-hyp : ¬ ( pdU[ r , c ] ≡ [] )
    ind-hyp = first≢[]→¬pdU≡[] {r} {c} {cs} first-r*≡c∷cs

first≢[]→¬pdU≡[] { l ● r ` loc } {c} {cs} first-l●r≡c∷cs with ε∈? l
... | no ¬ε∈l = λ map-fst-pdU-l-cs≡[] → ind-hyp (inv-map-[] map-fst-pdU-l-cs≡[])
  where
    ind-hyp : ¬ ( pdU[ l , c ] ≡ [] )
    ind-hyp = first≢[]→¬pdU≡[] {l} {c} {cs} first-l●r≡c∷cs
... | yes ε∈l = prf
  where
    prf : ¬ ( pdUConcat l r ε∈l loc c ≡ [] )
    prf = first≢[]→¬pdUConcat≡[] first-l●r≡c∷cs

{-# TERMINATING #-}
first≢[]→¬pdUConcat≡[] {ε} {r} {ε∈ε} {loc} {c} {cs} first-r≡c∷cs
  with (zip-es-flat-[]-es {ε} {ε∈ε} (mkAllEmptyU {ε} ε∈ε) (mkAllEmptyU-sound {ε} ε∈ε)) in eq 
... | [] = λ map-mk-snd-pdi-es → ¬∷≡[] eq   
... | (EmptyU , flat-[] EmptyU refl ) ∷ xs rewrite ++-identityʳ ( List.map (mk-snd-pdi {ε} {r} {loc} {c} (EmptyU , flat-[] EmptyU refl)) pdU[ r , c ] ) =
    λ map-mk-snd-pdi-pdu-r-c≡[] → (first≢[]→¬pdU≡[] first-r≡c∷cs) (inv-map-[] map-mk-snd-pdi-pdu-r-c≡[])


first≢[]→¬pdUConcat≡[] {l * ε∉l ` loc₁} {r} {ε∈*} {loc₂} {c} {cs} first-l*●r≡c∷cs
  with first l in first-l-eq  | first r in first-r-eq 
... | []                      | []        =  λ x → ¬∷≡[] (sym first-l*●r≡c∷cs)
... | []                      | c₁ ∷ cs₁ rewrite ++-identityʳ (List.map (mk-snd-pdi {l * ε∉l ` loc₁} {r} {loc₂} {c} (ListU [] , flat-[] (ListU []) refl)) pdU[ r , c ]) = prf
  where
    c₁≡c×cs₁≡cs : (c₁ ≡ c) × (cs₁ ≡ cs)
    c₁≡c×cs₁≡cs = (∷-inj first-l*●r≡c∷cs)
    ind-hyp : ¬ ( pdU[ r , c₁ ] ≡ [] )
    ind-hyp =  first≢[]→¬pdU≡[] first-r-eq
    prf : ¬ ( List.map (pdinstance-fst  {l * ε∉l ` loc₁} {r} {loc₂} {c}) (List.map pdinstance-star pdU[ l , c ]) ++ List.map (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl))  pdU[ r , c ] ≡ [] ) 
    prf map-fst-map-star-pdu-l-c++map-mk-snd-pdi-pdu-r-c≡[] rewrite sym (proj₁ c₁≡c×cs₁≡cs) = ind-hyp (inv-map-[] (++-conicalʳ (List.map pdinstance-fst (List.map pdinstance-star pdU[ l , c₁ ])) (List.map (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl)) pdU[ r , c₁ ])  map-fst-map-star-pdu-l-c++map-mk-snd-pdi-pdu-r-c≡[]))
... | c₁ ∷ cs₁               | cs₂       rewrite ++-identityʳ (List.map (mk-snd-pdi {l * ε∉l ` loc₁} {r} {loc₂} {c} (ListU [] , flat-[] (ListU []) refl)) pdU[ r , c ]) = prf 
  where
    c₁≡c×cs₁cs₂≡cs : (c₁ ≡ c) × (cs₁ ++ cs₂ ≡ cs)
    c₁≡c×cs₁cs₂≡cs = (∷-inj first-l*●r≡c∷cs) 
    ind-hyp : ¬ ( pdU[ l , c₁ ] ≡ [] )
    ind-hyp =  first≢[]→¬pdU≡[] first-l-eq
    prf : ¬ ( List.map (pdinstance-fst  {l * ε∉l ` loc₁} {r} {loc₂} {c}) (List.map pdinstance-star pdU[ l , c ]) ++ List.map (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl))  pdU[ r , c ] ≡ [] ) 
    prf map-fst-map-star-pdu-l-c++map-mk-snd-pdi-pdu-r-c≡[] rewrite sym (proj₁ c₁≡c×cs₁cs₂≡cs) = ind-hyp (inv-map-[] (inv-map-[] (++-conicalˡ (List.map pdinstance-fst (List.map pdinstance-star pdU[ l , c₁ ])) (List.map (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl)) pdU[ r , c₁ ])  map-fst-map-star-pdu-l-c++map-mk-snd-pdi-pdu-r-c≡[])))

first≢[]→¬pdUConcat≡[] {l + s ` loc₁} {r} {ε∈l+s} {loc₂} {c} {cs} first-l+s●r≡c∷cs
  with first (l + s ` loc₁) in first-l+s-eq | first r in first-r-eq
... | []                                    | []  = λ x → ¬∷≡[] (sym first-l+s●r≡c∷cs)
... | []                                    | c₁ ∷ cs₁    =  prf
    where
      c₁≡c×cs₁≡cs : (c₁ ≡ c) × (cs₁ ≡ cs)
      c₁≡c×cs₁≡cs = (∷-inj first-l+s●r≡c∷cs)
      ind-hyp : ¬ ( pdU[ r , c ] ≡ [] )
      ind-hyp rewrite sym (proj₁ c₁≡c×cs₁≡cs) =  first≢[]→¬pdU≡[] first-r-eq
      prf : ¬ ( List.map pdinstance-fst  (List.map pdinstance-left pdU[ l , c ] ++ List.map pdinstance-right pdU[ s , c ])
                ++
                List.foldr _++_ [] (List.map (λ x₁ → List.map (mk-snd-pdi x₁) pdU[ r , c ]) (zip-es-flat-[]-es {l + s ` loc₁} {ε∈l+s} (mkAllEmptyU ε∈l+s)
                                                                                         (mkAllEmptyU-sound ε∈l+s))) )
                ≡ []
      prf x = ind-hyp pdu-r-c≡[] 
        where
          y : (concatMap (λ x₁ → List.map (mk-snd-pdi x₁) pdU[ r , c ]) (zip-es-flat-[]-es {l + s ` loc₁} {ε∈l+s} (mkAllEmptyU ε∈l+s) (mkAllEmptyU-sound ε∈l+s))) ≡ []
          y = ++-conicalʳ (List.map pdinstance-fst  (List.map pdinstance-left pdU[ l , c ] ++ List.map pdinstance-right pdU[ s , c ]))
                                                (concatMap (λ x₁ → List.map (mk-snd-pdi x₁) pdU[ r , c ]) (zip-es-flat-[]-es {l + s ` loc₁} {ε∈l+s} (mkAllEmptyU ε∈l+s) (mkAllEmptyU-sound ε∈l+s))) x
          pdu-r-c≡[] : (pdU[ r , c ] ≡ [])
          pdu-r-c≡[] with inv-concatMap-map-f-[] y
          ...  | inj₁ zip-es-flat-[]-es≡[] = Nullary.contradiction (zip-es-flat-[]-es≡[]→es≡[]  {l + s ` loc₁} {ε∈l+s} (mkAllEmptyU ε∈l+s) (mkAllEmptyU-sound ε∈l+s) zip-es-flat-[]-es≡[]) ( mkAllEmptyU≢[] ε∈l+s )
          ...  | inj₂ pdu-r-c≡[] =  pdu-r-c≡[]
... | c₁ ∷ cs₁                              | cs₂      = prf
    where
      c₁≡c×cs₁≡cs : (c₁ ≡ c) × (cs₁ ++ cs₂ ≡ cs)
      c₁≡c×cs₁≡cs = (∷-inj first-l+s●r≡c∷cs)
      ind-hyp : ¬ ( pdU[ l + s ` loc₁ , c ] ≡ [] )
      ind-hyp rewrite sym (proj₁ c₁≡c×cs₁≡cs) =  first≢[]→¬pdU≡[] first-l+s-eq
      prf : ¬ ( List.map pdinstance-fst  (List.map pdinstance-left pdU[ l , c ] ++ List.map pdinstance-right pdU[ s , c ])
                ++
                List.foldr _++_ [] (List.map (λ x₁ → List.map (mk-snd-pdi x₁) pdU[ r , c ]) (zip-es-flat-[]-es {l + s ` loc₁} {ε∈l+s} (mkAllEmptyU ε∈l+s)
                                                                                         (mkAllEmptyU-sound ε∈l+s))) )
                ≡ []
      prf x = ind-hyp pdu-l+s-c≡[] 
        where
          y : List.map pdinstance-fst  (List.map pdinstance-left pdU[ l , c ] ++ List.map pdinstance-right pdU[ s , c ])  ≡ []
          y = ++-conicalˡ (List.map pdinstance-fst  (List.map pdinstance-left pdU[ l , c ] ++ List.map pdinstance-right pdU[ s , c ]))
                                                (concatMap (λ x₁ → List.map (mk-snd-pdi x₁) pdU[ r , c ]) (zip-es-flat-[]-es {l + s ` loc₁} {ε∈l+s} (mkAllEmptyU ε∈l+s) (mkAllEmptyU-sound ε∈l+s))) x
          pdu-l+s-c≡[] : (pdU[ l + s ` loc₁ , c ] ≡ [])
          pdu-l+s-c≡[] = inv-map-[] y


first≢[]→¬pdUConcat≡[] {l ● s ` loc₁} {r} {ε∈ ε∈l ● ε∈s} {loc₂} {c} {cs} first-l●s-●r≡c∷cs with  ε∈? l in l-eq | ε∈? s in s-eq 
... | no ¬ε∈l | _ = Nullary.contradiction ε∈l ¬ε∈l
... | yes ε∈l | no ¬ε∈s = Nullary.contradiction ε∈s ¬ε∈s 
... | yes ε∈l | yes ε∈s = λ x →  ind-hyp (inv-map-[] x)  
    where
      first-s●r≡first-s++first-r : first (s ● r ` loc₂) ≡ first s ++ first r
      first-s●r≡first-s++first-r rewrite s-eq = refl 
      first-l●s-●r≡first-l-●s●r : first l ++ (first (s ● r ` loc₂)) ≡ c ∷ cs 
      first-l●s-●r≡first-l-●s●r  = 
        begin
          (first l) ++ (first (s ● r ` loc₂)) 
        ≡⟨ cong ((first l) ++_ )  first-s●r≡first-s++first-r ⟩
          (first l) ++ ((first s)  ++ (first r)) 
        ≡⟨ sym ( ++-assoc (first l) (first s) (first r) ) ⟩
          (first l ++ first s)  ++ first r 
        ≡⟨ first-l●s-●r≡c∷cs ⟩
          c ∷ cs 
        ∎  
      ind-hyp : ¬ (pdUConcat l ( s ● r ` loc₂) ε∈l loc₁ c ≡ [] )
      ind-hyp  = first≢[]→¬pdUConcat≡[] {l}  {s ● r ` loc₂} {ε∈l} {loc₁} {c} {cs}   first-l●s-●r≡first-l-●s●r
```




#### Aux Lemma: All partial derivative descendants produce some parse tree.

Let r be a non problematic regular expression. 
Let pdi be a partial derivative descendant instance of r w.r.t to prefix pref.
Then there exists a parse tree u, such that u can be reconstructed from pdi. 

```agda
{-# TERMINATING #-}
pdi*-∃ : ∀ { r : RE } { pref : List Char }
       → ( pdi : PDInstance* r pref )
       → ∃[ u ] Recons* u pdi

pdi*-∃ {r} {pref} pdi@(pdinstance* {d} {r} {pref}  inj s-ev)
  with ε∈? d
... |  yes ε∈d with (mkAllEmptyU ε∈d )in mkAllEmptyU-e∈p-eq 
...              | ( e ∷ es ) = inj e , recons* (inj e) ((proj₂ (flat e)) , prf) -- base case, 
  where
    prf  : inj (unflat (Product.proj₂ (flat e))) ≡ inj e
    prf = cong (λ x → inj x ) unflat∘proj₂∘flat
...              | [] = Nullary.contradiction  mkAllEmptyU-e∈p-eq ( mkAllEmptyU≢[] ε∈d)     -- we need to create a contradiction here. mkAllEmptyU is not empty

pdi*-∃ {r} {pref} pdi@(pdinstance* {d} {r} {pref}  d→r s-ev-d-r)
    |  no ¬ε∈d  with first d in first-d-eq
...               |  [] =   Nullary.contradiction first-d-eq (ε∉r→¬first-r≡[] {d} {¬ε∈r→ε∉r ¬ε∈d})      
...               |  ( c₁ ∷ cs₁ ) with pdU[ d , c₁ ] in pdU-d-c₁-eq 
...                                | []  =  Nullary.contradiction pdU-d-c₁-eq (first≢[]→¬pdU≡[] first-d-eq)  -- since c₁ is in first d, pdU[ d , c₁ ] should not be [] 
...                                | (pdi'@(pdinstance {p} {d} {c₁} p→d s-ev-p-d) ∷ _ )
                                          with pdi*-∃ {r} {pref ∷ʳ c₁} (compose-pdi-with {r} {d} {pref} {c₁} d→r s-ev-d-r pdi' )
...                                         | ( u , recons* {p} {r} {w} { pref∷ʳc₁ } {p→r} {s-ev-p-r} .u (w∈⟦p⟧ , d→r∘p→d-unflat-w∈⟦p⟧≡u ) )
                                                with flat {d} (p→d (unflat w∈⟦p⟧)) in flat-p→d-unflat-w∈⟦p⟧-eq 
...                                              | c₁w , c₁w∈⟦d⟧ = prf 
                                                          where
                                                              -- sub goals
                                                              unflat-c₁w∈⟦d⟧≡p→d-unflat-w∈⟦p⟧ :  unflat c₁w∈⟦d⟧ ≡ p→d (unflat w∈⟦p⟧)
                                                              unflat-c₁w∈⟦d⟧≡p→d-unflat-w∈⟦p⟧ =
                                                                begin
                                                                  unflat c₁w∈⟦d⟧
                                                                ≡⟨ cong (λ x → unflat ( proj₂ x ) ) (sym flat-p→d-unflat-w∈⟦p⟧-eq)  ⟩
                                                                  unflat ( proj₂ (flat (p→d (unflat w∈⟦p⟧))) )
                                                                ≡⟨ unflat∘proj₂∘flat {d} {(p→d (unflat w∈⟦p⟧))} ⟩
                                                                  p→d (unflat w∈⟦p⟧)
                                                                ∎
                                                              d→r-unflat-c₁w∈⟦d⟧≡u : d→r (unflat c₁w∈⟦d⟧) ≡ u
                                                              d→r-unflat-c₁w∈⟦d⟧≡u rewrite  unflat-c₁w∈⟦d⟧≡p→d-unflat-w∈⟦p⟧ | d→r∘p→d-unflat-w∈⟦p⟧≡u = refl 

                                                              -- main goal 
                                                              prf : ∃[ u ] Recons* u (pdinstance* d→r s-ev-d-r)
                                                              prf   = u , recons*   u ( c₁w∈⟦d⟧  ,  d→r-unflat-c₁w∈⟦d⟧≡u )     



```

#### Aux Lemma : A parse tree this reconstructible from a pdinstance should not be flattened to empty word.

```agda
recons-v→¬proj₁flat-v≡[] : ∀ { r : RE } { c : Char }
  → ( v : U r )
  → ( pdi : PDInstance r c )
  → Recons v pdi
  ---------------------------------------------
  → ¬ proj₁ (flat v) ≡ []
recons-v→¬proj₁flat-v≡[] {r} {c} v pdi  (recons {p} {l} {c} {w} {inj} {s-ev} _ ( w∈⟦p⟧ , inj-unflat-w∈⟦p⟧≡v ) )= prf 
  where
    proj₁-flat-v≡c∷w : proj₁ (flat v) ≡ c ∷ w
    proj₁-flat-v≡c∷w =
      begin
        proj₁ (flat v)
      ≡⟨ cong (λ x → proj₁ (flat x)) ( sym inj-unflat-w∈⟦p⟧≡v ) ⟩
        proj₁ (flat (inj (unflat w∈⟦p⟧)))
      ≡⟨ s-ev (unflat w∈⟦p⟧)  ⟩
        c ∷ proj₁ (flat (unflat w∈⟦p⟧))
      ≡⟨ cong (λ x → c ∷ (proj₁ x) ) (flat∘unflat w∈⟦p⟧) ⟩
        c ∷ w 
      ∎ 
    prf : ¬  proj₁ (flat v) ≡ [] 
    prf rewrite ( proj₁-flat-v≡c∷w ) = λ () 
```



### Additional Corollary of the completeness result; trying to show the LNN is necessary


hm... dont we need this instead? 

```agda
{-
w∈⟦r⟧→¬parseAll-r-w≡[] : ∀ { r : RE } { w : List Char }
  → w ∈⟦ r ⟧
  → ¬ (parseAll[ r , w ] ≡ [])
w∈⟦r⟧→¬parseAll-r-w≡[] {ε} {[]} ε parseAll-ε-[]≡[] = {!!} 




w∈⟦r⟧→parseAll-r-w≡∷ : ∀ { r : RE } { w : List Char }
  → w ∈⟦ r ⟧
  → ∃[ u ] ∃[ us ] parseAll[ r , w ] ≡ ( u ∷ us )
w∈⟦r⟧→parseAll-r-w≡∷ {ε} {[]} ε = ( EmptyU , ( [] , refl ) )
w∈⟦r⟧→parseAll-r-w≡∷ {$ c ` loc} {c₁ ∷ []} ($ _ ) = ( LetterU c , ( [] , prf ) )
  where
    prf : parseAll[ $ c ` loc , c ∷ [] ] ≡ LetterU c ∷ []
    prf = begin
      parseAll[ $ c ` loc , c ∷ [] ]                                        ≡⟨⟩
      List.concatMap buildU (pdUMany[ $ c ` loc , c ∷ []  ])                ≡⟨⟩
      List.foldr _++_ [] (List.map buildU (pdUMany[ $ c ` loc , c ∷ []  ])) ≡⟨ {!!} ⟩ 
      LetterU c ∷ []                  ∎

w∈⟦r⟧→parseAll-r-w≡∷ {$ c ` loc} {c₁ ∷ c₂ ∷ cs} = λ()
  



parseAll-r-w≡[]→¬w∈⟦r⟧ : ∀ { r : RE } { w : List Char } 
  → parseAll[ r , w ] ≡ []
  → ¬ ( w ∈⟦ r ⟧ )
parseAll-r-w≡[]→¬w∈⟦r⟧ {r} {w} parseAll-r-w≡[] = prf
  where
    prf : ¬ (w ∈⟦ r ⟧ )
    prf w∈⟦r⟧ rewrite parseAll-r-w≡[] with w∈⟦r⟧→parseAll-r-w≡∷ w∈⟦r⟧
    ... | ( u , ( us , parseAll-r-w≡u∷us ) ) = ¬∷≡[] uus≡[] 
        where
          uus≡[] : u ∷ us ≡ []
          uus≡[] = begin
            u ∷ us             ≡⟨ sym parseAll-r-w≡u∷us ⟩
            parseAll[ r , w ] ≡⟨ parseAll-r-w≡[] ⟩
            []                 ∎
-}            

```
