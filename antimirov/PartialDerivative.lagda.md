This module contains the implementation of regular expression parsing algorithm using Antimriov's original partial derivative operation. 

```agda
{-# OPTIONS --rewriting #-}
module cgp.antimirov.PartialDerivative where

import cgp.RE as RE
open RE using (RE; ϕ ; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ε∉ϕ ; ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )

import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ;  inv-flat-pair-fst ; inv-flat-pair-snd ; inv-flat-star  )


import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU ; mkAllEmptyU-sound ; mkAllEmptyU-complete ; Flat-[] ; flat-[] )


import cgp.Utils as Utils
open Utils using (any-right-concat; any-left-concat ; all-concat ;  ∷-inj    )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; concatMap ; _∷ʳ_  )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; {-  unfold-reverse ; -} ∷ʳ-++ ; ++-cancelˡ )


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
pd[ ϕ , c ]    = []
pd[ ε , c ]    = []
pd[ $ c ` loc  , c' ] with c Char.≟ c'
...                      | yes refl = [ ε ]
...                      | no  _    = []
pd[ l ● r ` loc , c ] with ε∈? l
...                      | yes ε∈l = (List.map (λ l' → l' ● r ` loc ) pd[ l , c ]) ++ pd[ r , c ] 
...                      | no ¬ε∈l = List.map (λ l' → l' ● r ` loc ) pd[ l , c ]
pd[ l + r ` loc , c ]               = pd[ l , c ] ++ pd[ r , c ]
pd[ r * nε ` loc , c ]              = List.map (λ r' → r' ● ( r * nε ` loc ) ` loc ) pd[ r , c ]
```


### Definition 16: Partial derivatives with coercion functions 

```agda

flat-Uε≡[] : ∀ ( u : U ε )
  → proj₁ (flat u) ≡ []
flat-Uε≡[] EmptyU = refl

-- partial derivative (descendant?) relation and coercion function
-- the result type of pdU
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



------------------------------------------------------------------------------------

-- postulate
--   pdinstance-dist : ∀ { l r s : RE } { loc₁ loc₂ : ℕ } { c : Char } → PDInstance ( (l ● s ` loc₂) +  ( r ● s ` loc₂) ` loc₁ ) c → PDInstance (( l + r ` loc₁) ● s ` loc₂ ) c


-- pdU[_,_] :  ( r : RE ) → ( c :  Char ) →  List ( ∃ [ p ] p ∈ pd[ r , c ] × ( U p → U r ) )

pdU[_,_] :  ( r : RE ) → ( c :  Char ) →  List (PDInstance r c)
pdU[ ϕ , c ] = [] 
pdU[ ε , c ] = []
pdU[ $ c ` loc  , c' ] with c Char.≟ c'
...                       | yes refl = [  pdinstance {ε} {$ c ` loc} {c}
                                                 (λ u → LetterU {loc} c)
                                                 (λ EmptyU →                 -- ^ soudness ev
                                                   begin
                                                     [ c ]
                                                    ≡⟨⟩
                                                     c ∷ []
                                                    ≡⟨ cong ( λ x → ( c ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                                                     c ∷ (proj₁ (flat EmptyU))
                                                    ∎)
                                                 ] 
...                       | no _     = []
{-
-- shall we move this in to the case of yes ε∈l? 
pdU[ ( l + r ` loc₁ ) ● s ` loc₂ , c ] =
  -- List.map pdinstance-dist pdU[ ( ( l ● s ` loc₂ ) + ( r ● s ` loc₂) ` loc₁ ) , c ]  -- can't pass termination check
  List.map pdinstance-dist ( ( List.map pdinstance-left pdU[ l ● s ` loc₂  , c ] )
                             ++
                             ( List.map pdinstance-right pdU[ r ● s ` loc₂  , c ] ) )
-}                             
pdU[ l ● r ` loc , c ] with ε∈? l
...                       | no ¬ε∈l = List.map pdinstance-fst  pdU[ l , c ]
...                       | yes ε∈l =
                          ( List.map pdinstance-fst pdU[ l , c ] )
                          ++
                          -- ( List.concatMap (pdinstance-snd {l} {r}  {ε∈l} {loc} {c}) pdU[ r , c ]) -- inline concatMap with pdinstance-snd to make it easy to prove
                          concatmap-pdinstance-snd {l} {r}  {ε∈l} {loc} {c} pdU[ r , c ]
pdU[ l + r ` loc , c ] =
  ( List.map pdinstance-left pdU[ l , c ] )
    ++
  ( List.map pdinstance-right pdU[ r , c ])
pdU[ r * nε ` loc , c ] =
  List.map pdinstance-star  pdU[ r , c ]
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

```agda


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
any-recons-concatmap-pdinstance-snd {ϕ} {r} {ε∈l} {loc} {c} {w} {u} {v} proj1-flat-u≡[] _ _  = Nullary.contradiction ε∈l (ε∉r→¬ε∈r ε∉ϕ) -- getting rid of the ϕ so that mkAllEmptyU gives us non-empty list
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



-- intuition: give a parse tree u of r, flat u = c :: w;
-- we must be able to find a PDInstance record in pdU such that u can be reconstruct from w and c.



pdU-complete : ∀ { r : RE  } { c : Char } { w : List Char }
  → ( u : U r )  
  → ( proj₁ (flat {r} u) ≡ c ∷ w )
  → Any (Recons {r} {c} u) pdU[ r , c ] 
-- pdU-complete {ϕ}           {c}  {w} u = λ()
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
 
pdU-complete {l ● s ` loc} {c}  {w} (PairU u v) proj1-flat-pair-u-v≡cw       | yes ε∈l  = prove e1-e2-e3 
  where
    e1-e2-e3 :  ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) 
              ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) ) 
    e1-e2-e3 = inv-flat-pair-snd {l} {s} {ε∈l} {loc} {u} {v} {c} {w} proj1-flat-pair-u-v≡cw 
    prove : ( ∃[ ys ] (proj₁ (flat u) ≡ []) × (proj₁ (flat v) ≡ c ∷ ys ) × ( ys ≡ w ) ) ⊎ ( ∃[ xs ]  ∃[ ys ] (proj₁ (flat u) ≡ c ∷ xs) × (proj₁ (flat v) ≡ ys) × ( xs ++ ys ≡ w ) )
           → Any (Recons {l ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l , c ] ++ (concatmap-pdinstance-snd {- (concatMap pdinstance-snd -}  pdU[ s , c ]))  -- inlined to make it easier to prove
    prove (inj₂ ( xs , ys , proj1-flat-u≡cxs , proj1-flat-v≡ys , refl ) )  = any-left-concat bs
      where 
        as : Any (Recons {l} {c} u) pdU[ l , c ]
        as = pdU-complete {l} {c} {xs} u proj1-flat-u≡cxs   
        bs : Any (Recons { l ● s ` loc} {c} (PairU u v)) (List.map pdinstance-fst pdU[ l , c ])
        bs = any-recons-fst {l} {s} {loc} {c} {w} {u} {v} pdU[ l , c ] as 
    prove (inj₁ ( ys , proj1-flat-u≡[] , proj1-flat-v≡cys , refl ) ) = any-right-concat  bs
      where 
        as : Any (Recons {s} {c} v) pdU[ s , c ] 
        as = pdU-complete {s} {c} {ys} v proj1-flat-v≡cys
        -- bs : Any (Recons { l ● s ` loc} {c} (PairU u v)) (concatMap pdinstance-snd pdU[ s , c ])  -- inlined to make it easier to prove
        bs : Any (Recons { l ● s ` loc} {c} (PairU u v)) (concatmap-pdinstance-snd pdU[ s , c ]) 
        bs = any-recons-concatmap-pdinstance-snd {l} {s} {ε∈l} {loc} {c} {w} {u} {v} proj1-flat-u≡[] pdU[ s , c ] as

    
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
```

### Definition 19: Many steps Partial deriviatves with coercion functions `pdUMany[ r , w ]`


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

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite


{-# REWRITE ∷ʳ-++  #-}

-- the result type for pdUMany, a variant of PDInstance

data PDInstance* : ∀ ( r : RE ) ( pref : List Char ) → Set where
  pdinstance* : ∀ { p r : RE }            -- ^ partial derivative descendant p and input re r
                   { pref : List Char }   -- ^ the  prefix (has been consumed)
                → ( inj : U p → U r )     -- ^ the injection function
                → ( ∀ ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ pref ++ ( proj₁ (flat {p} u) )) ) -- ^ soundness evidence of the inject function
                ------------------------------------------------
                → PDInstance* r pref 
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
 --             pdis'' -- inline for the ease of proof.
 -- where
 --   pdis' : List (PDInstance* r (pref ∷ʳ  c))
 --   pdis' = concatMap (advance-pdi*-with-c {r} {pref} {c}) pdis
    {- inlined the lambda function ino advance-pdi*-with-c 
    pdis' = concatMap ( λ { (pdinstance* {d} {r} {pref} d→r s-ev-d-r) →
            List.map ( λ { (pdinstance {p} {d} {c} p→d s-ev-p-d) →
                           pdinstance* {p} {r} {pref ∷ʳ c } ( d→r ∘ p→d ) 
                                       (
                                        λ u →
                                          begin
                                            proj₁ (flat (d→r (p→d u)))
                                          ≡⟨ s-ev-d-r (p→d u) ⟩
                                            pref ++ proj₁ (flat (p→d u))
                                          ≡⟨ cong ( pref ++_ ) (s-ev-p-d u) ⟩
                                            pref ++ ( c ∷ Product.proj₁ (flat u) )
                                          ≡⟨ sym ( ∷ʳ-++ pref c (Product.proj₁ (flat u)) ) ⟩ 
                                            pref List.∷ʳ c ++ proj₁ (flat u) 
                                          ∎
                                        ) 
                                                                                  
                         } ) pdU[ d , c ]  } ) pdis
                         -} 
    -- pdis'' : List (PDInstance* r (pref ++  ( c ∷ cs )))                         
    -- pdis'' rewrite (cong (λ x → List (PDInstance* r x )) (sym (∷ʳ-++ pref c cs))) = pdUMany-aux {r} {pref ∷ʳ c} cs pdis'

pdUMany[_,_] : ( r : RE ) → ( cs : List Char ) → List (PDInstance* r cs )
pdUMany[ r , cs ]         =
   pdUMany-aux {r} {[]} cs [  ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ]


{-

-- working but too complex, involving existential quantifier 

pdUMany-aux :  ∀ { r : RE } { pref : List Char }
               → (suff : List Char) 
               → List (PDInstance* r pref)
               → ∃[ word ] (List (PDInstance* r word )) × ( word ≡ pref ++ suff )
pdUMany-aux {r} {pref} [] pdis = pref , pdis ,  sym (++-identityʳ pref) 
pdUMany-aux {r} {pref} (c ∷ cs) pdis =
  let
    (word , pdis'' , word≡pref++ccs ) = pdUMany-aux {r} {pref List.∷ʳ c} cs pdis' 
  in ( word , pdis'' , ( 
    begin
      word
    ≡⟨ word≡pref++ccs ⟩
      pref ∷ʳ c ++ cs
    ≡⟨  ∷ʳ-++ pref c cs    ⟩
      pref ++ ( c ∷ cs )
    ∎ ) )
  where
    pdis' : List (PDInstance* r (pref List.∷ʳ  c))
    pdis' = concatMap ( λ { (pdinstance* {d} {r} {pref} d→r s-ev-d-r) →
            List.map ( λ { (pdinstance {p} {d} {c} p→d s-ev-p-d) →
                           pdinstance* {p} {r} {pref List.∷ʳ c } ( d→r ∘ p→d ) 
                                       (
                                        λ u →
                                          begin
                                            proj₁ (flat (d→r (p→d u)))
                                          ≡⟨ s-ev-d-r (p→d u) ⟩
                                            pref ++ proj₁ (flat (p→d u))
                                          ≡⟨ cong ( pref ++_ ) (s-ev-p-d u) ⟩
                                            pref ++ ( c ∷ Product.proj₁ (flat u) )
                                          ≡⟨ sym ( ∷ʳ-++ pref c (Product.proj₁ (flat u)) ) ⟩ 
                                            pref List.∷ʳ c ++ proj₁ (flat u) 
                                          ∎
                                        ) 
                                                                                  
                         } ) pdU[ d , c ]  } ) pdis

pdUMany[_,_] : ( r : RE ) → ( cs : List Char ) → ∃[ word ] (List (PDInstance* r word )) × ( word ≡ cs ) 
pdUMany[ r , cs ]         =
  let ( word , pdis'' , word≡cs ) = pdUMany-aux {r} {[]} cs [  ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ]
  in ( word , pdis'' , word≡cs ) 

-}
```

### Lemma 20 : pdUMany[ r , w ] is sound

Let r  be a non problematic regular expresion.
Let w be a word.
Let p be a partial derivative descendant of r w.r.t c, i.e. p ∈ proj₁ (proj₂ pdUMany[ r , w ] )
Let f be the injection function from parse tree of o to parse tree of r.
Let u be a parse tree of p, then |(f u)| = w ++ | u |, where (f u) is a parse tree of r.


The proof is given as part of the PDInstance* being computed. 


### Definition 21 (Prefix Reconstructability):
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


### Lemma 22 : pdUMany[ r , pref ] is complete (ERROR)

Let r be a non problematic regular expression.
Let pref be a word.
Let u be a parse tree of r such that (flat u) = (pref ++ suff) for some word suff.
Then there exist a partial derivative descendant instance, pdi ∈ pdUMany[r,pref], such that
pdi is u-reconstructable w.r.t pref. 


** note : prefix is the partial input which has been consumed by pdU so far when we just started with pdUMany[ r , suff ], the prefix `pref` is []
** for each step, we take the leading letter c from suffix `suffand snoc it into `pref`.



### Lemma 22 (Fixed) : pdUMany[ r , w ] is complete ** this should by pdUMany-aux-complete?

Let r be a non problematic regular expression.
Let w be a word.
Let u be a parse tree of r such that (flat u) = w.
Then there exist a partial derivative descendant instance, pdi ∈ pdUMany[r, w], such that
pdi is u-reconstructable w.r.t w. 


** note : prefix is the partial input which has been consumed by pdU so far when we just started with pdUMany[ r , suff ], the prefix `pref` is []
** for each step, we take the leading letter c from suffix `suffand snoc it into `pref`.


```agda



-- aux lemmas

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
any-recons*-concatmap-advance-with-c {ϕ} {pref} {c} {cs} = λ() 
any-recons*-concatmap-advance-with-c {r} {pref} {c} {cs} u proj1-flatu≡pref++ccs ( pdi@(pdinstance* {d} {r} {_pref} d→r s-ev-d-r )  ∷ pdis) any-recons*u-pdis
  with any-recons*u-pdis
... | here px@(recons* u' ( w∈⟦d⟧ , d→r-unflat-w∈⟦d⟧≡u' )) = any-left-concat (any-advance-pdi*-with-c {r} {pref} {c} {cs} u proj1-flatu≡pref++ccs pdi px)
... | there pxs = any-right-concat (any-recons*-concatmap-advance-with-c {r} {pref} {c} {cs} u proj1-flatu≡pref++ccs pdis pxs )



-- completeness for pdUMany-aux function 
pdUMany-aux-complete : ∀ { r : RE } { pref : List Char } { suff : List Char }
    → ( u : U r )
    → ( proj₁ (flat {r} u) ≡ pref ++ suff )
    → ( pdis : List (PDInstance* r pref) )
    → Any (Recons* {r} {pref} u) pdis
    → Any (Recons* {r} {pref ++ suff} u) (pdUMany-aux {r} {pref} suff pdis)
pdUMany-aux-complete {r} {pref} {[]}     u proj1-flat-u≡pref      (pdi ∷ pdis) (here (recons* u' ( w∈⟦p⟧ , inj∘unflatw∈⟦p⟧≡u ))) rewrite (++-identityʳ pref) = here (recons* u (w∈⟦p⟧ , inj∘unflatw∈⟦p⟧≡u))   -- base case
pdUMany-aux-complete {r} {pref} {[]}     u proj1-flat-u≡pref      (pdi ∷ pdis) (there pxs) rewrite (++-identityʳ pref) = there pxs   -- base case
pdUMany-aux-complete {ϕ} {pref} {suff}   = λ() 
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




-- main lemma   
pdUMany-complete : ∀ { r : RE }
  → ( u : U r )
  → Any (Recons* {r} {proj₁ (flat u)} u) pdUMany[ r , proj₁ (flat u) ]
pdUMany-complete {r} u =
  pdUMany-aux-complete {r} {[]} {proj₁ (flat u)} u refl 
    [  ( pdinstance* {r} {r} {[]} (λ u → u) (λ u → refl) ) ]
    ( here (recons* {r} {r} {proj₁ (flat u)} {[]}  u (proj₂ (flat u),  unflat∘proj₂∘flat ) ) )



```

### Definition 22: ParseAll function

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

```
should yield

~~~~~~~
PairU (ListU (LetterU 'a' ∷ [])) (ListU []) ∷
PairU (ListU []) (ListU (LetterU 'a' ∷ [])) ∷ []
~~~~~~~

### Lemma 24 : buildU is sound
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

### Theorem 25 : ParseAll is sound 

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


### Lemma 25 : buildU is complete

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




### Theorem 26 : ParseAll is complete

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
