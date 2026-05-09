This module contains  the attempt of proving monotoncity of the pd injection over lnegen ordering by restricting to epsilon first normal form efn

```agda
{-# OPTIONS --rewriting  #-}

module cgp.lnegen.Efn where
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
open Order -- we should only white list those are used here 


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

```agda
-- epsilon first normal form
-- does not work, look at the comment "stuck here" below 

data Efn : ∀ (r : RE ) → Set where
  efn-ε : Efn ε
  efn-● : ∀ { p r : RE } { loc : ℕ }
    → Efn p
    ----------------------
    → Efn (p ● r ` loc)

data EfnPDInstance : ∀ {r : RE } { c : Char } → PDInstance r c → Set where
  efn-pdi : ∀ { p r : RE } { c : Char }
    → ( inj : U p → U r ) 
    → ( s-ev : ( u : U p ) → proj₁ (flat (inj u)) ≡ c ∷ proj₁ (flat u))
    → Efn p
    → EfnPDInstance {r} {c} (pdinstance {p} {r} {c} inj s-ev)

pdU-isEnf : ∀ { r : RE } { c : Char }
  → All (EfnPDInstance {r} {c}) pdU[ r , c ]
pdU-isEnf = {!!} 

data >-Inc-efn : ∀ { r : RE } { c : Char } →  PDInstance r c  → Set where
  >-inc-efn : ∀ { p r : RE } { c : Char } { inj : U p →  U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → Efn p 
    → ( (u₁ : U p) → (u₂ : U p)
        → length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
        →  p ⊢ u₁ > u₂ → r ⊢ inj u₁ > inj u₂ ) -- strict increasing evidence 
    → >-Inc-efn {r} {c} (pdinstance {p} {r} {c} inj sound-ev)

>-inc-fst-efn : ∀ { l r : RE } { loc : ℕ } { c : Char }
               → ( pdi : PDInstance l c )
               → >-Inc-efn {l} {c} pdi
               ------------------------
               → >-Inc-efn {l ● r ` loc} {c} (pdinstance-fst {l} {r} {loc} {c} pdi)
>-inc-fst-efn {l} {r} {loc} {c} (pdinstance {ε} {l} {c}  inj sound-ev) (>-inc-efn efn-ε u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) = >-inc-efn (efn-● efn-ε) >-inc-ev
  where
    injFst : U (ε ● r ` loc)   → U (l ● r ` loc ) -- the p can only be seq ε or ●
    injFst = mkinjFst inj
    injFstSnd :  ( u : U (ε ● r ` loc) )  → proj₁ (flat (injFst u))  ≡ c ∷ proj₁ (flat u)
    injFstSnd = mkinjFstSoundEv inj sound-ev
    >-inc-ev : ∀ (uv₁ : U ( ε ● r ` loc ))
              → (uv₂ : U ( ε ● r ` loc ))
              → length (proj₁ (flat uv₁)) ≡ length (proj₁ (flat uv₂))
              → ε ● r ` loc  ⊢ uv₁ > uv₂
              ------------------------------------
              → l ● r ` loc ⊢ (injFst uv₁) > (injFst uv₂)

    |injFst-pair-u-v|>0 : ∀ {u v} → length (proj₁ (flat (PairU {l} {r} {loc} (inj u) v))) Nat.> 0
    |injFst-pair-u-v|>0 {u} {v} rewrite injFstSnd (PairU u v) = Nat.s≤s Nat.z≤n

    >-inc-ev (PairU EmptyU v₁) (PairU EmptyU v₂) _ (be _ len|pair-u₂v₂|≡0 (seq₂ refl v₁>v₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₂ refl v₁>v₂)
    >-inc-ev (PairU EmptyU v₁) (PairU EmptyU v₂) _ (be _ _ (seq₁ u₁>u₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ EmptyU EmptyU refl u₁>u₂))
    >-inc-ev (PairU EmptyU v₁) (PairU EmptyU v₂) _ (bne _ _ (seq₂ refl v₁>v₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₂ refl v₁>v₂)
    >-inc-ev (PairU EmptyU v₁) (PairU EmptyU v₂) _ (bne _ _ (seq₁ u₁>u₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ EmptyU EmptyU refl u₁>u₂))
    >-inc-ev (PairU EmptyU v₁) (PairU EmptyU v₂) _ (lne len|pair-u₁v₁|>0 len|pair-u₂v₂|≡0)
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₂ refl (lne len|pair-u₁v₁|>0 len|pair-u₂v₂|≡0))


>-inc-fst-efn {l} {r} {loc} {c} (pdinstance {p ● t ` loc'} {l} {c}  inj sound-ev) (>-inc-efn (efn-● efn-p) u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) = >-inc-efn (efn-● (efn-● efn-p)) >-inc-ev
  where
    injFst : U (( p ● t ` loc') ● r ` loc)   → U (l ● r ` loc ) -- the p can only be seq ε or ●
    injFst = mkinjFst inj
    injFstSnd :  ( u : U (( p ● t ` loc') ● r ` loc) )  → proj₁ (flat (injFst u))  ≡ c ∷ proj₁ (flat u)
    injFstSnd = mkinjFstSoundEv inj sound-ev
    >-inc-ev : ∀ (uv₁ : U ( ( p ● t ` loc') ● r ` loc ))
              → (uv₂ : U ( ( p ● t ` loc') ● r ` loc ))
              → length (proj₁ (flat uv₁)) ≡ length (proj₁ (flat uv₂))
              → ( p ● t ` loc') ● r ` loc  ⊢ uv₁ > uv₂
              ------------------------------------
              → l ● r ` loc ⊢ (injFst uv₁) > (injFst uv₂)

    |injFst-pair-u-v|>0 : ∀ {u v} → length (proj₁ (flat (PairU {l} {r} {loc} (inj u) v))) Nat.> 0
    |injFst-pair-u-v|>0 {u} {v} rewrite injFstSnd (PairU u v) = Nat.s≤s Nat.z≤n

    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) len|uv₁|≡len|uv₂| (be len|pair-u₁v₁|≡len|pair-u₂v₂| len|pair-u₂v₂|≡0 (seq₁ u₁>u₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ len|u₁|≡len|u₂| u₁>u₂))
      where
        flat-u₂v₂≡[] : proj₁ (flat (PairU u₂ v₂)) ≡ []
        flat-u₂v₂≡[] = Utils.length≡0→[] len|pair-u₂v₂|≡0
        flat-u₂≡[] : proj₁ (flat u₂) ≡ []
        flat-u₂≡[] = ++-conicalˡ (proj₁ (flat u₂)) (proj₁ (flat v₂)) flat-u₂v₂≡[]
        flat-u₁v₁≡[] : proj₁ (flat (PairU u₁ v₁)) ≡ []
        flat-u₁v₁≡[] = Utils.length≡0→[] (trans len|pair-u₁v₁|≡len|pair-u₂v₂| len|pair-u₂v₂|≡0)
        flat-u₁≡[] : proj₁ (flat u₁) ≡ []
        flat-u₁≡[] = ++-conicalˡ (proj₁ (flat u₁)) (proj₁ (flat v₁)) flat-u₁v₁≡[]
        len|u₁|≡len|u₂| : length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
        len|u₁|≡len|u₂| = trans (cong length flat-u₁≡[]) (sym (cong length flat-u₂≡[]))
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) _ (be _ _ (seq₂ u₁≡u₂ v₁>v₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₂ (cong inj u₁≡u₂) v₁>v₂)
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) _ (bne _ _ (seq₁ u₁>u₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ len|u₁|≡len|u₂| u₁>u₂))
      where
        len|u₁|≡len|u₂| : length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
        len|u₁|≡len|u₂| = {!!} -- stuck here
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) _ (bne _ _ (seq₂ u₁≡u₂ v₁>v₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₂ (cong inj u₁≡u₂) v₁>v₂)
    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) len|pair-u₁v₁|≡len|pair-u₂v₂| (lne len|pair-u₁v₁|>0 len|pair-u₂v₂|≡0) =  Nullary.contradiction len|pair-u₁v₁|>0  (n≡0→¬n>0  len|pair-u₁v₁|≡0) 
      where
        len|pair-u₁v₁|≡0 : length (proj₁ (flat (PairU u₁ v₁))) ≡ 0
        len|pair-u₁v₁|≡0 rewrite len|pair-u₁v₁|≡len|pair-u₂v₂| = len|pair-u₂v₂|≡0

    {-
      with length (proj₁ (flat u₁)) Nat.≟ 0
    ... | no ¬len|u₁|≡0 = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ len|u₁|≡len|u₂| (lne (Utils.¬≡0→>0 ¬len|u₁|≡0) len|u₂|≡0)))
      where
        len|u₂|≡0 : length (proj₁ (flat u₂)) ≡ 0
        len|u₂|≡0 = Utils.[]→length≡0 (++-conicalˡ (proj₁ (flat u₂)) (proj₁ (flat v₂)) (Utils.length≡0→[] len|pair-u₂v₂|≡0))
        len|u₁|≡len|u₂| : length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
        len|u₁|≡len|u₂| = {!!}
    ... | yes len|u₁|≡0 = {!!}  -- COUNTEREXAMPLE: when u₁ is empty but differs from u₂ (e.g. p = ε ● ((ε + $d) + (ε + $d)) with u₁ = PairU EmptyU (RightU (LeftU EmptyU)) and u₂ = PairU EmptyU (LeftU (RightU EmptyU))), the goal is unprovable because seq₂ requires inj u₁ ≡ inj u₂ and seq₁ requires an ordering in l that may not exist.
 -}



```

