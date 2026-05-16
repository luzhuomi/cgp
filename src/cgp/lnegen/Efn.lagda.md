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
open Nat using ( ℕ ; suc ; zero ; _+_ ; _<_ )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; _≟_ ; +-identityˡ )



import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_ ; length )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalʳ ; ++-conicalˡ ; length-++ )


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


-- not in used,  it got stuck below
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

    sound-ev-len : ∀ (u : U (p ● t ` loc')) → length (proj₁ (flat (inj u))) ≡ suc (length (proj₁ (flat u)))
    sound-ev-len u rewrite sound-ev u = refl

    >-inc-ev (PairU u₁ v₁) (PairU u₂ v₂) len|uv₁|≡len|uv₂| (be len|pair-u₁v₁|≡len|pair-u₂v₂| len|pair-u₂v₂|≡0 (seq₁ u₁>u₂))
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (u₁→u₂→u₁>u₂→inj-u₁>inj-u₂ u₁ u₂ len|u₁|≡len|u₂| u₁>u₂))
      where
        flat-u₂v₂≡[] : proj₁ (flat (PairU {p ● t ` loc'} {r} {loc}  u₂ v₂)) ≡ []
        flat-u₂v₂≡[] = Utils.length≡0→[] len|pair-u₂v₂|≡0
        flat-u₂≡[] : proj₁ (flat u₂) ≡ []
        flat-u₂≡[] = ++-conicalˡ (proj₁ (flat u₂)) (proj₁ (flat v₂)) flat-u₂v₂≡[]
        flat-u₁v₁≡[] : proj₁ (flat (PairU {p ● t ` loc'} {r} {loc} u₁ v₁)) ≡ []
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


```agda
data >-Inc : ∀ { r : RE } { c : Char } →  PDInstance r c  → Set where
  >-inc : ∀ { p r : RE } { c : Char } { inj : U p →  U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → Efn p
    → ( (v₁ : U p) → (v₂ : U p)
        → proj₁ (flat v₁) ≡ proj₁ (flat v₂)
        →  p ⊢ v₁ > v₂ → r ⊢ inj v₁ > inj v₂ )
    → >-Inc {r} {c} (pdinstance {p} {r} {c} inj sound-ev)

>-inc-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
                → ( pdi : PDInstance l c )
                → >-Inc {l} {c} pdi
                ------------------------
                → >-Inc {l ● r ` loc} {c} (pdinstance-fst {l} {r} {loc} {c} pdi)

>-inc-fst {l} {r} {loc} {c} (pdinstance {l'} {l} {c} inj sound-ev) (>-inc efn-l inc-bne inc-lne inc-be) = >-inc (efn-● efn-l) inc-bne-fst inc-lne-fst inc-be-fst
  where
    injFst : U (l' ● r ` loc) → U (l ● r ` loc)
    injFst = mkinjFst inj

    injFstSnd : (u : U (l' ● r ` loc)) → proj₁ (flat (injFst u)) ≡ c ∷ proj₁ (flat u)
    injFstSnd = mkinjFstSoundEv inj sound-ev

    |injFst-pair-u-v|>0 : ∀ {u v} → length (proj₁ (flat (PairU {l} {r} {loc} (inj u) v))) Nat.> 0
    |injFst-pair-u-v|>0 {u} {v} rewrite injFstSnd (PairU u v) = Nat.s≤s Nat.z≤n

    sound-ev-len : ∀ (u : U l') → length (proj₁ (flat (inj u))) ≡ suc (length (proj₁ (flat u)))
    sound-ev-len u rewrite sound-ev u = refl

    flat-pair : ∀ {l₁ r₁ loc₁} (u : U l₁) (v : U r₁) → proj₁ (flat (PairU u v)) ≡ proj₁ (flat u) ++ proj₁ (flat v)
    flat-pair u v with flat u | flat v
    flat-pair u v | xs , _ | ys , _ = refl

    >-inc-seq₁-bne : ∀ (u₁ u₂ : U l') (v₁ v₂ : U r)
                     → length (proj₁ (flat u₁)) ≢ 0
                     → length (proj₁ (flat u₂)) ≢ 0
                     → l' ● r ` loc ⊢ PairU u₁ v₁ >ⁱ PairU u₂ v₂
                     → l ● r ` loc ⊢ PairU (inj u₁) v₁ >ⁱ PairU (inj u₂) v₂
    >-inc-seq₁-bne u₁ u₂ v₁ v₂ ¬u₁≡0 ¬u₂≡0 (seq₁ (be len-u₁-u₂ u₂≡0 u₁>ⁱu₂))
      = seq₁ (inc-be u₁ u₂ len-u₁-u₂ (be len-u₁-u₂ u₂≡0 u₁>ⁱu₂))
    >-inc-seq₁-bne u₁ u₂ v₁ v₂ ¬u₁≡0 ¬u₂≡0 (seq₁ (bne u₁>0' u₂>0' u₁>ⁱu₂))
      = seq₁ (inc-bne u₁ u₂ (¬≡0→>0 ¬u₁≡0) (¬≡0→>0 ¬u₂≡0) (bne u₁>0' u₂>0' u₁>ⁱu₂))
    >-inc-seq₁-bne u₁ u₂ v₁ v₂ ¬u₁≡0 ¬u₂≡0 (seq₁ (lne u₁>0' u₂≡0))
      = ⊥-elim (n≡0→¬n>0 u₂≡0 (¬≡0→>0 ¬u₂≡0))
    >-inc-seq₁-bne u₁ u₂ v₁ v₂ _ _ (seq₂ u₁≡u₂ v₁>v₂) = seq₂ (cong inj u₁≡u₂) v₁>v₂

    >-inc-seq₁-lne : ∀ (u₁ u₂ : U l') (v₁ v₂ : U r)
                     → length (proj₁ (flat u₁)) ≢ 0
                     → length (proj₁ (flat u₂)) ≡ 0
                     → l' ● r ` loc ⊢ PairU u₁ v₁ >ⁱ PairU u₂ v₂
                     → l ● r ` loc ⊢ PairU (inj u₁) v₁ >ⁱ PairU (inj u₂) v₂
    >-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 (seq₁ (be len-u₁-u₂ u₂≡0' u₁>ⁱu₂))
      = ⊥-elim (n≡0→¬n>0 (trans len-u₁-u₂ u₂≡0') (¬≡0→>0 ¬u₁≡0))
    >-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 (seq₁ (bne u₁>0' u₂>0' u₁>ⁱu₂))
      = ⊥-elim (n≡0→¬n>0 u₂≡0 u₂>0')
    >-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 (seq₁ (lne u₁>0' u₂≡0'))
      = seq₁ (inc-lne u₁ u₂ (¬≡0→>0 ¬u₁≡0) u₂≡0 (lne u₁>0' u₂≡0'))
    >-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 (seq₂ u₁≡u₂ v₁>v₂)
      = ⊥-elim (n≡0→¬n>0 (trans (cong (length ∘ proj₁ ∘ flat) u₁≡u₂) u₂≡0) (¬≡0→>0 ¬u₁≡0))

    >-inc-seq₁-be : ∀ (u₁ u₂ : U l') (v₁ v₂ : U r)
                    → length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
                    → l' ● r ` loc ⊢ PairU u₁ v₁ >ⁱ PairU u₂ v₂
                    → l ● r ` loc ⊢ PairU (inj u₁) v₁ >ⁱ PairU (inj u₂) v₂
    >-inc-seq₁-be u₁ u₂ v₁ v₂ len-u₁-u₂ (seq₁ (be len-u₁-u₂' u₂≡0 u₁>ⁱu₂))
      = seq₁ (inc-be u₁ u₂ len-u₁-u₂ (be len-u₁-u₂' u₂≡0 u₁>ⁱu₂))
    >-inc-seq₁-be u₁ u₂ v₁ v₂ len|u₁|≡len|u₂| (seq₁ (bne u₁>0 u₂>0 u₁>ⁱu₂))
      = seq₁ (inc-bne u₁ u₂ u₁>0 u₂>0 (bne u₁>0 u₂>0 u₁>ⁱu₂))
    >-inc-seq₁-be u₁ u₂ v₁ v₂ len-u₁-u₂ (seq₁ (lne u₁>0 u₂≡0))
      = ⊥-elim (n≡0→¬n>0 (trans len-u₁-u₂ u₂≡0) u₁>0)
    >-inc-seq₁-be u₁ u₂ v₁ v₂ len|u₁|≡len|u₂| (seq₂ u₁≡u₂ v₁>v₂) = seq₂ (cong inj u₁≡u₂) v₁>v₂

    inc-bne-fst : ∀ (uv₁ uv₂ : U (l' ● r ` loc))
                  → length (proj₁ (flat uv₁)) Nat.> 0
                  → length (proj₁ (flat uv₂)) Nat.> 0
                  → l' ● r ` loc ⊢ uv₁ > uv₂
                  → l ● r ` loc ⊢ injFst uv₁ > injFst uv₂
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ >ⁱ)
      with length (proj₁ (flat u₁)) ≟ 0 | length (proj₁ (flat u₂)) ≟ 0
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ >ⁱ) | yes u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-be u₁ u₂ v₁ v₂ (trans u₁≡0 (sym u₂≡0)) >ⁱ)
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ >ⁱ) | no ¬u₁≡0 | no ¬u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-bne u₁ u₂ v₁ v₂ ¬u₁≡0 ¬u₂≡0 >ⁱ)
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ >ⁱ) | no ¬u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 >ⁱ)
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ (seq₁ u₁>u₂)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (bne-impossible u₁>u₂)
      where
        bne-impossible : l' ⊢ u₁ > u₂ → ⊥
        bne-impossible (be l≡ l0 _) = ¬u₂≡0 l0
        bne-impossible (bne l>0 l0' _) = n≡0→¬n>0 u₁≡0 l>0
        bne-impossible (lne l>0 l0) = n≡0→¬n>0 u₁≡0 l>0
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ (seq₂ u₁≡u₂ _)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 u₂≡0)
      where
        u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
        u₂≡0 rewrite trans (cong (length ∘ proj₁ ∘ flat) (sym u₁≡u₂)) u₁≡0 = refl
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be _ _ >ⁱ)
      with length (proj₁ (flat u₁)) ≟ 0 | length (proj₁ (flat u₂)) ≟ 0
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be _ _ >ⁱ) | yes u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-be u₁ u₂ v₁ v₂ (trans u₁≡0 (sym u₂≡0)) >ⁱ)
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be len-pair-≡ len-u2v2-≡0 >ⁱ) | no ¬u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 len-u₂-≡0)
      where
        len-u₂-≡0 : length (proj₁ (flat u₂)) ≡ 0
        len-u₂-≡0 = Utils.[]→length≡0 (++-conicalˡ (proj₁ (flat u₂)) (proj₁ (flat v₂)) (Utils.length≡0→[] len-u2v2-≡0))
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be _ _ >ⁱ) | no ¬u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 >ⁱ)
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be _ _ (seq₁ u₁>u₂)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (bne-impossible u₁>u₂)
      where
        bne-impossible : l' ⊢ u₁ > u₂ → ⊥
        bne-impossible (be l≡ l0 _) = ¬u₂≡0 l0
        bne-impossible (bne l>0 l0' _) = n≡0→¬n>0 u₁≡0 l>0
        bne-impossible (lne l>0 l0) = n≡0→¬n>0 u₁≡0 l>0
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be _ _ (seq₂ u₁≡u₂ _)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 u₂≡0)
      where
        u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
        u₂≡0 rewrite trans (cong (length ∘ proj₁ ∘ flat) (sym u₁≡u₂)) u₁≡0 = refl
    inc-bne-fst (PairU u₁ v₁) (PairU u₂ v₂) u₁>0 u₂>0 (lne _ u₂≡0)
      = ⊥-elim (n≡0→¬n>0 u₂≡0 u₂>0)

    inc-lne-fst : ∀ (uv₁ uv₂ : U (l' ● r ` loc))
                  → length (proj₁ (flat uv₁)) Nat.> 0
                  → length (proj₁ (flat uv₂)) ≡ 0
                  → l' ● r ` loc ⊢ uv₁ > uv₂
                  → l ● r ` loc ⊢ injFst uv₁ > injFst uv₂
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ >ⁱ)
      with length (proj₁ (flat u₁)) ≟ 0 | length (proj₁ (flat u₂)) ≟ 0
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ >ⁱ) | yes u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-be u₁ u₂ v₁ v₂ (trans u₁≡0 (sym u₂≡0)) >ⁱ)
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ >ⁱ) | no ¬u₁≡0 | no ¬u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-bne u₁ u₂ v₁ v₂ ¬u₁≡0 ¬u₂≡0 >ⁱ)
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ >ⁱ) | no ¬u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 >ⁱ)
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ (seq₁ u₁>u₂)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (bne-impossible u₁>u₂)
      where
        bne-impossible : l' ⊢ u₁ > u₂ → ⊥
        bne-impossible (be l≡ l0 _) = ¬u₂≡0 l0
        bne-impossible (bne l>0 l0' _) = n≡0→¬n>0 u₁≡0 l>0
        bne-impossible (lne l>0 l0) = n≡0→¬n>0 u₁≡0 l>0
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (bne _ _ (seq₂ u₁≡u₂ _)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 u₂≡0)
      where
        u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
        u₂≡0 rewrite trans (cong (length ∘ proj₁ ∘ flat) (sym u₁≡u₂)) u₁≡0 = refl
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be _ _ >ⁱ)
      with length (proj₁ (flat u₁)) ≟ 0 | length (proj₁ (flat u₂)) ≟ 0
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be _ _ >ⁱ) | yes u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-be u₁ u₂ v₁ v₂ (trans u₁≡0 (sym u₂≡0)) >ⁱ)
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be len-pair-≡ len-u2v2-≡0 >ⁱ) | no ¬u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 len-u₂-≡0)
      where
        len-u₂-≡0 : length (proj₁ (flat u₂)) ≡ 0
        len-u₂-≡0 = Utils.[]→length≡0 (++-conicalˡ (proj₁ (flat u₂)) (proj₁ (flat v₂)) (Utils.length≡0→[] len-u2v2-≡0))
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be _ _ >ⁱ) | no ¬u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 >ⁱ)
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be _ _ (seq₁ u₁>u₂)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (bne-impossible u₁>u₂)
      where
        bne-impossible : l' ⊢ u₁ > u₂ → ⊥
        bne-impossible (be l≡ l0 _) = ¬u₂≡0 l0
        bne-impossible (bne l>0 l0' _) = n≡0→¬n>0 u₁≡0 l>0
        bne-impossible (lne l>0 l0) = n≡0→¬n>0 u₁≡0 l>0
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (be _ _ (seq₂ u₁≡u₂ _)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 u₂≡0)
      where
        u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
        u₂≡0 rewrite trans (cong (length ∘ proj₁ ∘ flat) (sym u₁≡u₂)) u₁≡0 = refl
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (lne _ _)
      with length (proj₁ (flat u₁)) ≟ 0 | length (proj₁ (flat u₂)) ≟ 0
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (lne uv₁>0 uv₂≡0) | yes u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (seq₁ (lne inj-u₁>0 inj-u₂≡0))
      where
        inj-u₁>0 : length (proj₁ (flat (inj u₁))) Nat.> 0
        inj-u₁>0 rewrite sound-ev u₁ = Nat.s≤s Nat.z≤n
        inj-u₂≡0 : length (proj₁ (flat (inj u₂))) ≡ 0
        inj-u₂≡0 rewrite sound-ev u₂ rewrite u₂≡0 = refl
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (lne uv₁>0 uv₂≡0) | no ¬u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 (seq₁ (lne (¬≡0→>0 ¬u₁≡0) u₂≡0)))
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (lne _ uv₂≡0) | no ¬u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 u₂≡0)
      where
        flat-u₂v₂≡[] : proj₁ (flat (PairU u₂ v₂)) ≡ []
        flat-u₂v₂≡[] = Utils.length≡0→[] uv₂≡0
        flat-u₂≡[] : proj₁ (flat u₂) ≡ []
        flat-u₂≡[] = ++-conicalˡ (proj₁ (flat u₂)) (proj₁ (flat v₂)) (trans (sym (flat-pair u₂ v₂)) flat-u₂v₂≡[])
        u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
        u₂≡0 = Utils.[]→length≡0 flat-u₂≡[]
    inc-lne-fst (PairU u₁ v₁) (PairU u₂ v₂) _ _ (lne _ u₂v₂≡0) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 u₂≡0)
      where
        u₂-flat-uv₂ : length (proj₁ (flat (PairU u₂ v₂))) ≡ length (proj₁ (flat u₂))
        u₂-flat-uv₂ = trans (trans (cong length (flat-pair u₂ v₂)) (length-++ (proj₁ (flat u₂)))) (sym (+-identityˡ (length (proj₁ (flat u₂)))))
        u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
        u₂≡0 = trans (sym u₂-flat-uv₂) u₂v₂≡0

    inc-be-fst : ∀ (uv₁ uv₂ : U (l' ● r ` loc))
                 → length (proj₁ (flat uv₁)) ≡ length (proj₁ (flat uv₂))
                 → l' ● r ` loc ⊢ uv₁ > uv₂
                 → l ● r ` loc ⊢ injFst uv₁ > injFst uv₂
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ >ⁱ)
      with length (proj₁ (flat u₁)) ≟ 0 | length (proj₁ (flat u₂)) ≟ 0
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ >ⁱ) | yes u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-be u₁ u₂ v₁ v₂ (trans u₁≡0 (sym u₂≡0)) >ⁱ)
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ >ⁱ) | no ¬u₁≡0 | no ¬u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-bne u₁ u₂ v₁ v₂ ¬u₁≡0 ¬u₂≡0 >ⁱ)
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ >ⁱ) | no ¬u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 >ⁱ)
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ (seq₁ u₁>u₂)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (bne-impossible u₁>u₂)
      where
        bne-impossible : l' ⊢ u₁ > u₂ → ⊥
        bne-impossible (be l≡ l0 _) = ¬u₂≡0 l0
        bne-impossible (bne l>0 l0' _) = n≡0→¬n>0 u₁≡0 l>0
        bne-impossible (lne l>0 l0) = n≡0→¬n>0 u₁≡0 l>0
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (bne _ _ (seq₂ u₁≡u₂ _)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 u₂≡0)
      where
        u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
        u₂≡0 rewrite trans (cong (length ∘ proj₁ ∘ flat) (sym u₁≡u₂)) u₁≡0 = refl
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ >ⁱ)
      with length (proj₁ (flat u₁)) ≟ 0 | length (proj₁ (flat u₂)) ≟ 0
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ >ⁱ) | yes u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-be u₁ u₂ v₁ v₂ (trans u₁≡0 (sym u₂≡0)) >ⁱ)
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be len-pair-≡ len-u2v2-≡0 >ⁱ) | no ¬u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 len-u₂-≡0)
      where
        len-u₂-≡0 : length (proj₁ (flat u₂)) ≡ 0
        len-u₂-≡0 = Utils.[]→length≡0 (++-conicalˡ (proj₁ (flat u₂)) (proj₁ (flat v₂)) (Utils.length≡0→[] len-u2v2-≡0))
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ >ⁱ) | no ¬u₁≡0 | yes u₂≡0
      = bne |injFst-pair-u-v|>0 |injFst-pair-u-v|>0 (>-inc-seq₁-lne u₁ u₂ v₁ v₂ ¬u₁≡0 u₂≡0 >ⁱ)
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ (seq₁ u₁>u₂)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (bne-impossible u₁>u₂)
      where
        bne-impossible : l' ⊢ u₁ > u₂ → ⊥
        bne-impossible (be l≡ l0 _) = ¬u₂≡0 l0
        bne-impossible (bne l>0 l0' _) = n≡0→¬n>0 u₁≡0 l>0
        bne-impossible (lne l>0 l0) = n≡0→¬n>0 u₁≡0 l>0
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (be _ _ (seq₂ u₁≡u₂ _)) | yes u₁≡0 | no ¬u₂≡0
      = ⊥-elim (¬u₂≡0 u₂≡0)
      where
        u₂≡0 : length (proj₁ (flat u₂)) ≡ 0
        u₂≡0 rewrite trans (cong (length ∘ proj₁ ∘ flat) (sym u₁≡u₂)) u₁≡0 = refl
    inc-be-fst (PairU u₁ v₁) (PairU u₂ v₂) uv₁≡uv₂ (lne uv₁>0 uv₂≡0)
      = ⊥-elim (n≡0→¬n>0 (trans uv₁≡uv₂ uv₂≡0) uv₁>0)
```
