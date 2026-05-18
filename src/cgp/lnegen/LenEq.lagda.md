This module contains the attempt of proving PD Injection monotonicity over lnegen ordering by restricting to same length equivalence form.


```agda
{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module cgp.lnegen.LenEq where
import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ¬≡[]→length>0 ; ¬≡0→>0 ; length≡0→[] ; n≡0→¬n>0 
 )


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; ListU ; unListU ; flat ; unflat ; unflat∘proj₂∘flat ; flat∘unflat ; RightU≢LeftU ; inv-pairU ) 

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

open import Data.List.Relation.Unary.Any using (Any; here; there ; map)


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

### Definition 32: >-Strict increasing PDInstance (length-equality variant)

Let r be a non problematic regular expression.
Let c be a letter.
Let pdi be a PDInstance  w.r.t r and c.
We say pdi is >-inc (strict increasing) iff,
  1. p is the partial derivative inhabited in pdi, and
  2. inj is the injection function from parse trees of p to parse trees of r.
  3. for all parse trees of p, u₁ and u₂  where
       length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
       and p ⊢ u₁ > u₂
     Then r ⊢ inj u₁ > inj u₂

```agda

data >-Inc : ∀ { r : RE } { c : Char } →  PDInstance r c  → Set where
  >-inc : ∀ { p r : RE } { c : Char } { inj : U p →  U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( (u₁ : U p) → (u₂ : U p)
        → length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
        →  p ⊢ u₁ > u₂  → r ⊢ inj u₁ > inj u₂ ) -- strict increasing evidence
    → >-Inc {r} {c} (pdinstance {p} {r} {c} inj sound-ev)


```

### Counterexample: `>-inc-fst` is unprovable even with length equality

The length-equality premise is not strong enough.

Regular expressions:
- `l = ($ 'c') + (($ 'c') ● ($ 'c'))`
- `r = ε + ($ 'c')`
- `p = ε + ($ 'c')`

The injection maps two trees of `p` with different lengths:
- `LeftU EmptyU` (len 0) → `LeftU (LetterU 'c')` (len 1)
- `RightU (LetterU 'c')` (len 1) → `RightU (PairU (LetterU 'c') (LetterU 'c'))` (len 2)

Key insight: `U p` has trees of different lengths (0 and 1), so
`>-Inc pdi` holds vacuously.  But in `p ● r`, we pair them with
complementary lengths in `r` to get equal total lengths.  The ordering
uses `seq₁` via `lne` (first component with len 1 > first component
with len 0).  After `mkinjFst`, both first components become
`RightU` vs `LeftU` in `l`, and `l ⊢ RightU > LeftU` is impossible
since only `choice-lr` (LeftU > RightU) exists.

```agda
module CounterExample-LenEq where

  l : RE
  l = ($ 'c' ` 1) + (($ 'c' ` 2) ● ($ 'c' ` 3) ` 4) ` 5

  r : RE
  r = ε + ($ 'c' ` 7) ` 8

  p : RE
  p = ε + ($ 'c' ` 6) ` 9

  inj : U p → U l
  inj (LeftU EmptyU) = LeftU (LetterU 'c')
  inj (RightU (LetterU _)) = RightU (PairU (LetterU 'c') (LetterU 'c'))

  sound-ev : ∀ (u : U p) → proj₁ (flat (inj u)) ≡ 'c' ∷ proj₁ (flat u)
  sound-ev (LeftU EmptyU) = refl
  sound-ev (RightU (LetterU _)) = refl

  pdi : PDInstance l 'c'
  pdi = pdinstance inj sound-ev
```

**Step 1: `pdi` satisfies the length-restricted `>-Inc`.**

`U p` has trees of lengths 0 and 1.  No equal-length non-reflexive
pair exists, so `>-Inc` is vacuous.

```agda
  pdi->-inc : >-Inc pdi
  pdi->-inc = >-inc (λ where
    (LeftU EmptyU) (LeftU EmptyU) _ p⊢> → ⊥-elim (>→¬≡ p⊢> refl)
    (RightU (LetterU _)) (RightU (LetterU _)) _ p⊢> → ⊥-elim (>→¬≡ p⊢> refl)
    (LeftU EmptyU) (RightU (LetterU _)) len≡ _ → ⊥-elim (¬0≡1 len≡)
    (RightU (LetterU _)) (LeftU EmptyU) len≡ _ → ⊥-elim (¬1≡0 len≡))
    where
      ¬0≡1 : ¬ (0 ≡ 1)
      ¬0≡1 ()
      ¬1≡0 : ¬ (1 ≡ 0)
      ¬1≡0 ()
```

**Step 2: a pair in `U (p ● r)` with equal lengths that is ordered.**

`top` pairs the len-1 tree of `p` with the len-0 tree of `r`.
`x` pairs the len-0 tree of `p` with the len-1 tree of `r`.
Both have total length 1, and `top > x` via `seq₁` using `lne`
(len 1 > len 0 in `p`).

```agda
  top : U (p ● r ` 10)
  top = PairU (RightU (LetterU 'c')) (LeftU EmptyU)

  x : U (p ● r ` 10)
  x = PairU (LeftU EmptyU) (RightU (LetterU 'c'))

  len|top|≡len|x| : length (proj₁ (flat top)) ≡ length (proj₁ (flat x))
  len|top|≡len|x| = refl

  p⊢RightU>LeftU : p ⊢ RightU (LetterU 'c') > LeftU EmptyU
  p⊢RightU>LeftU = lne (Nat.s≤s Nat.z≤n) refl

  p●r⊢top>x : (p ● r ` 10) ⊢ top > x
  p●r⊢top>x = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ p⊢RightU>LeftU)
```

**Step 3: after `pdinstance-fst` the ordering disappears.**

`injFst top` has first component `RightU (PairU ...)` and
`injFst x` has first component `LeftU (LetterU ...)`.
`seq₁` needs `l ⊢ RightU > LeftU` (impossible, only `choice-lr`
gives `LeftU > RightU`).  `seq₂` needs `RightU ≡ LeftU` (false).

```agda
  injFst : U (p ● r ` 10) → U (l ● r ` 10)
  injFst = mkinjFst inj

  len|injFst-top|>0 : length (proj₁ (flat (injFst top))) Nat.> 0
  len|injFst-top|>0 = Nat.s≤s Nat.z≤n

  len|injFst-x|>0 : length (proj₁ (flat (injFst x))) Nat.> 0
  len|injFst-x|>0 = Nat.s≤s Nat.z≤n

  ¬l⊢RightU>LeftU : ¬ (l ⊢ RightU (PairU (LetterU 'c') (LetterU 'c')) > LeftU (LetterU 'c'))
  ¬l⊢RightU>LeftU (be _ len|LeftU|≡0 _) = <-irrefl (sym len|LeftU|≡0) (Nat.s≤s Nat.z≤n)
  ¬l⊢RightU>LeftU (lne _ len|LeftU|≡0) = <-irrefl (sym len|LeftU|≡0) (Nat.s≤s Nat.z≤n)
  ¬l⊢RightU>LeftU (bne _ _ ())

  ¬l●r⊢>ⁱ : ¬ ((l ● r ` 10) ⊢ injFst top >ⁱ injFst x)
  ¬l●r⊢>ⁱ (seq₁ l⊢RightU>LeftU) = ¬l⊢RightU>LeftU l⊢RightU>LeftU
  ¬l●r⊢>ⁱ (seq₂ RightU≡LeftU _) = RightU≢LeftU _ _ RightU≡LeftU

  ¬l●r⊢injFst-top>injFst-x : ¬ ((l ● r ` 10) ⊢ injFst top > injFst x)
  ¬l●r⊢injFst-top>injFst-x (be len≡ len0 _) =
    n≡0→¬n>0 (trans len≡ len0) len|injFst-top|>0
  ¬l●r⊢injFst-top>injFst-x (lne _ len0) =
    n≡0→¬n>0 len0 len|injFst-x|>0
  ¬l●r⊢injFst-top>injFst-x (bne _ _ >ⁱprf) = ⊥-elim (¬l●r⊢>ⁱ >ⁱprf)
```

**Conclusion.**

```agda
  pdi-fst : PDInstance (l ● r ` 10) 'c'
  pdi-fst = pdinstance-fst pdi

  ¬>-inc-fst : ¬ (>-Inc pdi-fst)
  ¬>-inc-fst (>-inc ev) =
    ¬l●r⊢injFst-top>injFst-x (ev top x len|top|≡len|x| p●r⊢top>x)
```

Therefore `>-inc-fst` is unprovable even with the length-equality
restriction.  The root cause is structural: `>-Inc pdi` only constrains
ordering for equal-length pairs in `p`, but in `p ● r`, a locally
maximal list can contain pairs `(u₁, v₁)` and `(u₂, v₂)` where
`flat u₁ ++ flat v₁ ≡ flat u₂ ++ flat v₂` (same total word) but
`flat u₁ ≢ flat u₂` (different first-component words).  Since
`[u₁, u₂]` is not an equal-length pair in `U p`, the `>-Inc pdi`
hypothesis provides no guarantee about `l ⊢ inj u₁ > inj u₂`.

```agda

-- The unprovable lemma (kept as a hole for reference)
-- the reason is that pdi is unrestricted, it might not be from pdU[ l , c] 

>-inc-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
               → ( pdi : PDInstance l c )
               → >-Inc {l} {c} pdi
               ------------------------
               → >-Inc {l ● r ` loc} {c} (pdinstance-fst {l} {r} {loc} {c} pdi)
>-inc-fst {l} {r} {loc} {c} (pdinstance {p} {l} {c}  inj sound-ev)(>-inc u₁→u₂→len|u₁|≡len|u₂|→u₁>u₂→inj-u₁>inj-u₂) = >-inc >-inc-ev -- >-inc-ev
  where
    >-inc-ev : (u₁ u₂ : U (p ● r ` loc))
      → length (proj₁ (flat u₁)) ≡ length (proj₁ (flat u₂))
      → (p ● r ` loc) ⊢ u₁ > u₂
      → (l ● r ` loc) ⊢ mkinjFst inj u₁ >  mkinjFst inj u₂
    >-inc-ev = {!!}


```


```agda
>-inc-fst-strict : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( pdi : PDInstance l c )
  → Any (λ p → p ≡ pdi ) pdU[ l , c ] -- pdi ∈ pdU[ l , c ]
  → >-Inc {l} {c} pdi
  --------------------------------
  → >-Inc { l ● r ` loc } {c} (pdinstance-fst {l} {r} {loc} {c} pdi)
>-inc-fst-strict = {!!}
-- hm instead of carrying around pdi ∈ pdU [ l , c ], use Efn Epsilon First Normal form? 

```
