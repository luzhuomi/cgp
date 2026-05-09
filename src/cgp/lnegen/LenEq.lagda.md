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

The length-equality premise is not strong enough.  We reuse the
second counterexample from `CounterExample.lagda.md`.

Regular expressions:
- `l = ($ 'c') + (($ 'c') ● ($ 'c'))`
- `r = ε + ($ 'c')`
- `p = ε + ($ 'c')` (a partial derivative of `l` w.r.t. `'c'`)

```agda
module CounterExample-LenEq where

  l : RE
  l = ($ 'c' ` 1) + (($ 'c' ` 2) ● ($ 'c' ` 3) ` 4) ` 5

  r : RE
  r = ε + ($ 'c' ` 6) ` 7

  p : RE
  p = ε + ($ 'c' ` 8) ` 9

  inj : U p → U l
  inj (LeftU EmptyU)          = LeftU (LetterU 'c')
  inj (RightU (LetterU 'c'))  = RightU (PairU (LetterU 'c') (LetterU 'c'))

  sound-ev : ∀ (u : U p) → proj₁ (flat (inj u)) ≡ 'c' ∷ proj₁ (flat u)
  sound-ev (LeftU EmptyU)          = refl
  sound-ev (RightU (LetterU 'c'))  = refl

  pdi : PDInstance l 'c'
  pdi = pdinstance inj sound-ev
```

**Step 1: `pdi` satisfies the length-restricted `>-Inc`.**

`U p` has exactly two trees:
- `e = LeftU EmptyU` with `length (flat e) = 0`
- `a = RightU (LetterU 'c')` with `length (flat a) = 1`

The only pairs with equal length are reflexive (`e,e` and `a,a`),
but `>` is irreflexive, so the implication holds vacuously.

```agda
  e : U p
  e = LeftU EmptyU

  a : U p
  a = RightU (LetterU 'c')

  pdi->-inc : >-Inc pdi
  pdi->-inc = >-inc (λ where
    (LeftU EmptyU)          (LeftU EmptyU)          _ p⊢e>e → ⊥-elim (>→¬≡ p⊢e>e refl)
    (RightU (LetterU 'c'))  (RightU (LetterU 'c'))  _ p⊢a>a → ⊥-elim (>→¬≡ p⊢a>a refl)
    (LeftU EmptyU)          (RightU (LetterU 'c'))  () _
    (RightU (LetterU 'c'))  (LeftU EmptyU)          () _)
```

**Step 2: a pair in `U (p ● r)` with equal lengths that is ordered.**

```agda
  top : U (p ● r ` 10)
  top = PairU a (LeftU EmptyU)      -- flat = ['c'] ++ []

  x : U (p ● r ` 10)
  x = PairU e (RightU (LetterU 'c')) -- flat = [] ++ ['c']

  len|top|≡len|x| : length (proj₁ (flat top)) ≡ length (proj₁ (flat x))
  len|top|≡len|x| = refl

  p⊢a>e : p ⊢ a > e
  p⊢a>e = lne (Nat.s≤s Nat.z≤n) refl

  p●r⊢top>x : (p ● r ` 10) ⊢ top > x
  p●r⊢top>x = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ p⊢a>e)
```

**Step 3: after `pdinstance-fst` the ordering disappears.**

```agda
  injFst : U (p ● r ` 10) → U (l ● r ` 10)
  injFst = mkinjFst inj

  len|injFst-top|>0 : length (proj₁ (flat (injFst top))) Nat.> 0
  len|injFst-top|>0 = Nat.s≤s Nat.z≤n

  len|injFst-x|>0 : length (proj₁ (flat (injFst x))) Nat.> 0
  len|injFst-x|>0 = Nat.s≤s Nat.z≤n

  l⊢LeftU>RightU : l ⊢ LeftU (LetterU 'c') > RightU (PairU (LetterU 'c') (LetterU 'c'))
  l⊢LeftU>RightU = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) choice-lr

  -- No >ⁱ proof can relate injFst top and injFst x because:
  -- seq₁ needs l ⊢ inj a > inj e, which is impossible by asymmetry.
  -- seq₂ needs inj a ≡ inj e, which is impossible (different constructors).
  ¬l●r⊢>ⁱ : ¬ ((l ● r ` 10) ⊢ injFst top >ⁱ injFst x)
  ¬l●r⊢>ⁱ (seq₁ l⊢inja>inje) = >-asym l⊢LeftU>RightU l⊢inja>inje
  ¬l●r⊢>ⁱ (seq₂ eq _) = ⊥-elim (ParseTree.RightU≢LeftU _ _ eq)

  ¬l●r⊢injFst-top>injFst-x : ¬ ((l ● r ` 10) ⊢ injFst top > injFst x)
  -- `be` and `lne` are impossible because both sides are non-empty.
  ¬l●r⊢injFst-top>injFst-x (be len≡ len0 _) =
    n≡0→¬n>0 (trans len≡ len0) len|injFst-top|>0
  ¬l●r⊢injFst-top>injFst-x (lne _ len0) =
    n≡0→¬n>0 len0 len|injFst-x|>0
  -- `bne` delegates to the >ⁱ impossibility.
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
restriction.  The root cause is the same: in a sequential composition
`p ● r`, two trees can be ordered via `seq₁` while their first
components flatten to different words.  After `mkinjFst` the injected
first components always prepend one character, so the length-equality
of the *pairs* does not imply length-equality of the *first
components*.  The induction hypothesis therefore does not apply.

```agda

-- The unprovable lemma (kept as a hole for reference)

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
