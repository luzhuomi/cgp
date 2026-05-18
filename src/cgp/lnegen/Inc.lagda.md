This module contains  the attempt of proving monotonicity of the PD injection function for lnegen ordering without any restriction 

```agda
{-# OPTIONS --rewriting --allow-unsolved-metas #-}

module cgp.lnegen.Inc where
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

### Definition 32: >-Strict increasing PDInstance

Let r be a non problematic regular expression.
Let c be a letter.
Let pdi be a PDInstance  w.r.t r and c.
We say pdi is >-inc (strict increasing) iff,
  1. p is the partial derivative inhabited in pdi, and
  2. inj is the injection function from parse trees of p to parse trees of r.
  3. for all parse trees of p, u₁ and u₂  where p ⊢ u₁ > u₂
  Then r ⊢ inj u₁ > inj u₂

```agda

data >-Inc : ∀ { r : RE } { c : Char } →  PDInstance r c  → Set where
  >-inc : ∀ { p r : RE } { c : Char } { inj : U p →  U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( (u₁ : U p) → (u₂ : U p)
        →  p ⊢ u₁ > u₂  → r ⊢ inj u₁ > inj u₂ ) -- strict increasing evidence
    → >-Inc {r} {c} (pdinstance {p} {r} {c} inj sound-ev)


```

### Counterexample: `>-inc-fst` is unprovable

We show that `>-Inc` for a PDInstance does **not** lift through
`pdinstance-fst`.  The counterexample is adapted from
`CounterExample.lagda.md`.

Regular expressions:
- `l = ($ 'a') ● (ε + ε)`
- `r = ($ 'b') + ε`
- `p = ε ● (ε + ε)` (a partial derivative of `l` w.r.t. `'a'`)

```agda
module CounterExample-Inc where

  l : RE
  l = ($ 'a' ` 1) ● (ε + ε ` 2) ` 3

  r : RE
  r = ($ 'b' ` 4) + ε ` 5

  p : RE
  p = ε ● (ε + ε ` 2) ` 3

  inj : U p → U l
  inj (PairU EmptyU (LeftU EmptyU))  = PairU (LetterU 'a') (LeftU EmptyU)
  inj (PairU EmptyU (RightU EmptyU)) = PairU (LetterU 'a') (RightU EmptyU)

  sound-ev : ∀ (u : U p) → proj₁ (flat (inj u)) ≡ 'a' ∷ proj₁ (flat u)
  sound-ev (PairU EmptyU (LeftU EmptyU))  = refl
  sound-ev (PairU EmptyU (RightU EmptyU)) = refl

  pdi : PDInstance l 'a'
  pdi = pdinstance inj sound-ev
```

**Step 1: `pdi` satisfies `>-Inc`.**

The only two parse trees of `p` are
- `u₁ = PairU EmptyU (LeftU EmptyU)`
- `u₂ = PairU EmptyU (RightU EmptyU)`

```agda
  u₁ : U p
  u₁ = PairU EmptyU (LeftU EmptyU)

  u₂ : U p
  u₂ = PairU EmptyU (RightU EmptyU)

  p⊢u₁>u₂ : p ⊢ u₁ > u₂
  p⊢u₁>u₂ = be refl refl (seq₂ refl (be refl refl choice-lr))

  l⊢inju₁>inju₂ : l ⊢ inj u₁ > inj u₂
  l⊢inju₁>inju₂ = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                         (seq₂ refl (be refl refl choice-lr))

  -- The only ordering in U p is u₁ > u₂ (via seq₂ refl choice-lr).
  -- All other orderings are impossible.

  -- For ε + ε, RightU EmptyU > LeftU EmptyU is impossible:
  --   be/bne need a >ⁱ proof, but no >ⁱ constructor gives RightU >ⁱ LeftU.
  --   lne needs length > 0, but both flatten to [].
  ¬ε+ε⊢u₂>ⁱu₁ : ¬ ((ε + ε ` 2) ⊢ RightU EmptyU >ⁱ LeftU EmptyU)
  ¬ε+ε⊢u₂>ⁱu₁ ()

  ¬ε+ε⊢u₂>u₁ : ¬ ((ε + ε ` 2) ⊢ RightU EmptyU > LeftU EmptyU)
  ¬ε+ε⊢u₂>u₁ (be _ _ u₂>ⁱu₁) = ⊥-elim (¬ε+ε⊢u₂>ⁱu₁ u₂>ⁱu₁)
  ¬ε+ε⊢u₂>u₁ (bne _ _ u₂>ⁱu₁) = ⊥-elim (¬ε+ε⊢u₂>ⁱu₁ u₂>ⁱu₁)
  ¬ε+ε⊢u₂>u₁ (lne len>0 _) = <-irrefl refl len>0

  -- For p = ε ● (ε + ε), the internal >ⁱ on PairU uses seq₁ or seq₂.
  -- seq₁ requires ε ⊢ EmptyU > EmptyU (impossible by irreflexivity).
  -- seq₂ requires ε + ε ⊢ v₂ > v₂'.
  --   For u₂ > u₁, this would need ε + ε ⊢ RightU EmptyU > LeftU EmptyU,
  --   which we proved impossible above.
  ¬p⊢u₂>u₁ : ¬ (p ⊢ u₂ > u₁)
  ¬p⊢u₂>u₁ (be _ _ u₂>ⁱu₁) = ¬p●r⊢u₂>ⁱu₁ u₂>ⁱu₁
    where
      ¬p●r⊢u₂>ⁱu₁ : ¬ (p ⊢ PairU EmptyU (RightU EmptyU) >ⁱ PairU EmptyU (LeftU EmptyU))
      ¬p●r⊢u₂>ⁱu₁ (seq₁ ε⊢EmptyU>EmptyU) = ⊥-elim (>→¬≡ ε⊢EmptyU>EmptyU refl)
      ¬p●r⊢u₂>ⁱu₁ (seq₂ refl ε+ε⊢u₂>u₁') = ⊥-elim (¬ε+ε⊢u₂>u₁ ε+ε⊢u₂>u₁')
  ¬p⊢u₂>u₁ (bne _ _ u₂>ⁱu₁) = ¬p●r⊢u₂>ⁱu₁ u₂>ⁱu₁
    where
      ¬p●r⊢u₂>ⁱu₁ : ¬ (p ⊢ PairU EmptyU (RightU EmptyU) >ⁱ PairU EmptyU (LeftU EmptyU))
      ¬p●r⊢u₂>ⁱu₁ (seq₁ ε⊢EmptyU>EmptyU) = ⊥-elim (>→¬≡ ε⊢EmptyU>EmptyU refl)
      ¬p●r⊢u₂>ⁱu₁ (seq₂ refl ε+ε⊢u₂>u₁') = ⊥-elim (¬ε+ε⊢u₂>u₁ ε+ε⊢u₂>u₁')
  ¬p⊢u₂>u₁ (lne len>0 _) = <-irrefl refl len>0

  ¬p⊢u₁>u₁ : ¬ (p ⊢ u₁ > u₁)
  ¬p⊢u₁>u₁ (be _ _ u₁>ⁱu₁) = ¬p●r⊢u₁>ⁱu₁ u₁>ⁱu₁
    where
      ¬p●r⊢u₁>ⁱu₁ : ¬ (p ⊢ PairU EmptyU (LeftU EmptyU) >ⁱ PairU EmptyU (LeftU EmptyU))
      ¬p●r⊢u₁>ⁱu₁ (seq₁ ε⊢EmptyU>EmptyU) = ⊥-elim (>→¬≡ ε⊢EmptyU>EmptyU refl)
      ¬p●r⊢u₁>ⁱu₁ (seq₂ refl ε+ε⊢u₁>u₁') = ⊥-elim (>→¬≡ ε+ε⊢u₁>u₁' refl)
  ¬p⊢u₁>u₁ (bne _ _ u₁>ⁱu₁) = ¬p●r⊢u₁>ⁱu₁ u₁>ⁱu₁
    where
      ¬p●r⊢u₁>ⁱu₁ : ¬ (p ⊢ PairU EmptyU (LeftU EmptyU) >ⁱ PairU EmptyU (LeftU EmptyU))
      ¬p●r⊢u₁>ⁱu₁ (seq₁ ε⊢EmptyU>EmptyU) = ⊥-elim (>→¬≡ ε⊢EmptyU>EmptyU refl)
      ¬p●r⊢u₁>ⁱu₁ (seq₂ refl ε+ε⊢u₁>u₁') = ⊥-elim (>→¬≡ ε+ε⊢u₁>u₁' refl)
  ¬p⊢u₁>u₁ (lne len>0 _) = <-irrefl refl len>0

  ¬p⊢u₂>u₂ : ¬ (p ⊢ u₂ > u₂)
  ¬p⊢u₂>u₂ (be _ _ u₂>ⁱu₂) = ¬p●r⊢u₂>ⁱu₂ u₂>ⁱu₂
    where
      ¬p●r⊢u₂>ⁱu₂ : ¬ (p ⊢ PairU EmptyU (RightU EmptyU) >ⁱ PairU EmptyU (RightU EmptyU))
      ¬p●r⊢u₂>ⁱu₂ (seq₁ ε⊢EmptyU>EmptyU) = ⊥-elim (>→¬≡ ε⊢EmptyU>EmptyU refl)
      ¬p●r⊢u₂>ⁱu₂ (seq₂ refl ε+ε⊢u₂>u₂') = ⊥-elim (>→¬≡ ε+ε⊢u₂>u₂' refl)
  ¬p⊢u₂>u₂ (bne _ _ u₂>ⁱu₂) = ¬p●r⊢u₂>ⁱu₂ u₂>ⁱu₂
    where
      ¬p●r⊢u₂>ⁱu₂ : ¬ (p ⊢ PairU EmptyU (RightU EmptyU) >ⁱ PairU EmptyU (RightU EmptyU))
      ¬p●r⊢u₂>ⁱu₂ (seq₁ ε⊢EmptyU>EmptyU) = ⊥-elim (>→¬≡ ε⊢EmptyU>EmptyU refl)
      ¬p●r⊢u₂>ⁱu₂ (seq₂ refl ε+ε⊢u₂>u₂') = ⊥-elim (>→¬≡ ε+ε⊢u₂>u₂' refl)
  ¬p⊢u₂>u₂ (lne len>0 _) = <-irrefl refl len>0

  pdi->-inc-ev : (v₁ v₂ : U p) → p ⊢ v₁ > v₂ → l ⊢ inj v₁ > inj v₂
  pdi->-inc-ev (PairU EmptyU (LeftU EmptyU)) (PairU EmptyU (RightU EmptyU)) _ = l⊢inju₁>inju₂
  pdi->-inc-ev (PairU EmptyU (RightU EmptyU)) (PairU EmptyU (LeftU EmptyU)) p⊢u₂>u₁ = ⊥-elim (¬p⊢u₂>u₁ p⊢u₂>u₁)
  pdi->-inc-ev (PairU EmptyU (LeftU EmptyU)) (PairU EmptyU (LeftU EmptyU)) p⊢u₁>u₁ = ⊥-elim (¬p⊢u₁>u₁ p⊢u₁>u₁)
  pdi->-inc-ev (PairU EmptyU (RightU EmptyU)) (PairU EmptyU (RightU EmptyU)) p⊢u₂>u₂ = ⊥-elim (¬p⊢u₂>u₂ p⊢u₂>u₂)

  pdi->-inc : >-Inc pdi
  pdi->-inc = >-inc pdi->-inc-ev
```

**Step 2: after `pdinstance-fst` the ordering breaks.**

Consider the following pair trees in `U (p ● r)`:
- `top = PairU u₂ (LeftU (LetterU 'b'))`
- `x   = PairU u₁ (RightU EmptyU)`

They are ordered in `p ● r` via `lne` because `top` is non-empty
(length 1) while `x` is empty (length 0).  But after applying
`mkinjFst inj` the ordering disappears.

```agda
  top : U (p ● r ` 6)
  top = PairU u₂ (LeftU (LetterU 'b'))

  x : U (p ● r ` 6)
  x = PairU u₁ (RightU EmptyU)

  len|top|>0 : length (proj₁ (flat top)) Nat.> 0
  len|top|>0 = Nat.s≤s Nat.z≤n

  len|x|≡0 : length (proj₁ (flat x)) ≡ 0
  len|x|≡0 = refl

  p●r⊢top>x : (p ● r ` 6) ⊢ top > x
  p●r⊢top>x = lne len|top|>0 len|x|≡0

  injFst : U (p ● r ` 6) → U (l ● r ` 6)
  injFst = mkinjFst inj

  len|injFst-top|>0 : length (proj₁ (flat (injFst top))) Nat.> 0
  len|injFst-top|>0 = Nat.s≤s Nat.z≤n

  len|injFst-x|>0 : length (proj₁ (flat (injFst x))) Nat.> 0
  len|injFst-x|>0 = Nat.s≤s Nat.z≤n

  ¬inju₂≡inju₁ : ¬ (inj u₂ ≡ inj u₁)
  ¬inju₂≡inju₁ eq = ParseTree.RightU≢LeftU EmptyU EmptyU
                      (proj₂ (ParseTree.inv-pairU _ _ _ _ eq))
```

The `>` relation is asymmetric, so `l ⊢ inj u₂ > inj u₁` is false
(because `l ⊢ inj u₁ > inj u₂` holds).  Hence every `bne` case for
`l ● r ⊢ injFst top > injFst x` leads to a contradiction:

```agda
  ¬l●r⊢injFst-top>injFst-x : ¬ ((l ● r ` 6) ⊢ injFst top > injFst x)
  -- `be` is impossible because it implies len|injFst top| ≡ 0, contradicting len|injFst top| > 0.
  ¬l●r⊢injFst-top>injFst-x (be len|top|≡len|x| len|x|≡0 _) =
    n≡0→¬n>0 (trans len|top|≡len|x| len|x|≡0) len|injFst-top|>0
  -- `lne` is impossible because it implies len|injFst x| ≡ 0, contradicting len|injFst x| > 0.
  ¬l●r⊢injFst-top>injFst-x (lne _ len|x|≡0) =
    n≡0→¬n>0 len|x|≡0 len|injFst-x|>0
  -- `bne` with `seq₁` would need `l ⊢ inj u₂ > inj u₁`, contradicting asymmetry.
  ¬l●r⊢injFst-top>injFst-x (bne _ _ (seq₁ l⊢inju₂>inju₁)) =
    >-asym l⊢inju₁>inju₂ l⊢inju₂>inju₁
  -- `bne` with `seq₂` would need `inj u₂ ≡ inj u₁`, which is false.
  ¬l●r⊢injFst-top>injFst-x (bne _ _ (seq₂ inju₂≡inju₁ _)) =
    ¬inju₂≡inju₁ inju₂≡inju₁
```

**Conclusion.**

`pdi` satisfies `>-Inc`, yet `pdinstance-fst pdi` does **not**:

```agda
  pdi-fst : PDInstance (l ● r ` 6) 'a'
  pdi-fst = pdinstance-fst pdi

  ¬>-inc-fst : ¬ (>-Inc pdi-fst)
  ¬>-inc-fst (>-inc ev) =
    ¬l●r⊢injFst-top>injFst-x (ev top x p●r⊢top>x)
```

Therefore `>-inc-fst` is unprovable as stated.  The root cause is
that `>-Inc` only guarantees ordering preservation for pairs of
parse trees that flatten to the **same** word, but in a sequential
composition `p ● r` two trees can be ordered via `lne` even though
their first components flatten to different words.  After lifting
through `mkinjFst` that ordering can disappear.

```agda

-- The unprovable lemma (kept as a hole for reference)

>-inc-fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
               → ( pdi : PDInstance l c )
               → >-Inc {l} {c} pdi
               ------------------------
               → >-Inc {l ● r ` loc} {c} (pdinstance-fst {l} {r} {loc} {c} pdi)
>-inc-fst {l} {r} {loc} {c} (pdinstance {p} {l} {c}  inj sound-ev)(>-inc u₁→u₂→u₁>u₂→inj-u₁>inj-u₂) = >-inc >-inc-ev -- >-inc-ev
  where
    >-inc-ev : (u₁ u₂ : U (p ● r ` loc))
      → (p ● r ` loc) ⊢ u₁ > u₂
      → (l ● r ` loc) ⊢ mkinjFst inj u₁ >  mkinjFst inj u₂
    >-inc-ev = {!!}

```

#### ParseAll is not sorted


The following is defined in lnegen/PartialDerivative
  -- ((a●(ε+ε))●(ε+b))●(ε+b)
  a●ε+ε●ε+b●ε+b = ( ( (($ 'a' ` 1) ● ( ε + ε ` 2) ` 3) ● ( ε + ($ 'b' ` 4) ` 5) ` 6) ● (ε + ($ 'b' ` 7) ` 8) ` 9 )
  ex_sss : List (U a●ε+ε●ε+b●ε+b)
  ex_sss = parseAll[ a●ε+ε●ε+b●ε+b ,  'a' ∷ 'b' ∷  [] ]

ExampleParseAll.ex_sss

should yield

~~~~~~~

PairU (PairU (PairU (LetterU 'a') (LeftU EmptyU))   (RightU (LetterU 'b'))) (LeftU EmptyU) -- (a)
∷
PairU (PairU (PairU (LetterU 'a') (RightU EmptyU))  (RightU (LetterU 'b'))) (LeftU EmptyU) -- (b)
∷
PairU (PairU (PairU (LetterU 'a') (LeftU EmptyU)) (LeftU EmptyU)) (RightU (LetterU 'b'))   -- (c)
∷
PairU (PairU (PairU (LetterU 'a') (RightU EmptyU)) (LeftU EmptyU)) (RightU (LetterU 'b'))  -- (d)
∷ []


```agda
a●ε+ε●ε+b●ε+b : RE 
a●ε+ε●ε+b●ε+b = ( ( (($ 'a' ` 1) ● ( ε + ε ` 2) ` 3) ● ( ε + ($ 'b' ` 4) ` 5) ` 6) ● (ε + ($ 'b' ` 7) ` 8) ` 9 )
t_a t_b t_c t_d : U a●ε+ε●ε+b●ε+b
t_a = PairU (PairU (PairU (LetterU 'a') (LeftU EmptyU))   (RightU (LetterU 'b'))) (LeftU EmptyU) -- (a)
t_b = PairU (PairU (PairU (LetterU 'a') (RightU EmptyU))  (RightU (LetterU 'b'))) (LeftU EmptyU) -- (b)
t_c = PairU (PairU (PairU (LetterU 'a') (LeftU EmptyU)) (LeftU EmptyU)) (RightU (LetterU 'b'))   -- (c)
t_d = PairU (PairU (PairU (LetterU 'a') (RightU EmptyU)) (LeftU EmptyU)) (RightU (LetterU 'b'))  -- (d)

t_a>t_b : a●ε+ε●ε+b●ε+b ⊢ t_a > t_b
t_a>t_b = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₁
                                                           (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                            (seq₂ refl (be refl refl choice-lr))))) )

t_c>t_d : a●ε+ε●ε+b●ε+b ⊢ t_c > t_d
t_c>t_d = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₁
                                                           (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                            (seq₂ refl (be refl refl choice-lr))))) )

t_a>t_d : a●ε+ε●ε+b●ε+b ⊢ t_a > t_d
t_a>t_d = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₁
                                                           (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                            (seq₂ refl (be refl refl choice-lr))))))

t_a>t_c : a●ε+ε●ε+b●ε+b ⊢ t_a > t_c
t_a>t_c = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₂ refl (lne (Nat.s≤s Nat.z≤n) refl))) )


t_b>t_d : a●ε+ε●ε+b●ε+b ⊢ t_b > t_d
t_b>t_d = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₂ refl (lne (Nat.s≤s Nat.z≤n) refl))) )


-- however instead of t_b>t_c, we have

t_c>t_b : a●ε+ε●ε+b●ε+b ⊢ t_c > t_b
t_c>t_b = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n) (seq₁ (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                          (seq₁
                                                           (bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                                                            (seq₂ refl (be refl refl choice-lr))))))


```

