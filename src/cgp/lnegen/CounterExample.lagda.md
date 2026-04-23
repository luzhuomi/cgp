This module gives a concrete counterexample showing that `≥-max-preserve-fst`
is unprovable as stated.

```agda
{-# OPTIONS --rewriting --allow-unsolved-metas #-}
module cgp.lnegen.CounterExample where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; ε∈  ; ε∈_+_ ; ε∈_●_ ; ε∈ε )

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;  LeftU ; RightU ; PairU ; flat ; inv-pairU ; RightU≢LeftU )

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; mkinjFst )

import cgp.lnegen.Order as Order
open Order using ( _⊢_>_ ; _⊢_>ⁱ_ ; be ; bne ; lne ; seq₁ ; seq₂ ; choice-lr ; ≥-maximal ; ≥-join ; _⊢_≥_ ; ≥-Max-Preserve ; ≥-pres ; >-asym )

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )

import Data.Nat.Properties as NatProperties
open NatProperties using ( <-irrefl )

import Data.List as List
open List using (List ; _∷_ ; [] ; [_]; map; length )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong)

import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ ; proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (inj₁; inj₂)

import Data.List.Relation.Unary.All as All
open All using (All ; _∷_ ; [] )

import Relation.Nullary as Nullary 
open Nullary using (¬_)

```

We define the following regular expressions:

* `l = ($ 'a') ● (ε + ε)`
* `r = ($ 'b') + ε`

```agda
module CounterExample where

  l : RE
  l = ($ 'a' ` 1) ● (ε + ε ` 2) ` 3

  r : RE
  r = ($ 'b' ` 4) + ε ` 5
```

The partial derivative of `l` w.r.t. `'a'` has partial derivative
`p = ε ● (ε + ε)`.  Its injection maps `PairU EmptyU v` to
`PairU (LetterU 'a') v`.

```agda
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

### Step 1: `pdi` satisfies `≥-Max-Preserve`

The only two parse trees of `p` are

* `u₁ = PairU EmptyU (LeftU EmptyU)`
* `u₂ = PairU EmptyU (RightU EmptyU)`

and `p ⊢ u₁ > u₂` holds.  After injection we have
`l ⊢ inj u₁ > inj u₂`, so every `≥-maximal` list in `U p` maps to a
`≥-maximal` list in `U l`.

```agda
  u₁ : U p
  u₁ = PairU EmptyU (LeftU EmptyU)

  u₂ : U p
  u₂ = PairU EmptyU (RightU EmptyU)

  -- In U p, both trees are empty and the first component is equal,
  -- so the ordering reduces to the second component.
  p⊢u₁>u₂ : p ⊢ u₁ > u₂
  p⊢u₁>u₂ = be refl refl (seq₂ refl (be refl refl choice-lr))

  -- After injection both trees are non-empty (length 1).
  l⊢inju₁>inju₂ : l ⊢ inj u₁ > inj u₂
  l⊢inju₁>inju₂ = bne (Nat.s≤s Nat.z≤n) (Nat.s≤s Nat.z≤n)
                       (seq₂ refl (be refl refl choice-lr))
```

### Step 2: a `≥-maximal` list in `U (p ● r)`

Define

* `top = PairU u₂ (LeftU (LetterU 'b'))`
* `x   = PairU u₁ (RightU EmptyU)`

In `U (p ● r)` we have `len|top| = 1 > 0` and `len|x| = 0`, hence
`p ● r ⊢ top > x` via the `lne` rule.  Therefore `[top , x]` is
`≥-maximal`.

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

  maximal-top-x : ≥-maximal {p ● r ` 6} (top ∷ x ∷ [])
  maximal-top-x = ≥-join top (x ∷ []) (inj₁ p●r⊢top>x ∷ [])
```

### Step 3: after `pdinstance-fst` the list is no longer `≥-maximal`

Applying `mkinjFst inj` yields

* `mkinjFst inj top = PairU (inj u₂) (LeftU (LetterU 'b'))`
* `mkinjFst inj x   = PairU (inj u₁) (RightU EmptyU)`

Both resulting trees are non-empty (lengths 2 and 1 respectively),
so any `>` proof must use `bne` together with a `>ⁱ` proof.
But:

* `seq₁` would require `l ⊢ inj u₂ > inj u₁`, which is **false**
  (the opposite ordering holds).
* `seq₂` would require `inj u₂ ≡ inj u₁`, which is **false**.

Hence `l ● r ⊢ mkinjFst inj top ≯ mkinjFst inj x`, and the mapped
list is **not** `≥-maximal`.

```agda
  injFst = mkinjFst inj

  len|injFst-top|>0 : length (proj₁ (flat (injFst top))) Nat.> 0
  len|injFst-top|>0 = Nat.s≤s Nat.z≤n

  len|injFst-x|>0 : length (proj₁ (flat (injFst x))) Nat.> 0
  len|injFst-x|>0 = Nat.s≤s Nat.z≤n

  ¬inju₂≡inju₁ : ¬ (inj u₂ ≡ inj u₁)
  ¬inju₂≡inju₁ eq = RightU≢LeftU EmptyU EmptyU (proj₂ (inv-pairU _ _ _ _ eq))

  -- Attempting to prove l ● r ⊢ injFst top > injFst x leads to a
  -- contradiction: either seq₁ or seq₂ must hold, but both are false.
  ¬l●r⊢injFst-top>injFst-x : ¬ ((l ● r ` 6) ⊢ injFst top > injFst x)
  -- The `be` case is impossible because len|injFst top| > 0.
  ¬l●r⊢injFst-top>injFst-x (be _ len|v₂|≡0 _) =
    <-irrefl (sym len|v₂|≡0) len|injFst-top|>0
  -- The `lne` case is impossible because len|injFst x| > 0.
  ¬l●r⊢injFst-top>injFst-x (lne _ len|v₂|≡0) =
    <-irrefl (sym len|v₂|≡0) len|injFst-x|>0
  -- The `bne` case with `seq₁` contradicts asymmetry of >.
  ¬l●r⊢injFst-top>injFst-x (bne _ _ (seq₁ l⊢inju₂>inju₁)) =
    >-asym l⊢inju₁>inju₂ l⊢inju₂>inju₁
  -- The `bne` case with `seq₂` contradicts injectivity.
  ¬l●r⊢injFst-top>injFst-x (bne _ _ (seq₂ inju₂≡inju₁ _)) =
    ¬inju₂≡inju₁ inju₂≡inju₁
```

### Conclusion

The `PDInstance` `pdi` satisfies `≥-Max-Preserve` (the only
`≥-maximal` lists in `U p` are `[]`, `[u₁]`, `[u₂]`, and `[u₁ , u₂]`,
and all map to `≥-maximal` lists in `U l`).  However, the list
`[top , x]` is `≥-maximal` in `U (p ● r)` while
`map (mkinjFst inj) [top , x]` is **not** `≥-maximal` in `U (l ● r)`.
Therefore `≥-max-preserve-fst` is false as stated.

```agda
  -- The specific list [top , x] witnesses the failure.
  counterexample-list : List (U (p ● r ` 6))
  counterexample-list = top ∷ x ∷ []

  -- It is ≥-maximal before applying pdinstance-fst...
  before : ≥-maximal {p ● r ` 6} counterexample-list
  before = maximal-top-x

  -- ...but not after.
  after : ¬ (≥-maximal {l ● r ` 6} (map injFst counterexample-list))
  after (≥-join ._ ._ (inj₁ l●r⊢injFst-top>injFst-x ∷ _)) =
    ¬l●r⊢injFst-top>injFst-x l●r⊢injFst-top>injFst-x
  after (≥-join ._ ._ (inj₂ refl ∷ _)) =
    ¬inju₂≡inju₁ refl
```


---
Counterexample for the new definition
Regexes:
l = ($ 'a') + (($ 'a') ● ($ 'b'))
r = ($ 'b') + ε
Partial derivative pdi : PDInstance l 'a' with p = $ 'b':
inj : U ($ 'b') → U l
inj (LetterU 'b') = RightU (PairU (LetterU 'a') (LetterU 'b'))
≥-Max-Preserve holds:  
For u = LetterU 'b' and w = ['b'], u is trivially ≥-Max {p} ['b'] u (it is the only parse tree for that word). Its image inj u is also the only U l tree for ['a', 'b'], so ≥-Max {l} ['a', 'b'] (inj u) holds.
Now take v = RightU EmptyU (the empty tree of r):  
PairU u v = PairU (LetterU 'b') (RightU EmptyU) flattens to ['b'] and is trivially ≥-Max {p ● r} ['b'] (PairU u v).
After pdinstance-fst:  
mkinjFst inj (PairU u v) = PairU (RightU (PairU (LetterU 'a') (LetterU 'b'))) (RightU EmptyU) flattens to ['a', 'b'].
But in U (l ● r), the tree PairU (LeftU (LetterU 'a')) (LeftU (LetterU 'b')) also flattens to ['a', 'b'], and:
- l ● r ⊢ PairU (RightU (...)) (RightU EmptyU) ≯ PairU (LeftU (...)) (LeftU (...))
  - seq₁ would need l ⊢ RightU (...) > LeftU (...), impossible (only LeftU > RightU is derivable).
  - seq₂ would need RightU (...) ≡ LeftU (...), false.
Therefore ≥-Max {l ● r} ['a', 'b'] (mkinjFst inj (PairU u v)) is false, even though ≥-Max {p ● r} ['b'] (PairU u v) is true and pdi satisfies ≥-Max-Preserve.
---




The Counterexample
Regular expressions:
```agda
l = ($ 'c') + (($ 'c') ● ($ 'c') ` 2) ` 1
r = ε + ($ 'c' ` 4) ` 3
p = ε + ($ 'c' ` 6) ` 5
```
Injection inj : U p → U l with c = 'c':
```agda
inj (LeftU EmptyU)          = LeftU (LetterU 'c')                           -- flat [] ↦ flat ['c']
inj (RightU (LetterU 'c'))  = RightU (PairU (LetterU 'c') (LetterU 'c'))   -- flat ['c'] ↦ flat ['c','c']
``` 
Soundness verified:
```agda
- flat (inj (LeftU EmptyU)) = ['c'] = 'c' :: [] = 'c' :: flat (LeftU EmptyU) ✓
- flat (inj (RightU (LetterU 'c'))) = ['c','c'] = 'c' :: ['c'] = 'c' :: flat (RightU (LetterU 'c')) ✓
```
>-LocalMaxPreserve holds for this pdi:

- The only locally maximal lists in U p are singletons [LeftU EmptyU] (for w = []) and [RightU (LetterU 'c')] (for w = ['c']).
- These map to [LeftU (LetterU 'c')] and [RightU (PairU 'c' 'c')], which are trivially maximal in U l for their respective words.
---
The locally maximal list in U (p ● r) that breaks
```agda
top = PairU (RightU (LetterU 'c')) (RightU EmptyU)   -- flat = ['c'] ++ []      = ['c']
x   = PairU (LeftU EmptyU)          (LeftU (LetterU 'c')) -- flat = [] ++ ['c']      = ['c']
```
[top, x] is >-LocalMaximal {p ● r} {['c']} because:
- Both flatten to ['c']
- p ● r ⊢ top > x via bne + seq₁ (both non-empty, and p ⊢ RightU (LetterU 'c') > LeftU EmptyU via lne)
---
After pdinstance-fst
```agda
mkinjFst inj top = PairU (RightU (PairU 'c' 'c')) (RightU EmptyU)  -- flat = ['c','c'] ++ [] = ['c','c']
mkinjFst inj x   = PairU (LeftU (LetterU 'c'))     (LeftU (LetterU 'c')) -- flat = ['c']    ++ ['c'] = ['c','c']
```
Both flatten to ['c','c'], but l ● r ⊢ mkinjFst inj top ≯ mkinjFst inj x:
- seq₁ would require l ⊢ RightU (PairU 'c' 'c') > LeftU (LetterU 'c') — impossible because choice-lr only gives LeftU > RightU, never the reverse.
- seq₂ would require RightU (PairU 'c' 'c') ≡ LeftU (LetterU 'c') — false.
Therefore the mapped list is not >-LocalMaximal {l ● r} {['c','c']}.
---
Why this keeps happening
The root cause is structural: >-LocalMaxPreserve only guarantees ordering preservation when all p-trees in the list flatten to the same word. But in a sequential composition p ● r, a locally maximal list can contain pairs (u₁, v₁) and (u₂, v₂) where:
- flat u₁ ++ flat v₁ ≡ flat u₂ ++ flat v₂ (same total word)
- flat u₁ ≢ flat u₂ (different first-component words)
- p ⊢ u₁ > u₂ via seq₁
Since [u₁, u₂] is not locally maximal in U p (different words), the hypothesis gives us no control over l ⊢ inj u₁ > inj u₂. After mkinjFst, the ordering can disappear or reverse.
---
Conclusion: >-locmax-preserve-fst is unprovable as stated. The local maximality constraint on the first component alone is insufficient to make the lemma true. You would need either:
1. A stronger preservation property that also covers p-trees with different flat words, or
2. An additional structural invariant about pdU-generated instances that prevents the problematic case.
