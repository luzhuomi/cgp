# Finiteness of the set of partial-derivative descendants

The paper's Proposition `Finite Dissimilar Canonical Descendants`
(section 4, `prop:finite-dissimilar`):

> Let `r` be an expression. Then the set `Desc(r) = { canonic(s) | r ⋞ s }`
> is finite.

In this formalization a descendant *state* is a list of partial derivatives
(`cgp.ambig.Canonic.pd*-Desc r w`), so the statement becomes: for a fixed `r`
there is a **finite list** `L` such that every expression occurring in every
state is a member of `L` — and consequently every state itself is a member of
the finite list of all lists over `L` of the appropriate length.

## What is formalized here

1. Equality of `RE` values is decidable (`_≟ᴱ_`): locations and the `ε∉`
   evidence of a star are part of the value.  Membership `_∈L_` in a list of
   expressions, the test "every element of this list is a member of that list"
   (`All-in?`, and `All-in?-char` for words), and the test "this supply is
   closed under the partial derivatives" (`Closed!`) are decidable as a
   consequence.
2. `Closed L cs` — a *supply* of expressions `L` is closed under the partial
   derivatives of the alphabet `cs`; `Sat`/`Sat-iter` generate candidate
   supplies by saturation.
3. `Desc⊆` — if `L` contains `r` and is closed, then the elements of the state
   reached after **any** word over `cs` are members of `L`.  This is
   induction along `pdUMany-aux` with the one-step lemma `advance-level`
   (`compose-pdi-with` preserves the continuation, so the pd instances of a
   state stay inside the supply).
4. `Desc-finite` — combining 3 with the enumeration of lists over a finite
   supply: for each word, the state itself is a member of the computable finite
   list `listsOf (length …) L`.  The remaining hypothesis (that the word is
   over the alphabet) is decidable too (`All-in?-char`).
5. §6 computes supplies and *certifies* them: `Closed? L cs ≡ true` for the
   paper's A3 example `((a + b) · c) + (a · c)` (found by saturation) and for
   `a ⋆`, so `Desc⊆` applies to every word; it also shows by computation that
   the supply of subexpressions of `a ⋆` is **not** closed.
6. §7 shows by computation that the *lengths* of the states of
   `((ε + ε) · a) ⋆` are 2, 4, 8 for `a`, `aa`, `aaa`: the number of distinct
   expressions stays bounded while the state lists keep growing.

## What is not formalized

* A general proof that a closed supply exists for every `r` (Antimirov's
  bound).  A naive "subterm of `r`" supply is **false** here: the Kleene rule
  of `pdU` (`pdinstance-star`, `cgp.PDInstance`) glues a partial derivative of
  the star body in front of the star, so descendants have `p ● r*` shapes —
  `star-a-subterms-not-closed` of §6 checks that for `a ⋆`.  For
  `r = (a · b*) ⋆` the states are `ε · b* · (a · b*)⋆` after `a` and
  `(ε · b* · b*) · (a · b*)⋆` after `ab`.  A general bound needs a rank
  argument over such gluings.
* A bound on the *length* of a state list that is independent of the word —
  §7 measures the doubling.  `pdU` returns one instance per empty parse tree of
  a nullable left factor, so multiplicities are kept and each pass through a
  star multiplies them.  The paper quotients states by similarity (`canonic`,
  whose `dedup` drops later `≈₀`-duplicates of a `+` spine), which removes
  exactly those duplicates; with duplicate-free states the length would be
  bounded by `length L` and `listsOf (length L) L` would bound all states at
  once (not formalized).

```agda
{-# OPTIONS --rewriting #-}
module cgp.ambig.DescFinite where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉ ; ε∉$ ; ε∉fst ; ε∉snd ; ε∉_+_)

import cgp.ParseTree as ParseTree
open ParseTree using ( U ; flat )

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* )

import cgp.posix.PartialDerivative as PosixPD

import cgp.ambig.Canonic as Canonic
open Canonic using ( pd-expr ; pd*-expr ; pd*-Desc )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_] ; _∷ʳ_ ; map ; concatMap ; length)

import Data.List.Properties as ListProps
open ListProps using ( ++-identityʳ )

import Data.List.Relation.Unary.All as ListAll
open ListAll using (All)

import Data.List.Relation.Unary.All.Properties as ListAllProps
open ListAllProps using ( ++⁺ )

import Data.List.Relation.Unary.Any as ListAny
open ListAny using (here ; there)

import Data.List.Membership.Propositional as Mem
open Mem using () renaming (_∈_ to _∈L_)

import Data.Bool.Base as Bool
open Bool using (Bool ; true ; false ; T)

import Data.Unit as Unit
open Unit using (tt)

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using (ℕ ; zero ; suc)

import Data.Product as Prod
open Prod using (proj₁ ; proj₂ ; _×_ ; _,_ ; Σ)

import Data.Sum as Sum
open Sum using (_⊎_ ; inj₁ ; inj₂)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

import Relation.Nullary as Nullary
open Nullary using (¬_ ; Dec ; yes ; no)

```

## 1. Equality of expressions, and membership in a list of expressions

Locations and the nullability evidence of a star are part of an `RE` value, so
two expressions are equal when their locations and their evidence arguments are.
The similarity `_≈₀_` of `cgp.ambig.Canonic` is the coarser,
location-insensitive relation of the paper; it is not needed for the finiteness
argument (a bound for the fine equality implies one for the quotient), but it
means the computed supplies contain location-variants of the same expression —
`a3-supply` of §6 has several of them, and `Canonic.dedup` is the operation
that merges them.

```agda
-- constructor injectivity (matching on refl unifies the arguments)
ε∉-fst-inj : ∀ { l r : RE } { loc : ℕ } { nε₁ nε₂ : ε∉ l }
  → (ε∉fst {l = l} {r = r} {loc = loc} nε₁) ≡ (ε∉fst {l = l} {r = r} {loc = loc} nε₂)
  → nε₁ ≡ nε₂
ε∉-fst-inj {nε₂ = nε₁} refl = refl

ε∉-snd-inj : ∀ { l r : RE } { loc : ℕ } { nε₁ nε₂ : ε∉ r }
  → (ε∉snd {l = l} {r = r} {loc = loc} nε₁) ≡ (ε∉snd {l = l} {r = r} {loc = loc} nε₂)
  → nε₁ ≡ nε₂
ε∉-snd-inj {nε₂ = nε₁} refl = refl

ε∉-sum-injˡ : ∀ { l r : RE } { loc : ℕ } { nε₁₁ nε₂₁ : ε∉ l } { nε₁₂ nε₂₂ : ε∉ r }
  → (ε∉_+_ {l = l} {r = r} {loc = loc} nε₁₁ nε₁₂)
  ≡ (ε∉_+_ {l = l} {r = r} {loc = loc} nε₂₁ nε₂₂) → nε₁₁ ≡ nε₂₁
ε∉-sum-injˡ {nε₂₁ = nε₁₁} {nε₂₂ = nε₁₂} refl = refl

ε∉-sum-injʳ : ∀ { l r : RE } { loc : ℕ } { nε₁₁ nε₂₁ : ε∉ l } { nε₁₂ nε₂₂ : ε∉ r }
  → (ε∉_+_ {l = l} {r = r} {loc = loc} nε₁₁ nε₁₂)
  ≡ (ε∉_+_ {l = l} {r = r} {loc = loc} nε₂₁ nε₂₂) → nε₁₂ ≡ nε₂₂
ε∉-sum-injʳ {nε₂₁ = nε₁₁} {nε₂₂ = nε₁₂} refl = refl

$-char : ∀ { c d : Char } { loc₁ loc₂ : ℕ } → ($ c ` loc₁) ≡ ($ d ` loc₂) → c ≡ d
$-char {d = c} {loc₂ = loc₁} refl = refl

$-loc : ∀ { c d : Char } { loc₁ loc₂ : ℕ } → ($ c ` loc₁) ≡ ($ d ` loc₂) → loc₁ ≡ loc₂
$-loc {d = c} {loc₂ = loc₁} refl = refl

●-injˡ : ∀ { l₁ l₂ s₁ s₂ : RE } { loc₁ loc₂ : ℕ }
  → (l₁ ● s₁ ` loc₁) ≡ (l₂ ● s₂ ` loc₂) → l₁ ≡ l₂
●-injˡ {l₂ = l₁} {s₂ = s₁} {loc₂ = loc₁} refl = refl

●-injʳ : ∀ { l₁ l₂ s₁ s₂ : RE } { loc₁ loc₂ : ℕ }
  → (l₁ ● s₁ ` loc₁) ≡ (l₂ ● s₂ ` loc₂) → s₁ ≡ s₂
●-injʳ {l₂ = l₁} {s₂ = s₁} {loc₂ = loc₁} refl = refl

●-injloc : ∀ { l₁ l₂ s₁ s₂ : RE } { loc₁ loc₂ : ℕ }
  → (l₁ ● s₁ ` loc₁) ≡ (l₂ ● s₂ ` loc₂) → loc₁ ≡ loc₂
●-injloc {l₂ = l₁} {s₂ = s₁} {loc₂ = loc₁} refl = refl

+-injˡ : ∀ { l₁ l₂ s₁ s₂ : RE } { loc₁ loc₂ : ℕ }
  → (l₁ + s₁ ` loc₁) ≡ (l₂ + s₂ ` loc₂) → l₁ ≡ l₂
+-injˡ {l₂ = l₁} {s₂ = s₁} {loc₂ = loc₁} refl = refl

+-injʳ : ∀ { l₁ l₂ s₁ s₂ : RE } { loc₁ loc₂ : ℕ }
  → (l₁ + s₁ ` loc₁) ≡ (l₂ + s₂ ` loc₂) → s₁ ≡ s₂
+-injʳ {l₂ = l₁} {s₂ = s₁} {loc₂ = loc₁} refl = refl

+-injloc : ∀ { l₁ l₂ s₁ s₂ : RE } { loc₁ loc₂ : ℕ }
  → (l₁ + s₁ ` loc₁) ≡ (l₂ + s₂ ` loc₂) → loc₁ ≡ loc₂
+-injloc {l₂ = l₁} {s₂ = s₁} {loc₂ = loc₁} refl = refl

*-inj : ∀ { r₁ r₂ : RE } { nε₁ : ε∉ r₁ } { nε₂ : ε∉ r₂ } { loc₁ loc₂ : ℕ }
  → (r₁ * nε₁ ` loc₁) ≡ (r₂ * nε₂ ` loc₂) → r₁ ≡ r₂
*-inj {r₂ = r₁} {nε₂ = nε₁} {loc₂ = loc₁} refl = refl

*-injloc : ∀ { r₁ r₂ : RE } { nε₁ : ε∉ r₁ } { nε₂ : ε∉ r₂ } { loc₁ loc₂ : ℕ }
  → (r₁ * nε₁ ` loc₁) ≡ (r₂ * nε₂ ` loc₂) → loc₁ ≡ loc₂
*-injloc {r₂ = r₁} {nε₂ = nε₁} {loc₂ = loc₁} refl = refl

-- transporting the nullability evidence along an equality of the bodies
*-respˡ : ∀ { r₁ r₂ : RE } { nε₁ : ε∉ r₁ } { loc : ℕ }
  → ( p : r₁ ≡ r₂ ) → (r₁ * nε₁ ` loc) ≡ (r₂ * subst ( λ x → ε∉ x ) p nε₁ ` loc)
*-respˡ refl = refl

*-resp : ∀ { r : RE } { nε₁ nε₂ : ε∉ r } { loc : ℕ }
  → nε₁ ≡ nε₂ → (r * nε₁ ` loc) ≡ (r * nε₂ ` loc)
*-resp {r = r} {loc = loc} q = cong ( λ nε → r * nε ` loc ) q

*-inv-resp : ∀ { r₁ r₂ : RE } { nε₁ : ε∉ r₁ } { nε₂ : ε∉ r₂ } { loc : ℕ }
  → ( p : r₁ ≡ r₂ )
  → (r₁ * nε₁ ` loc) ≡ (r₂ * nε₂ ` loc) → subst ( λ x → ε∉ x ) p nε₁ ≡ nε₂
*-inv-resp {nε₂ = nε₁} refl refl = refl

ε∉-≟ : ∀ { r : RE } ( nε₁ nε₂ : ε∉ r ) → Dec ( nε₁ ≡ nε₂ )
ε∉-≟ ε∉$ ε∉$ = yes refl
ε∉-≟ (ε∉fst nε₁) (ε∉fst nε₂) with ε∉-≟ nε₁ nε₂
...   | yes p = yes (cong ε∉fst p)
...   | no ¬p = no λ p → ¬p (ε∉-fst-inj p)
ε∉-≟ (ε∉fst nε₁) (ε∉snd nε₂) = no λ()
ε∉-≟ (ε∉snd nε₁) (ε∉snd nε₂) with ε∉-≟ nε₁ nε₂
...   | yes p = yes (cong ε∉snd p)
...   | no ¬p = no λ p → ¬p (ε∉-snd-inj p)
ε∉-≟ (ε∉snd nε₁) (ε∉fst nε₂) = no λ()
ε∉-≟ {l + s ` loc} (ε∉ nε₁₁ + nε₁₂) (ε∉ nε₂₁ + nε₂₂)
  with ε∉-≟ nε₁₁ nε₂₁ | ε∉-≟ nε₁₂ nε₂₂
...   | yes p | yes q = yes (trans (cong ( λ x → ε∉ x + nε₁₂ ) p)
                                   (cong ( λ y → ε∉ nε₂₁ + y ) q))
...   | no ¬p | _ = no λ x → ¬p (ε∉-sum-injˡ x)
...   | _ | no ¬q = no λ x → ¬q (ε∉-sum-injʳ x)

-- comparing two stars whose bodies are already known to be equal
*-≟ : ∀ { r₁ r₂ : RE } { nε₁ : ε∉ r₁ } { nε₂ : ε∉ r₂ } { loc : ℕ }
  → ( p : r₁ ≡ r₂ ) → Dec ( (r₁ * nε₁ ` loc) ≡ (r₂ * nε₂ ` loc) )
*-≟ {r₁} {nε₁ = nε₁} {nε₂ = nε₂} p with ε∉-≟ (subst ( λ x → ε∉ x ) p nε₁) nε₂
...   | yes q = yes (trans (*-respˡ p) (*-resp q))
...   | no ¬q = no λ eq → ¬q (*-inv-resp p eq)

_≟ᴱ_ : ( r s : RE ) → Dec ( r ≡ s )
ε ≟ᴱ ε = yes refl
ε ≟ᴱ ($ d ` loc₂) = no λ()
ε ≟ᴱ (l₂ ● s₂ ` loc₂) = no λ()
ε ≟ᴱ (l₂ + s₂ ` loc₂) = no λ()
ε ≟ᴱ (r₂ * nε₂ ` loc₂) = no λ()
($ c ` loc₁) ≟ᴱ ε = no λ()
($ c ` loc₁) ≟ᴱ ($ d ` loc₂) with Char._≟_ c d | Nat._≟_ loc₁ loc₂
...   | yes refl | yes refl = yes refl
...   | no ¬c | _ = no λ eq → ¬c ($-char eq)
...   | _ | no ¬l = no λ eq → ¬l ($-loc eq)
($ c ` loc₁) ≟ᴱ (l₂ ● s₂ ` loc₂) = no λ()
($ c ` loc₁) ≟ᴱ (l₂ + s₂ ` loc₂) = no λ()
($ c ` loc₁) ≟ᴱ (r₂ * nε₂ ` loc₂) = no λ()
(l₁ ● s₁ ` loc₁) ≟ᴱ ε = no λ()
(l₁ ● s₁ ` loc₁) ≟ᴱ ($ d ` loc₂) = no λ()
(l₁ ● s₁ ` loc₁) ≟ᴱ (l₂ ● s₂ ` loc₂) with l₁ ≟ᴱ l₂ | s₁ ≟ᴱ s₂ | Nat._≟_ loc₁ loc₂
...   | yes p | yes q | yes refl = yes (cong₂ ( λ l s → l ● s ` loc₁ ) p q)
...   | no ¬p | _ | _ = no λ eq → ¬p (●-injˡ eq)
...   | _ | no ¬q | _ = no λ eq → ¬q (●-injʳ eq)
...   | _ | _ | no ¬l = no λ eq → ¬l (●-injloc eq)
(l₁ ● s₁ ` loc₁) ≟ᴱ (l₂ + s₂ ` loc₂) = no λ()
(l₁ ● s₁ ` loc₁) ≟ᴱ (r₂ * nε₂ ` loc₂) = no λ()
(l₁ + s₁ ` loc₁) ≟ᴱ ε = no λ()
(l₁ + s₁ ` loc₁) ≟ᴱ ($ d ` loc₂) = no λ()
(l₁ + s₁ ` loc₁) ≟ᴱ (l₂ ● s₂ ` loc₂) = no λ()
(l₁ + s₁ ` loc₁) ≟ᴱ (l₂ + s₂ ` loc₂) with l₁ ≟ᴱ l₂ | s₁ ≟ᴱ s₂ | Nat._≟_ loc₁ loc₂
...   | yes p | yes q | yes refl = yes (cong₂ ( λ l s → l + s ` loc₁ ) p q)
...   | no ¬p | _ | _ = no λ eq → ¬p (+-injˡ eq)
...   | _ | no ¬q | _ = no λ eq → ¬q (+-injʳ eq)
...   | _ | _ | no ¬l = no λ eq → ¬l (+-injloc eq)
(l₁ + s₁ ` loc₁) ≟ᴱ (r₂ * nε₂ ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟ᴱ ε = no λ()
(r₁ * nε₁ ` loc₁) ≟ᴱ ($ d ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟ᴱ (l₂ ● s₂ ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟ᴱ (l₂ + s₂ ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟ᴱ (r₂ * nε₂ ` loc₂) with r₁ ≟ᴱ r₂ | Nat._≟_ loc₁ loc₂
...   | no ¬p | _ = no λ eq → ¬p (*-inj eq)
...   | yes p | no ¬l = no λ eq → ¬l (*-injloc eq)
...   | yes p | yes refl = *-≟ p

∈-dec : ( r : RE ) ( xs : List RE ) → Dec ( r ∈L xs )
∈-dec r [] = no λ()
∈-dec r (x ∷ xs) with r ≟ᴱ x
...   | yes p = yes (here p)
...   | no ¬p with ∈-dec r xs
...   | yes q = yes (there q)
...   | no ¬q = no λ{ (here eq) → ¬p eq ; (there q) → ¬q q }

-- "every element of xs is a member of L"
All-in? : ( L xs : List RE ) → Dec ( All ( λ r → r ∈L L ) xs )
All-in? L [] = yes ListAll.[]
All-in? L (x ∷ xs) with ∈-dec x L | All-in? L xs
...   | yes p | yes q = yes (ListAll._∷_ p q)
...   | no ¬p | _ = no λ{ (ListAll._∷_ p _) → ¬p p }
...   | _ | no ¬q = no λ{ (ListAll._∷_ _ q) → ¬q q }

-- membership of a letter in a list of letters (the alphabet bound)
∈-dec-char : ( c : Char ) ( cs : List Char ) → Dec ( c ∈L cs )
∈-dec-char c [] = no λ()
∈-dec-char c (d ∷ cs) with Char._≟_ c d
...   | yes refl = yes (here refl)
...   | no ¬c with ∈-dec-char c cs
...   | yes q = yes (there q)
...   | no ¬q = no λ{ (here eq) → ¬c eq ; (there q) → ¬q q }

-- a Boolean view of a decision: `tt : T (Dec-bool d)` is inhabited exactly
-- when d answers yes, which is how the certificates of §6 are written
Dec-bool : ∀ { p } { P : Set p } → Dec P → Bool
Dec-bool (yes _) = true
Dec-bool (no _) = false

force : ∀ { p } { P : Set p } ( d : Dec P ) → T (Dec-bool d) → P
force (yes x) tt = x
force (no ¬x) ()

-- membership in the left part of an appended list
-- (the left list is explicit so that _++_ can reduce)
in-++ˡ : ∀ { A : Set } { ys : List A } { p } → ( xs : List A ) → p ∈L xs → p ∈L (xs ++ ys)
in-++ˡ [] ()
in-++ˡ (x ∷ xs) (here eq) = here eq
in-++ˡ (x ∷ xs) (there q) = there (in-++ˡ xs q)

-- membership in the right part of an appended list
in-++ʳ : ∀ { A : Set } ( xs : List A ) { ys : List A } { p } → p ∈L ys → p ∈L (xs ++ ys)
in-++ʳ [] p∈ = p∈
in-++ʳ (x ∷ xs) p∈ = there (in-++ʳ xs p∈)

-- membership through a map
∈-map : ∀ { A B : Set } { f : A → B } { y : A } { xs : List A }
  → y ∈L xs → f y ∈L (map f xs)
∈-map {f = f} (here eq) = here (cong f eq)
∈-map {f = f} (there q) = there (∈-map q)

-- membership through concatMap
∈-concatMap : ∀ { A B : Set } { f : A → List B } { ys : List A } { y : A }
  → y ∈L ys → ∀ { p } → p ∈L (f y) → p ∈L (concatMap f ys)
∈-concatMap {f = f} {x ∷ ys} (here refl) p∈ = in-++ˡ (f x) p∈
∈-concatMap {f = f} {x ∷ ys} (there q) p∈ = in-++ʳ (f x) (∈-concatMap {f = f} {ys = ys} q p∈)

```

## 2. Closed supplies of expressions

```agda
-- the continuation expressions of the partial derivatives of r on c
pd-next : ( r : RE ) → ( c : Char ) → List RE
pd-next r c = map pd-expr (PosixPD.pdU[ r , c ])

-- the alphabet of an expression / of a list of expressions
charsOf : RE → List Char
charsOf ε = []
charsOf ($ c ` loc) = c ∷ []
charsOf (l ● s ` loc) = charsOf l ++ charsOf s
charsOf (l + s ` loc) = charsOf l ++ charsOf s
charsOf (r * nε ` loc) = charsOf r

-- one saturation step: a candidate supply generator
Sat : List RE → List Char → List RE
Sat L cs = L ++ concatMap ( λ r → concatMap ( pd-next r ) cs ) L

Sat-iter : List RE → List Char → ℕ → List RE
Sat-iter L cs zero = L
Sat-iter L cs (suc n) = Sat (Sat-iter L cs n) cs

-- a supply L is closed if the partial derivatives of its members (for letters
-- of cs) have their continuations in L again
Closed-member : List RE → RE → List Char → Set
Closed-member L r cs = ∀ { c } → c ∈L cs → All ( λ p → p ∈L L ) (pd-next r c)

Closed : List RE → List Char → Set
Closed L cs = ∀ { r } → r ∈L L → Closed-member L r cs

-- the test for one member
Closed-member! : ( L : List RE ) ( r : RE ) ( cs : List Char )
  → Dec ( Closed-member L r cs )
Closed-member! L r [] = yes λ()
Closed-member! L r (c ∷ cs) with All-in? L (pd-next r c) | Closed-member! L r cs
...   | yes p | yes q = yes λ{ (here refl) → p ; (there m) → q m }
...   | no ¬p | _ = no λ h → ¬p (h (here refl))
...   | yes p | no ¬q = no λ h → ¬q (λ m → h (there m))

-- the finite conjunction "every member of the list bound is closed w.r.t. L",
-- used to decide Closed (the bound L never grows, so the recursion is
-- structural in the list of members)
data ClosedW : List RE → List RE → List Char → Set where
  cnil  : ∀ { L cs } → ClosedW L [] cs
  ccons : ∀ { L x bound cs } → Closed-member L x cs → ClosedW L bound cs
        → ClosedW L (x ∷ bound) cs

ClosedW→in : ( L bound : List RE ) ( cs : List Char )
  → ClosedW L bound cs → (∀ { r } → r ∈L bound → Closed-member L r cs)
ClosedW→in L [] cs cnil ()
ClosedW→in L (x ∷ bound) cs (ccons q p) {r} (here eq) =
  subst ( λ z → Closed-member L z cs ) (sym eq) q
ClosedW→in L (x ∷ bound) cs (ccons q p) {r} (there m) = ClosedW→in L bound cs p m

in→ClosedW : ( L bound : List RE ) ( cs : List Char )
  → (∀ { r } → r ∈L bound → Closed-member L r cs) → ClosedW L bound cs
in→ClosedW L [] cs h = cnil
in→ClosedW L (x ∷ bound) cs h =
  ccons (h (here refl)) (in→ClosedW L bound cs λ m → h (there m))

ClosedW! : ( L bound : List RE ) ( cs : List Char ) → Dec ( ClosedW L bound cs )
ClosedW! L [] cs = yes cnil
ClosedW! L (x ∷ bound) cs with Closed-member! L x cs | ClosedW! L bound cs
...   | yes q | yes p = yes (ccons q p)
...   | no ¬q | _ = no λ{ (ccons q _) → ¬q q }
...   | yes q | no ¬p = no λ{ (ccons _ p) → ¬p p }

-- is the supply closed under its own members?
Closed! : ( L : List RE ) ( cs : List Char ) → Dec ( Closed L cs )
Closed! L cs with ClosedW! L L cs
...   | yes w = yes (ClosedW→in L L cs w)
...   | no ¬w = no λ h → ¬w (in→ClosedW L L cs h)

-- the same test as a Boolean (used by the certificates of §6)
Closed? : ( L : List RE ) ( cs : List Char ) → Bool
Closed? L cs = Dec-bool (Closed! L cs)

-- and the same for a word: are all its letters in the alphabet?
All-in?-char : ( al w : List Char ) → Dec ( All ( λ c → c ∈L al ) w )
All-in?-char al [] = yes ListAll.[]
All-in?-char al (c ∷ w) with ∈-dec-char c al | All-in?-char al w
...   | yes p | yes q = yes (ListAll._∷_ p q)
...   | no ¬p | _ = no λ{ (ListAll._∷_ p _) → ¬p p }
...   | _ | no ¬q = no λ{ (ListAll._∷_ _ q) → ¬q q }

```

## 3. The bound is preserved by one partial-derivative step

```agda
-- compose-pdi-with keeps the continuation, so the bound transfers along it
map-compose-in : ∀ { r d pref c } ( M : List RE ) ( d→r : U d → U r )
  → ( s-ev : ∀ ( v : U d ) → proj₁ (flat {r} (d→r v)) ≡ pref ++ proj₁ (flat {d} v) )
  → ( pds : List (PDInstance d c) )
  → All ( λ p → p ∈L M ) (map pd-expr pds)
  → All ( λ q → pd*-expr q ∈L M ) (map (PDI.compose-pdi-with {r} {d} {pref} {c} d→r s-ev) pds)
map-compose-in M d→r s-ev [] h = ListAll.[]
map-compose-in M d→r s-ev (pdinstance {p} {d} {c} p→d ev ∷ pds) (ListAll._∷_ h₁ h₂) =
  ListAll._∷_ h₁ (map-compose-in M d→r s-ev pds h₂)

-- mapping a function over a list preserves the bound
map-All-in : ∀ { A : Set } ( f : A → RE ) ( xs : List A ) ( L : List RE )
  → All ( λ x → f x ∈L L ) xs → All ( λ p → p ∈L L ) (map f xs)
map-All-in f [] L h = ListAll.[]
map-All-in f (x ∷ xs) L (ListAll._∷_ hx h′) = ListAll._∷_ hx (map-All-in f xs L h′)

-- one path instance advanced by one letter
advance-level : ∀ { r pref c } ( L : List RE ) ( cs : List Char )
  ( pdi : PDInstance* r pref )
  → Closed L cs
  → pd*-expr pdi ∈L L
  → c ∈L cs
  → All ( λ q → pd*-expr q ∈L L ) (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi)
advance-level {r} {pref} {c} L cs (pdinstance* {d} {r} {pref} d→r s-ev) cl d∈ c∈ =
  map-compose-in L d→r s-ev (PosixPD.pdU[ d , c ]) (cl d∈ c∈)

-- a whole state advanced by one letter
all-advance-level : ∀ { r pref c } ( L : List RE ) ( cs : List Char )
  ( pdis : List (PDInstance* r pref) )
  → Closed L cs
  → All ( λ pdi → pd*-expr pdi ∈L L ) pdis
  → c ∈L cs
  → All ( λ pdi → pd*-expr pdi ∈L L )
        (List.concatMap (PosixPD.advance-pdi*-with-c {r} {pref} {c}) pdis)
all-advance-level {r} {pref} {c} L cs [] cl h c∈ = ListAll.[]
all-advance-level {r} {pref} {c} L cs (pdi ∷ pdis) cl (ListAll._∷_ h₁ h₂) c∈ =
  ++⁺ (advance-level L cs pdi cl h₁ c∈) (all-advance-level L cs pdis cl h₂ c∈)
-- any number of steps
aux-bound : ∀ { r pref } ( L : List RE ) ( al : List Char ) ( suff : List Char )
  → ( pdis : List (PDInstance* r pref) )
  → Closed L al
  → All ( λ pdi → pd*-expr pdi ∈L L ) pdis
  → All ( λ c → c ∈L al ) suff
  → All ( λ pdi → pd*-expr pdi ∈L L ) (PosixPD.pdUMany-aux {r} {pref} suff pdis)
-- the nil clause of pdUMany-aux rewrites its result with ++-identityʳ; the
-- bound does not inspect the consumed prefix, so the same rewrite here
aux-bound {r} {pref} L al [] pdis cl h wcs rewrite ++-identityʳ pref = h
aux-bound {r} {pref} L al (c ∷ w) pdis cl h (ListAll._∷_ wc wcs) =
  aux-bound {r} {pref ∷ʳ c} L al w
            (List.concatMap (PosixPD.advance-pdi*-with-c {r} {pref} {c}) pdis)
            cl (all-advance-level L al pdis cl h wc) wcs

```

## 4. The descendants of an expression are bounded by a closed supply

```agda
-- every element of the pd-descendant state of r after w is a member of L
Desc⊆ : ( r : RE ) ( L : List RE ) ( al : List Char ) ( w : List Char )
  → r ∈L L
  → Closed L al
  → All ( λ c → c ∈L al ) w
  → All ( λ p → p ∈L L ) (pd*-Desc r w)
Desc⊆ r L al w r∈ cl wc =
  map-All-in pd*-expr (PosixPD.pdUMany[ r , w ]) L
    (aux-bound {r} {[]} L al w
      (pdinstance* {r} {r} {[]} PosixPD.injId PosixPD.injId-sound ∷ [])
      cl (ListAll._∷_ r∈ ListAll.[]) wc)

-- for a single word the same statement is decidable without any closure proof
Desc⊆! : ( r : RE ) ( L : List RE ) ( w : List Char )
  → Dec ( All ( λ p → p ∈L L ) (pd*-Desc r w) )
Desc⊆! r L w = All-in? L (pd*-Desc r w)

-- all lists over L of length n (a computable finite enumeration)
listsOf : ℕ → List RE → List (List RE)
listsOf zero L = [] ∷ []
listsOf (suc n) L = concatMap ( λ x → map ( λ xs → x ∷ xs ) (listsOf n L) ) L

-- a list whose elements are all in L is one of those lists
listsOf-complete : ∀ ( L : List RE ) ( xs : List RE )
  → All ( λ p → p ∈L L ) xs → xs ∈L listsOf (length xs) L
listsOf-complete L [] h = here refl
listsOf-complete L (x ∷ xs) (ListAll._∷_ hx h′) =
  ∈-concatMap hx (∈-map {f = λ xs₁ → x ∷ xs₁} (listsOf-complete L xs h′))

-- the descendants of r form a finite set: for every word over al its state is
-- an element of the finite list listsOf (length ...) L
Desc-finite : ( r : RE ) ( L : List RE ) ( al : List Char ) ( w : List Char )
  → r ∈L L
  → Closed L al
  → All ( λ c → c ∈L al ) w
  → pd*-Desc r w ∈L listsOf (length (pd*-Desc r w)) L
Desc-finite r L al w r∈ cl wc =
  listsOf-complete L (pd*-Desc r w) (Desc⊆ r L al w r∈ cl wc)

```

`Desc⊆` / `Desc-finite` are the formal counterpart of the paper's
`prop:finite-dissimilar`.  A *closed supply* `L` is a finite list, the first
hypothesis `r ∈L L` is a reflexivity check, and the other two are decidable
(`Closed!` for the supply, `All-in?-char` for the word), so both can be
discharged by computation (§6).

Read precisely: for **each** word the state is an element of an explicitly
finite set (`listsOf (length (pd*-Desc r w)) L`, computable from `w` and `L`).
A *single* finite set containing the states of all words would additionally
need a bound on the length of the states; that fails for these un-quotiented
lists (§7) and is exactly what the paper's quotient by similarity buys.  What
*is* independent of the word is the bound on the expressions occurring in the
states (`Desc⊆`): the paper's descendants are assembled by gluing precisely
these continuations (`sum-build` of `cgp.ambig.Canonic`), so `L` bounds the
material every one of them is made of.  The quotienting step itself is not
formalized here.

## 5. Relation with the paper's statement

* The paper's states are single expressions obtained by re-gluing the partial
  derivatives (`derivᵖ r w` of `cgp.ambig.Canonic` §8); `canonic` then
  quotients them by similarity.  Quotienting can only shrink the set, so the
  bound above bounds the paper's `Desc(r)` as well.
* The paper's proof of finiteness is by induction on the structure of `r`
  (expressions generated by the derivative rules).  Here the same argument
  becomes a *semi-decision procedure*: `Sat-iter (r ∷ []) (charsOf r) n`
  enumerates the expressions reachable within `n` steps, and `Closed!` decides
  whether the result is already closed — if it is, the bound holds for every
  word.
* Whether the iteration always stabilizes (the general existence of a closed
  supply) is *not* proved here; §6 certifies it for concrete expressions.

## 6. Certified supplies (computed)

Both hypotheses of `Desc⊆` are decidable, so for a concrete expression the
supply can be *computed* (by saturation) and its closedness *checked* (by
`Closed?`).  The examples below are checked by the type checker: the
`refl` proofs only succeed if the computation really says yes.

```agda
-- the paper's A3 example of cgp.ambig.Canonic §6: ((a + b) · c) + (a · c)
a3-r : RE
a3-r = Canonic.pd-a3-target

a3-al : List Char
a3-al = charsOf a3-r

-- three rounds of saturation from r give a closed supply
a3-supply : List RE
a3-supply = Sat-iter (a3-r ∷ []) a3-al 3

a3-supply-closed-flag : Closed? a3-supply a3-al ≡ true
a3-supply-closed-flag = refl

a3-supply-closed : Closed a3-supply a3-al
a3-supply-closed = force (Closed! a3-supply a3-al) tt

-- hence: for every word over the alphabet, every expression of the state of
-- r after that word is one of the finitely many expressions of a3-supply
a3-Desc⊆ : ( w : List Char ) → All ( λ c → c ∈L a3-al ) w
  → All ( λ p → p ∈L a3-supply ) (pd*-Desc a3-r w)
a3-Desc⊆ w wc = Desc⊆ a3-r a3-supply a3-al w (here refl) a3-supply-closed wc

-- for a concrete word the bound is also checkable without any closure proof
a3-state-in-supply : Dec-bool (Desc⊆! a3-r a3-supply ( 'a' ∷ 'b' ∷ 'c' ∷ [] ))
  ≡ true
a3-state-in-supply = refl

-- and the same instance, proved through the general theorem: the word is over
-- the alphabet, so its state is an element of the finite enumeration of lists
-- over the supply (the paper's "Desc(r) is finite")
a3-word : All ( λ c → c ∈L a3-al ) ( 'a' ∷ 'b' ∷ 'c' ∷ [] )
a3-word = force (All-in?-char a3-al ( 'a' ∷ 'b' ∷ 'c' ∷ [] )) tt

a3-state-enumerated : pd*-Desc a3-r ( 'a' ∷ 'b' ∷ 'c' ∷ [] )
  ∈L listsOf (length (pd*-Desc a3-r ( 'a' ∷ 'b' ∷ 'c' ∷ [] ))) a3-supply
a3-state-enumerated =
  Desc-finite a3-r a3-supply a3-al ( 'a' ∷ 'b' ∷ 'c' ∷ []) (here refl)
    a3-supply-closed a3-word

```

Now a Kleene star, which is where a supply of subexpressions of `r` is not
enough: the rule of `pdU` for `r ⋆` glues a partial derivative of the body in
front of `r ⋆`.

```agda
-- a ⋆
star-a : RE
star-a = ($ 'a' ` 1) * ε∉$ ` 2

star-a-al : List Char
star-a-al = charsOf star-a

-- the subexpressions of a ⋆ (a ⋆ itself, a, ε): NOT closed, the missing
-- element is the continuation ε · (a ⋆) that the star rule produces
star-a-subterms : List RE
star-a-subterms = star-a ∷ ($ 'a' ` 1) ∷ ε ∷ []

star-a-subterms-not-closed : Closed? star-a-subterms star-a-al ≡ false
star-a-subterms-not-closed = refl

-- closing it up: one round of saturation is enough here
star-a-supply : List RE
star-a-supply = Sat-iter (star-a ∷ []) star-a-al 1

star-a-supply-closed-flag : Closed? star-a-supply star-a-al ≡ true
star-a-supply-closed-flag = refl

star-a-supply-closed : Closed star-a-supply star-a-al
star-a-supply-closed = force (Closed! star-a-supply star-a-al) tt

-- the state after `a` is the glued expression ε · (a ⋆), and it stays there:
-- the states of a ⋆ on a ⁺¹, a ⁺², a ⁺³ are all the same one-element state
star-a-state-a : pd*-Desc star-a ( 'a' ∷ [] ) ≡ ( ε ● star-a ` 2 ) ∷ []
star-a-state-a = refl

star-a-state-a³ : pd*-Desc star-a ( 'a' ∷ 'a' ∷ 'a' ∷ [] ) ≡ ( ε ● star-a ` 2 ) ∷ []
star-a-state-a³ = refl

-- all of them are in the supply (checked without any closure proof)
star-a-state-in-supply : Dec-bool (Desc⊆! star-a star-a-supply ( 'a' ∷ 'a' ∷ [] ))
  ≡ true
star-a-state-in-supply = refl

```

## 7. Duplicate instances: state *lengths* are not bounded

`pdU` returns one instance per empty parse tree of a nullable left factor
(the example at the top of `cgp.posix.PartialDerivative` §"Example":
`(ε + ε) · a` has two empty parse trees), so a state *list* keeps
duplicates.  A bound on the *expressions* of the states therefore does not
bound their lengths — this is exactly what the paper's quotient by similarity
removes (`canonic` of `cgp.ambig.Canonic`, whose `dedup` drops later
`≈₀`-duplicates of a `+` spine).

```agda
-- ( (ε + ε) · a ) ⋆
dual-r : RE
dual-r = ( ( ε + ε ` 10 ) ● ($ 'a' ` 1) ` 2 ) * (ε∉snd ε∉$) ` 3

dual-al : List Char
dual-al = charsOf dual-r

-- the state after `a` has the same expression twice (two empty parse trees
-- of ε + ε), so its length is 2 while the supply has fewer elements
dual-state-a-len : length (pd*-Desc dual-r ( 'a' ∷ [] )) ≡ 2
dual-state-a-len = refl

-- and the multiplicity doubles at every pass through the star
dual-state-a²-len : length (pd*-Desc dual-r ( 'a' ∷ 'a' ∷ [] )) ≡ 4
dual-state-a²-len = refl

dual-state-a³-len : length (pd*-Desc dual-r ( 'a' ∷ 'a' ∷ 'a' ∷ [] )) ≡ 8
dual-state-a³-len = refl

-- removing the duplicates (the similarity quotient) leaves one element
dual-state-a-dedup : Canonic.dedup (pd*-Desc dual-r ( 'a' ∷ [] ))
  ≡ ( ( ε ● dual-r ` 3 ) ∷ [] , true )
dual-state-a-dedup = refl

```

With duplicate-free states the length is bounded by the size of the supply and
the enumeration `listsOf (length L) L` of §4 can be replaced by
`listsOf (length supply) supply`; that refinement is not written up here.
