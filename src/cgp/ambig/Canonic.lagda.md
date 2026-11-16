# Canonical Representatives (Idemp) — the A3 mechanism

This module implements the *similarity* machinery of section 5 of

> Martin Sulzmann and Kenny Zhuo Ming Lu.
> Derivative-Based Diagnosis of Regular Expression Ambiguity. CIAA 2016.
> (`/home/luzm/assembla/regexp/trunk/ambig-check/finalCIAA2016.tex`)

needed for criterion **A3** of the Ambiguity Criteria proposition (paper section 6):

* **A3** `lang(canonic(deriv s x)) ≠ {}` and `deriv s x →fs canonic(deriv s x)`
  with rule **Idemp** applied.

## What is formalized here

1. Structural congruence `_≈₀_`: equality of expressions modulo the AST
   location annotations of this project (two occurrences of the same
   alternative in a source expression always carry *different* AST locations,
   so the paper's `Idemp  r + r ≈ r` must be implemented with a location
   insensitive equality).
2. `canonic : RE → RE × Bool` — the canonical representative of paper
   Definition `Canonical Representative`:
   (1) alternatives in right-associative normal form (`Assoc`),
   (2) duplicates removed (`Idemp`, keeping the first occurrence —
   "alternatives keep their relative position"),
   the second component records whether rule `Idemp` was applied.
   Following the paper's `Hole Expressions` there is no rewriting inside a
   Kleene star.
3. `Cast` — the parse tree transformation of paper Definition
   `Similarity with Parse Tree Transformation` for the congruence cases:
   `u ∈ 𝓣 r` is transported to `𝓣 s` for `r ≈₀ s`, preserving `| u |`.
4. The *statements* the A3 soundness needs: `pd-expr`, `pd-alts`, the
   `Idemp` transition test `pd-Idemp?`, the positioned duplicate witness
   (`dups-≈₀-dups`) and the member classification (§4.2) — and the
   `crit` disjunction of the criteria (§8).  The soundness closure
   itself — `dup-sum→Ambig` / `Ctx-dup→Ambig` (Soundness §1), the
   `a + a` example (Soundness §2), and the full `pdU`-clause chain
   Soundness §7–§11 ending in
   `pd-Idemp : pd-Idemp? (pdU[ q , c ]) ≡ true → Ambig q` — lives in
   `cgp.ambig.Soundness`; the converse direction lives in
   `cgp.ambig.Completeness`.  Together with `cgp.ambig.AmbigCheck`
   (`ambiguousSum`, `notA1Sum`, `notA2Sum`) the example shows the A3
   criterion genuinely adds detection power: `a + a` is missed by A1
   and A2 but caught there.
5. Section 5: the *general* form of the criteria — one master lift
   `lift-Ambig` (an injective path tree map with the soundness evidence of
   a `PDInstance*` transports `Ambig p → Ambig r`), from which
   `lift-A1→Ambig`, `lift-A2→Ambig` and the pd-state corollaries
   `pd*-A1→Ambig`, `pd*-A2→Ambig` factor (`AmbigCheck.A1→Ambig` etc.
   are the `w = []`, `inj = id` instances); the Ctx-dup versions
   `lift-Ctx-dup→Ambig` / `pd*-Ctx-dup→Ambig` travel with
   `Ctx-dup→Ambig` in `cgp.ambig.Soundness` §6.
6. Section 6: the paper's `Desc(r)` *as a single expression* via the
   `oplus` trick — `derivᵖ r w` re-glues the partial-derivative
   continuations of `pdUMany[ r , w ]` into one state expression, `_∈Desc_`
   states the paper's quantification over realizable states, and `A3?` is
   the paper's A3 test as a computable boolean (verified `true` on the
   §4.1 example).  This form exists only to state the paper's
   `canonic(deriv s x)` verbatim; for the tests §7's list form is used.
7. Section 7: the pd-native states — `pd*-Desc r w` is the Antimirov state
   itself (the list of partial-derivative continuations of `pdUMany[ r , w ]`,
   no re-gluing, no `Maybe`) and `A3-state? r w c` applies the A3 test to
   that list; §5's corollaries then apply to *any* member of the list.

## Why the full A3 condition is not stated

A3 quantifies over `deriv s x` for descendants `s ∈ Desc(r)` of the paper's
FST (section 4).  The current formalism cannot express that:

* the project's `RE` has **no empty-language constructor** (`data RE` in
  `cgp.RE` is `ε | $_`_ | _●_`_ | _+_`_ | _*_`_`), so the Brzozowski
  derivative is not a total operation on `RE` (e.g. `deriv ($ c ` loc) x`
  for `x ≠ c` would have to be `∅`);
* there is no FST / `Desc(r)` construction in the project (the partial
  derivative `pdU` works directly on parse trees, not on expressions);
* the non-emptiness side condition `lang(…) ≠ {}` holds of every project
  `RE` automatically (`ParseTree.r-∃u`).

Hence the top-level instance ("`Idemp` applies to `r` ⇒ `r` ambiguous") is
formalized, which is exactly the situation the paper's A3 detects, minus the
derivative construction.

**However** (section 4 below) the derivative can be *mimicked by partial
derivatives*: `pdU[ r , x ]` (in `cgp.posix.PartialDerivative`, the same
route as the old `cgp.posix.Related`, now `cgp.relatedwork.RelatedWorkOkuiSuzuki`)
yields the partial derivatives whose sum denotes `deriv r x`, and each comes
with its injection `U p → U r` (the paper's transition tree maps).
So A3's "Idemp applied when canonicalizing `deriv s x`" becomes: the
continuations produced by `pdU` (flattened over their `+` spines) contain
two `≈₀`-equal members, which is decidable, and the pair of injections
builds the two parse trees directly.

```agda
{-# OPTIONS --rewriting #-}
module cgp.ambig.Canonic where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉ ; ε∈ ; ε∈?)

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU; LetterU; LeftU; RightU; PairU; ListU ; unListU ; flat ; r-∃u ; LeftU≢RightU )

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using ( Ambig ; AmbigA1 ; AmbigA2 ; Ctx ; 𝟘 ; Ctx●R ; L●Ctx ; Ctx+R ; L+Ctx ; plug ; CtxT ; CtxT-pres-flat ; CtxT-injective ; A1→Ambig ; A2→Ambig )

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; pdinstance-left ; pdinstance-right ; pdinstance-fst ; PDInstance* ; pdinstance* )

import cgp.empty.AllEmptyParseTree as AllEmpty

import cgp.posix.PartialDerivative as PosixPD

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; map ; concatMap ; length)

open import Data.List.Properties using (++-assoc ; ∷-injectiveˡ ; ∷-injectiveʳ ; length-map ; length-++ ; ∷-injective ; ++-identityʳ)

import Data.List.Relation.Unary.Any as ListAny
open ListAny using (Any; here; there)

import Data.List.Membership.Propositional as Membership
open Membership using (_∈_)

import Data.Empty as Empty
open Empty using (⊥; ⊥-elim)

import Data.Bool.Base as Bool
open Bool using (Bool; true; false; _∨_)

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using ( ℕ ; zero ; suc ; _≤_ ; z≤n ; s≤s )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-refl ; ≤-trans ; m≤n⇒m≤1+n )

import Data.List.Relation.Unary.All as ListAll

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym; cong₂; subst)

import Data.Product as Product
open Product using ( Σ ; Σ-syntax ; _,_ ; _×_ )

import Data.Sum as Sum
-- (not opened: `inj₁`/`inj₂` are pattern variables in
--   `cgp.ambig.Soundness` §3; the constructors are used qualified here)
open Σ using (proj₁ ; proj₂)

import Data.Maybe as Maybe
open Maybe using ( Maybe ; just ; nothing )

import Relation.Nullary as Nullary
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using ( Dec; yes; no; ⌊_⌋)

```

## 1. Similarity: structural equality modulo AST location (`≈₀`)

The paper's rules `Idemp`, `Comm`, `Assoc` compare expressions up to the
AC-theory of `+`.  For duplicate *detection* we use the location-insensitive
structural congruence: two alternatives are duplicates when they have the
same shape (the `Idemp` side condition `r + r`).

```agda
data _≈₀_ : RE → RE → Set where
  ≈₀-ε : ε ≈₀ ε
  ≈₀-$ : ∀ ( c : Char ) ( loc₁ loc₂ : ℕ )
    → ($ c ` loc₁) ≈₀ ($ c ` loc₂)
  ≈₀-● : ∀ { l₁ s₁ l₂ s₂ : RE } { loc₁ loc₂ : ℕ }
    → l₁ ≈₀ l₂ → s₁ ≈₀ s₂ → (l₁ ● s₁ ` loc₁) ≈₀ (l₂ ● s₂ ` loc₂)
  ≈₀-+ : ∀ { l₁ s₁ l₂ s₂ : RE } { loc₁ loc₂ : ℕ }
    → l₁ ≈₀ l₂ → s₁ ≈₀ s₂ → (l₁ + s₁ ` loc₁) ≈₀ (l₂ + s₂ ` loc₂)
  ≈₀-* : ∀ { r s : RE } { nεr : ε∉ r } { nεs : ε∉ s } { loc₁ loc₂ : ℕ }
    → r ≈₀ s → (r * nεr ` loc₁) ≈₀ (s * nεs ` loc₂)

≈₀-refl : ∀ ( r : RE ) → r ≈₀ r
≈₀-refl ε = ≈₀-ε
≈₀-refl ($ c ` loc) = ≈₀-$ c loc loc
≈₀-refl (l ● s ` loc) = ≈₀-● (≈₀-refl l) (≈₀-refl s)
≈₀-refl (l + s ` loc) = ≈₀-+ (≈₀-refl l) (≈₀-refl s)
≈₀-refl (r * nε ` loc) = ≈₀-* (≈₀-refl r)

-- (purpose): `_≈₀_` is symmetric
-- (used in): `pdU-+-location` below — the §4.2 split carries the pair
--   as `later ≈₀ earlier` (a positional convention), while
--   `pd-cross-positions→Ambig` reads `≈₀` left-to-right along the
--   two branches of the sum
-- (proof idea): induction on the derivation
≈₀-sym : ∀ { r s : RE } → s ≈₀ r → r ≈₀ s
≈₀-sym ≈₀-ε = ≈₀-ε
≈₀-sym (≈₀-$ c loc₁ loc₂) = ≈₀-$ c loc₂ loc₁
≈₀-sym (≈₀-● p q) = ≈₀-● (≈₀-sym p) (≈₀-sym q)
≈₀-sym (≈₀-+ p q) = ≈₀-+ (≈₀-sym p) (≈₀-sym q)
≈₀-sym (≈₀-* p) = ≈₀-* (≈₀-sym p)

_≟₀_ : ( r s : RE ) → Dec ( r ≈₀ s )
ε ≟₀ ε = yes ≈₀-ε
ε ≟₀ ($ d ` loc₂) = no λ()
ε ≟₀ (l₂ ● s₂ ` loc₂) = no λ()
ε ≟₀ (l₂ + s₂ ` loc₂) = no λ()
ε ≟₀ (r₂ * nε₂ ` loc₂) = no λ()
($ c ` loc₁) ≟₀ ε = no λ()
($ c ` loc₁) ≟₀ ($ d ` loc₂) with c Char.≟ d
...   | yes refl = yes (≈₀-$ c loc₁ loc₂)
...   | no c≢d = no λ{(≈₀-$ .c .loc₁ .loc₂) → c≢d refl}
($ c ` loc₁) ≟₀ (l₂ ● s₂ ` loc₂) = no λ()
($ c ` loc₁) ≟₀ (l₂ + s₂ ` loc₂) = no λ()
($ c ` loc₁) ≟₀ (r₂ * nε₂ ` loc₂) = no λ()
(l₁ ● s₁ ` loc₁) ≟₀ ε = no λ()
(l₁ ● s₁ ` loc₁) ≟₀ ($ d ` loc₂) = no λ()
(l₁ ● s₁ ` loc₁) ≟₀ (l₂ ● s₂ ` loc₂) with l₁ ≟₀ l₂ | s₁ ≟₀ s₂
...   | yes p | yes q = yes (≈₀-● p q)
...   | no ¬p | _ = no λ{(≈₀-● p q) → ¬p p}
...   | _ | no ¬q = no λ{(≈₀-● p q) → ¬q q}
(l₁ ● s₁ ` loc₁) ≟₀ (l₂ + s₂ ` loc₂) = no λ()
(l₁ ● s₁ ` loc₁) ≟₀ (r₂ * nε₂ ` loc₂) = no λ()
(l₁ + s₁ ` loc₁) ≟₀ ε = no λ()
(l₁ + s₁ ` loc₁) ≟₀ ($ d ` loc₂) = no λ()
(l₁ + s₁ ` loc₁) ≟₀ (l₂ ● s₂ ` loc₂) = no λ()
(l₁ + s₁ ` loc₁) ≟₀ (l₂ + s₂ ` loc₂) with l₁ ≟₀ l₂ | s₁ ≟₀ s₂
...   | yes p | yes q = yes (≈₀-+ p q)
...   | no ¬p | _ = no λ{(≈₀-+ p q) → ¬p p}
...   | _ | no ¬q = no λ{(≈₀-+ p q) → ¬q q}
(l₁ + s₁ ` loc₁) ≟₀ (r₂ * nε₂ ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟₀ ε = no λ()
(r₁ * nε₁ ` loc₁) ≟₀ ($ d ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟₀ (l₂ ● s₂ ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟₀ (l₂ + s₂ ` loc₂) = no λ()
(r₁ * nε₁ ` loc₁) ≟₀ (r₂ * nε₂ ` loc₂) with r₁ ≟₀ r₂
...   | yes p = yes (≈₀-* p)
...   | no ¬p = no λ{(≈₀-* p) → ¬p p}

-- list membership via the location insensitive equality
any-≈₀ : ( r : RE ) → ( rs : List RE ) → Bool
any-≈₀ r rs = List.any ( λ s → ⌊ r ≟₀ s ⌋) rs

```

## 2. Parse tree transport along `≈₀` (paper's `Idemp` tree transformation)

For `r ≈₀ s` every parse tree of `r` is a parse tree of `s` (the congruence
rules of Definition `Similarity with Parse Tree Transformation` act as the
identity on the tree structure), and flattening is preserved.

```agda
Cast : ∀ { r s : RE } → r ≈₀ s → U r → U s
Cast ≈₀-ε EmptyU = EmptyU
Cast (≈₀-$ c loc₁ loc₂) (LetterU .c) = LetterU c
Cast (≈₀-● pq ps) (PairU u v) = PairU (Cast pq u) (Cast ps v)
Cast (≈₀-+ pq ps) (LeftU u) = LeftU (Cast pq u)
Cast (≈₀-+ pq ps) (RightU v) = RightU (Cast ps v)
Cast (≈₀-* p) (ListU us) = ListU (List.map ( λ u → Cast p u) us)

Cast-pres-flat : ∀ { r s : RE } ( p : r ≈₀ s ) ( u : U r )
  → proj₁ (flat (Cast p u)) ≡ proj₁ (flat u)
Cast-pres-flat ≈₀-ε EmptyU = refl
Cast-pres-flat (≈₀-$ c loc₁ loc₂) (LetterU .c) = refl
Cast-pres-flat (≈₀-● pq ps) (PairU u v) = cong₂ _++_ (Cast-pres-flat pq u) (Cast-pres-flat ps v)
Cast-pres-flat (≈₀-+ pq ps) (LeftU u) = Cast-pres-flat pq u
Cast-pres-flat (≈₀-+ pq ps) (RightU v) = Cast-pres-flat ps v
Cast-pres-flat (≈₀-* p) (ListU []) = refl
Cast-pres-flat (≈₀-* p) (ListU (u ∷ us)) = cong₂ _++_ (Cast-pres-flat p u) (Cast-pres-flat (≈₀-* p) (ListU us))

```

## 3. `canonic`: right associative normal form + duplicate removal

Paper Definition `Canonical Representative`:
(1) flatten all `+` to right-associative form (`Assoc`),
(2) remove duplicates (`Idemp`; the *first* occurrence is kept so that
"alternatives keep their relative position"),
(3) no rewriting inside a Kleene star (`Hole Expressions`).

The second component of the result records whether rule `Idemp` was applied
(the A3 side condition).

```agda
-- the + spine of an expression as a list of alternatives
sum-spine : RE → List RE
sum-spine (l + s ` loc) = sum-spine l ++ sum-spine s
sum-spine r = r ∷ []

-- the [] case never happens (a spine is never empty; the project has no ∅)
sum-build : List RE → ℕ → RE
sum-build [] loc = ε
sum-build (r ∷ []) loc = r
sum-build (r ∷ rs) loc = r + sum-build rs loc ` loc

-- remove later duplicates, keep the first occurrences in order
dedup : List RE → List RE × Bool
dedup xs = go [] xs
  where
    go : List RE → List RE → List RE × Bool
    go kept [] = kept , false
    go kept (r ∷ rs) with any-≈₀ r kept
    ...   | true = proj₁ (go kept rs) , true
    ...   | false = go (kept ++ (r ∷ [])) rs

canonic : RE → RE × Bool
canonic ε = ε , false
canonic ($ c ` loc) = ($ c ` loc) , false
canonic (l ● s ` loc) with canonic l | canonic s
...   | l₁ , fl | s₁ , fs = (l₁ ● s₁ ` loc) , fl ∨ fs
canonic (r * nε ` loc) = (r * nε ` loc) , false
canonic (l + s ` loc) with canonic l | canonic s
...   | l₁ , fl | s₁ , fs with dedup (sum-spine l₁ ++ sum-spine s₁)
...   | m , fd = sum-build m loc , fl ∨ fs ∨ fd

```

## 4. A3 by mimicking the derivative with partial derivatives

The paper's `deriv s x` is a single expression; this project computes
*partial* derivatives instead (`cgp.posix.PartialDerivative.pdU`).
A partial derivative instance `PDInstance r c` carries

* its continuation expression `p` (`pdinstance {p} inj ev`), and
* the injection `inj : U p → U r` with the soundness evidence
  `| inj u | = c ∷ | u |` — this is exactly the paper's transition
  parse-tree map (Definition `Injection`).

Since Brzozowski's derivative distributes over `+`, the union of the
continuations of `pdU[ r , x ]` (summed) denotes `deriv r x`; the
`posix` variant even *merges* two instances into one with a sum
continuation (`pdinstance-oplus`/`fuse`, needed for POSIX order).
Note `fuse` itself is the actualization of the *distributivity of the
derivative*, not of `Idemp` — it merges continuations without an
equality test.  `Idemp` fires exactly when the continuations combined
by `fuse` happen to be `≈₀`-equal, i.e. when the fused continuation
contains a duplicated alternative; detecting that is the job of
`pd-Idemp?` below.  So the A3 test becomes: *after flattening the `+`
spines of all continuations, do two `≈₀`-equal members exist?*  The
non-emptiness condition `lang(canonic(deriv s x)) ≠ {}` holds
automatically (`r-∃u`).

```agda
-- the continuation expression of one pd path
pd-expr : ∀ { r : RE } { c : Char } → PDInstance r c → RE
pd-expr (pdinstance {p} inj ev) = p

-- the transition map of one pd path, read off at a named continuation
pd-inj : ∀ { r p : RE } { c : Char } → ( pdi : PDInstance r c )
  → pd-expr pdi ≡ p → (U p → U r)
pd-inj (pdinstance {p} inj ev) refl = inj

pd*-expr : ∀ { r : RE } { pref : List Char } → PDInstance* r pref → RE
pd*-expr (pdinstance* {p} inj ev) = p

-- all alternatives of the (distributed) derivative deriv r x
pd-alts : ∀ { r : RE } { c : Char } → List (PDInstance r c) → List RE
pd-alts pdis = concatMap ( λ pdi → sum-spine (pd-expr pdi) ) pdis

-- does canonicalizing the sum of the continuations require the Idemp rule?
-- (`dups-≈₀-go` is the scan, hoisted out of a `where` clause so §4.2 can
-- reason about it; the equations are the ones `dups-≈₀` had)
dups-≈₀-go : List RE → List RE → Bool
dups-≈₀-go kept [] = false
dups-≈₀-go kept (r ∷ rs) with any-≈₀ r kept
...   | true = true
...   | false = dups-≈₀-go (kept ++ (r ∷ [])) rs

dups-≈₀ : List RE → Bool
dups-≈₀ xs = dups-≈₀-go [] xs

pd-Idemp? : ∀ { r : RE } { c : Char } → List (PDInstance r c) → Bool
pd-Idemp? pdis = dups-≈₀ (pd-alts pdis)

```

### 4.1. Example: the duplicate is *created by the derivative*

`((a + b) ● c) + (a ● c)` has no duplicate alternatives itself —
`canonic` reports `Idemp` was **not** applied (the first component below);
its structure is also not caught by A1/A2 (neither nullable nor a
concatenation with a duplicated empty component).  But its derivative on
`'a` has two equal continuations `ε ● c` (from the `a` inside `a + b` and
from the second `a`), so `pd-Idemp?` fires and `pd-pairs→Ambig` proves the
expression ambiguous.  This is precisely the situation the paper reserves
for **A3**.

```agda
pd-a3-target : RE
pd-a3-target = ( (($ 'a' ` 1) + ($ 'b' ` 2) ` 3) ● ($ 'c' ` 4) ` 5 )
               + ( ($ 'a' ` 6) ● ($ 'c' ` 7) ` 8 ) ` 9

-- the top-level Idemp test does NOT fire (unlike Soundness §2):
pd-a3-canonic-flag : proj₂ (canonic pd-a3-target) ≡ false
pd-a3-canonic-flag = refl

-- but computing the partial derivatives on 'a and flattening the
-- continuations ε ● ($ 'c' ` 4) ` 5  and  ε ● ($ 'c' ` 7) ` 8
-- finds the duplicate: the continuations of the partial derivatives of
-- pd-a3-target on 'a' are exactly the two equal terms ε ● ($ 'c' ` 4) ` 5
-- and ε ● ($ 'c' ` 7) ` 8 (the posix pd fuses them into one instance,
-- their + spine is recovered by sum-spine):
pd-a3-continuations : pd-alts (PosixPD.pdU[ pd-a3-target , 'a' ]) ≡ ((ε ● ($ 'c' ` 4) ` 5) ∷ (ε ● ($ 'c' ` 7) ` 8) ∷ [])
pd-a3-continuations = refl

pd-a3-Idemp-applied : pd-Idemp? (PosixPD.pdU[ pd-a3-target , 'a' ]) ≡ true
pd-a3-Idemp-applied = refl

-- the two pd instances (before the posix fusion), at the continuation

```

### 4.2. The test finds the duplicate when there is one

`pd-Idemp?` is defined as a scan, so none of the above says the scan *finds* a
duplicate that is there.  The instance `cgp.ambig.Completeness` §7's `pick-diff-record-prf` needs is the one
where `pdU[ r , c ]` holds two **distinct members** continuing at **one**
expression: flattening then puts the same alternative in the list twice, and the
scan has to answer `true`.  The two structural facts that make that go —
scanning more list never loses a `true`, and a value already in the scan's window
that occurs again in the rest fires it — are worth having in general.

```agda
≈₀-refl-≡ : ∀ { r s : RE } → r ≡ s → r ≈₀ s
≈₀-refl-≡ {r} refl = ≈₀-refl r

-- a decision procedure answers `true` wherever the proposition holds
Dec→true : ∀ { p : Set } ( d : Dec p ) → p → ⌊ d ⌋ ≡ true
Dec→true (yes _) _ = refl
Dec→true (no ¬p) p = ⊥-elim (¬p p)

∨-true : ( b : Bool ) → b ∨ true ≡ true
∨-true true = refl
∨-true false = refl

any-≈₀-witness : ( r : RE ) ( rs : List RE )
  → Any ( λ s → r ≈₀ s ) rs
  → any-≈₀ r rs ≡ true
any-≈₀-witness r (x ∷ rs) (here ≈₀xs) =
  trans (cong ( λ b → b ∨ any-≈₀ r rs ) (Dec→true (r ≟₀ x) ≈₀xs)) refl
any-≈₀-witness r (x ∷ rs) (there w) =
  trans (cong ( λ b → ⌊ r ≟₀ x ⌋ ∨ b ) (any-≈₀-witness r rs w))
        (∨-true ⌊ r ≟₀ x ⌋)

-- scanning `a` and then `b` from a window, or scanning `b` from the window
-- `kept ++ a`: the scan of the split version is what the joint scan reaches
-- anyway, so a `true` found there is found by the joint scan
++-idʳ : ( xs : List RE ) → xs ++ [] ≡ xs
++-idʳ [] = refl
++-idʳ (x ∷ xs) = cong (x ∷_) (++-idʳ xs)

dups-≈₀-go-++ : ( kept a b : List RE )
  → dups-≈₀-go (kept ++ a) b ≡ true
  → dups-≈₀-go kept (a ++ b) ≡ true
dups-≈₀-go-++ kept [] b h =
  subst ( λ q → dups-≈₀-go q b ≡ true ) (++-idʳ kept) h
dups-≈₀-go-++ kept (x ∷ a) b h with any-≈₀ x kept
...   | true = refl
...   | false = dups-≈₀-go-++ (kept ++ (x ∷ [])) a b h

-- the window only grows: anything in it is still in it after appending
∈-++ˡ : ( kept ys : List RE ) ( x : RE ) → x ∈ kept → x ∈ kept ++ ys
∈-++ˡ [] ys x ()
∈-++ˡ (z ∷ kept) ys x (here p) = here p
∈-++ˡ (z ∷ kept) ys x (there x∈) = there (∈-++ˡ kept ys x x∈)

-- the value just added to the window is a member of the window
∈-∷-++ʳ : ( kept : List RE ) ( x : RE ) → x ∈ kept ++ (x ∷ [])
∈-∷-++ʳ [] x = here refl
∈-∷-++ʳ (z ∷ kept) x = there (∈-∷-++ʳ kept x)

-- the test fires as soon as the head of the rest is `≈₀`-equal to the window
dups-≈₀-go-head : ( kept : List RE ) ( r : RE ) ( rs : List RE )
  → any-≈₀ r kept ≡ true
  → dups-≈₀-go kept (r ∷ rs) ≡ true
dups-≈₀-go-head kept r rs eq with any-≈₀ r kept | eq
...   | true  | refl = refl
...   | false | ()

-- membership of `h` in a list, transported along `y ≡ h`, gives an
-- `≈₀`-witness for `y`
∈-≈₀ : ( kept : List RE ) { y h : RE }
  → y ≡ h → h ∈ kept → Any ( λ s → y ≈₀ s ) kept
∈-≈₀ [] q ()
∈-≈₀ (z ∷ kept) q (here p) = here (≈₀-refl-≡ (trans q p))
∈-≈₀ (z ∷ kept) q (there w) = there (∈-≈₀ kept q w)

-- the window holds `h` and the rest contains `h` again: the test fires
dups-≈₀-go-repeat : ( kept ys : List RE ) ( h : RE )
  → h ∈ kept → h ∈ ys
  → dups-≈₀-go kept ys ≡ true
dups-≈₀-go-repeat kept [] h h∈ ()
dups-≈₀-go-repeat kept (y ∷ ys) h h∈ (here q) =
  dups-≈₀-go-head kept y ys
    (any-≈₀-witness y kept (∈-≈₀ kept (sym q) h∈))
dups-≈₀-go-repeat kept (y ∷ ys) h h∈ (there w) =
  dups-≈₀-go-++ kept (y ∷ []) ys
    (dups-≈₀-go-repeat (kept ++ (y ∷ [])) ys h (∈-++ˡ kept (y ∷ []) h h∈) w)

-- membership in the second half of an append
∈-++ʳ : ( t ys : List RE ) ( x : RE ) → x ∈ ys → x ∈ t ++ ys
∈-++ʳ [] ys x x∈ = x∈
∈-++ʳ (z ∷ t) ys x x∈ = there (∈-++ʳ t ys x x∈)

dups-≈₀-∷-repeat : ( kept : List RE ) ( h : RE ) ( t ys : List RE )
  → h ∈ ys
  → dups-≈₀-go kept (h ∷ (t ++ ys)) ≡ true
dups-≈₀-∷-repeat kept h t ys h∈ =
  dups-≈₀-go-++ kept (h ∷ []) (t ++ ys)
    (dups-≈₀-go-repeat (kept ++ (h ∷ [])) (t ++ ys) h
       (∈-∷-++ʳ kept h) (∈-++ʳ t ys h h∈))

-- a `+`-spine is never empty
sum-spine∷ : ( p : RE ) → Σ[ h ∈ RE ] Σ[ t ∈ List RE ] ( sum-spine p ≡ h ∷ t )
sum-spine∷ (l + s ` loc) with sum-spine∷ l | sum-spine∷ s
...   | ( h , t , eq₁ ) | ( h₂ , t₂ , eq₂ ) =
    ( h , t ++ ( h₂ ∷ t₂ )
    , trans (cong ( λ x → x ++ sum-spine s ) eq₁)
            (cong ( λ y → ( h ∷ t ) ++ y ) eq₂) )
sum-spine∷ ε = ( ε , [] , refl )
sum-spine∷ ( $ c ` loc ) = ( $ c ` loc , [] , refl )
sum-spine∷ ( l ● s ` loc ) = ( l ● s ` loc , [] , refl )
sum-spine∷ ( l * n ` loc ) = ( l * n ` loc , [] , refl )

-- an alternative of a member is an alternative of the state
pd-alts∈ : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) )
  ( z : PDInstance r c ) ( h : RE )
  → z ∈ pdis → h ∈ sum-spine (pd-expr z)
  → h ∈ pd-alts pdis
pd-alts∈ [] z h ()
pd-alts∈ (x ∷ pdis) z h (here p) h∈ with p | sum-spine∷ (pd-expr x)
...   | refl | ( h₀ , t , sp ) =
      let eq₂ = trans (cong ( λ q → q ++ pd-alts pdis ) (sym sp)) refl
      in  subst ( λ L → h ∈ L ) eq₂
            (∈-++ˡ (h₀ ∷ t) (pd-alts pdis) h (subst ( λ K → h ∈ K ) sp h∈))
pd-alts∈ (x ∷ pdis) z h (there z∈) h∈ with sum-spine∷ (pd-expr x)
...   | ( h₀ , t , sp ) =
      subst ( λ L → h ∈ L )
            (cong ( λ q → q ++ pd-alts pdis ) (sym sp))
            (∈-++ʳ (h₀ ∷ t) (pd-alts pdis) h (pd-alts∈ pdis z h z∈ h∈))

dups-≈₀-alts-head : ∀ { r : RE } { c : Char }
  ( kept : List RE ) ( x z′ : PDInstance r c ) ( pdis : List (PDInstance r c) )
  → pd-expr x ≡ pd-expr z′
  → z′ ∈ pdis
  → dups-≈₀-go kept (sum-spine (pd-expr x) ++ pd-alts pdis) ≡ true
dups-≈₀-alts-head {r} {c} kept x z′ pdis eq z′∈ with sum-spine∷ (pd-expr z′)
...   | ( h , t , sp ) =
      subst ( λ q → dups-≈₀-go kept (q ++ pd-alts pdis) ≡ true )
            (sym (trans (cong sum-spine eq) sp))
            (dups-≈₀-∷-repeat kept h t (pd-alts pdis)
               (pd-alts∈ pdis z′ h z′∈
                  (subst ( λ K → h ∈ K ) (sym sp) (here refl))))

pd-Idemp?-members-go : ∀ { r : RE } { c : Char } ( kept : List RE )
  ( pdis : List (PDInstance r c) ) ( z z′ : PDInstance r c )
  → z ∈ pdis → z′ ∈ pdis → ¬ ( z ≡ z′ )
  → pd-expr z ≡ pd-expr z′
  → dups-≈₀-go kept (pd-alts pdis) ≡ true
pd-Idemp?-members-go kept [] z z′ ()
pd-Idemp?-members-go kept (x ∷ pdis) z z′ (here p) (here q) z≢z′ eq with p | q
...   | refl | refl = ⊥-elim (z≢z′ refl)
pd-Idemp?-members-go kept (x ∷ pdis) z z′ (here p) (there z′∈) z≢z′ eq =
  dups-≈₀-alts-head kept x z′ pdis (trans (cong pd-expr (sym p)) eq) z′∈
pd-Idemp?-members-go kept (x ∷ pdis) z z′ (there z∈) (here q) z≢z′ eq =
  dups-≈₀-alts-head kept x z pdis (trans (sym (cong pd-expr q)) (sym eq)) z∈
pd-Idemp?-members-go kept (x ∷ pdis) z z′ (there z∈) (there z′∈) z≢z′ eq =
  dups-≈₀-go-++ kept (sum-spine (pd-expr x)) (pd-alts pdis)
    (pd-Idemp?-members-go (kept ++ sum-spine (pd-expr x)) pdis z z′ z∈ z′∈ z≢z′ eq)

-- the test of §4 fires on a member list that holds two distinct records with
-- one continuation
pd-Idemp?-members : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) )
  ( z z′ : PDInstance r c )
  → z ∈ pdis → z′ ∈ pdis → ¬ ( z ≡ z′ )
  → pd-expr z ≡ pd-expr z′
  → pd-Idemp? pdis ≡ true
pd-Idemp?-members pdis z z′ z∈ z′∈ z≢z′ eq =
  pd-Idemp?-members-go [] pdis z z′ z∈ z′∈ z≢z′ eq

-- (purpose): the reflection of the decision procedure — a `true` of the
--   boolean test `any-≈₀` always comes from the proposition `Any (≈₀)`
-- (used in): `dups-≈₀-go-wp` below (the head-match branch)
-- (proof idea): case-split the decision `r ≟₀ y` against the hypothesis;
--   `true` can only come from a `yes` cell, whose position is the witness
any-≈₀-true : ( r : RE ) ( ys : List RE )
  → any-≈₀ r ys ≡ true
  → Any ( λ s → r ≈₀ s ) ys
any-≈₀-true r [] ()
any-≈₀-true r (y ∷ ys) eq with r ≟₀ y | eq
...   | yes r≈₀y | _ = here r≈₀y
...   | no ¬r≈₀y | h = there (any-≈₀-true r ys h)

-- (purpose): the scan step inverts — a `true` of `dups-≈₀-go` came
--   either from the head matching the window or from the tail
-- (used in): `dups-≈₀-go-wp` below (the positioned reflection)
-- (proof idea): case-split on the window decision.  Returning the
--   disjunction, rather than splitting the goal on it, avoids the
--   with-abstraction blocking on the non-datatype goal
dups-≈₀-go-inv-step : ( kept xs : List RE ) ( x : RE )
  → dups-≈₀-go kept (x ∷ xs) ≡ true
  → Sum._⊎_ (any-≈₀ x kept ≡ true)
            (dups-≈₀-go (kept ++ (x ∷ [])) xs ≡ true)
dups-≈₀-go-inv-step kept xs x eq with any-≈₀ x kept | eq
...   | true  | h = Sum.inj₁ refl
...   | false | h = Sum.inj₂ h

-- (purpose): membership in an appended list resolves to one of the sides
-- (used in): `pd-alts∈-inv` below, `∈→◁` in Soundness §5
-- (proof idea): induction on the first list: at the head, `here` names
--   the left side; `there` recurses into the tail
∈-++-inv : ∀ { A : Set } ( xs ys : List A ) { x : A }
  → x ∈ xs ++ ys
  → Sum._⊎_ (x ∈ xs) (x ∈ ys)
∈-++-inv [] ys {x} x∈ = Sum.inj₂ x∈
∈-++-inv (z ∷ xs) ys {x} (here p) = Sum.inj₁ (here p)
∈-++-inv (z ∷ xs) ys {x} (there x∈) with ∈-++-inv xs ys x∈
...   | Sum.inj₁ y = Sum.inj₁ (there y)
...   | Sum.inj₂ y = Sum.inj₂ y

-- (purpose): the inverse of `pd-alts∈` — an alternative of the state
--   belongs to a member: it names a record `z` of the list with the
--   alternative inside `z`'s `sum-spine`
-- (used in): `pd-Idemp?-member-witness` below, and `pdU-Idemp?-member-witness`
--   in `Completeness` §8
-- (proof idea): induction on the record list, splitting each membership
--   in the concatenation with `∈-++-inv`
pd-alts∈-inv : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) )
  ( h : RE )
  → h ∈ pd-alts pdis
  → Σ[ z ∈ PDInstance r c ] ( z ∈ pdis × h ∈ sum-spine (pd-expr z) )
pd-alts∈-inv [] h ()
pd-alts∈-inv (x ∷ pdis) h h∈
  with ∈-++-inv (sum-spine (pd-expr x)) (pd-alts pdis) h∈
...   | Sum.inj₁ h∈₁ = ( x , here refl , h∈₁ )
...   | Sum.inj₂ h∈₂ with pd-alts∈-inv pdis h h∈₂
...   | ( z , z∈ , h∈₃ ) = ( z , there z∈ , h∈₃ )

-- a *positioned* duplicate pair inside a list: two occurrences, the
-- earlier one in a window between `pre` and `post`, the later one after
-- it.  Unlike `dups-≈₀-witness`'s Σ this keeps the occurrence identity
-- the scan is built on — two distinct positions, one value pair.
-- (form: an inductive with the positions as constructor arguments.  A
--   Σ-alias `Dups-w xs = Σ[...]` does *not* unfold when `xs` is neutral,
--   and pair construction against the stuck alias fails; the datatype is
--   rigid and elaborates directly)
data Dups-w : List RE → Set where
  dups-at : ∀ { xs : List RE }
              { pre mid post : List RE } { earlier later : RE }
    → pre ++ (earlier ∷ (mid ++ (later ∷ post))) ≡ xs
    → later ≈₀ earlier
    → Dups-w xs

-- the positioned pair is transportable along list equations
Dups-w-transp : ( xs ys : List RE ) → xs ≡ ys → Dups-w xs → Dups-w ys
Dups-w-transp xs .xs refl w = w

-- cast a scan hypothesis along a window equation (the boolean test does
-- not see how the window list is written)
dups-≈₀-go-cast : ( kept₁ kept₂ : List RE ) ( xs : List RE )
  → kept₁ ≡ kept₂ → dups-≈₀-go kept₁ xs ≡ true → dups-≈₀-go kept₂ xs ≡ true
dups-≈₀-go-cast .k₂ k₂ xs refl h = h

-- a window match located: an `Any` witness names the matched element and
-- the window split around it.
-- (purpose): the head branch of `dups-≈₀-go-wp`
-- (used in): `dups-≈₀-go-wp` below, via `any-≈₀-true`
-- (proof idea): recursion on the witness; the split is returned as
--   *equation data* (matching a Σ inside a with would block it)
any-≈₀-wloc : ( y : RE ) ( kept′ : List RE )
  → Any ( λ r → y ≈₀ r ) kept′
  → Σ[ r ∈ RE ] Σ[ pre ∈ List RE ] Σ[ post ∈ List RE ]
      ( kept′ ≡ pre ++ (r ∷ post) × y ≈₀ r )
any-≈₀-wloc y [] ()
any-≈₀-wloc y (z ∷ kept′) (here y≈₀z) = ( z , [] , kept′ , refl , y≈₀z )
any-≈₀-wloc y (z ∷ kept′) (there p) with any-≈₀-wloc y kept′ p
...   | ( r , pre , post , eq , y≈₀r ) =
          ( r , z ∷ pre , post , cong (_∷_ z) eq , y≈₀r )

-- The pair positions in one scanned step.  The window equation
-- `x ∷ kept ≡ pre ++ (r ∷ post)` from `any-≈₀-wloc` splits the *whole*
-- window around the matched element `r`; then in the scanned list
-- `(x ∷ kept) ++ (y ∷ xs)` the earlier occurrence `r` has prefix `pre`,
-- middle `post` (the window tail), and after the later occurrence `y`
-- the remainder `xs`.  The one reassociation needed
-- (`(pre ++ r ∷ post) ++ y ∷ xs ≡ pre ++ r ∷ (post ++ y ∷ xs)`) has
-- rigid endpoints on both sides — the direct layouts with a cons in the
-- transport context are NOT definitionally checkable, which is what the
-- first attempts kept tripping on.
dups-wp-head : ( x : RE ) ( kept xs : List RE ) ( y : RE )
  → ( w : Σ[ r ∈ RE ] Σ[ pre ∈ List RE ] Σ[ post ∈ List RE ]
          ( (x ∷ kept) ≡ pre ++ (r ∷ post) × y ≈₀ r ) )
  → Dups-w ((x ∷ kept) ++ (y ∷ xs))
dups-wp-head x kept xs y w =
    subst Dups-w (sym (cong ( λ K → K ++ (y ∷ xs) ) eqw))
      (dups-at {xs = (pre ++ (r ∷ post)) ++ (y ∷ xs)}
         {pre = pre} {mid = post} {post = xs} {earlier = r} {later = y}
         (sym (++-assoc pre (r ∷ post) (y ∷ xs))) y≈₀r)
  where
    r      = proj₁ w
    pre    = proj₁ (proj₂ w)
    post   = proj₁ (proj₂ (proj₂ w))
    eqw    = proj₁ (proj₂ (proj₂ (proj₂ w)))
    y≈₀r   = proj₂ (proj₂ (proj₂ (proj₂ w)))

dups-≈₀-go-wp : ( x : RE ) ( kept xs : List RE )
  → dups-≈₀-go (x ∷ kept) xs ≡ true
  → Dups-w ((x ∷ kept) ++ xs)
dups-≈₀-go-wp x kept [] ()
dups-≈₀-go-wp x kept (y ∷ xs) h
  with dups-≈₀-go-inv-step (x ∷ kept) xs y h
...   | Sum.inj₁ h₁ =
          dups-wp-head x kept xs y
            (any-≈₀-wloc y (x ∷ kept) (any-≈₀-true y (x ∷ kept) h₁))
...   | Sum.inj₂ h₂ =
      -- the scan appends the head to the window: `(x ∷ kept) ++ [y]`
      -- *is* `x ∷ (kept ++ [y])` definitionally, so the recursion keeps
      -- the one-cons window form; the remainder layouts differ by
      -- `++-assoc` only
      Dups-w-transp (x ∷ ((kept ++ (y ∷ [])) ++ xs)) ((x ∷ kept) ++ (y ∷ xs))
        (trans (cong ( λ K → x ∷ K ) (++-assoc kept (y ∷ []) xs)) refl)
        (dups-≈₀-go-wp x (kept ++ (y ∷ [])) xs
           (dups-≈₀-go-cast ((x ∷ kept) ++ (y ∷ [])) (x ∷ (kept ++ (y ∷ [])))
              xs refl h₂))

-- (purpose): the scan's output read back as positioned occurrences — a
--   fired `dups-≈₀` names the two positions of the duplicate pair
-- (used in): the §6.1 `pd-Idemp` hypothesis unpacking, composed with
--   `pd-Idemp?-witness`; the member-level classification of the pair
--   relative to `pd-alts` (design note below) is the step that consumes it
-- (proof idea): through the general-window form `dups-≈₀-go-wp`: the
--   whole list is the one-element window `[x]` followed by the rest
dups-≈₀-dups : ( xs : List RE )
  → dups-≈₀ xs ≡ true
  → Dups-w xs
dups-≈₀-dups [] ()
dups-≈₀-dups (x ∷ xs) eq = dups-≈₀-go-wp x [] xs eq

-- the reflection instantiates on a concrete fired scan (the scan on a
-- two-element list of `≈₀`-equal letters answers `true` by `refl`)
dups-w-test : Dups-w (($ 'a' ` 1) ∷ ($ 'a' ` 2) ∷ [])
dups-w-test = dups-≈₀-dups _ refl

-- two splices of one equation: the longer prefix extends the shorter,
-- the overlap is the shared middle.  (used by the cut-split below;
-- proof idea: induction peeling both prefixes, the overlap equation
-- carried through cons contexts in cong-normal form)
compare-++ : ( as bs cs ds : List RE )
  → as ++ bs ≡ cs ++ ds
  → Sum._⊎_ (Σ[ u ∈ List RE ] ( (cs ≡ as ++ u) × (bs ≡ u ++ ds) ))
            (Σ[ u ∈ List RE ] ( (as ≡ cs ++ u) × (ds ≡ u ++ bs) ))
compare-++ []       bs []       ds eq = Sum.inj₁ ( [] , refl , eq )
compare-++ []       bs (c ∷ cs) ds eq = Sum.inj₁ ( c ∷ cs , refl , eq )
compare-++ (a ∷ as) bs []       ds eq = Sum.inj₂ ( a ∷ as , refl , sym eq )
compare-++ (a ∷ as) bs (c ∷ cs) ds eq
  with compare-++ as bs cs ds (∷-injectiveʳ eq)
...   | Sum.inj₁ ( u , cs≡ , bs≡ ) =
          Sum.inj₁ ( u , ( trans (cong ( _∷_ c ) cs≡)
                               (cong ( λ z → z ∷ (as ++ u) )
                                     (sym (∷-injectiveˡ eq)))
                       , bs≡ ) )
...   | Sum.inj₂ ( u , as≡ , ds≡ ) =
          Sum.inj₂ ( u , ( trans (cong ( _∷_ a ) as≡)
                               (cong ( λ z → z ∷ (cs ++ u) )
                                     (∷-injectiveˡ eq))
                       , ds≡ ) )

-- the pair straddles the cut: earlier occurrence in the left part at
-- position `pre`, later occurrence in the right part at position `mid₂`
Dups-w-cross : ( xs ys : List RE ) → Set
Dups-w-cross xs ys =
    Σ[ pre ∈ List RE ] Σ[ mid₁ ∈ List RE ] Σ[ mid₂ ∈ List RE ]
    Σ[ post ∈ List RE ] Σ[ earlier ∈ RE ] Σ[ later ∈ RE ]
      ( (xs ≡ pre ++ (earlier ∷ mid₁))
      × (ys ≡ mid₂ ++ (later ∷ post))
      × (later ≈₀ earlier) )

-- (purpose): a positioned duplicate pair in a concatenation either has
--   both occurrences on one side of the cut or one on each side — the
--   case split that localises a fired test's pair relative to a list
--   structure
-- (used in): the member-level classification of the pair of a fired
--   `pd-Idemp?` against the `pd-alts` cuts (§6.1)
-- (proof idea): compare the layout prefix `pre` against the left part
--   `xs` with `compare-++`; in the overlap branch a second comparison
--   of `mid` against the overlap decides which side holds the later
--   occurrence.  (Clauses are ordered so each nested `with` comes last:
--   an outer with-function gets no clauses after an inner one is opened)
Dups-w-++-split : ( xs ys : List RE )
  → Dups-w (xs ++ ys)
  → Sum._⊎_ (Dups-w xs) (Sum._⊎_ (Dups-w-cross xs ys) (Dups-w ys))
Dups-w-++-split xs ys (dups-at {xs = .(xs ++ ys)} {pre = pre} {mid = mid}
                     {post = post} {earlier = e} {later = l} eq l≈₀e)
  with compare-++ pre (e ∷ (mid ++ (l ∷ post))) xs ys eq
...   | Sum.inj₂ ( u , pre≡ , ys≡ ) = Sum.inj₂ (Sum.inj₂ (dups-at {xs = ys}
          {pre = u} {mid = mid} {post = post}
          {earlier = e} {later = l} (sym ys≡) l≈₀e))
...   | Sum.inj₁ ( u , xs≡ , eq2 ) with u
...       | [] = Sum.inj₂ (Sum.inj₂ (dups-at {xs = [] ++ ys} {pre = []}
            {mid = mid} {post = post} {earlier = e} {later = l} eq2 l≈₀e))
...       | ( z ∷ us) with compare-++ mid (l ∷ post) us ys (∷-injectiveʳ eq2)
...           | Sum.inj₂ ( v , mid≡ , ys≡ ) = Sum.inj₂ (Sum.inj₁
                     ( pre , us , v , post , e , l
                     , ( trans xs≡
                           (sym (cong ( λ K → pre ++ (K ∷ us) )
                                      (∷-injectiveˡ eq2)))
                     , ys≡ , l≈₀e ) ))
...           | Sum.inj₁ ( v , us≡ , eq3 ) with v
...               | [] = Sum.inj₂ (Sum.inj₁
                       ( pre , us , [] , post , e , l
                       , ( trans xs≡
                             (sym (cong ( λ K → pre ++ (K ∷ us) )
                                        (∷-injectiveˡ eq2)))
                       , sym eq3 , l≈₀e ) ))
...               | ( w ∷ vs) = Sum.inj₁ (dups-at {xs = xs}
                    {pre = pre} {mid = mid} {post = vs}
                    {earlier = e} {later = l} eqGoal l≈₀e)
                 where
                   eqGoal : pre ++ (e ∷ (mid ++ (l ∷ vs))) ≡ xs
                   eqGoal =
                     trans (cong ( λ K → pre ++ (e ∷ K) )
                           (trans (cong ( λ z → mid ++ (z ∷ vs) )
                                        (∷-injectiveˡ eq3))
                                  (sym us≡)))
                           (trans (cong ( λ K → pre ++ (K ∷ us) )
                                        (∷-injectiveˡ eq2))
                                  (sym xs≡))

-- the split instantiates on the output of a concrete fired scan with a
-- cut between the two occurrences
dups-w-split-test : Sum._⊎_ (Dups-w (($ 'a' ` 1) ∷ []))
    (Sum._⊎_ (Dups-w-cross (($ 'a' ` 1) ∷ []) (($ 'a' ` 2) ∷ []))
             (Dups-w (($ 'a' ` 2) ∷ [])))
dups-w-split-test = Dups-w-++-split _ _ (dups-≈₀-dups _ refl)

-- (purpose): an inhabitant of a list forces its length to be at least 1
-- (used in): the crossing branch of `pd-alts-Dups-w-classify` below
-- (proof idea): induction on the membership witness; `here` reads the
--   cons cell, `there` weakens the bound along `_≤_`
x∈xs→1≤length : ∀ { a : Set } { xs : List a } { x : a }
  → x ∈ xs → suc zero ≤ length xs
x∈xs→1≤length (here refl) = s≤s z≤n
x∈xs→1≤length (there xs∈) = m≤n⇒m≤1+n (x∈xs→1≤length xs∈)

-- (purpose): the empty list carries no positioned duplicate pair
-- (used in): the nil case of `pd-alts-Dups-w-classify` below
-- (proof idea): the `dups-at` layout always has two cons cells, so its
--   layout equation against `[]` is impossible for either shape of `pre`
Dups-w-[] : Dups-w [] → ⊥
Dups-w-[] (dups-at {xs = []} {pre = []} () l≈₀e)
Dups-w-[] (dups-at {xs = []} {pre = z ∷ zs} () l≈₀e)

-- (purpose): the member-level classification — a positioned duplicate
--   pair of the flattened alternative list `pd-alts pdis` either sits at
--   two positions of *one* member's `sum-spine`, or has its earlier
--   occurrence in one member's spine and its later occurrence in
--   another member's spine
-- (used in): the §6.1 statement of `pd-Idemp` — the classification step of
--   its hypothesis unpacking; the left branch is the material of
--   configurations (a)/(b), the right branch of configuration (c)
-- (proof idea): induction on the member list, cutting
--   `pd-alts (z ∷ zs) ≡ sum-spine (pd-expr z) ++ pd-alts zs` with
--   `Dups-w-++-split`: the both-left branch is the goal's left branch
--   at the head member, the crossing branch names the second member
--   through `pd-alts∈-inv`, the both-right branch recurses.  The
--   crossing branch uses a `let`, not a nested `with`: a clause opening
--   a `with` must come last among its siblings, and the recursive
--   branch needs one
pd-alts-Dups-w-classify : ∀ { r : RE } { c : Char }
  ( pdis : List (PDInstance r c) )
  → Dups-w (pd-alts pdis)
  → Sum._⊎_
      (Σ[ z ∈ PDInstance r c ]
        ( (z ∈ pdis) × Dups-w (sum-spine (pd-expr z)) ))
      (Σ[ z ∈ PDInstance r c ] Σ[ z′ ∈ PDInstance r c ]
        Σ[ earlier ∈ RE ] Σ[ later ∈ RE ]
          ( (z ∈ pdis) × (z′ ∈ pdis)
          × (earlier ∈ sum-spine (pd-expr z))
          × (later ∈ sum-spine (pd-expr z′))
          × (later ≈₀ earlier)
          × ( suc (suc zero) ≤ length pdis ) ))
pd-alts-Dups-w-classify [] dw = ⊥-elim (Dups-w-[] dw)
pd-alts-Dups-w-classify (z ∷ zs) dw
  with Dups-w-++-split (sum-spine (pd-expr z)) (pd-alts zs) dw
...   | Sum.inj₁ d = Sum.inj₁ ( z , ( here refl , d ) )
...   | Sum.inj₂ (Sum.inj₁ ( pre , mid₁ , mid₂ , post , earlier , later
                           , ( xs≡ , ys≡ , later≈₀earlier ) )) =
      let ( z′ , z′∈ , later∈′ ) =
            pd-alts∈-inv zs later
              ( subst ( λ L → later ∈ L ) (sym ys≡)
                  ( ∈-++ʳ mid₂ (later ∷ post) later (here refl) ) )
      in  Sum.inj₂ ( z , z′ , earlier , later
                   , ( here refl , there z′∈
                     , ( subst ( λ L → earlier ∈ L ) (sym xs≡)
                           ( ∈-++ʳ pre (earlier ∷ mid₁) earlier
                               (here refl) )
                     , later∈′ , later≈₀earlier
                     , s≤s (x∈xs→1≤length z′∈) ) ) )
...   | Sum.inj₂ (Sum.inj₂ d) with pd-alts-Dups-w-classify zs d
...       | Sum.inj₁ ( z′ , z′∈ , d′ ) = Sum.inj₁ ( z′ , ( there z′∈ , d′ ) )
...       | Sum.inj₂ ( z′ , z″ , earlier , later
                     , ( z′∈ , z″∈ , earlier∈ , later∈ , later≈₀earlier
                       , 2≤len ) ) =
            Sum.inj₂ ( z′ , z″ , earlier , later
                     , ( there z′∈ , there z″∈ , earlier∈ , later∈
                       , later≈₀earlier , m≤n⇒m≤1+n 2≤len ) )

-- The classification instantiated at the §4.1 example: the fired test
-- read position-preservingly (`dups-≈₀-dups`), then classified against
-- the `pdU` member list
pd-alts-classify-a3 : Sum._⊎_
  (Σ[ z ∈ PDInstance pd-a3-target 'a' ]
    ( (z ∈ PosixPD.pdU[ pd-a3-target , 'a' ])
    × Dups-w (sum-spine (pd-expr z)) ))
  (Σ[ z ∈ PDInstance pd-a3-target 'a' ]
    Σ[ z′ ∈ PDInstance pd-a3-target 'a' ]
    Σ[ earlier ∈ RE ] Σ[ later ∈ RE ]
      ( (z ∈ PosixPD.pdU[ pd-a3-target , 'a' ])
      × (z′ ∈ PosixPD.pdU[ pd-a3-target , 'a' ])
      × (earlier ∈ sum-spine (pd-expr z))
      × (later ∈ sum-spine (pd-expr z′))
      × (later ≈₀ earlier)
      × ( suc (suc zero)
        ≤ length (PosixPD.pdU[ pd-a3-target , 'a' ]) ) ))
pd-alts-classify-a3 =
  pd-alts-Dups-w-classify (PosixPD.pdU[ pd-a3-target , 'a' ])
    (dups-≈₀-dups (pd-alts (PosixPD.pdU[ pd-a3-target , 'a' ]))
       pd-a3-Idemp-applied)

-- What remains after the classification is the analysis *inside* the
-- members: for the left branch, what a positioned pair inside one
-- `sum-spine` says about the expression (configurations (a)/(b) of
-- §6.1; Soundness §5's `pd-cross-positions→Ambig` is the tool once the
--   `_◁_`
-- position of the pair is extracted).  The right branch needs no record
-- analysis: its witnesses carry `2 ≤ length pdis` (the two members are
-- at distinct list positions), and Soundness §11's `pdU-2members→Ambig`
--   inverts
-- that length bound through the `pdU` clauses to an A1/A2
-- configuration.  The value-level form of the classification without
-- position preservation is `pd-Idemp?-member-witness` below.

-- forgetting the positions of a positioned pair recovers the plain
-- `≈₀` pair of values.  This is the demoted route: every consumer of
-- the old value-level scan witness is now stated through it, so the
-- one induction over the scan in this module is the positioned one
Dups-w-→-Σ : ( xs : List RE ) → Dups-w xs
  → Σ[ a ∈ RE ] Σ[ b ∈ RE ] ( a ∈ xs × b ∈ xs × a ≈₀ b )
Dups-w-→-Σ xs (dups-at {xs = xs} {pre = pre} {mid = mid} {post = post}
               {earlier = earlier} {later = later} eq later≈₀earlier) =
    ( later , earlier
    , ( subst ( λ L → later ∈ L ) eq
          ( ∈-++ʳ pre (earlier ∷ (mid ++ (later ∷ post))) later
              ( there (∈-++ʳ mid (later ∷ post) later (here refl)) ) )
      , subst ( λ L → earlier ∈ L ) eq
          ( ∈-++ʳ pre (earlier ∷ (mid ++ (later ∷ post))) earlier
              (here refl) )
      , later≈₀earlier ) )

-- (purpose): the value-level form of the scan reflection: a fired
--   scan has an `≈₀` pair of values in the list (positions forgotten)
-- (used in): `pd-Idemp?-witness` below
-- (proof idea): the positioned reflection `dups-≈₀-dups` followed by
--   `Dups-w-→-Σ`
dups-≈₀-witness : ( xs : List RE )
  → dups-≈₀ xs ≡ true
  → Σ[ a ∈ RE ] Σ[ b ∈ RE ] ( a ∈ xs × b ∈ xs × a ≈₀ b )
dups-≈₀-witness xs eq = Dups-w-→-Σ xs (dups-≈₀-dups xs eq)

-- (purpose): the test of §4 reflected — a fired `pd-Idemp?` means the
--   flattened alternative list holds an `≈₀` pair of values
-- (used in): `pd-Idemp?-member-witness` below, and (with
--   `pd-alts∈-inv`) `pdU-Idemp?-member-witness` in `Completeness` §8
-- (proof idea): `dups-≈₀-witness` at the list `pd-alts pdis`
pd-Idemp?-witness : ∀ { r : RE } { c : Char } ( pdis : List (PDInstance r c) )
  → pd-Idemp? pdis ≡ true
  → Σ[ a ∈ RE ] Σ[ b ∈ RE ] ( a ∈ pd-alts pdis × b ∈ pd-alts pdis × a ≈₀ b )
pd-Idemp?-witness pdis eq = dups-≈₀-witness (pd-alts pdis) eq

-- (purpose): the test of §4 reflected *through the member list* — a
--   fired `pd-Idemp?` names two members and one alternative of each,
--   `≈₀`-equal
-- (used in): the §6.1 statement of `pd-Idemp` — the value-level half of its
--   hypothesis unpacking (the positioned half is `dups-≈₀-dups`).
--   `Completeness`'s `pdU-Idemp?-member-witness` adds `pdU-const`'s
--   equation (for a `pdU` list the two members have one continuation,
--   so both alternatives sit in one `sum-spine`) and composes
--   `pd-Idemp?-witness` + `pd-alts∈-inv` directly: this combined Σ
--   passed through a module boundary produced a phantom conversion
--   error, the small-step composition does not
-- (proof idea): `pd-Idemp?-witness`, then `pd-alts∈-inv` at each side
pd-Idemp?-member-witness : ∀ { r : RE } { c : Char }
  ( pdis : List (PDInstance r c) )
  → pd-Idemp? pdis ≡ true
  → Σ[ z ∈ PDInstance r c ] Σ[ z′ ∈ PDInstance r c ]
      Σ[ a ∈ RE ] Σ[ b ∈ RE ]
        ( z ∈ pdis × z′ ∈ pdis
        × a ∈ sum-spine (pd-expr z) × b ∈ sum-spine (pd-expr z′)
        × a ≈₀ b )
pd-Idemp?-member-witness pdis eq with pd-Idemp?-witness pdis eq
...   | ( a , b , ( a∈ , b∈ , a≈₀b ) )
    with pd-alts∈-inv pdis a a∈ | pd-alts∈-inv pdis b b∈
...   | ( z , z∈ , a∈₁ ) | ( z′ , z′∈ , b∈₁ ) =
        ( z , z′ , a , b , ( z∈ , z′∈ , a∈₁ , b∈₁ , a≈₀b ) )

-- (membership inverses for `map`/`concatMap`; the `pdinstance-oplus`
--   inversion `∈-oplus⁻` lives with the clause analysis in `cgp.ambig.Soundness`)
-- (purpose): membership in a mapped list names the preimage
-- (used in): `∈-oplus⁻` (Soundness §7), `pd-alts-Dups-w-classify` above
-- (proof idea): induction on the list, reading the `here`/`there` position
∈-map⁻ : { A B : Set } ( f : A → B ) ( xs : List A ) ( y : B )
  → y ∈ map f xs
  → Σ[ x ∈ A ] ( x ∈ xs × f x ≡ y )
∈-map⁻ f [] y ()
∈-map⁻ f (x ∷ xs) y (here p) = ( x , here refl , sym p )
∈-map⁻ f (x ∷ xs) y (there w) with ∈-map⁻ f xs y w
...   | ( x′ , x∈ , eq ) = ( x′ , there x∈ , eq )

-- (purpose): membership in a concatenated map names the element whose
--   block carries it
-- (used in): `∈-oplus⁻` (Soundness §7), `pd-alts-Dups-w-classify` above
-- (proof idea): induction on the list, splitting each block's `++`
--   membership with `∈-++-inv`
∈-concatMap⁻ : { A B : Set } ( f : A → List B ) ( xs : List A ) ( y : B )
  → y ∈ concatMap f xs
  → Σ[ x ∈ A ] ( x ∈ xs × y ∈ f x )
∈-concatMap⁻ f [] y ()
∈-concatMap⁻ f (x ∷ xs) y y∈ with ∈-++-inv (f x) (concatMap f xs) y∈
...   | Sum.inj₁ y∈₁ = ( x , here refl , y∈₁ )
...   | Sum.inj₂ y∈₂ with ∈-concatMap⁻ f xs y y∈₂
...     | ( x′ , x∈ , y∈′ ) = ( x′ , there x∈ , y∈′ )
```

Note what is *not* claimed here: the two records may continue at one expression
without that expression being syntactically a sum, which is why this is stated
for members and not read off `dups-≈₀`'s definition.  §4.1's `pd-a3-target` is
exactly that shape — `pdU` fuses the two branch instances, and the flattened
list still contains `ε ● ($ c \` 4) \` 5` twice — and `pd-a3-Idemp-applied` is
the computation that this section's lemmas now justify.

## 5. Lifting a criterion from a reachable state (the full form of the paper's criteria)


`A1→Ambig` / `A2→Ambig` (in `cgp.ambig.AmbigCheck`) and `Ctx-dup→Ambig`
(`cgp.ambig.Soundness` §1) cover only the initial state `s = r`, i.e. a path
of length 0.  The
Ambiguity Criteria proposition of the paper quantifies over *realizable*
`s ∈ Desc(r)`: if a criterion fires at a state reached after consuming a
word `w`, then `r` is ambiguous — the ambiguity witness (two distinct parse
trees of `s` reading the same word) is lifted to parse trees of `r` along
the path, and both read the word `w ++ | u |`.

In this formalism "state `p` reached after `w` together with its path tree
map" is exactly a `PDInstance* r w` (`pdUMany[ r , w ]` produces them): the
continuation is the state `p`, `inj : U p → U r` is the composed transition
map and `ev` states `| inj u | = w ++ | u |`.  All three criteria then share
*one* proof, the master lift below: the criterion supplies `Ambig p`, and
`lift-Ambig` transports the witness.  The paper hides one side condition in
its construction — distinct trees must stay distinct under the lift; here it
becomes the explicit hypothesis `inj-inj` (the transition maps of the paper's
`AllParseFST` are injective by construction; in this project the pd builders
`pdinstance-left/right/fst/snd/star` are injective given an injective
input — the `posix` `mkfuseInj` is the exception, it can identify trees
coming from different branches).

```agda
-- accessors for the data carried by a PDInstance*
pd*-inj : ∀ { r : RE } { pref : List Char } ( pdi : PDInstance* r pref )
  → U (pd*-expr pdi) → U r
pd*-inj (pdinstance* {p} inj ev) = inj

pd*-ev : ∀ { r : RE } { pref : List Char } ( pdi : PDInstance* r pref )
  → ∀ ( u : U (pd*-expr pdi) ) → proj₁ (flat (pd*-inj pdi u)) ≡ pref ++ proj₁ (flat u)
pd*-ev (pdinstance* {p} inj ev) = ev

-- master lift: an ambiguity witness of the state p survives the path lift
lift-Ambig : ∀ { r p : RE } { w : List Char }
  → ( inj : U p → U r )
  → ( ev : ∀ ( u : U p ) → proj₁ (flat {r} (inj u)) ≡ w ++ proj₁ (flat {p} u) )
  → ( inj-inj : ∀ ( u v : U p ) → inj u ≡ inj v → u ≡ v )
  → Ambig p
  → Ambig r
lift-Ambig {r} {p} {w} inj ev inj-inj (u , v , w≡ , u≢v) =
    ( inj u
    , inj v
    , trans (trans (ev u) (cong ( λ z → w ++ z) w≡)) (sym (ev v))
    , λ trees≡ → u≢v (inj-inj u v trees≡) )

-- A1 at the state ⇒ r ambiguous
lift-A1→Ambig : ∀ { r p : RE } { w : List Char }
  → ( inj : U p → U r )
  → ( ev : ∀ ( u : U p ) → proj₁ (flat {r} (inj u)) ≡ w ++ proj₁ (flat {p} u) )
  → ( inj-inj : ∀ ( u v : U p ) → inj u ≡ inj v → u ≡ v )
  → AmbigA1 p
  → Ambig r
lift-A1→Ambig inj ev inj-inj a1 = lift-Ambig inj ev inj-inj (A1→Ambig _ a1)

-- A2 at the state ⇒ r ambiguous
lift-A2→Ambig : ∀ { r p : RE } { w : List Char }
  → ( inj : U p → U r )
  → ( ev : ∀ ( u : U p ) → proj₁ (flat {r} (inj u)) ≡ w ++ proj₁ (flat {p} u) )
  → ( inj-inj : ∀ ( u v : U p ) → inj u ≡ inj v → u ≡ v )
  → AmbigA2 p
  → Ambig r
lift-A2→Ambig inj ev inj-inj a2 = lift-Ambig inj ev inj-inj (A2→Ambig _ a2)

-- (purpose): the context lift on its own — an ambiguity of the hole
--   expression transfers to the filled expression
-- (used in): the §6.1 statement of `pd-Idemp` (the closer a located
--   sum-branch pair composes with); `Ctx-dup→Ambig` (Soundness §1) builds the
--   same witness inline
-- (proof idea): `CtxT` embeds the two trees, `CtxT-pres-flat` keeps the
--   word equation, `CtxT-injective` reflects the disequality
lift-Ctx : ∀ ( ctx : Ctx ) { s : RE } → Ambig s → Ambig (plug ctx s)
lift-Ctx ctx ( u , v , word≡ , u≢v ) =
    ( CtxT ctx u
    , CtxT ctx v
    , CtxT-pres-flat ctx word≡
    , λ trees≡ → u≢v (CtxT-injective ctx trees≡) )

-- the three criteria at a pd-reachable state (pdUMany witnesses)
pd*-Ambig→Ambig : ∀ { r : RE } { pref : List Char }
  → ( pdi : PDInstance* r pref )
  → ( ∀ ( u v : U (pd*-expr pdi) ) → pd*-inj pdi u ≡ pd*-inj pdi v → u ≡ v )
  → Ambig (pd*-expr pdi)
  → Ambig r
pd*-Ambig→Ambig pdi inj-inj = lift-Ambig (pd*-inj pdi) (pd*-ev pdi) inj-inj

pd*-A1→Ambig : ∀ { r : RE } { pref : List Char }
  → ( pdi : PDInstance* r pref )
  → ( ∀ ( u v : U (pd*-expr pdi) ) → pd*-inj pdi u ≡ pd*-inj pdi v → u ≡ v )
  → AmbigA1 (pd*-expr pdi)
  → Ambig r
pd*-A1→Ambig pdi inj-inj a1 = pd*-Ambig→Ambig pdi inj-inj (A1→Ambig (pd*-expr pdi) a1)

pd*-A2→Ambig : ∀ { r : RE } { pref : List Char }
  → ( pdi : PDInstance* r pref )
  → ( ∀ ( u v : U (pd*-expr pdi) ) → pd*-inj pdi u ≡ pd*-inj pdi v → u ≡ v )
  → AmbigA2 (pd*-expr pdi)
  → Ambig r
pd*-A2→Ambig pdi inj-inj a2 = pd*-Ambig→Ambig pdi inj-inj (A2→Ambig (pd*-expr pdi) a2)

```

Notes:

* `A1→Ambig` / `A2→Ambig` / `Ctx-dup→Ambig` are the special cases
  `w = []`, `inj = id` (realizability in the paper's sense is automatic
  here: every project `RE` has a parse tree, `r-∃u`).
* `cgp.ambig.Soundness` §3's `pd-pairs→Ambig` / `pd*-pairs→Ambig`
  is an *already lifted* form of
  A3: the two parse trees are built directly under the injections, so no
  injectivity hypothesis is needed (the pair sits in different sum branches,
  `LeftU≢RightU`).
* The remaining gap towards the paper's full proposition is unchanged:
  proving that `inj-inj` holds for the concrete injections produced by
  `pdUMany` (routine for the `lne`/`greedy` builders, false for
  `mkfuseInj`), and the converse direction
  ("`r` ambiguous ⇒ some realizable state fires A1/A2/A3"), which needs
  the FST / `Desc(r)` construction.  The converse does *not* hold without
  the quantification over `Desc(r)`: for `r = ( a + a · a ) ⋆` the word
  `a a` has two parse trees (`ListU [ a , a ]`, `ListU [ a · a ]`), yet no
  criterion fires at `r` — a star has a single empty parse tree, and the
  paper's hole contexts have no hole under a star.

## 6. `Desc(r)` — the paper's states, built from partial derivatives

The paper's `Desc(r) = { s | r Descendant s }` is defined by the
Brzozowski derivative, which `cgp` lacks.  The `posix` `pdU` already
contains the trick that repairs this: `pdinstance-oplus`/`fuse` merges
sibling alternatives *inside* every pd step, so one fused `pdinstance`
carries one continuation expression — and iterating single-character
steps with `advance-pdi*-with-c`/`pdUMany` composes those continuations
along a word (this is the "encode the derivative via partial
derivatives" construction of the old `cgp.posix.Related` /
`cgp.relatedwork.RelatedWorkOkuiSuzuki`).

Only a residual multi-instance list can remain (from nullable-`●`
products and under stars).  Its sum is the derivative: by Antimirov,
`deriv r w` is denoted by the *sum of all partial derivative
continuations*, so re-gluing them with `sum-build` produces a single
expression (`derivᵖ r w` below) that plays the role of `deriv r w`
(denotes the same language — the project formalizes exactly this
correspondence, `pdUMany` soundness / reconstructability, Lemmas 21–22).
`nothing` is the `∅`-case.  With it the paper's quantification "there
exists a realizable `s ∈ Desc(r)`" becomes the concrete type `_∈Desc_`
below — realizability is automatic (every reachable `RE` is inhabited,
`r-∃u`; the `∅` cases are filtered out by `just`).

```agda
-- alternatives of the (distributed) derivative of a word
pd*-alts : ∀ { r : RE } { w : List Char } → List (PDInstance* r w) → List RE
pd*-alts pdis = concatMap ( λ pdi → sum-spine (pd*-expr pdi) ) pdis

-- the derivative of r w.r.t. w, encoded via partial derivatives
-- (sum-build re-glues the residual instances; the loc zero of the
-- artificial top '+' is irrelevant, ≈₀ and the theorems are loc-agnostic)
derivᵖ : ( r : RE ) → ( w : List Char ) → Maybe RE
derivᵖ r w with PosixPD.pdUMany[ r , w ]
...   | [] = nothing
...   | pdis = just (sum-build (pd*-alts pdis) zero)

-- s ∈Desc r  ⟺  s is a (realizable) descendant state of r
-- (paper: s ∈ Desc(r); the realizable side condition is automatic here)
infix 4 _∈Desc_
_∈Desc_ : RE → RE → Set
s ∈Desc r = Σ[ w ∈ List Char ] ( derivᵖ r w ≡ just s )

```

### 6.1. A3 stated verbatim for the initial state

With `derivᵖ`, the paper's A3 condition for the initial state,
"`lang(canonic(deriv r x)) ≠ {}` and `Idemp` applied", becomes a
computable boolean:

```agda
A3? : ( r : RE ) → ( c : Char ) → Bool
A3? r c with derivᵖ r (c ∷ [])
...   | nothing = false
...   | just s = proj₂ (canonic s)

-- the paper's A3 test fires on the §4.1 example:
-- after consuming 'a' the descendant state
--   (ε ● ($ 'c' ` 4) ` 5) + (ε ● ($ 'c' ` 7) ` 8) ` 0
-- is reached, and its canonical representative applies Idemp:
pd-a3-state : RE
pd-a3-state = (ε ● ($ 'c' ` 4) ` 5) + ((ε ● ($ 'c' ` 7) ` 8)) ` zero

pd-a3-Desc : pd-a3-state ∈Desc pd-a3-target
pd-a3-Desc = ( 'a' ∷ [] , refl )

pd-a3-A3?-fires : A3? pd-a3-target 'a' ≡ true
pd-a3-A3?-fires = refl

-- sanity check: a single letter reaches the state ε, no Idemp fires:
letter-A3?-silent : A3? ($ 'a' ` 1) 'a' ≡ false
letter-A3?-silent = refl

```

Caveats (consistent with §4/§5):

* `derivᵖ r w` is a *witness term* for the derivative (same language),
  not a syntactic replica of Brzozowski's — stars unfold positionally
  (`pdinstance-star` appends `r * ε∉r ` loc`) and `sum-build`
  introduces artificial `+` locations.  The paper's own FST quotients by
  similarity anyway, and `≈₀`/`canonic` are location-insensitive, so
  the A3 *test* is unaffected.
* The soundness of a fired `A3?` is composed in `cgp.ambig.Soundness` §11,
  unconditionally:

  > `pd-Idemp : pd-Idemp? (PosixPD.pdU[ q , c ]) ≡ true → Ambig q`

  Its test hypothesis is fully unpacked (§4.2: the positioned reflection
  `dups-≈₀-dups : dups-≈₀ xs ≡ true → Dups-w xs` reads a fired scan
  back as a *positioned* duplicate pair — two list positions, not just
  two values (the value-only form is too weak: the same value may
  legitimately occur twice in an unambiguous list); the value-level
  forms `pd-Idemp?-witness` / `pd-Idemp?-member-witness` and
  `Completeness` §8's `pdU-Idemp?-member-witness` remain as demoted
  records of the same reflection).  The *classification* is proved
  (`Dups-w-++-split` + `pd-alts-Dups-w-classify`, this module's §4.2,
  instantiated at the example by `pd-alts-classify-a3`): the pair of a fired test either
  sits at two positions of one member's `sum-spine`, or has its earlier
  occurrence in one member's spine and its later occurrence in another's.
  The first branch is closed in full by Soundness §10's
  `pdU-member-pair→Ambig`,
  an induction along the clauses of the `pdU` definition —
  configurations (a) and (b) through `spine-pair→Ambig` /
  `member-pair→Ambig` (Soundness §9) and the record lifts (Soundness
  §8), the crossings of a `+` clause through Soundness §5's
  `pd-cross-positions→Ambig` and of the nullable-`●` clause through
  Soundness §10's `pd-cross-●→Ambig` (which closes a
  first-factor/empty-first-factor pair by *word* distinctness, `c ∷ _`
  versus `[]` via `flat-[]`, the one place where branch-constructor
  injectivity is unavailable because both records share their input
  expression).  The second branch is closed by Soundness §11's
  `pdU-2members→Ambig`, a second induction along the `pdU` clauses: the
  classification hands over the *length bound* `2 ≤ length (pdU[ q , c ])`
  (the two members sit at distinct positions of the member list), and
  that bound alone suffices — each clause either factors it through a
  branch list (`length-map`, `pdU-oplus-≥2`, `pdU-cms-len`, `×-≥2→`) and
  lifts the resulting ambiguity back through the sum/consumption contexts
  (`lift-Ctx`, `star-Ambig`), or ends at the empty-tree factor of the
  nullable-`●` clause, where `≥ 2` empty parse trees of the left factor
  is exactly the A2 criterion record at the clause's own concatenation
  node (`A2→Ambig`).  No record-distinctness question arises on this
  branch: the ambiguity comes from the clause structure of the member
  list, not from comparing the pair's values.
  The `mkfuseInj` gap of §5 does not arise in (a) — the
  branch maps are only used through different parent branches.

For the *criteria* themselves the single-expression form is not needed: the
states are lists of partial derivatives, see §7.

## 7. `Desc(r)` as a list of partial derivatives (the pd-native form)

An Antimirov state *is* a set of partial derivatives, so the faithful
formalization of `Desc(r)` keeps the list and drops `sum-build`/`Maybe`:

```agda
-- the pd-descendant state of r after w: the list of continuations of the
-- partial derivatives produced by pdUMany (the Antimirov state)
pd*-Desc : ( r : RE ) → ( w : List Char ) → List RE
pd*-Desc r w = map pd*-expr (PosixPD.pdUMany[ r , w ])

-- s ∈Descᵖ r  ⟺  s is the (list) state reached after some word
-- (paper: s ∈ Desc(r); 'realizable' is automatic, and the ∅ state is the
-- empty list rather than a Maybe case)
infix 4 _∈Descᵖ_
_∈Descᵖ_ : List RE → RE → Set
ss ∈Descᵖ r = Σ[ w ∈ List Char ] ( pd*-Desc r w ≡ ss )

```

The three criteria are then tests *on the list*, and §5's `lift-Ambig`
applies componentwise — every element of `pd*-Desc r w` is the continuation
of some `pdi : PDInstance* r w`, and `pd*-A1→Ambig` / `pd*-A2→Ambig` /
`pd*-Ctx-dup→Ambig` are universally quantified over such an instance, so a
criterion firing at *any* member of the state list already gives `Ambig r`
(the `pd*-Ctx-dup→Ambig` instance travels with `Ctx-dup→Ambig` in
`cgp.ambig.Soundness` §6).
Only A3 needs an additional list-level test, which is exactly `dups-≈₀` —
no re-glued expression and no artificial `+` locations involved:

```agda
-- the paper's A3 test on the state reached after w then c:
-- does canonicalizing that state apply Idemp?
A3-list? : ( r : RE ) → ( w : List Char ) → ( c : Char ) → Bool
A3-list? r w c = dups-≈₀ (pd*-alts (PosixPD.pdUMany[ r , w ++ (c ∷ []) ]))

-- the §4.1 example, in list form: after 'a the state is the single fused
-- instance whose continuation is the sum of the two equal continuations
-- (the ' + ' carries the location 9 of the source expression, §6's
-- pd-a3-state differs from it only by the artificial location):
pd-a3-Descᵖ : ( (ε ● ($ 'c' ` 4) ` 5) + ((ε ● ($ 'c' ` 7) ` 8)) ` 9 ) ∷ []
              ∈Descᵖ pd-a3-target
pd-a3-Descᵖ = ( 'a' ∷ [] , refl )

pd-a3-A3-list?-fires : A3-list? pd-a3-target [] 'a' ≡ true
pd-a3-A3-list?-fires = refl

-- a two-step word reaches the same situation one level deeper
-- (consume 'a' then 'c': both continuations become ε, so the state
-- contains two copies of ε):
pd-a3-A3-list?-step2 : A3-list? pd-a3-target ( 'a' ∷ [] ) 'c' ≡ true
pd-a3-A3-list?-step2 = refl

-- negative controls: a dead state has no duplicates
letter-A3-list?-silent : A3-list? ($ 'a' ` 1) [] 'a' ≡ false
letter-A3-list?-silent = refl

```

For one step the list form is the same computation as §4's `pd-Idemp?`:
`pdUMany[ r , x ∷ [] ]` is `pdU[ r , x ]` composed with the identity path
map, and `compose-pdi-with` keeps the continuation of its argument
(`pdinstance* {p}` with the same `p`), so `pd*-alts` of the one-step state
coincides with `pd-alts (pdU[ r , x ])`.  The list form is therefore a
*conservative* extension: it runs the same test on the state reached after
an arbitrary prefix, which is the paper's A3 for a descendant `s`, stated
without ever leaving the partial-derivative setting.





## 8. The diagnosis disjunction `crit`

The completeness half (`cgp.ambig.Completeness`) proves "ambiguous ⇒ some
realizable state fires a criterion"; its diagnosing lemmas and the pd-state
soundness reading (`cgp.ambig.Soundness` §12) share one codomain, the
disjunction of the paper's criteria at a state.  It is stated here, next to
the tests it mentions:

```agda
-- the diagnosis disjunction: one of the paper's criteria fires at `p`
-- (purpose): the single codomain every diagnosing lemma targets
-- (used in): `desc-concl`/`Desc-complete` (Completeness §6), `pick-diff-record-prf`
--   (Completeness §7), the `completeness` statement (Completeness §9), and the
--   `soundness` reading (Soundness §12)
-- (proof idea): definition — A1/A2 from `AmbigCheck`, the duplicate pattern and
-- the transition `Idemp` test read under a hole context
crit : RE → Set
crit p = Sum._⊎_
      (AmbigCheck.AmbigA1 p)
      (Sum._⊎_
        (AmbigCheck.AmbigA2 p)
        (Sum._⊎_
          ( Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
              ( ( AmbigCheck.plug ctx ( l + s ` loc ) ≡ p )
              × ( _≈₀_ l s ) ) )
          ( Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ q ∈ RE ] Σ[ c ∈ Char ]
              ( ( AmbigCheck.plug ctx q ≡ p )
              × ( pd-Idemp? (PosixPD.pdU[ q , c ]) ≡ true ) ) )))

-- The fourth disjunct is worth naming outright at the empty context, since
-- it is a decidable test on the transition out of the state and needs no
-- descent: a positive `Idemp` test on the transition out of `r` is a
-- criterion at `r` itself.
-- (purpose): the fourth disjunct at the empty context
-- (used in): `pick-diff-record-prf` (Completeness §7), the `soundness` cases
--   (Soundness §12)
-- (proof idea): by inspection: `𝟘 , r , c` plugs to `r` at `refl`, and the
--   hypothesis is exactly the fourth component
crit-A3-test : ∀ ( r : RE ) ( c : Char )
  → pd-Idemp? (PosixPD.pdU[ r , c ]) ≡ true
  → crit r
crit-A3-test r c p≡true = Sum.inj₂ (Sum.inj₂ (Sum.inj₂ ( AmbigCheck.𝟘 , r , c , ( refl , p≡true ) )))
```
