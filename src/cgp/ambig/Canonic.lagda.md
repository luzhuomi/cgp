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
4. Soundness of the A3 mechanism at the top level:
   `dup-sum→Ambig` / `Ctx-dup→Ambig`: if `Idemp` applies to (a subterm
   context of) `r` then `r` is ambiguous.
   Together with `cgp.ambig.AmbigCheck` (`ambiguousSum`, `notA1Sum`,
   `notA2Sum`) this shows the A3 criterion genuinely adds detection power:
   `a + a` is missed by A1 and A2 but caught here.
5. Section 7: the *general* form of the criteria — one master lift
   `lift-Ambig` (an injective path tree map with the soundness evidence of
   a `PDInstance*` transports `Ambig p → Ambig r`), from which
   `lift-A1→Ambig`, `lift-A2→Ambig` and `lift-Ctx-dup→Ambig` and their
   pd-state corollaries `pd*-A1→Ambig`, `pd*-A2→Ambig`,
   `pd*-Ctx-dup→Ambig` factor (`AmbigCheck.A1→Ambig` etc. are the
   `w = []`, `inj = id` instances).
6. Section 8: the paper's `Desc(r)` *as a single expression* via the
   `oplus` trick — `derivᵖ r w` re-glues the partial-derivative
   continuations of `pdUMany[ r , w ]` into one state expression, `_∈Desc_`
   states the paper's quantification over realizable states, and `A3?` is
   the paper's A3 test as a computable boolean (verified `true` on the
   §6.2 example).  This form exists only to state the paper's
   `canonic(deriv s x)` verbatim; for the tests §9's list form is used.
7. Section 9: the pd-native states — `pd*-Desc r w` is the Antimirov state
   itself (the list of partial-derivative continuations of `pdUMany[ r , w ]`,
   no re-gluing, no `Maybe`) and `A3-state? r w c` applies the A3 test to
   that list; §7's corollaries then apply to *any* member of the list.

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

**However** (section 6 below) the derivative can be *mimicked by partial
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
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉)

import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU; LetterU; LeftU; RightU; PairU; ListU ; flat ; r-∃u ; LeftU≢RightU )

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using ( Ambig ; AmbigA1 ; AmbigA2 ; Ctx ; 𝟘 ; Ctx●R ; L●Ctx ; Ctx+R ; L+Ctx ; plug ; CtxT ; CtxT-pres-flat ; CtxT-injective ; A1→Ambig ; A2→Ambig )

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; pdinstance-left ; pdinstance-right ; pdinstance-fst ; PDInstance* ; pdinstance* )

import cgp.posix.PartialDerivative as PosixPD

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; map ; concatMap)

import Data.Bool.Base as Bool
open Bool using (Bool; true; false; _∨_)

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using ( ℕ ; zero )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; cong; sym; cong₂)

import Data.Product as Product
open Product using ( Σ ; Σ-syntax ; _,_ ; _×_ )
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

## 4. Soundness: `Idemp` applied implies ambiguity

If a sum contains two `≈₀`-equal alternatives then the expression is
ambiguous: the same inhabitant tree (all expressions are inhabited,
`r-∃u`) embedded via `LeftU` and, transported along `≈₀`, via `RightU`
(the two parse trees the paper gets when applying `Idemp`).

```agda
dup-sum→Ambig : ∀ { l s : RE } { loc : ℕ }
  → l ≈₀ s
  → Ambig (l + s ` loc)
dup-sum→Ambig {l} {s} {loc} p =
  let u = proj₁ (r-∃u l) in
  ( LeftU {l} {s} {loc} u
  , RightU {l} {s} {loc} (Cast p u)
  , sym (Cast-pres-flat p u)
  , LeftU≢RightU u (Cast p u) )

-- the same under a hole context R[]:  A3 fires on the subterm  ⇒  r ambiguous
Ctx-dup→Ambig : ∀ ( ctx : Ctx ) { l s : RE } { loc : ℕ }
  → ( r : RE )
  → plug ctx (l + s ` loc) ≡ r
  → l ≈₀ s
  → Ambig r
Ctx-dup→Ambig ctx {l} {s} {loc} .(plug ctx (l + s ` loc)) refl p =
  let u = proj₁ (r-∃u l) in
  ( CtxT ctx (LeftU {l} {s} {loc} u)
  , CtxT ctx (RightU {l} {s} {loc} (Cast p u))
  , CtxT-pres-flat ctx (sym (Cast-pres-flat p u))
  , λ trees≡ → LeftU≢RightU u (Cast p u) (CtxT-injective ctx trees≡) )

```

## 5. The A3 example: `a + a` (missed by A1/A2, caught by Idemp)

`cgp.ambig.AmbigCheck` proves that `($ 'a' ` 1) + ($ 'a' ` 2) ` 3` is
ambiguous (`ambiguousSum`) although it satisfies neither A1 (`notA1Sum`) nor
A2 (`notA2Sum`).  Here `canonic` detects it: the canonical representative
removes the second alternative and reports that `Idemp` was applied, and
`Ctx-dup→Ambig` turns this into the ambiguity witness.

```agda
a3-target : RE
a3-target = ($ 'a' ` 1) + ($ 'a' ` 2) ` 3

-- A1 and A2 do not fire (from cgp.ambig.AmbigCheck)
a3-notA1 : ¬ AmbigA1 a3-target
a3-notA1 = AmbigCheck.notA1Sum

a3-notA2 : ¬ AmbigA2 a3-target
a3-notA2 = AmbigCheck.notA2Sum

-- computing the canonical representative removes the duplicate alternative:
a3-canonic : proj₁ (canonic a3-target) ≡ ($ 'a' ` 1)
a3-canonic = refl

-- and reports that rule Idemp was applied:
a3-Idemp-applied : proj₂ (canonic a3-target) ≡ true
a3-Idemp-applied = refl

-- soundness of the detection:
a3-ambiguous : Ambig a3-target
a3-ambiguous = Ctx-dup→Ambig 𝟘 _ refl (≈₀-$ 'a' 1 2)

-- a duplicate under a context (here R[] = [] ● b) is detected as well
a3-nested-target : RE
a3-nested-target = a3-target ● ($ 'b' ` 4) ` 5

a3-nested-Idemp-applied : proj₂ (canonic a3-nested-target) ≡ true
a3-nested-Idemp-applied = refl

a3-nested-ambiguous : Ambig a3-nested-target
a3-nested-ambiguous = Ctx-dup→Ambig (Ctx●R 𝟘 ($ 'b' ` 4) 5) _ refl (≈₀-$ 'a' 1 2)

```

## 6. A3 by mimicking the derivative with partial derivatives

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

pd*-expr : ∀ { r : RE } { pref : List Char } → PDInstance* r pref → RE
pd*-expr (pdinstance* {p} inj ev) = p

-- all alternatives of the (distributed) derivative deriv r x
pd-alts : ∀ { r : RE } { c : Char } → List (PDInstance r c) → List RE
pd-alts pdis = concatMap ( λ pdi → sum-spine (pd-expr pdi) ) pdis

-- does canonicalizing the sum of the continuations require the Idemp rule?
dups-≈₀ : List RE → Bool
dups-≈₀ xs = go [] xs
  where
    go : List RE → List RE → Bool
    go kept [] = false
    go kept (r ∷ rs) with any-≈₀ r kept
    ...   | true = true
    ...   | false with go (kept ++ (r ∷ [])) rs
    ...   | d = d

pd-Idemp? : ∀ { r : RE } { c : Char } → List (PDInstance r c) → Bool
pd-Idemp? pdis = dups-≈₀ (pd-alts pdis)

```

### 6.1. Soundness: a duplicated continuation pair implies ambiguity

The two injections embed the (equal up to `≈₀`) continuations through
*different* sum branches, so the transported parse trees are distinct —
this is the paper's A3 ambiguity witness, built from the pd injections.

```agda
pd-pairs→Ambig : ∀ { l s : RE } { loc : ℕ } { c : Char }
  → ( pdi₁ : PDInstance l c )
  → ( pdi₂ : PDInstance s c )
  → pd-expr pdi₁ ≈₀ pd-expr pdi₂
  → Ambig (l + s ` loc)
pd-pairs→Ambig {l} {s} {loc} {c} (pdinstance {d₁} inj₁ ev₁) (pdinstance {d₂} inj₂ ev₂) p =
  let u = proj₁ (r-∃u d₁) in
  ( LeftU {l} {s} {loc} (inj₁ u)
  , RightU {l} {s} {loc} (inj₂ (Cast p u))
  , trans (ev₁ u) (trans (cong ( λ z → c ∷ z) (sym (Cast-pres-flat p u))) (sym (ev₂ (Cast p u))))
  , LeftU≢RightU (inj₁ u) (inj₂ (Cast p u)) )

-- the same for whole word prefixes (mimics deriv s x for a state s reached
-- after consuming w; PDInstance* is produced by pdUMany[ r , w ])
pd*-pairs→Ambig : ∀ { l s : RE } { loc : ℕ } { w : List Char }
  → ( pdi₁ : PDInstance* l w )
  → ( pdi₂ : PDInstance* s w )
  → pd*-expr pdi₁ ≈₀ pd*-expr pdi₂
  → Ambig (l + s ` loc)
pd*-pairs→Ambig {l} {s} {loc} {w} (pdinstance* {d₁} inj₁ ev₁) (pdinstance* {d₂} inj₂ ev₂) p =
  let u = proj₁ (r-∃u d₁) in
  ( LeftU {l} {s} {loc} (inj₁ u)
  , RightU {l} {s} {loc} (inj₂ (Cast p u))
  , trans (ev₁ u) (trans (cong ( λ z → w ++ z) (sym (Cast-pres-flat p u))) (sym (ev₂ (Cast p u))))
  , LeftU≢RightU (inj₁ u) (inj₂ (Cast p u)) )

```

### 6.2. Example: the duplicate is *created by the derivative*

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

-- the top-level Idemp test does NOT fire (unlike section 5):
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
-- level ε ● ($ 'c' ` 4) ` 5  and  ε ● ($ 'c' ` 7) ` 8 :
-- soundness evidence for a letter partial derivative (cf. the letter case of pdU)
letter-ev : ( c : Char ) ( loc : ℕ ) ( u : U ε )
  → proj₁ (flat (LetterU {loc} c)) ≡ c ∷ proj₁ (flat u)
letter-ev c loc EmptyU = refl

a1-inst : PDInstance ($ 'a' ` 1) 'a'
a1-inst = pdinstance {ε} {($ 'a' ` 1)} {'a'}
            ( λ u → LetterU {1} 'a')
            ( letter-ev 'a' 1)

a6-inst : PDInstance ($ 'a' ` 6) 'a'
a6-inst = pdinstance {ε} {($ 'a' ` 6)} {'a'}
            ( λ u → LetterU {6} 'a')
            ( letter-ev 'a' 6)

left-pdi : PDInstance ((( $ 'a' ` 1) + ($ 'b' ` 2) ` 3) ● ($ 'c' ` 4) ` 5) 'a'
left-pdi = pdinstance-fst {(($ 'a' ` 1) + ($ 'b' ` 2) ` 3)} {($ 'c' ` 4)} {5} {'a'}
             ( pdinstance-left {($ 'a' ` 1)} {($ 'b' ` 2)} {3} {'a'} a1-inst)

right-pdi : PDInstance (($ 'a' ` 6) ● ($ 'c' ` 7) ` 8) 'a'
right-pdi = pdinstance-fst {($ 'a' ` 6)} {($ 'c' ` 7)} {8} {'a'} a6-inst

pd-a3-ambiguous : Ambig pd-a3-target
pd-a3-ambiguous = pd-pairs→Ambig left-pdi right-pdi
                    (≈₀-● (≈₀-ε) (≈₀-$ 'c' 4 7))

```

## 7. Lifting a criterion from a reachable state (the full form of the paper's criteria)

`A1→Ambig` / `A2→Ambig` (in `cgp.ambig.AmbigCheck`) and `Ctx-dup→Ambig`
(§4) cover only the initial state `s = r`, i.e. a path of length 0.  The
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

-- Idemp inside the state (the A3 shape) ⇒ r ambiguous
lift-Ctx-dup→Ambig : ∀ { r p : RE } { w : List Char }
  → ( inj : U p → U r )
  → ( ev : ∀ ( u : U p ) → proj₁ (flat {r} (inj u)) ≡ w ++ proj₁ (flat {p} u) )
  → ( inj-inj : ∀ ( u v : U p ) → inj u ≡ inj v → u ≡ v )
  → ( ctx : Ctx ) { l s : RE } { loc : ℕ }
  → plug ctx (l + s ` loc) ≡ p
  → l ≈₀ s
  → Ambig r
lift-Ctx-dup→Ambig {p = p} inj ev inj-inj ctx {l} {s} {loc} eq dup =
  lift-Ambig inj ev inj-inj (Ctx-dup→Ambig ctx {l} {s} {loc} p eq dup)

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

pd*-Ctx-dup→Ambig : ∀ { r : RE } { pref : List Char }
  → ( pdi : PDInstance* r pref )
  → ( ∀ ( u v : U (pd*-expr pdi) ) → pd*-inj pdi u ≡ pd*-inj pdi v → u ≡ v )
  → ( ctx : Ctx ) { l s : RE } { loc : ℕ }
  → plug ctx (l + s ` loc) ≡ pd*-expr pdi
  → l ≈₀ s
  → Ambig r
pd*-Ctx-dup→Ambig pdi inj-inj ctx eq dup =
  pd*-Ambig→Ambig pdi inj-inj (Ctx-dup→Ambig ctx (pd*-expr pdi) eq dup)

```

Notes:

* `A1→Ambig` / `A2→Ambig` / `Ctx-dup→Ambig` are the special cases
  `w = []`, `inj = id` (realizability in the paper's sense is automatic
  here: every project `RE` has a parse tree, `r-∃u`).
* §6's `pd-pairs→Ambig` / `pd*-pairs→Ambig` is an *already lifted* form of
  A3: the two parse trees are built directly under the injections, so no
  injectivity hypothesis is needed (the pair sits in different sum branches,
  `LeftU≢RightU`).
* The remaining gap towards the paper's full proposition is unchanged:
  proving that `inj-inj` holds for the concrete injections produced by
  `pdUMany` (routine for the `lne`/`greedy` builders, false for
  `mkfuseInj`), and the converse direction
  ("`r` ambiguous ⇒ some realizable state fires A1/A2/A3"), which needs
  the FST / `Desc(r)` construction.

## 8. `Desc(r)` — the paper's states, built from partial derivatives

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

### 8.1. A3 stated verbatim for the initial state

With `derivᵖ`, the paper's A3 condition for the initial state,
"`lang(canonic(deriv r x)) ≠ {}` and `Idemp` applied", becomes a
computable boolean:

```agda
A3? : ( r : RE ) → ( c : Char ) → Bool
A3? r c with derivᵖ r (c ∷ [])
...   | nothing = false
...   | just s = proj₂ (canonic s)

-- the paper's A3 test fires on the §6.2 example:
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

Caveats (consistent with §6/§7):

* `derivᵖ r w` is a *witness term* for the derivative (same language),
  not a syntactic replica of Brzozowski's — stars unfold positionally
  (`pdinstance-star` appends `r * ε∉r ` loc`) and `sum-build`
  introduces artificial `+` locations.  The paper's own FST quotients by
  similarity anyway, and `≈₀`/`canonic` are location-insensitive, so
  the A3 *test* is unaffected.
* Soundness of a fired `A3?` still runs through `pd-pairs→Ambig` /
  `pd*-pairs→Ambig` (whose hypotheses need the duplicate pair in
  different sum branches).  To make `A3? r x ≡ true → Ambig r` itself a
  theorem, `canonic`'s rewrite trace would have to be reflected into a
  concrete `Ctx`/`plug` + pair witness — that reflection lemma is the
  missing piece, not the machinery around it.

For the *criteria* themselves the single-expression form is not needed: the
states are lists of partial derivatives, see §9.

## 9. `Desc(r)` as a list of partial derivatives (the pd-native form)

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

The three criteria are then tests *on the list*, and §7's `lift-Ambig`
applies componentwise — every element of `pd*-Desc r w` is the continuation
of some `pdi : PDInstance* r w`, and `pd*-A1→Ambig` / `pd*-A2→Ambig` /
`pd*-Ctx-dup→Ambig` are universally quantified over such an instance, so a
criterion firing at *any* member of the state list already gives `Ambig r`.
Only A3 needs an additional list-level test, which is exactly `dups-≈₀` —
no re-glued expression and no artificial `+` locations involved:

```agda
-- the paper's A3 test on the state reached after w then c:
-- does canonicalizing that state apply Idemp?
A3-list? : ( r : RE ) → ( w : List Char ) → ( c : Char ) → Bool
A3-list? r w c = dups-≈₀ (pd*-alts (PosixPD.pdUMany[ r , w ++ (c ∷ []) ]))

-- the §6.2 example, in list form: after 'a the state is the single fused
-- instance whose continuation is the sum of the two equal continuations
-- (the ' + ' carries the location 9 of the source expression, §8's
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

For one step the list form is the same computation as §6's `pd-Idemp?`:
`pdUMany[ r , x ∷ [] ]` is `pdU[ r , x ]` composed with the identity path
map, and `compose-pdi-with` keeps the continuation of its argument
(`pdinstance* {p}` with the same `p`), so `pd*-alts` of the one-step state
coincides with `pd-alts (pdU[ r , x ])`.  The list form is therefore a
*conservative* extension: it runs the same test on the state reached after
an arbitrary prefix, which is the paper's A3 for a descendant `s`, stated
without ever leaving the partial-derivative setting.



