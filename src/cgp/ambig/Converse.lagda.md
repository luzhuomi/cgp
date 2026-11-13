# Is the converse of the ambiguity criteria provable?

`cgp.ambig.Canonic` §7 proves the *soundness* direction of the three criteria
of section 6 of

> Sulzmann & Lu, *Derivative-Based Diagnosis of Regular Expression Ambiguity*,
> CIAA 2016

lifted along a partial-derivative path: `lift-A1→Ambig`, `lift-A2→Ambig` and
`lift-Ctx-dup→Ambig` all have the form "criterion at the state `p` ⇒ `Ambig r`".
This module asks about the reverse direction

> `Ambig r` ⇒ there is a state at which A1, A2 or the `Idemp` duplicate fires.

Short answer: **not as stated**, and the two readings have to be separated.

1. *Read at the initial state* (`w = []`, i.e. `Ambig r → AmbigA1 r ⊎ AmbigA2 r
   ⊎ CtxDup r`): **false**.  `r = ( a + a · a ) ⋆` is ambiguous — the word
   `a a` has the two parse trees `ListU [ a , a ]` and `ListU [ a · a ]` — and
   no criterion fires at `r`: a star has exactly one empty parse tree (¬ A1),
   and the hole contexts `Ctx` of the paper have no hole under a star, so
   neither the concatenation `a · a` nor the sum `a + a · a` of `r` is
   reachable by A2 or by the `Idemp` test (¬ A2, ¬ Ctx-dup).  §2–§3.  The
   ambiguity of `r` is a *factorisation* of the word inside the star, which is
   not one of the three syntactic patterns; that is exactly why the paper
   quantifies the criteria over `Desc(r)` instead of over `r`.
 2. *Read over the reachable states* (the paper's proposition): **not refuted
    by this example** — for this same `r` the criteria do fire further down.
    The state reached after `a a` is `( (ε · r⋆) + ((ε + ε · a) · r⋆) )`,
    which has two empty parse trees, so **A1 fires there**, `A1→Ambig` proves
    that state ambiguous, and `pd*-A1→Ambig` turns it into an ambiguity of `r`
    as soon as the injectivity of the transition map of that path is supplied
    (§4); A3 (`Idemp`) fires one letter later (§6).  Finding such a state out
    of an arbitrary ambiguity witness is the paper's `AllParseFST` / `Desc(r)`
    construction; §7 lists what is missing here.  The direction itself — an
    ambiguity witness followed letter by letter through the pd-states until a
    criterion fires at a reached state — is developed in
    `cgp.ambig.Complete`.
 3. *The duplicate one would expect here* — the choice
    `[ ε · r⋆ , ε · a · r⋆ , ε · r⋆ ]` an **unfused** (Antimirov) derivative
    would produce, whose third element repeats the first — is *not* what this
    project's derivative computes: the posix `pdinstance-oplus`/`fuse` merges
    the two branches into the single instance `pdUMany` reaches after `a a`
    (whose continuation is `sd-s2`, §4), and the two alternatives of that
    continuation are `≈₀`-different, so the list-level `Idemp` test stays
    `false` there.  The fusion is exactly where an alternative-level duplicate
    disappears; the multiplicity survives as the second empty parse tree of the
    state — i.e. as A1 (§4) — and the genuine `Idemp` situation for this `r`
    is one letter deeper (§6).

```agda
{-# OPTIONS --rewriting #-}
module cgp.ambig.Converse where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉ ; ε∈ ; ε∈ε ; ε∈_●_ ; ε∈_+_ ; ε∈_<+_ ; ε∈* ; ε∉$ ; ε∉fst ; ε∉snd ; ε∉_+_)

import cgp.ParseTree as ParseTree
open ParseTree using ( U ; EmptyU ; LetterU ; LeftU ; RightU ; PairU ; ListU ; flat ; unListU ; LeftU≢RightU )

import cgp.PDInstance as PDI
open PDI using ( PDInstance* )

import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( mkAllEmptyU )

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using ( Ambig; AmbigA1; AmbigA2; Ctx; 𝟘; Ctx●R; L●Ctx; Ctx+R; L+Ctx; plug; A1→Ambig; not-2-le-1 )

import cgp.ambig.Canonic as Canonic
open Canonic using ( _≈₀_ ; _≟₀_ ; pd*-Desc ; pd*-expr ; pd*-inj ; pd*-A1→Ambig ; _∈Descᵖ_
                   ; dups-≈₀ ; dedup ; A3-list? ; sum-spine ; sum-build ; canonic
                   ; ≈₀-● ; ≈₀-ε ; ≈₀-$ ; ≈₀-+ ; ≈₀-refl )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_] ; map ; length ; any)


import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using ( ℕ ; zero ; suc ; _≤_ ; s≤s )

import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-refl )

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; sym ; trans ; cong ; cong₂ ; subst)

import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_)
open Σ using (proj₁ ; proj₂)

import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂)

import Relation.Nullary as Nullary
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using (Dec; yes; no; ⌊_⌋)

import Data.Bool.Base as BoolB
open BoolB using (Bool; true; false)

import Data.Empty as Empty
open Empty using (⊥ ; ⊥-elim)
```

## 1. The candidate statement, and the expression

```agda
-- the Ctx-dup hypothesis of lift-Ctx-dup→Ambig / Ctx-dup→Ambig, as a
-- predicate on the state
-- (purpose): the third top-level reading ("a criterion at the initial
--   expression") needs this disjunct to be stated at all
-- (used in): `Complete-Top`, `sd-not-CtxDup`, `Complete-Top-sd`
-- (proof idea): definition — the shape `Canonic`'s soundness lift consumes,
--   read as a predicate
CtxDup : RE → Set
CtxDup r = Σ[ ctx ∈ Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
             ( plug ctx (l + s ` loc) ≡ r × l ≈₀ s )

-- the disjunction the three soundness lemmas would have to be complete for
-- (purpose): the *top-level* reading of the converse, to be refuted
-- (used in): `Complete-Top-sd`, `converse-Top-fails`
-- (proof idea): definition — A1 ⊎ A2 ⊎ CtxDup at the expression itself
Complete-Top : RE → Set
Complete-Top r = AmbigA1 r ⊎ AmbigA2 r ⊎ CtxDup r

-- r = ( a + a · a ) ⋆
-- (purpose): the running example's body — the ambiguous star of the paper's
--   example expression
-- (used in): `sd` below, `deriv-a-sd`, the test evaluations of §4
-- (proof idea): definition — a literal RE in normal form, chosen so every
--   derived list in this module computes by `refl`
sd-body : RE
sd-body = ( ($ 'a' ` 1) + ( ($ 'a' ` 2) ● ($ 'a' ` 3) ` 4 ) ` 5 )

-- (purpose): the non-nullability evidence the star constructor asks for
-- (used in): `sd` below
-- (proof idea): the sum is non-nullable because neither branch is
sd-ε∉ : ε∉ sd-body
sd-ε∉ = (ε∉_+_) ε∉$ (ε∉fst ε∉$)

-- (purpose): the concrete `r` of the whole module: ambiguous, with no
--   criterion at the top, criteria firing two steps down
-- (used in): everywhere — §§2–§4, §6, the test evaluations
-- (proof idea): definition — `sd-body` under the star
sd : RE
sd = sd-body * sd-ε∉ ` 6
```

## 2. `sd` is ambiguous: the word `a a` factors in two ways

```agda
-- ListU [ a ] [ a ]  (both letters through the left branch `a`)
-- (purpose): first parse tree of `sd` for the word `a a`
-- (used in): `sd-word`, `sd-u≢v`, `sd-ambig`
-- (proof idea): definition — a `ListU` star node with two `LeftU`-injected
--   letter trees
sd-u : U sd
sd-u = ListU ( LeftU (LetterU 'a') ∷ LeftU (LetterU 'a') ∷ [] )

-- ListU [ a · a ]  (both letters through the right branch `a · a`)
-- (purpose): second parse tree of `sd` for the same word
-- (used in): `sd-word`, `sd-u≢v`, `sd-ambig`
-- (proof idea): definition — a `ListU` star node with one `RightU`-injected
--   pair tree
sd-v : U sd
sd-v = ListU ( RightU (PairU (LetterU 'a') (LetterU 'a')) ∷ [] )

-- (purpose): both trees spell the same word `a a` — the ambiguity's
--   equal-flattening half
-- (used in): `sd-ambig`
-- (proof idea): both `flat`s compute to `'a' ∷ 'a' ∷ []`, so `refl`
sd-word : proj₁ (flat {sd} sd-u) ≡ proj₁ (flat {sd} sd-v)
sd-word = refl

-- (purpose): the two trees are different — the ambiguity's disequality half
-- (used in): `sd-ambig`
-- (proof idea): equality of the trees would equate their `unListU` lists,
--   where a `LeftU` row head is distinct from a `RightU` one (`()` clause)
sd-u≢v : ¬ (sd-u ≡ sd-v)
sd-u≢v eq with cong unListU eq
...   | ()

-- (purpose): `sd` is ambiguous — the hypothesis the converse's antecedent
--   satisfies, so that §3's refutation is non-vacuous
-- (used in): `converse-Top-fails`
-- (proof idea): package `sd-u`, `sd-v` with `sd-word` and `sd-u≢v`
sd-ambig : Ambig sd
sd-ambig = ( sd-u , sd-v , sd-word , sd-u≢v )
```

## 3. No criterion fires at `sd`

```agda
-- the empty parse trees of a star are exactly the empty list
-- (purpose): ¬ A1 at `sd` — the first disjunct of the top-level reading fails
-- (used in): `Complete-Top-sd`
-- (proof idea): any `ε∈ sd` is an `ε∈*`, whose empty tree is `ListU []`;
--   A1 asks for ≥ 2 of them, and `not-2-le-1` refutes that
sd-not-A1 : ¬ AmbigA1 sd
sd-not-A1 (ε∈sd , len≥2) with ε∈sd 
...   | ε∈* = not-2-le-1 len≥2

-- (purpose): no hole context of the paper ever plugs a concatenation to get
--   `sd` — the syntactic reason A2 cannot see inside a star
-- (used in): `sd-not-A2`
-- (proof idea): case analysis on `ctx`: at `𝟘` the plug result is a `●` node
--   but `sd` is a `*` node (absurd `()`); under `Ctx●R`/`L●Ctx`/`Ctx+R`/`L+Ctx`
--   the outermost node carries the context's own location, never `sd`'s `6`
sd-plug-●≢sd : ∀ ( ctx : Ctx ) ( l t : RE ) ( loc : ℕ )
  → plug ctx (l ● t ` loc) ≡ sd → ⊥
sd-plug-●≢sd 𝟘 l t loc ()
sd-plug-●≢sd (Ctx●R ctx s loc₁) l t loc ()
sd-plug-●≢sd (L●Ctx s ctx loc₁) l t loc ()
sd-plug-●≢sd (Ctx+R ctx s loc₁) l t loc ()
sd-plug-●≢sd (L+Ctx s ctx loc₁) l t loc ()

-- (purpose): ¬ A2 at `sd` — the second disjunct fails
-- (used in): `Complete-Top-sd`
-- (proof idea): an `AmbigA2 sd` exhibits a context plugging a concatenation
--   to `sd`, excluded by `sd-plug-●≢sd`
sd-not-A2 : ¬ AmbigA2 sd
sd-not-A2 (ctx , l , t , loc , (eq , _)) = sd-plug-●≢sd ctx l t loc eq

-- (purpose): the same for sums — no context plugs a `+` node to `sd`, so the
--   Ctx-dup pattern is unreachable at the top too
-- (used in): `sd-not-CtxDup`
-- (proof idea): same case analysis on `ctx` as `sd-plug-●≢sd`
sd-plug-+≢sd : ∀ ( ctx : Ctx ) ( l s : RE ) ( loc : ℕ )
  → plug ctx (l + s ` loc) ≡ sd → ⊥
sd-plug-+≢sd 𝟘 l s loc ()
sd-plug-+≢sd (Ctx●R ctx s₁ loc₁) l s loc ()
sd-plug-+≢sd (L●Ctx s₁ ctx loc₁) l s loc ()
sd-plug-+≢sd (Ctx+R ctx s₁ loc₁) l s loc ()
sd-plug-+≢sd (L+Ctx s₁ ctx loc₁) l s loc ()

-- (purpose): ¬ CtxDup at `sd` — the third disjunct fails
-- (used in): `Complete-Top-sd`
-- (proof idea): a `CtxDup sd` exhibits a context plugging a congruent sum to
--   `sd`; the plug equation alone is excluded by `sd-plug-+≢sd`
sd-not-CtxDup : ¬ CtxDup sd
sd-not-CtxDup (ctx , l , s , loc , (eq , _)) = sd-plug-+≢sd ctx l s loc eq

-- A3 has the shape "at the state r, on the letter x, Idemp applies to
-- deriv r x", so a reading at the initial state also has to fail there.
-- The Brzozowski derivative of sd (paper's rule for _conc_, the residual
-- of a star is deriv r x · r⋆):  d_a sd = a · r⋆ + r · r⋆
-- (purpose): the paper-form derivative `d_a sd` — the term A3 would inspect
--   if the converse were read at the initial state
-- (used in): `deriv-a-sd-no-Idemp`
-- (proof idea): definition — the derivative by the paper's rules, written
--   out with the locations the original expression carries
deriv-a-sd : RE
deriv-a-sd = ( ($ 'a' ` 1) ● sd ` 30 ) + ( sd-body ● sd ` 31 ) ` 32

-- (purpose): A3 fails at the top as well — `canonic` finds no duplicate in
--   `d_a sd` (`a · r⋆` and `(a + a·a) · r⋆` are `≈₀`-different)
-- (used in): the §3 conclusion quoted in §6's summary
-- (proof idea): `canonic` normalises and `dups-≈₀` compares; the compute
--   reduces to `false`, so `refl`
deriv-a-sd-no-Idemp : proj₂ (canonic deriv-a-sd) ≡ false
deriv-a-sd-no-Idemp = refl

-- (purpose): no disjunct of the top-level reading holds at `sd`
-- (used in): `converse-Top-fails`
-- (proof idea): three cases on the disjunction, each discharged by the
--   matching §3 non-firing lemma
Complete-Top-sd : Complete-Top sd → ⊥
Complete-Top-sd (inj₁ a1) = sd-not-A1 a1
Complete-Top-sd (inj₂ (inj₁ a2)) = sd-not-A2 a2
Complete-Top-sd (inj₂ (inj₂ cd)) = sd-not-CtxDup cd

-- (purpose): the module's negative result — the converse read at the initial
--   state is false
-- (used in): the header's reading 1
-- (proof idea): instantiate the universal claim at `sd` and `sd-ambig`, then
--   apply `Complete-Top-sd`
converse-Top-fails : ¬ ( ∀ ( r : RE ) → Ambig r → Complete-Top r )
converse-Top-fails h = Complete-Top-sd (h sd sd-ambig)
```

## 4. The same expression *is* caught two steps down

The state of `sd` after `a` and after `a a`, computed by `pdUMany` (the
continuation of the body after one `a` is the posix fusion of the two
branches, `ε + ε · a`):

```agda
-- (purpose): the body `sd-body` after `a` — the posix fusion of the two
--   branches' residuals, `ε + ε · a`
-- (used in): `sd-s1`, `ε∈res-a`
-- (proof idea): definition — what `pdUMany`'s fuse computes for `sd-body`
--   on `a` (checked by `sd-Desc₂`'s `refl` one level up)
res-a : RE
res-a = ( ε + ( ε ● ($ 'a' ` 3) ` 4 ) ` 5 )

-- the state after `a`
-- (purpose): the pd-state reached from `sd` after the letter `a`
-- (used in): `sd-s2`, `ε∈sd-s1`, `sd-s1-criteria`, `sd-Ambig-from-descendant`'s
--   path
-- (proof idea): definition — the residual `res-a` followed by the star
sd-s1 : RE
sd-s1 = ( res-a ● sd ` 6 )


-- the continuation of the ε-branch of that state
-- (purpose): the first alternative of `sd-s2` — the outer star re-glued
-- (used in): `sd-s2`, `ε∈sd-x`
-- (proof idea): definition — the ε summand of `res-a` extended by `r⋆`
sd-x : RE
sd-x = ( ε ● sd ` 6 )

-- the state after `a a`: one instance, its continuation is the sum of the
-- continuations of the two branches
-- (purpose): the pd-state reached after `a a` — the state where A1 fires
-- (used in): `sd-s2-A1`, `sd-s2-Ambig`, `ε∈sd-s2`, `sd-s2-criteria`,
--   `sd-Desc₂`, `sd-Ambig-from-descendant`
-- (proof idea): definition — `sd-x + sd-s1`, the fused single instance's
--   continuation
sd-s2 : RE
sd-s2 = ( sd-x + sd-s1 ` 6 )

-- (purpose): the descent really is realizable — `sd-s2 ∷ []` is the state
--   list `pdUMany` computes for the prefix `a a`
-- (used in): the §4 prose (non-vacuity of `sd-Ambig-from-descendant`'s
--   hypotheses)
-- (proof idea): the membership is a `refl` pair (the prefix, the computed
--   list equation)
sd-Desc₂ : ( sd-s2 ∷ [] ) ∈Descᵖ sd
sd-Desc₂ = ( 'a' ∷ 'a' ∷ [] , refl )
```

At `sd-s1` the sum has the non-congruent branches `ε` and `ε · a`, and every
concatenation there has a left factor with a single empty parse tree, so none
of the three criteria fires (checked as tests below, `sd-s1-criteria`).
`sd-s2`, however, is nullable **twice over** — once through `ε · r⋆` and once
through `(ε + ε · a) · r⋆` — so A1 fires there:

```agda
-- (purpose): `sd-x` is nullable — the ε-branch re-enters the star
-- (used in): `ε∈sd-s2`
-- (proof idea): `ε∈ · ε∈*` through the concatenation rule
ε∈sd-x : ε∈ sd-x
ε∈sd-x = (ε∈_●_) ε∈ε ε∈*

-- (purpose): `res-a` is nullable through its *first* summand only — this is
--   the second empty path §4's prose counts
-- (used in): `ε∈sd-s1`
-- (proof idea): left-injection into the sum; the other branch `ε · a` is not
--   nullable (`ε∉snd ε∉$`)
ε∈res-a : ε∈ res-a
ε∈res-a = (ε∈_<+_) ε∈ε (ε∉snd ε∉$)

-- (purpose): `sd-s1` is nullable — residual ε-path extended by the star
-- (used in): `ε∈sd-s2`
-- (proof idea): `ε∈res-a · ε∈*` through the concatenation rule
ε∈sd-s1 : ε∈ sd-s1
ε∈sd-s1 = (ε∈_●_) ε∈res-a ε∈*

-- (purpose): `sd-s2` is nullable by two distinct proofs — through `sd-x` and
--   through `sd-s1`
-- (used in): `sd-s2-A1`
-- (proof idea): the sum rule applied to the two different proofs above
ε∈sd-s2 : ε∈ sd-s2
ε∈sd-s2 = (ε∈_+_) ε∈sd-x ε∈sd-s1

-- (purpose): A1 fires at `sd-s2` — two empty parse trees
-- (used in): `sd-s2-Ambig`, `sd-Ambig-from-descendant`
-- (proof idea): `ε∈sd-s2` plus the two-empty-trees evidence `2 ≤ 2`
sd-s2-A1 : AmbigA1 sd-s2
sd-s2-A1 = ( ε∈sd-s2 , s≤s (s≤s ≤-refl) )

-- (purpose): the reached state is ambiguous by the paper's soundness direction
--   of A1
-- (used in): `sd-Ambig-from-descendant`
-- (proof idea): `A1→Ambig` applied to `sd-s2-A1`
sd-s2-Ambig : Ambig sd-s2
sd-s2-Ambig = A1→Ambig sd-s2 sd-s2-A1
```

The same picture for the criteria as *tests*, i.e. in the form in which an
implementation would compute them (`A1?`/`A2?` use the canonical nullability
proof `ε∈?`, and both look at *every* subterm, while the hole contexts of the
paper have no hole under a star).  A `false` here therefore rules out the
corresponding proposition, and the results agree with §3 and with `sd-s2-A1`:

```agda
-- (purpose): all subterms of an expression — the quantification the *tests*
--   use in place of the paper's hole contexts
-- (used in): `A2?`, `CtxDup?`
-- (proof idea): definition — structural recursion, node first then branches
subterms : RE → List RE
subterms ε = ε ∷ []
subterms ( $ c ` loc ) = ( $ c ` loc ) ∷ []
subterms ( l ● s ` loc ) = ( l ● s ` loc ) ∷ subterms l ++ subterms s
subterms ( l + s ` loc ) = ( l + s ` loc ) ∷ subterms l ++ subterms s
subterms ( r * nε ` loc ) = ( r * nε ` loc ) ∷ subterms r

-- (purpose): the boolean version of "at least two empty parse trees" for the
--   length of `mkAllEmptyU`'s list
-- (used in): `A1?`, `A2-node?`
-- (proof idea): definition — two constructors match, the rest is `false`
len≥2 : ∀ { a : Set } → List a → Bool
len≥2 (_ ∷ _ ∷ _) = true
len≥2 _ = false

-- A1: allEps of the expression itself
-- (purpose): A1 as a computable test (header: the form an implementation uses)
-- (used in): `sd-criteria`, `sd-s1-criteria`, `sd-s2-criteria`
-- (proof idea): decide nullability, then count the canonical empty-tree list
A1? : RE → Bool
A1? r with RE.ε∈? r
...   | yes ε∈r = len≥2 (mkAllEmptyU ε∈r)
...   | no ¬ε∈r = false

-- A2: a concatenation subterm with a nullable left factor having ≥ 2 empty trees
-- (purpose): the per-node half of the A2 test
-- (used in): `A2?`
-- (proof idea): same nullability/all-empty check, only at `●` nodes
A2-node? : RE → Bool
A2-node? ( l ● s ` loc ) with RE.ε∈? l
...   | yes ε∈l = len≥2 (mkAllEmptyU ε∈l)
...   | no ¬ε∈l = false
A2-node? ( $ c ` loc ) = false
A2-node? ( l + s ` loc ) = false
A2-node? ( r * nε ` loc ) = false
A2-node? ε = false

-- (purpose): A2 as a test — any subterm fires the node test
-- (used in): `sd-criteria`, `sd-s1-criteria`
-- (proof idea): `List.any` over `subterms`
A2? : RE → Bool
A2? r = List.any A2-node? (subterms r)

-- Idemp: a sum subterm with congruent branches
-- (purpose): the per-node half of the Ctx-dup/Idemp test — a `+` with
--   `≈₀`-equal branches
-- (used in): `CtxDup?`
-- (proof idea): decision procedure `≟₀` on the two branches, only at `+` nodes
+dup-node? : RE → Bool
+dup-node? ( l + s ` loc ) = ⌊ l ≟₀ s ⌋
+dup-node? ( $ c ` loc ) = false
+dup-node? ( l ● s ` loc ) = false
+dup-node? ( r * nε ` loc ) = false
+dup-node? ε = false

-- (purpose): the Idemp duplicate as a test on the expression's subterms
-- (used in): `sd-criteria`, `sd-s1-criteria`
-- (proof idea): `List.any` over `subterms`
CtxDup? : RE → Bool
CtxDup? r = List.any +dup-node? (subterms r)

-- (purpose): test-side agreement with §3 — all three tests are `false` at `sd`
-- (used in): the §4 prose ("the results agree with §3")
-- (proof idea): the whole vector computes by `refl`
sd-criteria : ( A1? sd ) ∷ ( A2? sd ) ∷ ( CtxDup? sd ) ∷ []
  ≡ false ∷ false ∷ false ∷ []
sd-criteria = refl

-- (purpose): no test fires one step down either, at `sd-s1`
-- (used in): the §4 prose about `sd-s1`
-- (proof idea): computes by `refl` — the branches `ε`/`ε · a` are not `≈₀`
--   equal and every left factor has one empty tree
sd-s1-criteria : ( A1? sd-s1 ) ∷ ( A2? sd-s1 ) ∷ ( CtxDup? sd-s1 ) ∷ []
  ≡ false ∷ false ∷ false ∷ []
sd-s1-criteria = refl

-- (purpose): the A1 test fires at `sd-s2`, agreeing with `sd-s2-A1`
-- (used in): the §4 prose and the §6 summary
-- (proof idea): computes by `refl`
sd-s2-criteria : A1? sd-s2 ≡ true
sd-s2-criteria = refl
```

and the ambiguity of `sd` follows from it along the path `a a` — the last step
is `pd*-A1→Ambig` of `cgp.ambig.Canonic` §7, whose only remaining argument is
the injectivity of that path's transition map:

```agda
-- (purpose): the reading that survives — an ambiguity of `sd` lifted from the
--   descendant reached along `a a`, given that path's transition injectivity
-- (used in): the §4 closing prose, the header's reading 2
-- (proof idea): transport `sd-s2-A1` along the hypothesis `pd*-expr pdi ≡ sd-s2`
--   and feed it to `Canonic`'s `pd*-A1→Ambig`
sd-Ambig-from-descendant : ( pdi : PDInstance* sd ( 'a' ∷ 'a' ∷ [] ) )
  → pd*-expr pdi ≡ sd-s2
  → ( ∀ ( u v : U (pd*-expr pdi) )
        → pd*-inj pdi u ≡ pd*-inj pdi v → u ≡ v )
  → Ambig sd
sd-Ambig-from-descendant pdi eq inj-inj =
  pd*-A1→Ambig pdi inj-inj (subst ( λ p → AmbigA1 p ) (sym eq) sd-s2-A1)
```

The hypotheses are not vacuous: `sd-Desc₂` above is a `refl`, i.e. `pdUMany`
really does produce exactly one instance for `a a` and its continuation is
`sd-s2`.  What is left open is the injectivity hypothesis — for this concrete
instance it is exactly the item §7 lists as missing (the per-builder
injectivity of the maps `pdUMany` builds, which needs the Antimirov-
disjointness half); `cgp.ambig.Complete` develops the completeness direction
instead, which reaches the same conclusion by a descent and never asks that
hypothesis.

## 6. Where `Idemp` does fire: one level deeper

```agda
-- the word one letter longer than the descent to `sd-s2`
-- (purpose): the prefix on which the list-level A3 test finally fires
-- (used in): `A3-sd-none`
-- (proof idea): definition — the word `a a`
aa : List Char
aa = 'a' ∷ 'a' ∷ []

-- the list-level A3 test (`A3-list?`) at the initial expression, after `a`,
-- and after `a a` -- the first two are false, the third is true
-- (purpose): §6's claim in computed form — A3 does not fire at the top or at
--   `sd-s1`, it fires one level deeper, after `a a` on the letter `a`
-- (used in): the §6 prose and the §6 summary's last bullet
-- (proof idea): the whole vector of test results computes by `refl`
A3-sd-none : ( A3-list? sd [] 'a' ) ∷ ( A3-list? sd ( 'a' ∷ [] ) 'a' ) ∷ ( A3-list? sd aa 'a' ) ∷ []
  ≡ false ∷ false ∷ true ∷ []
A3-sd-none = refl
```

The computed block above is the list-level A3 test (`A3-list?`, `Canonic` §9)
at the initial expression, after `a`, and after `a a`: `false`, `false`,
`true`.  Where it fires: the continuation of the *outer* star
is glued onto the first summand `(ε · r⋆)`, whose own continuation is `r⋆`;
extending that inner star gives the same continuation, so `deriv`-ing the state
after `a a` yields `ε · r⋆ · r⋆` twice.  In this project the two copies are
merged by `fuse` into a literal `+` node with `≈₀`-equal branches — which is
exactly what `dups-≈₀` of `Canonic` §9 detects.  Written out, the derivative of
`sd-s1 = (ε + ε · a) · r⋆` is

    d_a( (ε + ε·a)·r⋆ ) = ε·r⋆ + (ε·a)·r⋆ + r·(ε·r⋆ + (ε·a)·r⋆)

whose first alternative, extended once more, is `ε · r⋆ · r⋆` — the same term
the star extension of `ε · r⋆` produces.

Whether the *same* depth already shows it in the paper's form is a bookkeeping
question: with the nullable-prefix rule applied first — the normal form the
paper's `deriv` maintains — the state after `a a` keeps `a · r⋆` instead of
`ε · a · r⋆`, and its star extension is `d_a(r) · r⋆ = (a + a · a)·r⋆`, i.e.
`a · r⋆ + r · r⋆` with `a ≢₀ r`, so no `+` with congruent branches appears
there.  Both derivations
describe the same ambiguity (two ways of gluing the outer star onto a
continuation that is itself a star); pinning the difference down would need
the `pdUMany`/`deriv` correspondence listed in §7.

That settles what `sd` can and cannot be used for:

* the reading "a criterion fires **at the initial expression**" is refuted
  (§3): `sd` is ambiguous and `¬ A1`, `¬ A2`, `¬ CtxDup` there, and A3 in the
  paper's own form fails too (`deriv-a-sd-no-Idemp`);
* the reading of the paper's proposition — "there is a *realizable descendant*
  `s ∈ Desc(r)` and a letter `x`" — is **not** refuted by `sd`: A1 holds at
  the pd-state `sd-s2` reached after `a a` (§4) and the A3 *test* holds for
  the pd-state after `a a` on the letter `a` (§6).  `sd` witnesses the
  *soundness* lifts working, not a gap in the proposition.

## 7. What a completeness proof would need

* A witness search over `Desc(r)`: from `Ambig r` (two parse trees of `r` for a
  word `w`) produce the state of `pd*-Desc r u` (for a prefix `u` of `w`) at
  which a criterion fires.  The paper does this with `AllParseFST`; here that
  would mean the correspondence between `U r`-trees and `pdUMany` paths
  (partial: `ParseTree.unflat`/`recons` on one side, `pd*-Desc` on the other).
* The three criteria as *decidable* tests on the state list (`A1?`/`A2?` via
  `mkAllEmptyU`, duplicate detection via `dups-≈₀`) and a proof that firing of
  the test is equivalent to the proposition used by the lift lemmas.
* `inj-inj` for the concrete injections built by `pdUMany` — the per-builder
  injectivity proofs (`injId`, the list/pair/sum extensions) were developed in
  an earlier, wider version of `cgp.ambig.Complete` and removed with its
  example arc; `PosixPD.mkfuseInj` is injective only relative to a
  disjointness of its two branch ranges, which is the Antimirov-disjointness
  half missing above.  A state reached through a fused instance cannot be
  lifted without recovering the multiplicity.  §4's `sd-s2` computation shows
  the fusion is exactly
  where an alternative-level duplicate disappears; for this `r` at that depth
  the multiplicity survives only as the second empty parse tree of the state,
  i.e. as A1 (§4), while the `Idemp` situation only shows up one level deeper
  (§6).
