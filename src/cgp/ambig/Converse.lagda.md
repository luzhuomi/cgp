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
 2. *Read over the reachable states* (the paper's proposition): for this same
   `r` the criteria do fire, two letters down — the state reached after `a a`
   is `( (ε · r⋆) + ((ε + ε · a) · r⋆) )`, which has two empty parse trees, so
   **A1 fires there**, `A1→Ambig` proves that state ambiguous, and
   `pd*-A1→Ambig` turns it into an ambiguity of `r` as soon as the injectivity
   of the transition map of that path is supplied (§4).  Finding such a state
   out of an arbitrary ambiguity witness is the paper's `AllParseFST` /
   `Desc(r)` construction; §5 lists what is missing here.

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
open Canonic using ( _≈₀_ ; _≟₀_ ; pd*-Desc ; pd*-expr ; pd*-inj ; pd*-A1→Ambig ; _∈Descᵖ_ )

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
CtxDup : RE → Set
CtxDup r = Σ[ ctx ∈ Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
             ( plug ctx (l + s ` loc) ≡ r × l ≈₀ s )

-- the disjunction the three soundness lemmas would have to be complete for
Complete-Top : RE → Set
Complete-Top r = AmbigA1 r ⊎ AmbigA2 r ⊎ CtxDup r

-- r = ( a + a · a ) ⋆
sd-body : RE
sd-body = ( ($ 'a' ` 1) + ( ($ 'a' ` 2) ● ($ 'a' ` 3) ` 4 ) ` 5 )

sd-ε∉ : ε∉ sd-body
sd-ε∉ = (ε∉_+_) ε∉$ (ε∉fst ε∉$)

sd : RE
sd = sd-body * sd-ε∉ ` 6
```

## 2. `sd` is ambiguous: the word `a a` factors in two ways

```agda
-- ListU [ a ] [ a ]  (both letters through the left branch `a`)
sd-u : U sd
sd-u = ListU ( LeftU (LetterU 'a') ∷ LeftU (LetterU 'a') ∷ [] )

-- ListU [ a · a ]  (both letters through the right branch `a · a`)
sd-v : U sd
sd-v = ListU ( RightU (PairU (LetterU 'a') (LetterU 'a')) ∷ [] )

sd-word : proj₁ (flat {sd} sd-u) ≡ proj₁ (flat {sd} sd-v)
sd-word = refl

sd-u≢v : ¬ (sd-u ≡ sd-v)
sd-u≢v eq with cong unListU eq
...   | ()

sd-ambig : Ambig sd
sd-ambig = ( sd-u , sd-v , sd-word , sd-u≢v )
```

## 3. No criterion fires at `sd`

```agda
-- the empty parse trees of a star are exactly the empty list
sd-not-A1 : ¬ AmbigA1 sd
sd-not-A1 (ε∈sd , len≥2) with ε∈sd 
...   | ε∈* = not-2-le-1 len≥2

-- a hole context (no hole under a star) can never produce the ⋆ at the root
-- of sd, and neither can it reach the concatenation a · a through the ⋆
sd-plug-●≢sd : ∀ ( ctx : Ctx ) ( l t : RE ) ( loc : ℕ )
  → plug ctx (l ● t ` loc) ≡ sd → ⊥
sd-plug-●≢sd 𝟘 l t loc ()
sd-plug-●≢sd (Ctx●R ctx s loc₁) l t loc ()
sd-plug-●≢sd (L●Ctx s ctx loc₁) l t loc ()
sd-plug-●≢sd (Ctx+R ctx s loc₁) l t loc ()
sd-plug-●≢sd (L+Ctx s ctx loc₁) l t loc ()

sd-not-A2 : ¬ AmbigA2 sd
sd-not-A2 (ctx , l , t , loc , (eq , _)) = sd-plug-●≢sd ctx l t loc eq

sd-plug-+≢sd : ∀ ( ctx : Ctx ) ( l s : RE ) ( loc : ℕ )
  → plug ctx (l + s ` loc) ≡ sd → ⊥
sd-plug-+≢sd 𝟘 l s loc ()
sd-plug-+≢sd (Ctx●R ctx s₁ loc₁) l s loc ()
sd-plug-+≢sd (L●Ctx s₁ ctx loc₁) l s loc ()
sd-plug-+≢sd (Ctx+R ctx s₁ loc₁) l s loc ()
sd-plug-+≢sd (L+Ctx s₁ ctx loc₁) l s loc ()

sd-not-CtxDup : ¬ CtxDup sd
sd-not-CtxDup (ctx , l , s , loc , (eq , _)) = sd-plug-+≢sd ctx l s loc eq

-- the top-level reading of the converse is refutable
Complete-Top-sd : Complete-Top sd → ⊥
Complete-Top-sd (inj₁ a1) = sd-not-A1 a1
Complete-Top-sd (inj₂ (inj₁ a2)) = sd-not-A2 a2
Complete-Top-sd (inj₂ (inj₂ cd)) = sd-not-CtxDup cd

converse-Top-fails : ¬ ( ∀ ( r : RE ) → Ambig r → Complete-Top r )
converse-Top-fails h = Complete-Top-sd (h sd sd-ambig)
```

## 4. The same expression *is* caught two steps down

The state of `sd` after `a` and after `a a`, computed by `pdUMany` (the
continuation of the body after one `a` is the posix fusion of the two
branches, `ε + ε · a`):

```agda
res-a : RE
res-a = ( ε + ( ε ● ($ 'a' ` 3) ` 4 ) ` 5 )

-- the state after `a`
sd-s1 : RE
sd-s1 = ( res-a ● sd ` 6 )

sd-Desc₁ : ( sd-s1 ∷ [] ) ∈Descᵖ sd
sd-Desc₁ = ( 'a' ∷ [] , refl )

-- the continuation of the ε-branch of that state
sd-x : RE
sd-x = ( ε ● sd ` 6 )

-- the state after `a a`: one instance, its continuation is the sum of the
-- continuations of the two branches
sd-s2 : RE
sd-s2 = ( sd-x + sd-s1 ` 6 )

sd-Desc₂ : ( sd-s2 ∷ [] ) ∈Descᵖ sd
sd-Desc₂ = ( 'a' ∷ 'a' ∷ [] , refl )
```

At `sd-s1` the sum has the non-congruent branches `ε` and `ε · a`, and every
concatenation there has a left factor with a single empty parse tree, so none
of the three criteria fires (checked as tests below, `sd-s1-criteria`).
`sd-s2`, however, is nullable **twice over** — once through `ε · r⋆` and once
through `(ε + ε · a) · r⋆` — so A1 fires there:

```agda
ε∈sd-x : ε∈ sd-x
ε∈sd-x = (ε∈_●_) ε∈ε ε∈*

ε∈res-a : ε∈ res-a
ε∈res-a = (ε∈_<+_) ε∈ε (ε∉snd ε∉$)

ε∈sd-s1 : ε∈ sd-s1
ε∈sd-s1 = (ε∈_●_) ε∈res-a ε∈*

ε∈sd-s2 : ε∈ sd-s2
ε∈sd-s2 = (ε∈_+_) ε∈sd-x ε∈sd-s1

sd-s2-A1 : AmbigA1 sd-s2
sd-s2-A1 = ( ε∈sd-s2 , s≤s (s≤s ≤-refl) )

sd-s2-Ambig : Ambig sd-s2
sd-s2-Ambig = A1→Ambig sd-s2 sd-s2-A1
```

The same picture for the criteria as *tests*, i.e. in the form in which an
implementation would compute them (`A1?`/`A2?` use the canonical nullability
proof `ε∈?`, and both look at *every* subterm, while the hole contexts of the
paper have no hole under a star).  A `false` here therefore rules out the
corresponding proposition, and the results agree with §3 and with `sd-s2-A1`:

```agda
subterms : RE → List RE
subterms ε = ε ∷ []
subterms ( $ c ` loc ) = ( $ c ` loc ) ∷ []
subterms ( l ● s ` loc ) = ( l ● s ` loc ) ∷ subterms l ++ subterms s
subterms ( l + s ` loc ) = ( l + s ` loc ) ∷ subterms l ++ subterms s
subterms ( r * nε ` loc ) = ( r * nε ` loc ) ∷ subterms r

len≥2 : ∀ { a : Set } → List a → Bool
len≥2 (_ ∷ _ ∷ _) = true
len≥2 _ = false

-- A1: allEps of the expression itself
A1? : RE → Bool
A1? r with RE.ε∈? r
...   | yes ε∈r = len≥2 (mkAllEmptyU ε∈r)
...   | no ¬ε∈r = false

-- A2: a concatenation subterm with a nullable left factor having ≥ 2 empty trees
A2-node? : RE → Bool
A2-node? ( l ● s ` loc ) with RE.ε∈? l
...   | yes ε∈l = len≥2 (mkAllEmptyU ε∈l)
...   | no ¬ε∈l = false
A2-node? ( $ c ` loc ) = false
A2-node? ( l + s ` loc ) = false
A2-node? ( r * nε ` loc ) = false
A2-node? ε = false

A2? : RE → Bool
A2? r = List.any A2-node? (subterms r)

-- Idemp: a sum subterm with congruent branches
+dup-node? : RE → Bool
+dup-node? ( l + s ` loc ) = ⌊ l ≟₀ s ⌋
+dup-node? ( $ c ` loc ) = false
+dup-node? ( l ● s ` loc ) = false
+dup-node? ( r * nε ` loc ) = false
+dup-node? ε = false

CtxDup? : RE → Bool
CtxDup? r = List.any +dup-node? (subterms r)

sd-criteria : ( A1? sd ) ∷ ( A2? sd ) ∷ ( CtxDup? sd ) ∷ []
  ≡ false ∷ false ∷ false ∷ []
sd-criteria = refl

sd-s1-criteria : ( A1? sd-s1 ) ∷ ( A2? sd-s1 ) ∷ ( CtxDup? sd-s1 ) ∷ []
  ≡ false ∷ false ∷ false ∷ []
sd-s1-criteria = refl

sd-s2-criteria : A1? sd-s2 ≡ true
sd-s2-criteria = refl
```

and the ambiguity of `sd` follows from it along the path `a a` — the last step
is `pd*-A1→Ambig` of `cgp.ambig.Canonic` §7, whose only remaining argument is
the injectivity of that path's transition map:

```agda
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
`sd-s2`; what is missing is a proof that the injection of that instance
(built with `PosixPD.mkfuseInj`) is injective.

## 5. What a completeness proof would need

* A witness search over `Desc(r)`: from `Ambig r` (two parse trees of `r` for a
  word `w`) produce the state of `pd*-Desc r u` (for a prefix `u` of `w`) at
  which a criterion fires.  The paper does this with `AllParseFST`; here that
  would mean the correspondence between `U r`-trees and `pdUMany` paths
  (partial: `ParseTree.unflat`/`recons` on one side, `pd*-Desc` on the other).
* The three criteria as *decidable* tests on the state list (`A1?`/`A2?` via
  `mkAllEmptyU`, duplicate detection via `dups-≈₀`) and a proof that firing of
  the test is equivalent to the proposition used by the lift lemmas.
* `inj-inj` for the concrete injections built by `pdUMany` — the `lne`/`greedy`
  builders are injective, `PosixPD.mkfuseInj` is not in general, and a state
  reached through a fused instance cannot be lifted without recovering the
  multiplicity, which is where the paper's `canonic`/similarity construction
  (and its `Idemp` rule) enters.
