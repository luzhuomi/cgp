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
    construction; §7 lists what is missing here.  The injectivity half of that
    direction — the transition map of each pd builder is injective under
    conditions that are the negations of the criteria — is developed in
    `cgp.ambig.Complete`.
 3. *The duplicate one would expect here* — the choice
    `[ ε · r⋆ , ε · a · r⋆ , ε · r⋆ ]` an **unfused** (Antimirov) derivative
    would produce, whose third element repeats the first — is indeed detected
    (`ant-aa-dup`; `canonic` applies `Idemp` to the oplus'ed form), but it is
    not a *canonical* state: the nullable-prefix elimination the derivative
    itself performs turns the third alternative into `ε · a · r⋆`, i.e. into
    the second one, so the canonical state after `a a` is `{ r⋆ , a · r⋆ }` and
    `Idemp` does not apply there.  This project's `pdUMany` (the posix variant)
    reaches the same pair even more directly, as the single fused instance
    `sd-s2`.  The genuine `Idemp` situation for this `r` is one letter deeper
    (§5.1, §6).

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

-- A3 has the shape "at the state r, on the letter x, Idemp applies to
-- deriv r x", so a reading at the initial state also has to fail there.
-- The Brzozowski derivative of sd (paper's rule for _conc_, the residual
-- of a star is deriv r x · r⋆):  d_a sd = a · r⋆ + r · r⋆
deriv-a-sd : RE
deriv-a-sd = ( ($ 'a' ` 1) ● sd ` 30 ) + ( sd-body ● sd ` 31 ) ` 32

deriv-a-sd-no-dup : dups-≈₀ ( sum-spine deriv-a-sd ) ≡ false
deriv-a-sd-no-dup = refl

deriv-a-sd-no-Idemp : proj₂ (canonic deriv-a-sd) ≡ false
deriv-a-sd-no-Idemp = refl

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

## 5. The duplicate that is (and is not) there

One might expect the state after `a a` to be the Antimirov triple

    [ ε · r⋆ ]  [ ε · a · r⋆ ]  [ ε · r⋆ ]

(the `a` branch of the body and the `a · a` branch each contribute a
continuation, and the first and third are the same `r⋆`), and to read the third
element as a duplicate of the first, i.e. as criterion A3/`Idemp`.  With
`aa = 'a' ∷ 'a' ∷ []`, the computed facts (`sd-s2-state`, `no-pd-dup`,
`all-dups`, …) say what actually happens:

* this project's `pdU` is the **posix** one: `pdinstance-oplus`/`PosixPD.fuse`
  merge the two branches into *one* instance, so `pd*-Desc sd aa` is the
  singleton list `[ sd-s2 ]` (`sd-s2-state`), and `sum-spine sd-s2` has exactly
  the two alternatives `sd-x = ε · r⋆` and `sd-s1 = (ε + ε · a) · r⋆`
  (`sd-s2-alts`).  There is no second copy of `ε · r⋆` to compare with;
* the two alternatives are *not* congruent: `¬ ( sd-x ≈₀ sd-s1 )` (`≈₀` is
  structural and needs left components `ε ≈₀ ε + ε · a`, which is empty);
* so the list-level A3 test of `Canonic` §9 stays `false`
  (`dups-≈₀ (pd*-Desc sd aa) ≡ false`), and so does the syntactic one, for the
  same reason as at `sd`: `CtxDup? sd-s2 ≡ false` — there is no *sum subterm*
  with congruent branches anywhere in `sd-s2`;
* `canonic sd-s2` performs no rewrite (`proj₂ ≡ false`); it removes duplicates
  only *inside* a `+` node, and the only `+` node here has the two
  non-congruent alternatives;
* if one duplicates the Antimirov list by hand, the duplicate *is* found —
  `dups-≈₀ ( sd-x ∷ sd-s1 ∷ sd-x ∷ [] ) ≡ true` — so the reading is right for
  *a* list of alternatives, it just is not what `pdUMany` computes; §5.1 checks
  the list an unfused (`Antimirov`) `pdU` would really produce;
* even distributing the concatenation, `(ε · r⋆) + (ε · a · r⋆)`, does not
  create the duplicate: its two summands are `≈₀`-different.  Only the sum of
  *all three* alternatives makes `Idemp` fire (`canonic` of
  `ε · r⋆ + ε · a · r⋆ + ε · r⋆` reports the flag `true` and drops the last
  alternative).  The paper's `deriv` is exactly that distributed form
  (`deriv (r₁ · r₂) x = deriv r₁ x · r₂ + deriv r₂ x` when `r₁` is nullable),
  and its similarity rules are only `Idemp`/`Comm`/`Assoc` — no distributivity
  — so whether A3 fires for this `r` depends on the *position/AST marking* of
  its `deriv`.  In the marking computed here `A1` is what fires at this depth
  (the duplicate alternative is precisely what makes `mkAllEmptyU ε∈sd-s2` have
  length 2); §6 shows the depth at which the `Idemp` test really does fire.

```agda
aa : List Char
aa = 'a' ∷ 'a' ∷ []

-- the state list has exactly one element (this is `sd-Desc₂` read as a
-- computation: one fused instance, not three Antimirov ones)
sd-s2-state : pd*-Desc sd aa ≡ ( sd-s2 ∷ [] )
sd-s2-state = refl

-- the two alternatives of the state after `a a`
sd-s2-alts : sum-spine sd-s2 ≡ ( sd-x ∷ sd-s1 ∷ [] )
sd-s2-alts = refl

-- and they are not congruent
sd-x≉sd-s1 : ¬ ( sd-x ≈₀ sd-s1 )
sd-x≉sd-s1 (≈₀-● () _)

sd-x≉sd-s1-bool : ¬ ( ⌊ sd-x ≟₀ sd-s1 ⌋ ≡ true )
sd-x≉sd-s1-bool ()

-- A2 and Idemp/Ctx-dup stay false at sd-s2 as well
sd-s2-A2?≢true : A2? sd-s2 ≡ false
sd-s2-A2?≢true = refl

sd-s2-CtxDup?≢true : CtxDup? sd-s2 ≡ false
sd-s2-CtxDup?≢true = refl

-- list level A3 of Canonic §9 on the pd state: no duplicate
no-pd-dup : dups-≈₀ ( pd*-Desc sd aa ) ≡ false
no-pd-dup = refl

-- canonic on the state performs no rewrite
sd-s2-canonic : ( proj₁ (canonic sd-s2) ≡ sd-s2 ) × ( proj₂ (canonic sd-s2) ≡ false )
sd-s2-canonic = ( refl , refl )
```

```agda
-- the Antimirov triple, written by hand: the duplicate is in *that* form
ant-tri : List RE
ant-tri = sd-x ∷ sd-s1 ∷ sd-x ∷ []

all-dups : dups-≈₀ ant-tri ≡ true
all-dups = refl

-- distributing the concatenation of sd-s1 instead (one copy per summand of
-- res-a, i.e. what the paper's deriv does): still no duplicate among them
distrib : RE
distrib = ( ( ε ● sd ` 7 ) + ( ( ε ● ($ 'a' ` 3) ` 4 ) ● sd ` 8 ) ` 9 )

distrib-no-dup : dups-≈₀ ( sum-spine distrib ) ≡ false
distrib-no-dup = refl

-- the sum of all three alternatives is where Idemp fires
distrib₃ : RE
distrib₃ = sum-build ( sd-x ∷ ( ( ε ● ($ 'a' ` 3) ` 4 ) ● sd ` 8 ) ∷ sd-x ∷ [] ) 9

distrib₃-dup : dups-≈₀ ( sum-spine distrib₃ ) ≡ true
distrib₃-dup = refl

distrib₃-Idemp : proj₂ (canonic distrib₃) ≡ true
distrib₃-Idemp = refl

distrib₃-removed : sum-spine (proj₁ (canonic distrib₃))
  ≡ ( sd-x ∷ ( ( ε ● ($ 'a' ` 3) ` 4 ) ● sd ` 8 ) ∷ [] )
distrib₃-removed = refl
```

### 5.1 The unfused (Antimirov) state after `a a`

With `pdinstance-oplus` replaced by plain list concatenation, one `PDInstance`
per partial derivative, the state after `a a` is the choice of three
alternatives (fresh locations stand for the AST nodes a derivative would
build):

```agda
ant-aa : List RE
ant-aa = ( ε ● sd ` 21 )
       ∷ ( ( ε ● ($ 'a' ` 3) ` 22 ) ● sd ` 23 )
       ∷ ( ε ● sd ` 24 )
       ∷ []

ant-aa-dup : dups-≈₀ ant-aa ≡ true
ant-aa-dup = refl

ant-aa-13 : ( ε ● sd ` 21 ) ≈₀ ( ε ● sd ` 24 )
ant-aa-13 = ≈₀-● ≈₀-ε (≈₀-refl sd)
```

So *that* form does contain the 1st/3rd duplicate, and `canonic` of the
expression oplus'ing it applies `Idemp` (`proj₂ ≡ true`) and drops the third
alternative.  It is however not a *canonical* state: the rules the derivative
itself performs eliminate a nullable prefix (`deriv (ε · t) x = t` for the
paper, `concatmap-pdinstance-snd`/`pdinstance-snd` here), so the third
alternative is `ε · a · r⋆`, which is the second one,

```agda
ant-aa-23 : ( ( ε ● ($ 'a' ` 3) ` 22 ) ● sd ` 23 ) ≈₀ ( ( ε ● ($ 'a' ` 3) ` 4 ) ● sd ` 6 )
ant-aa-23 = ≈₀-● p q
  where
    p : ( ε ● ($ 'a' ` 3) ` 22 ) ≈₀ ( ε ● ($ 'a' ` 3) ` 4 )
    p = ≈₀-● ≈₀-ε (≈₀-$ 'a' 3 3)

    q : sd ≈₀ sd
    q = ≈₀-refl sd

ant-aa-dedup : proj₁ ( dedup ant-aa )
  ≡ ( ε ● sd ` 21 ) ∷ ( ( ε ● ($ 'a' ` 3) ` 22 ) ● sd ` 23 ) ∷ []
ant-aa-dedup = refl
```

and the Antimirov state of `sd` after `a a` is `{ r⋆ , a · r⋆ }` — two
alternatives, no duplicate.  (This is the paper's own pattern: in
`deriv (deriv (x+y)* x) y = (φ + φ) · (x+y)* + (φ + ε) · (x+y)*` the residual
`y` of the `x · y` branch survives in the second term.)  A3 at the state after
`a a`, in the pd-native form of `Canonic` §9, is therefore `false`, and so is
it at the initial expression and at the state after `a`:

```agda
A3-sd-none : ( A3-list? sd [] 'a' ) ∷ ( A3-list? sd ( 'a' ∷ [] ) 'a' ) ∷ ( A3-list? sd aa 'a' ) ∷ []
  ≡ false ∷ false ∷ true ∷ []
A3-sd-none = refl
```

## 6. Where `Idemp` does fire: one level deeper

Continuing one letter further: `A3-list? sd aa 'a' ≡ true` (third component of
`A3-sd-none` above).  What happens is that the continuation of the *outer* star
is glued onto the first summand `(ε · r⋆)`, whose own continuation is `r⋆`;
extending that inner star gives the same continuation, so `deriv`-ing the state
after `a a` yields `ε · r⋆ · r⋆` twice.  In this project the two copies are
merged by `fuse` into a literal `+` node with `≈₀`-equal branches — which is
exactly what `dups-≈₀` of `Canonic` §9 detects.  Written out, the derivative of
`sd-s1 = (ε + ε · a) · r⋆` is

    d_a( (ε + ε·a)·r⋆ ) = ε·r⋆ + (ε·a)·r⋆ + r·(ε·r⋆ + (ε·a)·r⋆)

whose first alternative, extended once more, is `ε · r⋆ · r⋆` — the same term
the star extension of `ε · r⋆` produces.

Whether the *same* depth already shows it in the paper's form depends on the
normal form its FST state is kept in: for the canonical pair of §5.1 the
star extension is `d_a(r) · r⋆ = (a + a · a)·r⋆`, i.e. `a · r⋆ + r · r⋆` with
`a ≢₀ r`, so no `+` with congruent branches appears there.  Both derivations
describe the same ambiguity (two ways of gluing the outer star onto a
continuation that is itself a star); this is a difference of bookkeeping, and
pinning it down would need the `pdUMany`/`deriv` correspondence listed in §7.

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
  injectivity proofs are in `cgp.ambig.Complete` §3 (`injId`, `mkinjList`, the
  pair and sum extensions); `PosixPD.mkfuseInj` is injective only relative to a
  disjointness of its two branch ranges, which is the Antimirov-disjointness
  half missing above.  A state reached through a fused instance cannot be
  lifted without recovering the multiplicity.  §5 shows the fusion is exactly
  where an alternative-level duplicate disappears; for this `r` at that depth
  the multiplicity survives only as the second empty parse tree of the state,
  i.e. as A1 (§4), while the `Idemp` situation only shows up one level deeper
  (§6).
