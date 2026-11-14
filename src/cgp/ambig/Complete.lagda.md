# Completeness of the criteria: the injectivity half

`cgp.ambig.Canonic` §7 proves for each criterion of section 6 of

> Martin Sulzmann, Kenny Zhuo Ming Lu. *Derivative-Based Diagnosis of Regular
> Expression Ambiguity.* CIAA 2016.

that a witness *at a pd-state* lifts to an ambiguity of the original expression
(`pd*-A1→Ambig`, `pd*-A2→Ambig`, `pd*-Ctx-dup→Ambig`; all three are instances
of the master lift `lift-Ambig`).  The top-level reading of the converse —
"criterion fires at `r` itself" — fails: for `r = ( a + a · a ) ⋆` the word
`a a` has two parse trees (`ListU [ a , a ]` and `ListU [ a · a ]`), yet no
criterion fires at `r` itself — a star has exactly one empty parse tree
(¬ A1), and the hole contexts of the paper have no hole under a star, so
neither the concatenation `a · a` nor the sum `a + a · a` is reachable
(¬ A2, ¬ Ctx-dup).  The paper's proposition escapes this: computed along the
pd-states, A1 holds at the state reached after `a a` —
`( ( ε · r⋆ ) + ( ( ε + ε · a ) · r⋆ ) )`, nullable through both branches —
and the A3 test fires for that state on the letter `a`.  What is left is the direction the paper obtains from
its `AllParseFST` construction:

> if `u ≢ v` are parse trees of `r` for the same word, then for the pd-state
> reached by that word the transition tree map identifies two distinct trees —
> that state is ambiguous — and hence (by the soundness proofs in
> `cgp.ambig.AmbigCheck`/`cgp.ambig.Canonic`) one of the criteria fires there.

This module proves that direction.  Its arc: state the goal (§8), close its
base case (§9), build the descent's two machineries — the pd-side plumbing
(§10) and path structures (§12) — name the one-step facts (§13), reduce the
goal to a single recursion (§16), make the recursion's stop test computable
(§20), prove the structural fact that collapses the paper's enumeration
(§23), and run the recursion with a decidable test (§24).

* §8 states the goal of the whole arc — the *completeness* direction proper:
  given distinct parse trees `u ≢ v` of `r` for one word, some pd-descendant
  state reached by a prefix of that word carries a criterion (`crit`, the
  four-branch diagnosis disjunction: A1, A2, the duplicate pattern, the
  transition `Idemp` test).  The goal is stated here and its signature and
  body are §24's, assembled through §16's `completeness-from-desc`.
* §9 is the base case of the descent: two distinct parse trees with empty
  word force `AmbigA1` at the state (`base-A1-at-root`), for any
  expression — via `flat`'s language component, `Word.[]∈⟦r⟧→ε∈r` and
  `mkAllEmptyU-complete`.
* §10 is the descent's pd-side plumbing: `chain*` (advances of a single
  instance) is `pdUMany-aux` on the singleton list (`chain-aux`); the
  equations the letter step uses (`aux-concatMap`, `concatMap-compose`,
  `concatMap-∷[]-id`, `map-Any`) hold by induction on the run, every
  `pdUMany-aux` case going through `rewrite (++-identityʳ …)`.
* §12 is the descent's path structure: a `Path` is a chain of letter
  instances carrying their `pdU` memberships as fields — never case-split,
  which is what sidesteps the stuck-computed-list obstacle of §10 — and its
  run-lift is proved (`path-chain` composes the steps with
  `compose-pdi-with`, exactly as `advance-pdi*-with-c` does; `path-chain∈`
  puts the composed instance in the `chain*` list that contains it;
  `path-chain-pd` tracks the end state; `pdesc` turns a path into a
  `pd*-Desc` membership through `chain-aux`).  One structural fact shapes
  paths: `pdU[ l + s \` loc , c ]` is `pdinstance-oplus` of the branch
  lists, which *fuses* when both sides derive, so a path below one branch
  does not extend through the sum head — paths are anchored at the state the
  descent stands in.
* §13 is the one letter step's facts: a member of an instance list with its
  witness (`pick-Any` — the list must be a parameter, since at the call
  sites it is the stuck `pdU[ r , c ]`), and the residual tree of a
  reconstruction with its forced word (`Recons-residual`, read off the
  instance's own soundness evidence, no `flat∘unflat`).
* §16 states what is left as one named hypothesis.  `Desc-complete` is the
  single-expression form of the descent (two trees of one `r`, pick-only,
  never asking whether a list is empty), `desc-concl` its conclusion; its
  base is §9's `base-A1-at-root` (`desc-base`), its one-instance step is
  proved (`desc-step`, extending the path by `pcons`).  §8's statement then
  follows from `Desc-complete` through `pdesc` (`completeness-from-desc`):
  the whole completeness direction is reduced to running the recursion.
* §20 names the recursion's two stop facts: the residual of a
  reconstruction as a term (`residual`, `residual-word`), and the A3 rule —
  two *distinct* members of one `pdU[ r , c ]` continuing at one expression
  make the criterion fire at `r` (`pick-diff-record-prf`, via
  `Canonic.pd-Idemp?-members`: the member list then holds two entries with
  one continuation, exactly what `Canonic`'s `Idemp` test reads).
* §23 proves the structural fact that collapses the paper's enumeration: in
  this formalization *all members of `pdU[ r , c ]` continue at one
  expression* (`pdU-const`, by induction over the `pdU` clauses — each maps
  its sublists through constructor maps that respect continuations
  (`pd-expr-resp∘*`) or fuses them pairwise (`fuse-pair-const`), and the
  POSIX `pdinstance-oplus` only ever joins constant lists (`oplus-const`)).
  Two picks therefore never continue at *different* expressions, and the
  descent is left with one question only: are the two picks *one record*?
* §24 closes the goal with no postulate: the descent never needs record
  identity — what its two branches use it for is choosing between continuing
  through one shared transition and firing the criterion, and that choice is
  decidable on the *residual trees*: both residuals sit at one expression
  (`pdU-const`'s equation, `flat-resp` moves words with the transport), and
  tree identity there is `ParseTree._⊢_≟_`.  Different residuals: continue
  through one member; equal residuals: the records cannot have been equal
  (one record maps distinct trees to distinct residuals — `diff-records-≟`),
  which is the A3 configuration closed by §20's `pick-diff-record-prf`.
  `desc-picks-≟` instantiates §16's `Desc-complete` (`Desc-complete-≟`), and
  `completeness-from-desc` proves §8's `completeness`.
```agda
-- `data Path` is strictly positive by inspection (`pcons` carries it only in
-- argument position), but Agda 2.7.0.1's positivity checker false-positives on
-- it through the `subst` motive in `path-chain∈`'s type (and the descent's
-- transports in §24) once the module is instantiated (agda/agda#7669, fixed
-- in 2.8.0), so the check is off here
{-# OPTIONS --rewriting --no-positivity-check #-}
module cgp.ambig.Complete where

import cgp.RE as RE
open RE using (RE; ε; $_`_; _●_`_; _+_`_; _*_`_; ε∉ ; ε∈ ; ε∉$ ; ε∉fst ; ε∉snd ; ε∉_+_)

import cgp.ParseTree as ParseTree
open ParseTree using ( U ; EmptyU ; LetterU ; LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unListU
                     ; flat-Uε≡[] ; inv-leftU ; inv-rightU ; inv-pairU
                     ; LeftU≢RightU ; RightU≢LeftU )

import cgp.Word as Word
open Word using (_∈⟦_⟧ ; _+L_ ; $_)

import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance*
               ; mkinjList ; mkinjFst ; mkinjSnd ; compose-pdi-with
               ; pdinstance-left ; pdinstance-right ; pdinstance-fst ; pdinstance-star ; mk-snd-pdi )

import cgp.empty.AllEmptyParseTree as AllEmpty
open AllEmpty using ( flat-[] ; mkAllEmptyU ; mkAllEmptyU-complete )

import cgp.posix.PartialDerivative as PosixPD
open PosixPD using ( mkfuseInj ; fuse ; pdinstance-oplus ; injId ; injId-sound ; pdU-complete ; pdUMany-complete )

import cgp.Utils as Utils
open Utils using ( ∷-inj )

import cgp.ambig.AmbigCheck as AmbigCheck
open AmbigCheck using ( Ambig )

import cgp.ambig.Canonic as Canonic

import cgp.Recons as Recons
open Recons using ( Recons ; recons )

open import Data.Char using (Char)
import Data.Char as Char
open import Data.Nat using (ℕ; _≟_ ; suc ; zero ; _≤_ ; _+_ ; s≤s ; z≤n)
import Data.Nat.Properties as NatProperties
open NatProperties using ( ≤-refl ; ≤-reflexive ; ≤-trans ; m≤m+n ; m≤n+m ; n≤1+n )
open import Data.List using (List; _∷_; _∷ʳ_; []; _++_; map; concat; concatMap; [_]; length)
open import Data.List.Properties using (++-cancelˡ ; ++-identityʳ ; ++-assoc ; length-map ; length-++ )
{-# REWRITE ++-identityʳ #-}
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Empty using (⊥ ; ⊥-elim)
open import Data.Sum using (_⊎_ ; inj₁ ; inj₂)
open import Data.Product using (_×_; _,_; Σ ; proj₁ ; proj₂; Σ-syntax; ∃-syntax)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym; trans; cong; cong₂ ; subst)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)
open import Function using (_∘_)
open import Relation.Nullary using (¬_; Dec ; yes ; no)
open import Data.Bool using (true)
```

## 8. The goal: the completeness direction, stated

The reading the earlier modules give is the easy direction (`Canonic.lift-Ambig`:
a criterion at a pd-state lifts to an ambiguity of the original expression).
What is stated here is the other one — the paper's proposition, section 6:

> given an ambiguity of `r` — two distinct parse trees for one word — the word
> has a prefix whose pd-states include one at which a criterion fires.

The diagnosis disjunction is named once, here, since every later section states
its result in terms of it: the first two disjuncts are the paper's A1 and A2
(`cgp.ambig.AmbigCheck` §3, §4), the third is the `Idemp` *pattern* (a sum with
`≈₀`-equal members under a hole context — the shape `Canonic.Ctx-dup→Ambig`
consumes), the fourth is A3 proper: the `Idemp` *test* firing on a transition out
of a state, again read under a hole context, since the paper's criteria range
over descendants `s ∈ Desc(r)` and a hole context is what this project has of
that (`cgp.ambig.Canonic`'s `pd-Idemp?`; `cgp.ambig.Canonic` §8 shows that is
the right shape and what it fires on).  The stability of the disjuncts under
plugging a hole context (`A2-Ctx`, `dup-Ctx`, `A3-Ctx`) was developed with the
split case in the version of this module that included it; nothing below needs
that transport — the descent always fires the criterion *at the state it stands
in*.

```agda
-- the diagnosis disjunction: one of the paper's criteria fires at `p`
-- (purpose): the single codomain every diagnosing lemma in this module targets
-- (used in): `desc-concl`/`Desc-complete` (§16), `pick-diff-record-prf` (§20),
--   the `completeness` statement (§24)
-- (proof idea): definition — A1/A2 from `AmbigCheck`, the duplicate pattern and
-- the transition `Idemp` test from `Canonic`, the last two read under a hole
-- context
crit : RE → Set
crit p = AmbigCheck.AmbigA1 p
       ⊎ AmbigCheck.AmbigA2 p
       ⊎ Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ l ∈ RE ] Σ[ s ∈ RE ] Σ[ loc ∈ ℕ ]
             ( ( AmbigCheck.plug ctx ( l + s ` loc ) ≡ p )
             × ( Canonic._≈₀_ l s ) )
       ⊎ Σ[ ctx ∈ AmbigCheck.Ctx ] Σ[ q ∈ RE ] Σ[ c ∈ Char ]
             ( ( AmbigCheck.plug ctx q ≡ p )
             × ( Canonic.pd-Idemp? (PosixPD.pdU[ q , c ]) ≡ true ) )

-- (the signature of `completeness` is stated at the head of §24, next to its
-- body: the proof needs `Desc-complete` (§16) and the descent `desc-picks-≟`,
-- both defined below)
```

The fourth disjunct is worth naming outright at the empty context, since it is a
decidable test on the transition out of the state and needs no descent to be
applied at the state itself:

```agda
-- (purpose): a positive `Idemp` test on the transition out of `r` is a
--   criterion at `r` itself — the fourth disjunct at the empty context
-- (used in): `pick-diff-record-prf` (§20), which is §24's A3 stop
-- (proof idea): by inspection: `𝟘 , r , c` plugs to `r` at `refl`, and the
--   hypothesis is exactly the fourth component
crit-A3-test : ∀ ( r : RE ) ( c : Char )
  → Canonic.pd-Idemp? (PosixPD.pdU[ r , c ]) ≡ true
  → crit r
crit-A3-test r c p≡true = inj₂ (inj₂ (inj₂ ( AmbigCheck.𝟘 , r , c , ( refl , p≡true ) )))
```

To fill this for an *arbitrary* pair `( u , v )` one has to *find* the
prefix `w′` — the paper's `AllParseFST` argument over parse trees of the
word.  It is not formalized here (like the realizable-states / FST side of
the paper), and this is the actual research gap of the program.  §16 reduces
this statement to one named hypothesis, `Desc-complete`: its two cases are
`pdesc pnil` at the state itself and `pdesc` of the path the descent returns,
so nothing else stands between that hypothesis and this statement.  §20 names
the two facts a run of the descent needs to stop on, §23 shows one of the
two configurations the earlier versions branched on cannot occur at all, and
§24 supplies the remaining decision as a computation on residuals — the
signature and the assembled body of `completeness` are at the end of §24.

## 9. Toward the general proof: the base case of the descent

The general `completeness` above is proved by following the two trees through
their common word letter by letter (the paper's `AllParseFST` argument).  Its
base case — the word is consumed, what remains are two distinct *empty* parse
trees of the state reached — forces A1 *at that state*, for every expression.
Formalized here, for arbitrary `r`:

```agda
-- (purpose): a list carrying two distinct members has length ≥ 2 — the
--   counting half of an A1 witness
-- (used in): `base-A1-at-root` below
-- (proof idea): by pattern match on the list: two `here` witnesses at one
--   singleton contradict `x ≢ y`, and any two members of a 2-long list fit
--   `s≤s (s≤s z≤n)`; no induction needed since `Any` pins the positions
two-distinct-members→len≥2 : ∀ {A : Set} {x y : A} ( xs : List A )
  → Any ( λ z → x ≡ z ) xs → Any ( λ z → y ≡ z ) xs → ¬ ( x ≡ y )
  → suc (suc zero) ≤ length xs
two-distinct-members→len≥2 (x ∷ x₁ ∷ xs) _ _ _ = s≤s (s≤s z≤n)
two-distinct-members→len≥2 (x ∷ []) (here refl) (here refl) x≢y = ⊥-elim (x≢y refl)
two-distinct-members→len≥2 (x ∷ []) (here p) (there ()) _
two-distinct-members→len≥2 (x ∷ []) (there ()) _ _
two-distinct-members→len≥2 [] () _ _

-- two distinct parse trees of r for the empty word ⇒ A1 fires at r
-- (purpose): the descent's base case — at a final state, distinct empty trees
--   *are* an A1 witness, for any expression
-- (used in): `desc-base` (§16), the empty-word clause of the descent
-- (proof idea): the empty word of `r` makes `r` nullable (`Word.[]∈⟦r⟧→ε∈r`);
--   `mkAllEmptyU` then enumerates *all* empty trees of `r`
--   (`mkAllEmptyU-complete`), so `u` and `v` are two distinct members of that
--   list and the length bound above closes the A1 pair
base-A1-at-root : ( r : RE ) ( u v : U r )
  → proj₁ (flat {r} u) ≡ [] → proj₁ (flat {r} v) ≡ [] → ¬ ( u ≡ v )
  → AmbigCheck.AmbigA1 r
base-A1-at-root r u v u≡[] v≡[] u≢v = ( ε∈r , two-distinct-members→len≥2 list u∈ v∈ u≢v )
  where
    ε∈r : ε∈ r
    ε∈r = Word.[]∈⟦r⟧→ε∈r (subst ( λ w → w ∈⟦ r ⟧) u≡[] (proj₂ (flat {r} u)))
    list = mkAllEmptyU {r} ε∈r
    u∈ : Any ( λ z → u ≡ z ) list
    u∈ = mkAllEmptyU-complete ε∈r u (flat-[] u u≡[])
    v∈ : Any ( λ z → v ≡ z ) list
    v∈ = mkAllEmptyU-complete ε∈r v (flat-[] v v≡[])
```

(`u ∈ mkAllEmptyU` is `Any (u ≡_)` by definition of `List._∈_` — the
membership `mkAllEmptyU-complete` produces is used directly.)

The step case of the descent — given a pair at word `c ++ cs`, move both
trees across the letter `c` and recurse on `cs` — is where the Antimirov
nondeterminism bites: the two trees may cross `c` through *different*
instances of `pdU[ r , c ]`, into *different* continuation states, so a
priori the recursion has to run on a pair of states as in the paper's
`AllParseFST`, and the criteria would have to be found from a pair-derivation
whose two sides eventually merge or split (the merge = A1 by the base case
just proved; a split at a sum or a duplicated subterm = A2 / the `Idemp`
pattern).  That pair machinery was indeed built once, in the version of this
module that developed the split case; what §23 shows is that it is *not
needed* here: in this formalization every instance of `pdU[ r , c ]`
continues at one and the same expression, so the two picks never part into
two states — the descent stays single-state, and only the merge half of the
pair argument, the base case proved above, is ever reached.

## 10. Walking pd paths (the descent's plumbing)

The letter step of the descent reads an IH that lives at a *continuation
state* and must be heard from the *whole expression*: if the word `pref`
reaches the instance `pdi` of `r` (`pdi ∈ pdUMany[ r , pref ]`) and from
`pdi` the suffix `suff` reaches the state `p`, then `p` is a pd-descendant of
`r` for the concatenated word —

> `pdi ∈ pdUMany[ r , pref ]` and `p ∈ Canonic.pd*-Desc (pd r pref) suff`
> together imply `p ∈ Canonic.pd*-Desc r (pref ++ suff)` .

Formally: a chain of advances `chain*` from a single instance — the same
recursion as `pdUMany-aux` but started from one instance — *is* `pdUMany-aux`
on the singleton list (`chain-aux`, induction on `pref`).  The equations its
letter step uses — running a suffix through a `concatMap` of instance lists
(`aux-concatMap`), the `concatMap` laws it runs on (`concatMap-++`,
`concatMap-compose`, `concatMap-cong-λ`, `concatMap-∷[]-id`), and membership
transport through `map` (`map-Any`) — hold by induction on the suffix.  The
index plumbing needs the `++-identityʳ` equation
added as a rewrite rule next to the project-wide `∷ʳ-++`; both are used
exactly as `pdUMany-aux` itself uses them.  (The transfer from a reachable
instance to a `pd*-Desc` membership of the concatenation — the lemma this
section used to state as `chain-in-aux` / `chain-in-pd*-Desc` — survives in
path form as §12's `pdesc`, which is what the descent actually calls.)

```agda
-- concatMap f distributes over ++
-- (purpose): the basic list law the descent's run equations rewrite with
-- (used in): `concatMap-compose` here, `aux-concatMap` below
-- (proof idea): induction on the first list; the step is `cong` of the
--   recursive equation plus symmetry of `++`-assoc
concatMap-++ : ∀ {A B : Set} (f : A → List B) (xs ys : List A)
  → concatMap f (xs ++ ys) ≡ concatMap f xs ++ concatMap f ys
concatMap-++ f [] ys = refl
concatMap-++ f (x ∷ xs) ys = trans
  ( cong (f x ++_) (concatMap-++ f xs ys) )
  ( sym (++-assoc (f x) (concatMap f xs) (concatMap f ys)) )

-- pointwise equal maps, under one concatMap
-- (purpose): concatMap respects pointwise equality of its function
-- (used in): `chain-aux` and `aux-concatMap` below (swapping one lambda for
--   another under a run)
-- (proof idea): induction on the list, `cong₂ _++_` at each block
concatMap-cong-λ : ∀ {A B : Set} (zs : List A) (f g : A → List B)
  → ( ∀ x → f x ≡ g x ) → concatMap f zs ≡ concatMap g zs
concatMap-cong-λ [] f g f≡g = refl
concatMap-cong-λ (z ∷ zs) f g f≡g = cong₂ _++_ (f≡g z) (concatMap-cong-λ zs f g f≡g)

-- (purpose): nested `concatMap`s collapse into one
-- (used in): `aux-concatMap` below (the letter step of a run through a
--   `concatMap` of instance lists)
-- (proof idea): induction on the outer list, rewriting each block with
--   `concatMap-++`
concatMap-compose : ∀ {A B C : Set} (f : B → List C) (g : A → List B) (zs : List A)
  → concatMap f (concatMap g zs) ≡ concatMap (λ z → concatMap f (g z)) zs
concatMap-compose f g [] = refl
concatMap-compose f g (z ∷ zs) = trans
  ( concatMap-++ f (g z) (concatMap g zs) )
  ( cong (concatMap f (g z) ++_) (concatMap-compose f g zs) )

-- concatMap of singletons is the identity
-- (purpose): `concatMap (λ x → x ∷ [])` is the identity on instance lists —
--   the shape `pdUMany-aux` uses to cons a head instance onto a run
-- (used in): `chain-aux` below (last step)
-- (proof idea): induction, `cong (y ∷_)` per element
concatMap-∷[]-id : ∀ {A : Set} (ys : List A)
  → concatMap (λ x → x ∷ []) ys ≡ ys
concatMap-∷[]-id [] = refl
concatMap-∷[]-id (y ∷ ys) = cong (y ∷_) (concatMap-∷[]-id ys)
-- (purpose): transport a membership witness through `map`
-- (used in): `path-chain∈` and `pdesc` (§12) — membership of the composed
--   path instance in the run list
-- (proof idea): map the `Any` proof pointwise: `here`/`there` both preserve
--   position
map-Any : ∀ {A B : Set} (f : A → B) {P : A → Set} {Q : B → Set}
  → (∀ x → P x → Q (f x)) → {xs : List A} → Any P xs → Any Q (map f xs)
map-Any f P→Q (here p) = here (P→Q _ p)
map-Any f P→Q (there p) = there (map-Any f P→Q p)


-- running a suffix through a concatMap of instance lists
-- (purpose): a suffix run distributes through `concatMap`: running `suff` on
--   all blocks equals concatenating the per-block runs
-- (used in): `chain-aux` below (the letter step)
-- (proof idea): induction on the suffix; the step rewrites the nested advance
--   with `concatMap-compose`, then reassociates with the recursive equation
--   and `concatMap-cong-λ`
aux-concatMap : ∀ {r : RE} {pref : List Char} (suff : List Char)
  → {A : Set} (g : A → List (PDI.PDInstance* r pref)) (zs : List A)
  → PosixPD.pdUMany-aux {r} {pref} suff (concatMap g zs)
    ≡ concatMap (λ z → PosixPD.pdUMany-aux {r} {pref} suff (g z)) zs
aux-concatMap {r} {pref} [] g zs rewrite ++-identityʳ pref = refl
aux-concatMap {r} {pref} (c ∷ cs) g zs = trans
  ( cong (λ l → PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs l)
         (concatMap-compose (PosixPD.advance-pdi*-with-c {r} {pref} {c}) g zs) )
  ( trans ( aux-concatMap {r} {pref ∷ʳ c} cs
              (λ z → concatMap (PosixPD.advance-pdi*-with-c {r} {pref} {c}) (g z)) zs )
          ( concatMap-cong-λ zs
              (λ z → PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs
                       (concatMap (PosixPD.advance-pdi*-with-c {r} {pref} {c}) (g z)))
              (λ z → PosixPD.pdUMany-aux {r} {pref} (c ∷ cs) (g z))
              (λ z → refl) ) )
-- (purpose): advances of a *single* instance over a suffix — the descent's
--   walk in list form, mirroring `pdUMany-aux`'s recursion
-- (used in): `chain-aux` below, `path-chain∈` and `pdesc` (§12)
-- (proof idea): definition — unfold `pdUMany-aux`'s clause for one instance
chain* : ∀ {r : RE} {pref : List Char}
  → ( pdi : PDI.PDInstance* r pref ) → ( suff : List Char )
  → List (PDI.PDInstance* r (pref ++ suff))
chain* {r} {pref} pdi [] = pdi ∷ []
chain* {r} {pref} pdi (c ∷ cs)
  = concatMap (λ x → chain* {r} {pref ∷ʳ c} x cs)
              (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi)

-- (purpose): the single-instance chain *is* the multi-instance run on the
--   singleton list — the equation that turns a path's chain into membership of
--   the real computed list `pdUMany[ r , w ]`
-- (used in): `pdesc` (§12), via the `subst` over this equation
-- (proof idea): induction on the suffix; the empty-suffix case needs
--   `rewrite (++-identityʳ pref)` because `pdUMany-aux` at `[]` is defined on
--   the reduct of `pref ++ []`, and the step rewrites the advance list with
--   `aux-concatMap` and the singleton map with `concatMap-∷[]-id`
chain-aux : ∀ {r : RE} {pref : List Char} ( pdi : PDI.PDInstance* r pref ) ( suff : List Char )
  → chain* {r} {pref} pdi suff
    ≡ PosixPD.pdUMany-aux {r} {pref} suff (pdi ∷ [])
chain-aux {r} {pref} pdi [] rewrite ++-identityʳ pref = refl
chain-aux {r} {pref} pdi (c ∷ cs) = trans
  ( concatMap-cong-λ (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi)
      (λ x → chain* {r} {pref ∷ʳ c} x cs)
      (λ x → PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs (x ∷ []))
      (λ x → chain-aux {r} {pref ∷ʳ c} x cs) )
  ( trans
      ( sym ( aux-concatMap {r} {pref ∷ʳ c} cs (λ x → x ∷ [])
                       (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi) ) )
      ( cong (λ l → PosixPD.pdUMany-aux {r} {pref ∷ʳ c} cs l)
             (concatMap-∷[]-id (PosixPD.advance-pdi*-with-c {r} {pref} {c} pdi)) ) )
```

## 12. Descent paths and their run-lift

The conclusion the descent's induction hypothesis hands back is not a bare
`pd*-Desc` membership but a witness of *how the state was reached*: a
chain of letter instances carrying their `pdU` memberships as fields.
That is the `Path` structure below — it sidesteps the §10 stuck-list
obstacle entirely, since every transfer along a path is by construction
and no membership is ever case-split.  The run-lift is proved here:
`path-chain` composes a path's steps into one `PDInstance*`, `path-chain∈`
shows the composition is a member of the `chain*` list §10 defined,
`path-chain-pd` tracks the end state (`pdend`), and `pdesc` turns all of
it into the `pd*-Desc` membership §16's reduction consumes.  (The `Any`
combinator lemmas the membership proof runs on — `any-++₂`, `any++₁`,
`any-concatMap` — are here too.)
One structural fact shapes how
paths may enter a sum: `pdU[ l + s \` loc , c ]` is *not*
`map pdinstance-left … ++ map pdinstance-right …` but
`pdinstance-oplus` of the two lists, and when both sides derive by `c`
the lists **fuse** — every member pairs a left and a right instance
(PartialDerivative 362–368) — so a path below one branch does *not*
extend through the sum head in general; the singleton equations of
`pdinstance-oplus` (one side deriving nowhere) are the only clean
embeddings.  A path is therefore never threaded *through* a sum head: it
is anchored at the state the descent stands in.  (The pair arc that used
this fact — a witness below one branch of a sum, with the `($a`1 + ε) +
$a`2` counterexample showing why path anchors must not move below branches —
was developed in the split-case half of this module; the general descent
below never leaves the single anchor it starts at, so nothing here needs
that machinery.)

```agda
-- a descent path: each step names its letter instance and carries its
-- pdU membership as a field (never to be case-split)
-- (purpose): a *witness of how a state was reached*: a chain of letter
--   instances, so the descent can transfer conclusions along it without ever
--   splitting a computed `pdU`/`pdUMany` list (the §10 stuck-term obstacle)
-- (used in): `desc-concl`/`desc-step` (§16) carry it; `pdesc` below converts
--   it to a `pd*-Desc` membership
-- (proof idea): data — membership is stored at construction, so no lemma ever
--   has to ask whether a list is empty
data Path : ( r : RE ) → ( w : List Char ) → Set where
  pnil  : ∀ { r } → Path r []
  pcons : ∀ { r c ws } ( z : PDInstance r c )
    → z ∈ PosixPD.pdU[ r , c ]
    → Path (Canonic.pd-expr z) ws
    → Path r (c ∷ ws)

-- the state a path ends in
-- (purpose): read the end state off a path
-- (used in): `pdesc` below (the member it names), `completeness-from-desc`
--   (§16) (the state claimed in the conclusion)
-- (proof idea): recursion on the path; the equations compose with
--   `path-chain-pd` below
pdend : ∀ { r w } → Path r w → RE
pdend {r} pnil          = r
pdend (pcons z m q) = pdend q

-- membership injection into a concatenation, from the right part
-- (purpose): membership in the right half of an append
-- (used in): `any-concatMap` below
-- (proof idea): induction, adding `there` per skipped element
any-++₂ : ∀ { A : Set } { P : A → Set } ( xs : List A ) { ys : List A }
  → Any P ys → Any P (xs ++ ys)
any-++₂ [] p = p
any-++₂ (x ∷ xs) p = there (any-++₂ xs p)

-- membership injection into a concatenation, from the left part
-- (purpose): membership in the left half of an append
-- (used in): `any-concatMap` below (its first clause)
-- (proof idea): `here`/`there` preserve position because the left half is a
--   non-`[]` pattern
any++₁ : ∀ {A : Set} {P : A → Set} {xs ys : List A}
  → Any P xs → Any P (xs ++ ys)
any++₁ {xs = x ∷ xs} {ys = ys} (here p) = here p
any++₁ {xs = x ∷ xs} {ys = ys} (there p) = there (any++₁ {xs = xs} {ys = ys} p)

-- membership in a concatenated list, from membership in the parts
-- (purpose): lift a nested membership witness into a `concatMap` list — the
--   shape `chain*` unfolds to
-- (used in): `path-chain∈` below
-- (proof idea): induction over the outer `Any`, assembling with `any++₁`/
--   `any-++₂`
any-concatMap : ∀ { A B : Set } ( g : A → List B ) { xs : List A } { P : B → Set }
  → Any ( λ x → Any P (g x) ) xs → Any P (concatMap g xs)
any-concatMap g {xs = x ∷ xs} (here p) = any++₁ {ys = concatMap g xs} p
any-concatMap g {xs = x ∷ xs} (there m) =
  any-++₂ (g x) {ys = concatMap g xs} (any-concatMap g m)

-- the run instance of a path: steps are composed with `compose-pdi-with`,
-- exactly as `advance-pdi*-with-c` composes a head instance with a `pdU`
-- step, so each constructed step *heads* the concatMap that `chain*`
-- unfolds to, and membership follows by construction.
-- (purpose): fold a path into the single advanced instance it describes
-- (used in): `path-chain∈`/`path-chain-pd` below, `pdesc`
-- (proof idea): recursion on the path, composing at each step.  (The
-- constructors are matched directly in the left-hand sides, not through
-- `with`: the Path field's type mentions `pd*-expr hd` and must reduce
-- through the matched constructor — a `with`-abstraction leaves `z :
-- PDInstance (pd*-expr hd) c` stuck on the un-reduced projection.)
path-chain : ∀ { r pref ws } ( hd : PDInstance* r pref )
  → Path (Canonic.pd*-expr hd) ws
  → PDInstance* r (pref ++ ws)
path-chain {r} {pref} hd pnil = hd
path-chain {r} {pref} (pdinstance* {d} d→r ev)
               (pcons {c = c} {ws = ws} z@(pdinstance {p} p→d evz) m q) =
  path-chain {r} {pref = pref ∷ʳ c} (compose-pdi-with {r} {d} {pref} {c} d→r ev z) q

-- (purpose): the instance a path composes to is a *member* of the `chain*`
--   run list — the construction and the computation agree
-- (used in): `pdesc` below (first step of its `subst`)
-- (proof idea): induction on the path: each step's composition sits in the
--   `map` of `compose-pdi-with` over the next `pdU` list (`map-Any` of the
--   step's stored membership), which `any-concatMap` lifts into the `chain*`
--   unfold
path-chain∈ : ∀ { r pref ws } ( hd : PDInstance* r pref )
  ( π : Path (Canonic.pd*-expr hd) ws )
  → path-chain hd π ∈ chain* {r} {pref} hd ws
path-chain∈ hd pnil = here refl
path-chain∈ {r} {pref} (pdinstance* {d} d→r ev)
                     (pcons {c = c} {ws = ws} z@(pdinstance {p} p→d evz) m q) =
  any-concatMap ( λ x → chain* {r} {pref ∷ʳ c} x ws )
    ( map-Any (compose-pdi-with {r} {d} {pref} {c} d→r ev)
        ( λ a eq → subst ( λ h → path-chain (compose-pdi-with {r} {d} {pref} {c} d→r ev z) q
                              ∈ chain* {r} {pref ∷ʳ c} h ws )
                         ( cong (compose-pdi-with {r} {d} {pref} {c} d→r ev) eq )
                         ( path-chain∈ (compose-pdi-with {r} {d} {pref} {c} d→r ev z) q ) )
        m )

-- (purpose): the pattern field of that composed instance *is* the path's end
--   state `pdend`
-- (used in): `pdesc` below (identifying the member's expression)
-- (proof idea): recursion on the path, `refl` at the end — `compose-pdi-with`
--   builds the pattern field exactly as `pdend` reads it
path-chain-pd : ∀ { r pref ws } ( hd : PDInstance* r pref )
  ( π : Path (Canonic.pd*-expr hd) ws )
  → Canonic.pd*-expr (path-chain hd π) ≡ pdend π
path-chain-pd hd pnil = refl
path-chain-pd {r} {pref} (pdinstance* {d} d→r ev)
                       (pcons {c = c} {ws = ws} z@(pdinstance {p} p→d evz) m q) =
  path-chain-pd (compose-pdi-with {r} {d} {pref} {c} d→r ev z) q

-- the run-lift bridge in path form: a path from r is a run of r for its
-- word, so its end state appears in pd*-Desc r w.
-- (purpose): turn the descent's path into the `pd*-Desc` membership §8's
--   conclusion asks for
-- (used in): `completeness-from-desc` (§16) — both of its cases
-- (proof idea): the path instance is a member of `chain* hd₀ w` through
--   `path-chain∈`, and `chain-aux` (§10) identifies that singleton run
--   with `pdUMany[ r , w ]` itself; `path-chain-pd` names the member's
--   expression.  (The alternative route through a
--   generic composition-after-a-run operator would first need the syntactic
--   identity `compose id ≡ id`, which its soundness-evidence plumbing does not
--   give; `compose-pdi-with` builds the instance in the very shape of the
--   list that contains it.)
pdesc : ∀ { r w } ( π : Path r w )
  → Any ( λ x → x ≡ pdend π ) (Canonic.pd*-Desc r w)
pdesc pnil = here refl
pdesc {r} π@(pcons {c = c} {ws = ws} z m q) =
  map-Any Canonic.pd*-expr
    ( λ a eq → trans ( cong Canonic.pd*-expr ( sym eq ) ) ( path-chain-pd hd₀ π ) )
    ( subst ( λ L → path-chain hd₀ π ∈ L ) ( chain-aux hd₀ (c ∷ ws) )
        ( path-chain∈ hd₀ π ) )
  where
    hd₀ : PDInstance* r []
    hd₀ = pdinstance* {r} {r} {[]} injId injId-sound
```

## 13. The letter step's facts: picking and residuals

Both trees of the pair consume the same first letter, so `pdU-complete`
turns each of them into a member of *its own* expression's instance list
together with a reconstruction witness.  Two facts turn that pair of
witnesses into data the descent can act on: extracting a concrete member,
its witness and its list membership out of an `Any` (`pick-Any` — the list
must be a parameter, since at the call sites it is the stuck computed term
`pdU[ r , c ]`), and the residual tree a reconstruction implies, with its
word *forced* to be the tail (`Recons-residual`).

```agda
-- (purpose): extract a concrete member of an instance list with its witness
--   and its membership — the descent's pick
-- (used in): `desc-picks-≟` (§24), on both `pdU-complete` results
-- (proof idea): recursion on the `Any`, carrying the membership through
--   `there`.  The list is a
-- parameter and not the stuck term `pdU[ r , c ]` of the call sites: the
-- case-split has to happen once, here.
pick-Any : ∀ { A : Set } { P : A → Set } { xs : List A }
  → Any P xs
  → Σ[ y ∈ A ] ( P y × y ∈ xs )
pick-Any (here {x = y} {xs = xs} p) = ( y , p , here refl )
pick-Any (there {xs = xs} p) with pick-Any p
... | ( y , q , m ) = ( y , q , there m )

-- (purpose): read the *residual tree* off a reconstruction witness — its word
--   is *forced* to be the tail, because the instance's soundness evidence
--   prefixes the same letter on both sides
-- (used in): `residual`/`residual-word` (§20), which feed the whole descent
--   of §24
-- (proof idea): `unflat` the word witness from the `Recons` completeness
--   component; the word equation is `∷-inj` applied to the instance's own
--   evidence composed with the reconstruction equation.  No `flat∘unflat`
--   computation is needed — the equation is read off the instance's evidence.
Recons-residual : ∀ { r : RE } { c : Char } { pdi : PDInstance r c } { u : U r } { ws : List Char }
  → Recons {r} {c} u pdi
  → proj₁ (flat {r} u) ≡ c ∷ ws
  → Σ[ x ∈ U (Canonic.pd-expr pdi) ] ( proj₁ (flat {Canonic.pd-expr pdi} x) ≡ ws )
Recons-residual {pdi = pdinstance {p} inj ev} (recons _ ( w∈ , eq )) u≡cw =
  ( unflat w∈
  , proj₂ (∷-inj (trans (sym (ev (unflat w∈))) (trans (cong ( λ z → proj₁ (flat z) ) eq) u≡cw))) )
```

What the fusion fact means concretely — this is the counterexample the pair
arc recorded: take `u = LeftU (LetterU a) : U ( $ a \` 1 + ε )` and
`v = LetterU a : U ( $ a \` 2 )`, both with word `[ a ]`.  No criterion
holds at the sum `( $ a \` 1 + ε ) + $ a \` 2` — it has exactly one empty
tree (via the inner right branch), no concatenation subterm, and its two
branch expressions are `≈₀`-apart — and no criterion is reachable below
either branch: the only path below `l` for `[ a ]` and the only path below
`s` both end at `ε`, where no criterion ever holds.  What happens instead:
`pdU[ ( $ a \` 1 + ε ) + $ a \` 2 , a ]` has exactly *one* member — the
`fuse` pairing of the two branch instances — and that member's continuation
is `ε + ε`, the state where two distinct empty trees *do* put A1 on the
record.  The witness of a branching pair lives at the *fused derivative*,
never below either branch.

(The pair descent that used the facts in this paragraph — membership of a
branch pair in the sum's list and its continuation equation (`pdU∈-⊕`,
`pd-expr-fuse-⊕`), and the closed split forms firing A1/A3 at sums
(`split-+-A1`, `crit-ε+`, `crit-+ε`, `crit-$$`) — was developed in the
split-case half of this module and needed the path anchored at the sum
itself for exactly this reason.  The single-expression descent of §16 never
threads between two expressions, so it needs none of them: §23 proves the
strictly stronger property — *all* members of `pdU[ r , c ]`, fused or not,
continue at one expression.)

(The counting form of the same fact: `pdU[ r , c ]` has more than
one member only below a nullable concatenation, where
`concatmap-pdinstance-snd` enumerates one instance per empty tree of the
left factor — the paper's "these are the only situations" in counting
form, and the configuration the second criterion exists for.)

## 16. The remaining step, stated exactly

The general `completeness` is the case where both trees live in **one**
expression `r`, so the descent has to stay inside `r`'s own states: at each
letter it picks *one* member of `pdU[ r , c ]` per tree and recurses at that
member's continuation — never asking whether a list is empty, never switching
expressions.  Stating that single-expression recursion as one named
hypothesis (`Desc-complete`) is the reduction: §8's statement follows from it
by reading the recursion's path as a `pd*-Desc` membership (`pdesc`), and
everything after this section is about discharging the hypothesis.

```agda
-- what the descent produces at a state for a word
-- (purpose): the descent's codomain — a criterion *here*, or one at the end
--   of an explicit path, with the word split at the path's length
-- (used in): `desc-base`/`desc-step` below, `Desc-complete`, and through them
--   the whole of §24
-- (proof idea): definition — a sum with the path carried as a field, so no
--   membership of a computed list ever has to be examined
desc-concl : ( r : RE ) → ( w : List Char ) → Set
desc-concl r w = crit r
             ⊎ ( ∃[ w′ ] ∃[ w″ ] ( ( w ≡ w′ ++ w″ )
                   × ( Σ[ π ∈ Path r w′ ] crit (pdend π) ) ) )

-- the single-expression descent, as one named hypothesis: for *one* `r`,
-- two trees of one word can be walked letter by letter through `r`'s own
-- states until a criterion is found
-- (purpose): the whole completeness direction in one case — the §8 statement
--   is derived from this alone (§16's reduction)
-- (used in): `completeness-from-desc` below; instantiated by
--   `Desc-complete-≟` (§24)
-- (proof idea): a recursion on the word; its two structural halves are
--   `desc-base`/`desc-step` below, and §24 supplies the decision the step
--   needs
Desc-complete : Set
Desc-complete = ∀ ( r : RE ) ( w : List Char ) ( u v : U r )
  → proj₁ (flat {r} u) ≡ w → proj₁ (flat {r} v) ≡ w → ¬ ( u ≡ v )
  → desc-concl r w
```

`Desc-complete` is a recursion on the word, and both structural halves of
that recursion are proved here; what is missing is the decision inside the
step — which it is discharged by in §23–§24.

```agda
-- the base: two distinct empty trees of `r` *are* A1 at `r` (§9)
-- (purpose): the empty-word clause of the descent
-- (used in): `desc-picks-≟` (§24)
-- (proof idea): §9's `base-A1-at-root`, injected twice into `desc-concl`
desc-base : ∀ { r : RE } ( u v : U r )
  → proj₁ (flat {r} u) ≡ [] → proj₁ (flat {r} v) ≡ [] → ¬ ( u ≡ v )
  → desc-concl r []
desc-base u v u≡[] v≡[] u≢v = inj₁ (inj₁ (base-A1-at-root _ u v u≡[] v≡[] u≢v))

-- the step: one letter through *one* instance carries a conclusion of the
-- continuation back to the state — the path is extended by `pcons`, the word
-- split by one letter.  Note that it constructs no instance of the
-- continuation and examines no list.
-- (purpose): the descent's only recursive clause
-- (used in): `desc-picks-≟` (§24), the different-residuals branch
-- (proof idea): `pcons` the step's stored membership onto the path the
--   recursive call returns; the word split moves one letter, and a stop at
--   the continuation becomes the one-letter prefix `[ c ]`
desc-step : ∀ { r : RE } { c : Char } { ws : List Char }
  ( z : PDInstance r c ) → z ∈ PosixPD.pdU[ r , c ]
  → desc-concl (Canonic.pd-expr z) ws → desc-concl r (c ∷ ws)
desc-step {r} {c} {ws} z z∈ (inj₁ cr) =
  inj₂ ( [ c ] , ws , refl , ( pcons z z∈ pnil , cr ) )
desc-step {r} {c} {ws} z z∈ (inj₂ ( w′ , w″ , w≡w′++w″ , path , cr )) =
  inj₂ ( ( c ∷ w′ ) , w″ , cong (c ∷_) w≡w′++w″
        , ( pcons z z∈ path , cr ) )
```

The gap is inside the step and it is a single case.  `pdU-complete` gives *an*
instance for `u` and *an* instance for `v`: when those coincide,
`Recons-residual` supplies both residuals at one state and `desc-step` closes
the step by recursion.  When they do not, the residuals live at different
states and need not be distinct at all, so the step cannot continue by
recursion; what closes that case is a diagnosis *at the state* — the paper's
enumeration of the only situations in which the transition-tree construction
branches.  A first guess would be the counting form: two members of `pdU[ r , c ]`
arise only where `pdU` duplicates instances, below a nullable concatenation
through
`concatmap-pdinstance-snd`, one instance per empty tree of the left factor.
A *sum* whose left branch reappears in its right branch derives the *same*
tree through the branch injection and through the fused member `pdU` computes,
with no concatenation in the expression at all — and what saves the argument
there is that the two derivations differ by an injection through a sum of
`≈₀`-similar alternatives, exactly the `Idemp`/A3 situation: `crit`'s fourth
disjunct, the transition test `Canonic.pd-Idemp?`.  So the classification runs
through that disjunct — and §23 shows the counting guess was in fact the whole
truth about *continuations*: whatever the multiplicity, all members of
`pdU[ r , c ]` continue at one expression, so the "different states" case never
arises.

What is proved is the reduction: the §8 goal is a corollary of `Desc-complete`,
because a path is a `pd*-Desc` membership (`pdesc`) and the state itself is the
pd-descendant of the empty prefix.

```agda
-- (purpose): the reduction — derive §8's goal from `Desc-complete`
-- (used in): `completeness` below (§24)
-- (proof idea): run the descent on the whole word and read its output: the
--   criterion-at-state case is `pdesc pnil` at `r` itself, the path case is
--   `pdesc` of the returned path with `pdend` as the witness state
completeness-from-desc : ( dc : Desc-complete )
  → ( r : RE ) ( u v : U r )
  → proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) → ¬ ( u ≡ v )
  → ∃[ w′ ] ∃[ w″ ]
      ( ( proj₁ (flat {r} u) ≡ w′ ++ w″ )
      × ∃[ p ] ( Any ( λ s → s ≡ p ) (Canonic.pd*-Desc r w′) × crit p ) )
completeness-from-desc dc r u v w≡ u≢v with dc r (proj₁ (flat {r} u)) u v refl (sym w≡) u≢v
... | inj₁ cr = ( [] , proj₁ (flat {r} u) , refl , ( r , pdesc pnil , cr ) )
... | inj₂ ( w′ , w″ , w≡w′++w″ , ( path , cr ) )
    = ( w′ , w″ , w≡w′++w″ , ( pdend path , pdesc path , cr ) )
```

## 20. The pick test, made computable

The one decision the step of the recursion cannot avoid is identity of
*records*: `pdinstance` stores its transition as a function field
(`inj : U p → U r`), so `Dec ( z ≡ z′ )` is not computable here.  What the
decision is *for*, though, is two stop configurations, and this section names
both sides of them as terms and as theorems: the residual of a
reconstruction and its word (`residual`, `residual-word`, read off
§13's `Recons-residual`), and the fact that the second configuration — two
*distinct* records of `pdU[ r , c ]` continuing at one expression — fires the
fourth disjunct of `crit` *by computation*
(`pick-diff-record-prf`, via `Canonic.pd-Idemp?-members`: the member list
then holds two entries with one continuation, exactly what `Canonic`'s
`Idemp` test reads).  The first configuration — the two picks continuing at
*different* expressions — is the one §23 rules out; the record decision
itself is what §24 replaces by a decidable question.

```agda
-- (purpose): the residual tree of a reconstruction, as a term at the
--   instance's continuation
-- (used in): the test and the recursive call of `desc-picks-≟` (§24)
-- (proof idea): first projection of `Recons-residual` (§13)
residual : ∀ { r : RE } { c : Char } { ws : List Char } { z : PDInstance r c } { u : U r }
  → Recons {r} {c} u z → proj₁ (flat {r} u) ≡ c ∷ ws → U (Canonic.pd-expr z)
residual u∈ u≡ = proj₁ (Recons-residual u∈ u≡)

-- (purpose): the residual's word *is* the tail of the pair's word
-- (used in): the recursive call of `desc-picks-≟` (§24)
-- (proof idea): second projection of `Recons-residual`
residual-word : ∀ { r : RE } { c : Char } { ws : List Char } { z : PDInstance r c } { u : U r }
  ( u∈ : Recons {r} {c} u z ) ( u≡ : proj₁ (flat {r} u) ≡ c ∷ ws )
  → proj₁ (flat {Canonic.pd-expr z} (residual u∈ u≡)) ≡ ws
residual-word u∈ u≡ = proj₂ (Recons-residual u∈ u≡)
```

The shape §24's descent takes its branches from: were the record decision
available, a `yes` would send the pair through the shared record — one
`Recons-residual` per tree at one state, and `desc-step` lifting whatever
the recursion finds there — and a `no` would end the step at one of two
configurations: the picks continuing at *different* expressions, or *distinct*
records continuing at one expression.  The second configuration is the
fourth disjunct, and it is a theorem, not a rule:

```agda
-- (purpose): two *distinct* members of `pdU[ r , c ]` with one continuation
--   make the fourth disjunct of `crit` fire at `r` — the A3 stop, as a theorem
-- (used in): `desc-picks-≟`'s equal-residuals branch (§24)
-- (proof idea): `Canonic.pd-Idemp?-members` turns two distinct members with
--   equal continuations into a positive `Idemp` test on the real list, and
--   `crit-A3-test` (§8) injects it
pick-diff-record-prf : ∀ { r : RE } { c : Char }
  ( z z′ : PDInstance r c )
  → z ∈ PosixPD.pdU[ r , c ] → z′ ∈ PosixPD.pdU[ r , c ]
  → ¬ ( z ≡ z′ )
  → Canonic.pd-expr z ≡ Canonic.pd-expr z′
  → crit r
pick-diff-record-prf {r} {c} z z′ z∈ z′∈ z≢z′ eq =
  crit-A3-test r c
    (Canonic.pd-Idemp?-members (PosixPD.pdU[ r , c ]) z z′ z∈ z′∈ z≢z′ eq)
```

The record case — one letter, two members, one continuation — is here made
precise, and it is a theorem, not a rule: two *distinct* members continuing
at one expression leave a repeated alternative in the flattened continuations
(`Canonic.pd-Idemp?-members`, `cgp.ambig.Canonic` §6.3), which is exactly what
`Idemp` would merge, and the A3 test fires at *this* transition.  So the only
part of the step that is not already a computation is the choice *between* the
continuation cases — and §23 shows the configuration where they genuinely
differ cannot occur, while §24 discharges the choice itself by a decidable
test on residuals.

## 23. One continuation per transition

The descent's step turns on a single property of this project's derivative
list.  The POSIX merging (`pdinstance-oplus`, applied in the sum clause and in
the nullable-concatenation clause of `pdU`) makes `pdU[ r , c ]` behave like the
paper's single derivative expression `deriv s x`: the list has several members
only when the transition leaves `l ● s` with nullable `l` — one member per empty
tree of the left factor, which is the second criterion's own configuration —
and *all members of `pdU[ r , c ]` continue at one and the same
expression*.  Two picks therefore never continue at *different* expressions,
and the descent of §20 runs with only the record decision left.  That decision
is what this section cannot supply — `pdinstance` stores a function field —
and §24 shows
the descent does not need it: an equivalent question on residual trees is
decidable.  With it the §8 statement follows through §16's
`completeness-from-desc`.

The result also places this file precisely against the paper's diagnosis.  The
proof walks the pair to the state reached by the *whole* word, and there
§9's `base-A1-at-root` reads the two empty trees as A1: a criterion does fire, at the
latest possible state.  The A2/A3 machinery of `cgp.ambig.AmbigCheck` and
`cgp.ambig.Canonic` is what finds a criterion
*earlier* — at the transition where the pair first separates, which is what
the paper's enumeration is for (this module's §20 theorem
`pick-diff-record-prf` is one instance of it); it sharpens the diagnosis, and
the completeness
direction itself does not depend on it.

```agda
-- every element of a `map`/`concatMap` comes from an element of the argument
-- (purpose): pull a membership back through `map`, with the defining equation
-- (used in): `map-const`, `concatMap-hyp` below
-- (proof idea): induction on the list, reading the `here`/`there` position
∈-map⁻ : {A B : Set} ( f : A → B ) ( xs : List A ) ( y : B )
  → y ∈ map f xs → Σ[ x ∈ A ] ( x ∈ xs × f x ≡ y )
∈-map⁻ f [] y ()
∈-map⁻ f (x ∷ xs) y (here p) = ( x , here refl , sym p )
∈-map⁻ f (x ∷ xs) y (there w) with ∈-map⁻ f xs y w
...   | ( x₂ , x∈ , eq ) = ( x₂ , there x∈ , eq )

-- (purpose): split a membership at an append
-- (used in): `∈-concat-dest` below
-- (proof idea): induction counting skipped elements with `there`
∈-++-dest : {A : Set} ( xs ys : List A ) ( y : A )
  → y ∈ xs ++ ys → ( y ∈ xs ) ⊎ ( y ∈ ys )
∈-++-dest [] ys y w = inj₂ w
∈-++-dest (x ∷ xs) ys y (here q) = inj₁ (here q)
∈-++-dest (x ∷ xs) ys y (there w) with ∈-++-dest xs ys y w
...   | inj₁ u = inj₁ (there u)
...   | inj₂ v = inj₂ v

-- (purpose): find the block a member of a `concat` lives in.  The element
--   lists must be matched in constructor form, hence the `[] ∷ `_`_` patterns
-- (used in): `concat-const` below
-- (proof idea): induction on the block list, splitting inner memberships with
--   `∈-++-dest`
∈-concat-dest : {A : Set} ( xss : List ( List A ) ) ( y : A )
  → y ∈ concat xss → Σ[ xs ∈ List A ] ( xs ∈ xss × y ∈ xs )
∈-concat-dest [] y ()
∈-concat-dest ([] ∷ xss) y z∈ with ∈-concat-dest xss y z∈
...   | ( xs₂ , xs∈ , q ) = ( xs₂ , there xs∈ , q )
∈-concat-dest ((x ∷ xs) ∷ xss) y (here q) = ( x ∷ xs , here refl , here q )
∈-concat-dest ((x ∷ xs) ∷ xss) y (there w) with ∈-++-dest xs (concat xss) y w
...   | inj₁ u = ( x ∷ xs , here refl , there u )
...   | inj₂ v with ∈-concat-dest xss y v
...     | ( xs₂ , xs∈ , q ) = ( xs₂ , there xs∈ , q )

-- (purpose): the property "every two members of this list continue at the
--   same expression" — the invariant §23 proves for all `pdU` lists
-- (used in): every clause of `pdU-const` below
-- (proof idea): definition — a universal statement over memberships
PdConst : ( r : RE ) ( c : Char ) → List ( PDInstance r c ) → Set
PdConst r c xs = ∀ ( z z′ : PDInstance r c )
  → z ∈ xs → z′ ∈ xs → Canonic.pd-expr z ≡ Canonic.pd-expr z′

-- (purpose): constancy is preserved by maps that send equal continuations to
--   equal continuations — which is what the `pdinstance-*` constructors do,
--   each one wrapping the pattern field in a fixed RE context
--   (`pd-expr-resp∘*` below)
-- (used in): the `+` and `●` clauses of `pdU-const` below
-- (proof idea): pull both memberships back with `∈-map⁻`, transport the
--   equality of continuations along the two constructor equations, apply the
--   responsiveness hypothesis
map-const : ( r s : RE ) ( c : Char ) ( f : PDInstance r c → PDInstance s c )
  → ( resp : ( x x₂ : PDInstance r c )
        → Canonic.pd-expr x ≡ Canonic.pd-expr x₂
        → Canonic.pd-expr (f x) ≡ Canonic.pd-expr (f x₂) )
  → ( xs : List ( PDInstance r c ) ) → PdConst r c xs → PdConst s c (map f xs)
map-const r s c f resp xs u z z′ z∈ z′∈
  with ∈-map⁻ f xs z z∈ | ∈-map⁻ f xs z′ z′∈
...   | ( x , x∈ , eq ) | ( x₂ , x₂∈ , eq₂ ) =
    trans (sym (cong Canonic.pd-expr eq))
      (trans (resp x x₂ (u x x₂ x∈ x₂∈)) (cong Canonic.pd-expr eq₂))

-- (purpose): a `concat` of blocks is constant when the blocks are constant
--   with each other
-- (used in): `concatMap-const` below (and through it the concatenation
--   clauses of `pdU-const`)
-- (proof idea): locate both members' blocks with `∈-concat-dest` and apply
--   the cross-block hypothesis
concat-const : ( s : RE ) ( c : Char )
  → ( xss : List ( List ( PDInstance s c ) ) )
  → (∀ ( xs xs′ : List ( PDInstance s c ) ) → xs ∈ xss → xs′ ∈ xss
       → ( z z′ : PDInstance s c ) → z ∈ xs → z′ ∈ xs′
       → Canonic.pd-expr z ≡ Canonic.pd-expr z′)
  → PdConst s c (concat xss)
concat-const s c xss hyp z z′ z∈ z′∈ with ∈-concat-dest xss z z∈ | ∈-concat-dest xss z′ z′∈
...   | ( xs , x∈ , q ) | ( xs′ , x′∈ , q′ ) = hyp xs xs′ x∈ x′∈ z z′ q q′

-- (purpose): the cross-block hypothesis `concat-const` needs, discharged from
--   a hypothesis on `concatMap`'s *arguments*
-- (used in): `concatMap-const` below
-- (proof idea): invert the block memberships with `∈-map⁻`, transport the
--   element memberships along the equations, apply the argument hypothesis
concatMap-hyp : { A : Set } ( s : RE ) ( c : Char )
  → ( f : A → List ( PDInstance s c ) ) → ( xs : List A )
  → (∀ ( x x′ : A ) → x ∈ xs → x′ ∈ xs → ( y y′ : PDInstance s c )
        → y ∈ f x → y′ ∈ f x′ → Canonic.pd-expr y ≡ Canonic.pd-expr y′)
  → ( xs₁ xs₂ : List ( PDInstance s c ) )
  → xs₁ ∈ map f xs → xs₂ ∈ map f xs
  → ( z z′ : PDInstance s c ) → z ∈ xs₁ → z′ ∈ xs₂
  → Canonic.pd-expr z ≡ Canonic.pd-expr z′
concatMap-hyp s c f xs hyp xs₁ xs₂ m₁ m₂ z z′ q q′
  with ∈-map⁻ f xs xs₁ m₁ | ∈-map⁻ f xs xs₂ m₂
...   | ( x , x∈ , eq ) | ( x₂ , x₂∈ , eq₂ ) =
    hyp x x₂ x∈ x₂∈ z z′
      (subst ( λ L → z ∈ L ) (sym eq) q)
      (subst ( λ L → z′ ∈ L ) (sym eq₂) q′)

-- (purpose): a `concatMap` is constant when its blocks are constant
--   pairwise over the arguments
-- (used in): the `⋆` and nullable-`●` clauses of `pdU-const` below
-- (proof idea): `concat-const` of the block list, hypothesis by
--   `concatMap-hyp`
concatMap-const : ( s : RE ) ( c : Char ) { A : Set }
  → ( f : A → List ( PDInstance s c ) ) → ( xs : List A )
  → (∀ ( x x′ : A ) → x ∈ xs → x′ ∈ xs → ( y y′ : PDInstance s c )
        → y ∈ f x → y′ ∈ f x′ → Canonic.pd-expr y ≡ Canonic.pd-expr y′)
  → PdConst s c (concatMap f xs)
concatMap-const s c f xs hyp =
  concat-const s c (map f xs)
    (λ xs₁ xs₂ m₁ m₂ z z′ q q′ →
       concatMap-hyp s c f xs hyp xs₁ xs₂ m₁ m₂ z z′ q q′)

-- continuations of the constructed records, in terms of their inputs
-- (purpose): where a fused pair continues — a sum of the two continuations
-- (used in): `fuse-pair-const` and the `+` clause of `pdU-const` below
-- (proof idea): `refl` — destructure both records, the pattern field is
--   built by the same expression
pd-expr∘fuse : ( r : RE ) ( c : Char ) ( loc : ℕ )
  ( x y : PDInstance r c )
  → Canonic.pd-expr (fuse {r} {loc} {c} x y)
    ≡ Canonic.pd-expr x + Canonic.pd-expr y ` loc
pd-expr∘fuse r c loc (pdinstance {pˡ} injˡ evˡ) (pdinstance {pʳ} injʳ evʳ) = refl

-- (purpose): the nullable-concatenation second-factor instance continues
--   where its input does
-- (used in): `snd-pair-const` below, the nullable-`●` clause of `pdU-const`
-- (proof idea): `refl` after destructuring the record and the empty-tree
--   evidence
pd-expr∘snd : ∀ { l r : RE } { loc : ℕ } { c : Char }
  → ( ex : Σ[ e ∈ U l ] ( AllEmpty.Flat-[] l e ) ) ( y : PDInstance r c )
  → Canonic.pd-expr (mk-snd-pdi {l} {r} {loc} {c} ex y) ≡ Canonic.pd-expr y
pd-expr∘snd ( e , flat-[] .e eq ) (pdinstance {p} inj ev) = refl

-- the `pdU` constructor maps respect continuations: each computes the new
-- pattern field from the old one, definitionally after the record is
-- destructured (`left`/`right` keep it; `fst`/`star` put it into a fixed
-- concatenation)
-- (purpose): the sum-left injection keeps the continuation
-- (used in): the `+` clause of `pdU-const` below (via `map-const`)
-- (proof idea): the stored equation, after destructuring both records
pd-expr-resp∘left : ∀ { l r : RE } { loc : ℕ } { c : Char }
  ( z z′ : PDInstance l c ) → Canonic.pd-expr z ≡ Canonic.pd-expr z′
  → Canonic.pd-expr (pdinstance-left {l} {r} {loc} {c} z)
    ≡ Canonic.pd-expr (pdinstance-left {l} {r} {loc} {c} z′)
pd-expr-resp∘left (pdinstance {p} inj ev) (pdinstance {p₂} inj′ ev′) eq = eq

-- (purpose): the sum-right injection keeps the continuation
-- (used in): the `+` clause of `pdU-const` below (via `map-const`)
-- (proof idea): the stored equation, after destructuring both records
pd-expr-resp∘right : ∀ { l r : RE } { loc : ℕ } { c : Char }
  ( z z′ : PDInstance r c ) → Canonic.pd-expr z ≡ Canonic.pd-expr z′
  → Canonic.pd-expr (pdinstance-right {l} {r} {loc} {c} z)
    ≡ Canonic.pd-expr (pdinstance-right {l} {r} {loc} {c} z′)
pd-expr-resp∘right (pdinstance {p} inj ev) (pdinstance {p₂} inj′ ev′) eq = eq

-- (purpose): the concatenation first-factor injection puts the continuation
--   into the fixed context `_ ● r \` loc`
-- (used in): the `●` clauses of `pdU-const` below (via `map-const`)
-- (proof idea): `cong` of the context, after destructuring both records
pd-expr-resp∘fst : ∀ { l r : RE } { loc : ℕ } { c : Char }
  ( z z′ : PDInstance l c ) → Canonic.pd-expr z ≡ Canonic.pd-expr z′
  → Canonic.pd-expr (pdinstance-fst {l} {r} {loc} {c} z)
    ≡ Canonic.pd-expr (pdinstance-fst {l} {r} {loc} {c} z′)
pd-expr-resp∘fst {l} {r} {loc} {c}
  (pdinstance {p} inj ev) (pdinstance {p₂} inj′ ev′) eq =
    cong ( λ q → q ● r ` loc ) eq

-- (purpose): the star injection puts the continuation into the fixed
--   context `_ ● (r ⋆) \` loc`
-- (used in): the `⋆` clause of `pdU-const` below (via `map-const`)
-- (proof idea): `cong` of the context, after destructuring both records
pd-expr-resp∘star : ∀ { r : RE } { ε∉r : ε∉ r } { loc : ℕ } { c : Char }
  ( z z′ : PDInstance r c ) → Canonic.pd-expr z ≡ Canonic.pd-expr z′
  → Canonic.pd-expr (pdinstance-star {r} {ε∉r} {loc} {c} z)
    ≡ Canonic.pd-expr (pdinstance-star {r} {ε∉r} {loc} {c} z′)
pd-expr-resp∘star {r} {ε∉r} {loc} {c}
  (pdinstance {p} inj ev) (pdinstance {p₂} inj′ ev′) eq =
    cong ( λ q → q ● (r * ε∉r ` loc) ` loc ) eq

-- (purpose): two fusions built over one right list, from left instances with
--   equal continuations, continue equally
-- (used in): `oplus-const` below
-- (proof idea): invert both memberships with `∈-map⁻`, compute both
--   fusions' continuations with `pd-expr∘fuse`, and move between them with
--   the block constancy plus the left instances' equation
fuse-pair-const : ( r : RE ) ( c : Char ) ( loc : ℕ )
  → ( ys : List ( PDInstance r c ) ) → PdConst r c ys
  → ( x₁ x₂ : PDInstance r c ) → Canonic.pd-expr x₁ ≡ Canonic.pd-expr x₂
  → ( z z′ : PDInstance r c )
  → z ∈ map (fuse {r} {loc} {c} x₁) ys → z′ ∈ map (fuse {r} {loc} {c} x₂) ys
  → Canonic.pd-expr z ≡ Canonic.pd-expr z′
fuse-pair-const r c loc ys uy x₁ x₂ x₁≡x₂ z z′ q q₂
  with ∈-map⁻ (fuse {r} {loc} {c} x₁) ys z q | ∈-map⁻ (fuse {r} {loc} {c} x₂) ys z′ q₂
...   | ( w , w∈ , eq ) | ( w₂ , w₂∈ , eq₂ ) =
    trans (sym (cong Canonic.pd-expr eq))
      (trans (pd-expr∘fuse r c loc x₁ w)
        (trans (cong₂ ( λ a b → a + b ` loc ) x₁≡x₂ (uy w w₂ w∈ w₂∈))
               (trans (sym (pd-expr∘fuse r c loc x₂ w₂))
                      (cong Canonic.pd-expr eq₂))))

-- (purpose): `pdinstance-oplus` of two constant lists is constant — its
--   members are the pairwise fusions, each continuing at the sum of one pair
--   of continuations
-- (used in): the `+` and nullable-`●` clauses of `pdU-const` below
-- (proof idea): by cases on the two lists: a singleton side falls back to
--   that side, both-nonempty is a `concatMap` of `map (fuse x₁)` blocks,
--   constant by `concatMap-const` with `fuse-pair-const`
oplus-const : ( r : RE ) ( c : Char ) ( loc : ℕ )
  → ( xs ys : List ( PDInstance r c ) )
  → PdConst r c xs → PdConst r c ys
  → PdConst r c (pdinstance-oplus {r} {loc} {c} xs ys)
oplus-const r c loc []       ys ux uy z z′ z∈ z′∈ = uy z z′ z∈ z′∈
oplus-const r c loc (x ∷ xs) []  ux uy z z′ z∈ z′∈ = ux z z′ z∈ z′∈
oplus-const r c loc (x ∷ xs) (y ∷ ys) ux uy =
  concatMap-const r c ( λ x₁ → map (fuse {r} {loc} {c} x₁) (y ∷ ys) ) (x ∷ xs)
    ( λ x₁ x₂ x₁∈ x₂∈ → fuse-pair-const r c loc (y ∷ ys) uy x₁ x₂ (ux x₁ x₂ x₁∈ x₂∈) )

-- (purpose): two members made by `pdinstance-snd` — one per empty tree of the
--   left factor — continue at the *right factor's* continuation, whichever
--   empty tree was used
-- (used in): `snd-list-const` below
-- (proof idea): invert both memberships with `∈-map⁻`, move along
--   `pd-expr∘snd` to the underlying `pdU[ s , c ]` members, apply the block
--   constancy there
snd-pair-const : ∀ { l s : RE } { loc : ℕ } { c : Char }
  → ( ex ex′ : Σ[ e ∈ U l ] ( AllEmpty.Flat-[] l e ) )
  → PdConst s c (PosixPD.pdU[ s , c ])
  → ( y y′ : PDInstance ( l ● s ` loc ) c )
  → y ∈ PDI.pdinstance-snd {l} {s} {loc} {c} ex (PosixPD.pdU[ s , c ])
  → y′ ∈ PDI.pdinstance-snd {l} {s} {loc} {c} ex′ (PosixPD.pdU[ s , c ])
  → Canonic.pd-expr y ≡ Canonic.pd-expr y′
snd-pair-const {l} {s} {loc} {c} ex ex′ u y y′ q q₂
  with ∈-map⁻ (mk-snd-pdi {l} {s} {loc} {c} ex) (PosixPD.pdU[ s , c ]) y q
    | ∈-map⁻ (mk-snd-pdi {l} {s} {loc} {c} ex′) (PosixPD.pdU[ s , c ]) y′ q₂
...   | ( w , w∈ , eq ) | ( w₂ , w₂∈ , eq₂ ) =
    trans (sym (cong Canonic.pd-expr eq))
      (trans (pd-expr∘snd ex w)
        (trans (u w w₂ w∈ w₂∈)
          (trans (sym (pd-expr∘snd ex′ w₂)) (cong Canonic.pd-expr eq₂))))

-- (purpose): the whole nullable-concatenation second-side list — one instance
--   per empty tree of the left factor — is constant
-- (used in): the nullable-`●` clause of `pdU-const` below
-- (proof idea): `concatMap-const` over the empty-tree list: the blocks are
--   nonempty (a `concatmap` lemma on `mkAllEmptyU`'s soundness) and pairwise
--   constant by `snd-pair-const`
snd-list-const : ∀ { l s : RE } { ε∈l : RE.ε∈ l } { loc : ℕ } { c : Char }
  → PdConst s c (PosixPD.pdU[ s , c ])
  → PdConst ( l ● s ` loc ) c
      (PDI.concatmap-pdinstance-snd {l} {s} {ε∈l} {loc} {c} (PosixPD.pdU[ s , c ]))
snd-list-const {l} {s} {ε∈l} {loc} {c} u =
  concatMap-const ( l ● s ` loc ) c
    ( λ ex → PDI.pdinstance-snd {l} {s} {loc} {c} ex (PosixPD.pdU[ s , c ]) )
    ( PDI.zip-es-flat-[]-es {l} {ε∈l} (mkAllEmptyU {l} ε∈l)
        (AllEmpty.mkAllEmptyU-sound {l} ε∈l) )
    ( λ ex ex′ ex∈ ex′∈ → snd-pair-const {l} {s} {loc} {c} ex ex′ u )

-- (purpose): THE structural fact: every two members of `pdU[ r , c ]`
--   continue at the same expression — the transition list behaves like the
--   paper's single derivative expression `deriv s x`
-- (used in): `desc-picks-≟` and `diff-records-≟` (§24) — it places both
--   residuals at one expression, where equality is decidable
-- (proof idea): induction on `r`: each clause maps a constant list or
--   oplus's two constant lists — constant by `map-const` (the constructor
--   maps respect continuations) and `oplus-const`; the nullable-concatenation
--   clause discharges its right side with `snd-list-const`
pdU-const : ( r : RE ) ( c : Char ) ( z z′ : PDInstance r c )
  → z ∈ PosixPD.pdU[ r , c ] → z′ ∈ PosixPD.pdU[ r , c ]
  → Canonic.pd-expr z ≡ Canonic.pd-expr z′
pdU-const ε c z z′ ()
pdU-const ( $ c₀ ` loc ) c z z′ z∈ z′∈ with c₀ Char.≟ c | z∈ | z′∈
...   | yes refl | here p | here q = cong Canonic.pd-expr (trans p (sym q))
...   | yes refl | here p | there ()
...   | yes refl | there () | _
...   | no ¬c | () | _
pdU-const ( l + s ` loc ) c z z′ z∈ z′∈ =
  oplus-const ( l + s ` loc ) c loc
    ( map (pdinstance-left {l} {s} {loc} {c}) (PosixPD.pdU[ l , c ]) )
    ( map (pdinstance-right {l} {s} {loc} {c}) (PosixPD.pdU[ s , c ]) )
    ( map-const l ( l + s ` loc ) c (pdinstance-left {l} {s} {loc} {c})
        (pd-expr-resp∘left {l} {s} {loc} {c})
        (PosixPD.pdU[ l , c ]) (pdU-const l c) )
    ( map-const s ( l + s ` loc ) c (pdinstance-right {l} {s} {loc} {c})
        (pd-expr-resp∘right {l} {s} {loc} {c})
        (PosixPD.pdU[ s , c ]) (pdU-const s c) )
    z z′ z∈ z′∈
pdU-const ( r * ε∉r ` loc ) c z z′ z∈ z′∈ =
  map-const r ( r * ε∉r ` loc ) c (pdinstance-star {r} {ε∉r} {loc} {c})
    (pd-expr-resp∘star {r} {ε∉r} {loc} {c})
    (PosixPD.pdU[ r , c ]) (pdU-const r c) z z′ z∈ z′∈
pdU-const ( l ● s ` loc ) c z z′ z∈ z′∈ with RE.ε∈? l
...   | no ¬ε∈l =
      map-const l ( l ● s ` loc ) c (pdinstance-fst {l} {s} {loc} {c})
        (pd-expr-resp∘fst {l} {s} {loc} {c})
        (PosixPD.pdU[ l , c ]) (pdU-const l c) z z′ z∈ z′∈
...   | yes ε∈l =
      oplus-const ( l ● s ` loc ) c loc
        ( map (pdinstance-fst {l} {s} {loc} {c}) (PosixPD.pdU[ l , c ]) )
        ( PDI.concatmap-pdinstance-snd {l} {s} {ε∈l} {loc} {c}
            (PosixPD.pdU[ s , c ]) )
        ( map-const l ( l ● s ` loc ) c (pdinstance-fst {l} {s} {loc} {c})
            (pd-expr-resp∘fst {l} {s} {loc} {c})
            (PosixPD.pdU[ l , c ]) (pdU-const l c) )
        ( snd-list-const {l} {s} {ε∈l} {loc} {c} (pdU-const s c) )
        z z′ z∈ z′∈
```

## 24. The record decision, computed: the completeness direction, closed

The one question §23 leaves is whether the two picks are *one record*.  As
stated that question has no decision procedure — `pdinstance` stores a function
(`U p → U r`), so record identity is intensional — and a decision would mean
quotienting instances by pattern (the `Cast`/`≈₀` machinery is the natural
candidate, and would also make the descent run on canonical states).  But the
descent never uses record identity *as such*: it uses it to choose between
continuing through one shared transition and firing the criterion.  That choice
has an equivalent form on the other side of the reconstruction, where it is
decidable: the two **residual trees**.  By `pdU-const` both residuals, after
transport along one equation, live at the same expression, and tree identity at
one expression is decidable (`ParseTree._⊢_≟_`).

- *different residuals*: the descent continues — at the single reached state,
  through the single member `z`, exactly as §20's `desc-step` does;
- *equal residuals*: the two records cannot have been one: a single record maps
  distinct trees to distinct residuals, so equal residuals mean *two distinct
  members with one continuation* — the A3 configuration, closed by §20's
  `pick-diff-record-prf`.

In `diff-records-≟` the claim's two transports cancel in a single clause: the
record equation and the continuation equation are case-split, which identifies
the two records and dissolves the transport — constructor injectivity does all
the work, no postulate and no transport coherence.

```agda
-- (purpose): transporting a tree across an equation of expressions does not
--   move its word
-- (used in): `desc-picks-≟` below (the recursive call's word equation for the
--   transported residual)
-- (proof idea): `refl` — the transport is a `subst`, which dissolves at
--   `refl`
flat-resp : ∀ { r r′ : RE } ( eq : r ≡ r′ ) ( u : U r )
  → proj₁ (flat {r′} (subst ( λ e → U e ) eq u)) ≡ proj₁ (flat {r} u)
flat-resp refl u = refl

-- (purpose): equal residuals ⇒ distinct records — the two picks are *not* one
--   record when their residuals agree
-- (used in): `desc-picks-≟` below, the equal-residuals branch (supplies the
--   distinctness premise of `pick-diff-record-prf`)
-- (proof idea): were the picks one record, its own transition map would
--   separate distinct trees (`cong inj` under one `inj`); both records are
--   matched in constructor form, and the record equation and the continuation
--   equation are case-split in the `with` — identifying the two records and
--   dissolving the transport, constructor injectivity does the work
diff-records-≟ : ∀ { r : RE } { c : Char } { ws : List Char } { u v : U r }
  ( z z′ : PDInstance r c )
  ( rec-l : Recons {r} {c} u z ) ( rec-r : Recons {r} {c} v z′ )
  ( u≡ : proj₁ (flat {r} u) ≡ c ∷ ws ) ( v≡ : proj₁ (flat {r} v) ≡ c ∷ ws )
  ( q : Canonic.pd-expr z′ ≡ Canonic.pd-expr z )
  → residual rec-l u≡ ≡ subst ( λ e → U e ) q ( residual rec-r v≡ )
  → ¬ ( u ≡ v )
  → ¬ ( z ≡ z′ )
diff-records-≟ z z′ (recons {inj = inj} uˡ ( w∈ˡ , eqˡ ))
                  (recons {inj = inj′} vʳ ( w∈ʳ , eqʳ ))
  u≡ v≡ q eq u≢v ρ with q | ρ
...   | refl | refl = u≢v (trans (sym eqˡ) (trans (cong inj eq) eqʳ))

-- (purpose): the completeness descent itself, with a decidable test where the
--   record decision used to be: pick both members, place the second residual
--   at the first member's continuation (`pdU-const`), and decide the
--   residuals
-- (used in): `Desc-complete-≟` below — the whole of `completeness`
-- (proof idea): recursion on the word.  Different residuals: one
--   `desc-step` through the shared member `z` (its continuation *is* the
--   single reached state).  Equal residuals: the picks are distinct records
--   with one continuation (`diff-records-≟`), i.e. the A3 configuration:
--   `pick-diff-record-prf` closes the step without recursion
desc-picks-≟ : ( r : RE ) → ( w : List Char )
  → ( u v : U r )
  → proj₁ (flat {r} u) ≡ w → proj₁ (flat {r} v) ≡ w → ¬ ( u ≡ v )
  → desc-concl r w
desc-picks-≟ r [] u v u≡[] v≡[] u≢v = desc-base u v u≡[] v≡[] u≢v
desc-picks-≟ r (c ∷ ws) u v u≡ v≡ u≢v
  with pick-Any (PosixPD.pdU-complete {r} {c} u u≡)
... | ( z , rec-l , z∈ ) with pick-Any (PosixPD.pdU-complete {r} {c} v v≡)
...   | ( z′ , rec-r , z′∈ )
      with (ParseTree._⊢_≟_ (Canonic.pd-expr z) (residual rec-l u≡)
             ( subst ( λ e → U e ) (sym (pdU-const r c z z′ z∈ z′∈))
               (residual rec-r v≡) ))
...     | yes eq =
          inj₁ (pick-diff-record-prf z z′ z∈ z′∈
                  (diff-records-≟ z z′ rec-l rec-r u≡ v≡
                     (sym (pdU-const r c z z′ z∈ z′∈)) eq u≢v)
                  (pdU-const r c z z′ z∈ z′∈))
...     | no x≢y =
          desc-step z z∈
            (desc-picks-≟ (Canonic.pd-expr z) ws x y x≡ y≡ x≢y)
        where
          q  = sym (pdU-const r c z z′ z∈ z′∈)
          x  = residual rec-l u≡
          x≡ = residual-word rec-l u≡
          y  = subst ( λ e → U e ) q ( residual rec-r v≡ )
          y≡ = trans (flat-resp q (residual rec-r v≡)) (residual-word rec-r v≡)

-- (purpose): discharge §16's hypothesis — the completeness direction, closed
--   with no postulate at all
-- (used in): `completeness` below
-- (proof idea): §23's `pdU-const` supplies the shared continuation, the
--   residual test replaces the record decision: `desc-picks-≟` *is* a
--   `Desc-complete`
Desc-complete-≟ : Desc-complete
Desc-complete-≟ r w u v = desc-picks-≟ r w u v

-- §8's goal, stated here at its proof: given distinct parse trees of one
-- word, a pd-descendant state of a prefix carries a criterion.
-- (purpose): the completeness direction — the module's theorem
-- (used in): the module's statement
-- (proof idea): §16's `completeness-from-desc` applied to `Desc-complete-≟`
completeness : ∀ { r : RE }
  → ( u v : U r )
  → proj₁ (flat {r} u) ≡ proj₁ (flat {r} v) → ¬ ( u ≡ v )
  → ∃[ w′ ] ∃[ w″ ]
      ( ( proj₁ (flat {r} u) ≡ w′ ++ w″ )
      × ∃[ p ]
          ( Any ( λ s → s ≡ p ) (Canonic.pd*-Desc r w′)
          × crit p ) )
completeness {r} u v w≡ u≢v = completeness-from-desc Desc-complete-≟ r u v w≡ u≢v

-- What the `crit p` of the conclusion means: each disjunct is the hypothesis
-- of one soundness lemma of `cgp.ambig.Canonic` (§4/§6.1/§7), so the
-- conclusion says "some reachable state satisfies the input condition of a
-- soundness lift":
--
--   1  AmbigA1 p
--        → pd*-A1→Ambig                   (lift also asks pd*-inj pdi injective)
--   2  AmbigA2 p
--        → pd*-A2→Ambig                   (ditto)
--   3  ctx , l , s , loc ,
--      plug ctx ( l + s ` loc ) ≡ p × l ≈₀ s
--        → Ctx-dup→Ambig (no lift needed) / pd*-Ctx-dup→Ambig (asks injective)
--   4  ctx , q , c ,
--      plug ctx q ≡ p × pd-Idemp? (pdU[ q , c ]) ≡ true
--        → taken by no soundness lemma.  A3's soundness lemma is
--          pd-pairs→Ambig / pd*-pairs→Ambig: its hypothesis is the *pair of
--          derivative records* (instances of the two branches of one sum with
--          ≈₀-equal continuations), not the boolean test.  Canonic §6.3
--          reflects the fired scan into an ≈₀ pair at located positions of
--          `pd-alts` (`pd-Idemp?-witness`), and `pd-Idemp?-members` goes the
--          other way (a real duplicate pair makes the scan answer `true`,
--          which is what §20/§22's stop needs); what remains open is locating
--          the matched positions as the two branches of one `+` node under one
--          context — the gap stated in Canonic §8.1.
--
-- The `Any ( λ s → s ≡ p ) (pd*-Desc r w′)` membership unfolds to
-- `pd*-expr pdi ≡ p` for some `pdi : PDInstance* r w′` (the list is
-- `map pd*-expr (pdUMany[ r , w′ ])`), i.e. it supplies the instance the
-- lifts quantify over; only their injectivity hypothesis is not supplied —
-- and not needed here, since `u ≢ v` is already given: running a lift after
-- the fact certifies the diagnosis, it produces no new witness.


soundness : ∀ { r : RE } { w₁ w₂ : List Char }
  → ( u : U r )
  → ( proj₁ (flat {r} u) ≡ w₁ ++ w₂ )
  → ( p : RE )
  → crit p 
  → Any ( λ s → s ≡ p ) (Canonic.pd*-Desc r w₁)
  → ∃[ v ] ( proj₁ (flat {r} u) ≡ proj₁ (flat {r} v))  × (¬ ( u ≡ v ) ) 
soundness = {!!}   

```
