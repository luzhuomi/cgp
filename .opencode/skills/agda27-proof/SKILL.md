---
name: agda27-proof
description: Proving theorems in Agda 2.7.0.1 - implicit argument inference, rewrite pitfalls, with abstractions, existential threading, absurd patterns, asymmetry proofs, and helper construction
license: MIT
compatibility: opencode
metadata:
  audience: proof-assistant-developers
  workflow: agda
---

## What I Do

Guide proof construction in Agda 2.7.0.1, focusing on the constraint solver's limitations compared to newer Agda versions.

## When To Use Me

Use this skill when proving theorems in Agda 2.7.0.1, especially when dealing with implicit arguments, `with` expressions, `rewrite`, existential types, absurd patterns, or proving asymmetry properties.

## Key Lessons

### 1. Implicit Arguments Require Explicit Annotations

Agda 2.7.0.1's constraint solver cannot infer implicit `r : RE` in nested `where` clauses. Always annotate calls that depend on implicit `r`:

```agda
-- BAD: r not inferred
trans-SublenEq q' (sym (cond₁ q' ...)) ...
-- GOOD: explicit r
trans-SublenEq {r} q' (sym (cond₁ q' ...)) ...
```


### 2. `rewrite` changes the goal of the current clause

`rewrite` modifies the goal type for the current clause. Use `subst` or isolate in a helper function if you dont want the the change.

```agda
-- BAD: rewrite pollutes the (there y∈) clause
go-pos-shift-map (q ∷ qs) (here p) rewrite suc-injective ... = ... -- goal is modified
go-pos-shift-map (q ∷ qs) (there y∈) = ...

-- GOOD: use subst
go-pos-shift-map (q ∷ qs) (here p) =
  subst (λ n' → n' ∷ xs ∈ ...) (sym (suc-injective ...)) (subst (λ xs' → ...) (sym ...) (here refl))

-- GOOD: isolate in helper (helper is scoped to one clause)
go-pos-shift-map (q ∷ qs) (here p) = helper-here p
  where helper-here : ... → ...
        helper-here p rewrite suc-injective ... = here refl
```

### 3. `with` Expressions Create Abstraction Barriers

Functions defined with `with` don't reduce definitionally without the `with` abstraction threaded. Two solutions:

```agda
-- If sublen uses: sublen (PairU u v) q with length (proj₁ (flat (PairU u v)))
-- Then sublen (PairU u v) [] is ABSTRACTED, not just k

-- Solution 1: thread the same with
sublen-∈-just {PairU u v} [] (here p) with length (proj₁ (flat (PairU {l} {r} {loc} u v)))
... | k = k , refl

-- Solution 2: define a helper that matches the with
sublen-nil-∈ : ∀ {r} (u : U r) → ∃[ n ] sublen u [] ≡ just n
sublen-nil-∈ (PairU u v) with length (proj₁ (flat (PairU {l} {r} {loc} u v)))
... | k = k , refl
```

### 4. Existential Types Need Explicit Witnesses

In recursive contexts, Agda 2.7.0.1 cannot infer existential witnesses from `just _`:

```agda
-- BAD: witness _ cannot be inferred recursively
... → sublen u x ≡ just _
-- GOOD: use explicit existential
... → ∃[ n ] sublen u x ≡ just n
```

### 5. `()` Absurd Patterns Need Full Reduction

For `()` to fire, the type must reduce to an empty type. If implicit arguments aren't inferred, the type won't reduce:

```agda
-- BAD: PairU u _ leaves implicit un-inferred
sublen-∈-just {PairU u _} (0 ∷ xs) (there x∈xs++) | inj₂ ()
-- GOOD: pattern on both, enabling implicit inference
sublen-∈-just {PairU u v} (0 ∷ xs) (there x∈xs++) | inj₂ x∈ = ⊥-elim (¬prefix∈map ¬0≡1 x∈)
```

### 6. Nested `where` Clauses Lose Implicit Scope

Implicit arguments from function signatures are NOT automatically available in deeply nested `where` clauses. Capture them explicitly:

```agda
eq-cond-q-helper {r} u₁ u₂ u₃ p q cond₁ cond₂ q≺p q' q'∈ q'≺q = helper ...
  where
  -- r is NOT in scope here without explicit capture
  helper ... = trans-SublenEq {r} q' ...  -- must annotate {r}
```

### 7. Top-Level Helpers Avoid Scope Issues

When a helper is stuck in a nested `where` clause with inference problems, move it to the top level with explicit arguments:

```agda
-- Moved from nested where to top-level
go-pos-shift-map : (k n : ℕ) (xs : List ℕ) (qs : List (List ℕ))
  → (suc n ∷ xs) ∈ List.map (suc k ∷_) qs → (n ∷ xs) ∈ List.map (k ∷_) qs
go-pos-shift-map k n xs [] ()
go-pos-shift-map k n xs (q ∷ qs) (here p) = subst ...
go-pos-shift-map k n xs (q ∷ qs) (there y∈) = there (go-pos-shift-map k n xs qs y∈)
```

### 8. `∈-++⁻` Requires Explicit Arguments

The `∈-++⁻` function sometimes needs explicit `{v = ...}` and the first list argument:

```agda
-- BAD: can't infer the split
¬[]∈ x∈ with ∈-++⁻ {v = []} x∈
-- GOOD: provide the left list explicitly
¬[]∈ x∈ with ∈-++⁻ {v = []} (List.map (0 ∷_) (pos u)) x∈
```

### 9. Asymmetry Proofs Use `with` + `go` Helper Pattern

When proving `¬ P` (negation), you can't pattern-match the argument directly. Use `with` to deconstruct the first argument, then define a `go` helper that takes the negated argument:

```agda
-- BAD: can't pattern match u₂≺u₁ (it's inside ¬)
≺-asym u₁≺u₂ u₂≺u₁ with ≺Lex-trichotomous p₁ p₂

-- GOOD: use with to deconstruct first arg, then go helper for second
≺-asym u₁≺u₂ u₂≺u₁ with open-exist u₁≺u₂
... | pw₁ , ≺p _ _ pw₁ (sublen< _ _ pw₁ mb₁) cond₁ = go u₂≺u₁
  where
    go : r ⊢ u₂ ≺ u₁ → ⊥
    go (≺ _ _ (pw₂ , ≺p _ _ pw₂ (sublen< _ _ pw₂ mb₂) cond₂))
      with ≺Lex-trichotomous pw₁ pw₂
```

The `open-exist` helper extracts the existential from `r ⊢ u ≺ v`:
```agda
open-exist : ∀ {r : RE} {u v : U r} → r ⊢ u ≺ v → Σ (List ℕ) (λ p → r , p ⊢ u ≺ v)
open-exist (≺ u v e) = e
```

### 10. `<-irrefl` Takes `refl` First, Then the Self-Loop Proof

In Agda 2.7.0.1, `<-irrefl` expects `m ≡ m` as the first argument and `m < m` as the second:

```agda
-- BAD: wrong argument order, type mismatch
<-irrefl mm
-- GOOD: refl first, self-loop second
<-irrefl refl mm
  where
    mm : mx < mx
    mm = <-trans mn nm
```

### 11. Explicit Implicit Bindings in Constructor Patterns

When a constructor has implicit `{x y}` and you need to reference them in a `where` clause, bind them explicitly in the pattern:

```agda
-- BAD: m and n not in scope in where clause
maybeNat<-asym (maybenat-just-just mn) (maybenat-just-just nm) = <-irrefl refl mm
  where mm : m < m  -- m, n not bound!
        mm = <-trans mn nm

-- GOOD: explicit bindings in pattern
maybeNat<-asym {just mx} {just my} (maybenat-just-just mn) (maybenat-just-just nm) = <-irrefl refl mm
  where
    mm : mx < mx
    mm = <-trans mn nm
```

### 12. Avoid Global Name Clashes in Patterns

Some names (`p₁`, `p₂`) may already exist in global scope from earlier definitions. Use distinct local names:

```agda
-- BAD: p₁ clashes with global p₁ : [] , ε ⇒ EmptyU
... | p₁ , ≺p _ _ p₁ ...
-- GOOD: distinct local names
... | pw₁ , ≺p _ _ pw₁ ...
```

### 13. `subst` Direction for Reversing Ordering Witnesses

When `pw₁ ≡ pw₂` and you have `mb₂ : MaybeNat< (sublen u₂ pw₂) (sublen u₁ pw₂)`, use `subst` with `sym` to align the variable:

```agda
-- To get MaybeNat< (sublen u₂ pw₁) (sublen u₁ pw₁) from mb₂:
subst (λ y → MaybeNat< (sublen u₂ y) (sublen u₁ y)) (sym pw₁≡pw₂) mb₂
```

### 14. `with` Rewrites Dependent Argument Types — Prefer Over `subst`

When a function is defined mutually with a helper (e.g., `pdU[l ● r, c] = pdU● (ε∈? l)`), `refl` proofs bridging the two are stuck because the mutual block prevents reduction. This makes explicit `subst` or `rewrite` approaches fail:

```agda
-- STUCK: pdU and pdU● are mutual, so refl doesn't reduce
pdU●-def : pdU[ l ● r ` loc , c ] ≡ pdU● (ε∈? l)
pdU●-def = refl      -- type-checks but doesn't reduce

-- FAILS: subst with this refl leaves ∈-map⁻ stuck on the subst term
●-decomp g' g'∈ with ε∈? l | it
... | no ¬ε∈l = helper (subst _ (sym it) g'∈)  -- STUCK
```

**The fix:** Use `with` **without** the `| it` pattern. Agda's dependent type-directed rewriting automatically rewrites the type of dependent arguments in each branch:

```agda
-- WORKS: Agda rewrites g'∈'s type to match the branch definition
●-decomp {l} {r} {loc} {c} g' g'∈ with ε∈? l
... | no ¬ε∈l = ●-decomp-no g' g'∈   -- g'∈ : g' ∈ List.map pdinstance-fst pdU[l,c]
... | yes ε∈l = ●-decomp-yes g' g'∈   -- g'∈ : g' ∈ List.map ... ++ concatmap-pdinstance-snd ...
```

No `subst` needed. No `| it` needed. Agda's with-mechanism does the type rewriting automatically. This works whenever the branches of the `with` scrutinee align definitionally with the target types — it's the preferred approach over manual `subst` for mutual-block barriers.

### 15. Extend Chains Instead of Pushing Through Injections

When a predicate quantifies over a chain/sequence of steps (e.g., `Chain p₀ p` with `chain-inj`), and you must show a composed step preserves the predicate, don't push the chain through the new injection (needs preservation/maximality lemmas). Instead **extend the chain**: `chain-inj (cons g prf chain)` is *definitionally* `pdi-inj g ∘ chain-inj chain`, so the existing evidence applies directly:

```agda
-- Goal: r ⊢ d→r (p→d (chain-inj chain u₀)) ≥ d→r (p→d (chain-inj chain v₀))
-- d-pres : ∀ (chain' : Chain p₀ d) ... → r ⊢ d→r (chain-inj chain' u₀) ≥ ...
-- Since chain-inj (cons g g∈ chain) ≡ p→d ∘ chain-inj chain definitionally:
ev chain u₀ max-u₀ v₀ u₀≥v₀ = d-pres (cons g g∈ chain) u₀ max-u₀ v₀ u₀≥v₀
```

### 16. Explicit Implicits for Data Constructors in Nested `where`

Agda 2.7 fails to infer implicit arguments of data constructors (e.g., `Chain`'s `cons {p₀} {p} {d} {c}`) inside doubly-nested `where` clauses, producing "Unsolved metas" at the constructor. Bind the enclosing function's implicits explicitly in the LHS AND supply the constructor's implicits explicitly:

```agda
-- FAILS: Unsolved metas at `cons`
ev chain u₀ max-u₀ v₀ u₀≥v₀ = d-pres (cons (pdinstance p→d s-ev) g∈ chain) ...

-- WORKS: bind {p₀} in LHS, give cons's implicits
ev {p₀} chain u₀ max-u₀ v₀ u₀≥v₀ = d-pres chain' u₀ max-u₀ v₀ u₀≥v₀
  where
    chain' : Chain p₀ d
    chain' = cons {p₀} {p} {d} {c} (pdinstance p→d s-ev) g∈ chain
```

### 14. Explicit Type Arguments for Helper Functions

When a helper takes implicit `{x y}` that Agda can't infer from context, provide them explicitly:

```agda
-- BAD: implicit args not inferred
maybeNat<-asym mb₁ mb₂
-- GOOD: explicit type arguments
maybeNat<-asym {sublen u₁ pw₁} {sublen u₂ pw₁} mb₁ mb₂
```

### 15. Implicit Pattern Variables and Dot-Implicit Patterns

When a constructor has implicit `{xs ys}` and a derived implicit `{zs}` (where `zs ≡ xs ++ ys`), you cannot reference `xs` and `ys` in the clause body unless you bind them in the pattern. Use `{xs} {ys}` to bind them, then write `.{zs}` for the dot pattern (Agda infers it from `xs` and `ys`):

```agda
-- Constructor: _●_⧺_ {xs} {ys} {zs} xs∈l ys∈r xs++ys≡zs → zs ∈⟦ l ● r ⟧

-- BAD: xs and ys not bound in pattern; can't use them in the body
inv-recons-fst ... w' (_●_⧺_ xs∈⟦p⟧ ys∈⟦r⟧ xs++ys≡w') = recons {xs} ...
  -- "Not in scope: xs"

-- GOOD: bind xs and ys, dot the derived w'
inv-recons-fst ... w' (_●_⧺_ {xs} {ys} .{w'} xs∈⟦p⟧ ys∈⟦r⟧ xs++ys≡w') = recons {xs} ...
```

The `.{w'}` syntax tells Agda: "infer w' from xs and ys (i.e., w' ≡ xs ++ ys) — don't try to match it against the context." Without the dot, Agda tries to unify `w'` with the surrounding implicit, which can cause "xs₁ != xs₂" errors because Agda can't see that the two are definitionally equal.

This also applies when changing a constructor from explicit to implicit arguments: every call site must remove the explicit arguments from the pattern, and any reference to those variables must use `{x}` to re-bind them.


## Common Patterns

### Transitivity Helper for Sublen Equalities

```agda
trans-SublenEq : ∀ {r} {u₁ u₂ : U r} (q : List ℕ)
  → sublen u₁ q ≡ sublen u₂ q
  → ∃[ n ] sublen u₂ q ≡ just n
  → ∃[ n ] sublen u₁ q ≡ just n
trans-SublenEq q eq (n , eq₂) = n , trans eq eq₂
```

### MaybeNat< Extractor

```agda
MaybeNat<-just-r : ∀ (x y : Maybe ℕ) → MaybeNat< x y → ∃[ z ] y ≡ just z
MaybeNat<-just-r nothing (just z) maybenat-nothing-just = z , refl
MaybeNat<-just-r (just x') (just y') (maybenat-just-just _<_) = y' , refl
```

### Asymmetry Helper for MaybeNat<

```agda
maybeNat<-asym : ∀ {x y : Maybe ℕ} → MaybeNat< x y → MaybeNat< y x → ⊥
maybeNat<-asym maybenat-nothing-just ()
maybeNat<-asym {just mx} {just my} (maybenat-just-just mn) (maybenat-just-just nm) = <-irrefl refl mm
  where
    mm : mx < mx
    mm = <-trans mn nm
```

### Trichotomy-Based Case Analysis on Witnesses

For proofs involving `≺` or `≼`, use `≺Lex-trichotomous` on the position witnesses:

```agda
-- Pattern: deconstruct both witnesses, analyze their lex-order relationship
≺-proof (≺ _ _ (p , ≺p _ _ p mb₁ cond₁)) (≺ _ _ (q , ≺p _ _ q mb₂ cond₂))
  with ≺Lex-trichotomous p q
... | inj₁ p≺q   = ... -- p comes before q
... | inj₂ (inj₁ q≺p) = ... -- q comes before p
... | inj₂ (inj₂ p≡q) = ... -- p equals q
```

### Negation Proof Template

```agda
theorem-asym : ∀ {a b} → a ≺ b → ¬ (b ≺ a)
theorem-asym ab ba with open-exist ab
... | w₁ , witness₁ = go ba
  where
    go : b ≺ a → ⊥
    go (≺ _ _ (w₂ , witness₂))
      with trichotomy w₁ w₂
    ... | case₁ = contradiction₁
    ... | case₂ = contradiction₂
    ... | case₃ = contradiction₃
```

## Verification

Always run `agda <filename>` after changes. Agda 2.7.0.1 reports:
- "Failed to solve the following constraints" → implicit inference problem
- "Unsolved metas at the following locations" → missing explicit arguments
- "Is empty: ... (stuck)" → absurd pattern can't reduce
- "Not in scope: X" → implicit not bound in pattern, or name clash
- "X !=< Y when checking expression Z has type W" → argument order or type mismatch (often `<-irrefl` or `subst`)

## Relevant Files

- `src/cgp/posix/Related.lagda.md` - Main proof file (≺-trans, ≺-asym, ≼-trans, ≼-refl, ≼-antisym)
- `src/cgp/ParseTree.lagda.md` - Defines `U r`, `pos`, `sublen`, `flat`, `RE`

### 16. Reasoning Syntax in Agda 2.7

Agda 2.7.0.1 has parsing issues with `begin_`/`≡⟨_⟩`/`_∎` reasoning syntax in certain contexts (especially inside `where` clauses and nested in `with` branches). Use `trans`/`cong`/`cong₂` chains instead:

```agda
-- BAD: reasoning syntax may fail to parse in Agda 2.7 inside where
len-eq = begin
  length (xs ++ ys)
  ≡⟨ sym (length-++ xs ys) ⟩
  length xs + length ys ∎

-- GOOD: trans/cong chain
len-eq = trans (sym (length-++ xs ys)) (trans (cong (_+ length ys) xs≡ys) (trans (cong (zero +_) ys≡[]) (sym (+-identityˡ (length ys)))))
```

For simple chains, use `trans` composition:
```agda
-- a ≡ b ≡ c ≡ d
trans eq1 (trans eq2 eq3)
```

When you need `cong f` on an equality, the direction matters:
- `cong f x≡y` gives `f x ≡ f y`
- `cong f (sym x≡y)` gives `f y ≡ f x`

For `subst`, the predicate must be a lambda: `subst (λ x → P x) eq proof`.

### 17. Passing Telescope Variables to Sub-Lemma `with` Abstraction

Agda 2.7 cannot use `with` on expressions containing parent telescope variables. Solution: define the helper at the **top level** (outside `where`/`mutual`) with telescope variables as **explicit arguments**, then call it from within the `where` clause.

Reference pattern from `greedy/ExtendedOrder.lagda.md` (`dist-right-ex>-maybe`):

```agda
-- Top-level helper takes telescope vars as explicit arguments
dist-right-ex>-maybe : ∀ { l s r : RE } {loc₁ loc₂ : ℕ } { c : Char}
  → ( pdi : PDInstance ( s ● r ` loc₂ ) c )
  → ( pdis : List (PDInstance ( s ● r ` loc₂ ) c ) )
  → Ex>-maybe (pdinstance-right pdi) (head (List.map pdinstance-right pdis))
  → Ex>-maybe (pdinstance-dist (pdinstance-right pdi))
    (head (List.map pdinstance-dist (List.map pdinstance-right pdis)))
dist-right-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi [] ex>-nothing = ex>-nothing
dist-right-ex>-maybe {l} {s} {r} {loc₁} {loc₂} {c} pdi₁ (pdi₂ ∷ pdis) (ex>-just ev) = ex>-just ev->
  where
    ev-> : (u₁ u₂ : U ((l + s ` loc₁) ● r ` loc₂))
      → Recons u₁ (pdinstance-dist (pdinstance-right pdi₁))
      → Recons u₂ (pdinstance-dist (pdinstance-right pdi₂))
      → ((l + s ` loc₁) ● r ` loc₂) ⊢ u₁ > u₂
    ev-> (PairU (RightU v₁) v₂) (PairU (RightU v₁') v₂') recons₁ recons₂
      with right-pair-v₁-v₂>right-pair-v₁'-v₂'
    ... | choice-rr ev = ev
      where
        right-pair-v₁-v₂>right-pair-v₁'-v₂' = ...
```

Key rule: if a `where` clause needs to `with` on an expression using a variable from the parent telescope, **move the helper out** and pass the variable as an explicit argument.

### 18. `≥-Max` Proof for Concatenation (`●`)

When proving `≥-Max w (PairU u₁ u₂)` for `l ● r`, the `dom` proof needs to show `PairU u₁ u₂ ≥ v` for all `v` with same word. Use `>-trichotomy u₁ v₁` to split into three cases:
- `u₁ > v₁`: lift via `seq₁` (may need explicit length proofs)
- `u₁ ≡ v₁`: use `cong₂ PairU u₁≡v₁ (μ-u₂ v₂ flat-v₂≡ys)` with `++-cancelˡ` to derive `flat-v₂≡ys`
- `v₁ > u₁`: contradiction (requires well-foundedness argument)

```agda
cat-dom-help {l} {r} {loc} {w} {xs} {ys} {u₁} {u₂} v₁ v₂ flat-v≡w xs++ys≡w flat-u₁≡xs flat-u₂≡ys max-u₁ max-u₂
  with >-trichotomy u₁ v₁
... | inj₁ u₁>v₁ = inj₁ (lift-fst> u₁>v₁)
... | inj₂ (inj₂ u₁≡v₁) = inj₂ (cong₂ PairU u₁≡v₁ (μ-u₂ v₂ flat-v₂≡ys))
  where
    μ-u₂ (≥-max _ _ _ μ) = μ
    flat-v≡xs++ys = trans (sym flat-v≡w) (sym xs++ys≡w)
    flat-v₂≡ys rewrite ++-cancelˡ proj₁ (flat v₁) xs ys flat-v≡xs++ys | u₁≡v₁ = flat-u₂≡ys
... | inj₂ (inj₁ v₁>u₁) = ⊥-elim (v₁>u₁-contradiction v₁>u₁)
```

The `++-cancelˡ` lemma: `xs₁ ++ ys₁ ≡ xs₂ ++ ys₂ → xs₁ ≡ xs₂ → ys₁ ≡ ys₂`. Here it cancels the common prefix after rewriting `flat-v₁ ≡ flat-u₁` with `u₁≡v₁`.

### 19. `with` on Function Calls with `in` Clause

When a `with` clause patterns on a function call (e.g., `pdU[ l , c ]`), Agda 2.7 needs an `in` clause to generate the definitional equality for rewriting:

```agda
-- BAD: without `in`, the function call is not reduced
f ... with pdU[ l , c ]
... | x ∷ xs = ... -- pdU[ l , c ] still appears as a stuck term

-- GOOD: `in eq` gives x ∷ xs ≡ pdU[ l , c ], enabling rewriting
f ... with pdU[ l , c ] in eq
... | x ∷ xs rewrite eq = ...
```

The `in` clause is essential when the target type contains the function call that was scrutinized. Without it, Agda can't see that the matched pattern equals the original call, causing type mismatches in proofs that reference the function.

### 20. Bridging `recons` Word Mismatch with `≡-Reasoning` and `rewrite`

When extracting a word from a `recons` proof (`w'∈p : w' ∈⟦ p ⟧`), the word `w'` may differ from the expected word `w` in the goal. The bridge is:

1. **Pattern-match the `pdinstance` constructor** to expose `p`, `inj`, `sound-ev`.
2. **Prove `c ∷ w' ≡ c ∷ w`** using `sound-ev` and `flat∘unflat`:
   ```agda
   c∷w'≡c∷w = begin
     c ∷ w'
    ≡⟨ cong (λ x → c ∷ proj₁ x) (sym (flat∘unflat {p} w'∈p)) ⟩
     c ∷ proj₁ (flat (unflat w'∈p))
    ≡⟨ sym (sound-ev (unflat w'∈p)) ⟩
     proj₁ (flat (inj (unflat w'∈p)))
    ≡⟨ cong proj₁ inj∘unflat≡u ⟩
     proj₁ (flat (unflat c∷w∈⟦l⟧))
    ≡⟨ cong proj₁ (flat∘unflat {l} c∷w∈⟦l⟧) ⟩
     c ∷ w
   ∎
   ```
3. **Use `∷-injective`** to get `w' ≡ w`.
4. **Rewrite the membership proof**: `w∈p rewrite sym w'≡w = w'∈p`.

This avoids `subst` and works because `rewrite` modifies the goal type of the current clause.

### 21. `≡-Reasoning` in `where` Clauses for `just-injective` Chains

When proving `pdi ≡ pdinstance-left pdi₀` via `just-injective`, build the intermediate equality chain in a `where` helper using `≡-Reasoning` and `rewrite` to bridge stuck terms. This avoids pushing through multiple layers of `first-inhibit-++-just-left-pres` and lets Agda handle the definitional equalities from `with` abstractions:

```agda
just-left-pdi₀≡just-pdi : just (pdinstance-left pdi₀) ≡ just pdi
just-left-pdi₀≡just-pdi =
  begin
    just (pdinstance-left pdi₀)
   ≡⟨ sym eq-left+right ⟩
    first-inhabit (l + r ` loc) c w (pdU[ l + r ` loc , c ])
   ≡⟨⟩
    first-inhabit ... (List.map pdinstance-left pdU[l,c] ++ List.map pdinstance-right pdU[r,c])
   ≡⟨ cong _ pdu-lc-eq ⟩
    first-inhabit-cons ...
   ≡⟨ first-inhabit-cw-pdu-lr-c≡just-pdi ⟩
    just pdi
  ∎
pdi≡left = just-injective (sym just-left-pdi₀≡just-pdi)
```

### 22. `_ ∷ _` Pattern in Type Annotations Blocks Type Checking

Using `_ ∷ _` as a type annotation (e.g., `pdu-lc-eq : pdU[ l , c ] ≡ _ ∷ _`) causes Agda 2.7 to refuse to type-check the rest of the lemma body — it cannot construct a value matching the anonymous pattern in the return type. Always use explicit variable names:

```agda
-- BAD: _ ∷ _ blocks type checking
f ... (pdu-lc-eq : pdU[ l , c ] ≡ _ ∷ _) ...

-- GOOD: explicit head and tail
f ... (pdu-lc-eq : pdU[ l , c ] ≡ head-pdi ∷ tail-pdis) ...
```

### 23. Full Dot-Patterns for `recons` Destructuring

The `Recons` constructor carries many implicit arguments. When pattern matching, bind ALL implicits explicitly — including dot-patters for derived ones — or Agda 2.7 cannot infer the types:

```agda
-- Constructor: recons {p} {r} {c} {w} {inj} {sound-ev} u (w∈p , inj∘unflat≡u)

-- BAD: insufficient implicit binding
recons-w∈src (pdinstance {p} inj sound-ev) (recons u (w∈p , inj≡u)) = ...

-- GOOD: full explicit binding with dot-patterns for derived implicits
recons-w∈src {l} {c} {w} {c∷w∈⟦l⟧} (pdinstance {p} .{l} .{c} inj sound-ev)
  (recons .{p} .{l} .{c} {w'} .{inj} .{sound-ev} .(unflat {l} {(c ∷ w)} c∷w∈⟦l⟧)
    (w'∈p , inj∘unflatw'∈p≡unflat-c∷w∈⟦l⟧)) = ...
```

### 24. Return Existentials from `Any` Structural Induction

When doing structural induction on `Any P xs`, the induction hypothesis must return a concrete witness, not an equality with an anonymous `_`:

```agda
-- BAD: can't thread the witness through recursive calls
Any→just ... → first-inhabit l c w pdis ≡ just _

-- GOOD: existential carries the concrete pdi
Any→just ... → ∃[ pdi ] (pdi ∈ pdis) × first-inhabit l c w pdis ≡ just pdi
```

This lets the `there` case thread the recursive result: `proj₁ ind-hyp , there (proj₁ (proj₂ ind-hyp)) , proj₂ (proj₂ ind-hyp)`.

### 25. Prefer Structural Induction over `with` + Abstraction for `first-inhabit`

`first-inhabit` is a mutual function that abstracts through `first-inhabit-cons` via a `with (w ∈?⟦ pdi-src pdi' ⟧)` clause. This makes `refl` proofs and `rewrite` approaches fail because the abstraction barrier prevents definitional reduction. Instead, define a top-level structural induction lemma on `Any` that handles the `Dec` case analysis explicitly:

```agda
-- Top-level lemma: structural induction on Any Pdis
first-inhabit-++-just-left-any ... Any (Recons ...) pdisˡ ... with w ∈?⟦ p ⟧
... | no ¬w∈p = first-inhabit-++-just-left-any ... pdisˡ pdisʳ ar  -- recursive on tail
... | yes w∈p = pdi₀ , refl , refl                                  -- head accepts
```

Then call it once in the main proof, avoiding multiple `with` clauses that create nested abstractions.

### 26. Explicit Type Parameters for `pdinstance-left`/`pdinstance-right`

These functions carry implicit `{l} {r} {loc}` arguments that Agda 2.7 often fails to infer inside `List.map` or nested applications. Provide them explicitly:

```agda
-- BAD: implicits not inferred
List.map pdinstance-left xs

-- GOOD: explicit parameters
List.map (λ x → pdinstance-left {l} {r} {loc} x) xs
```

### 27. Know When a Lemma Is Unprovable

Some lemma signatures cannot be proven with the available evidence. The `first-inhibit-++-just-left-pdi-there-no` lemma attempted to decompose a combined result without knowing the head of `tail-pdis` — this is structurally impossible because there is no induction hypothesis that relates the combined list to the tail alone. In such cases, comment out the lemma and look for an alternative approach (e.g., structural induction on `Any` directly).

### 28. Explicit Implicits at Call Site for Opaque `parseAll` Terms

`parseAll[ r , w ]` is opaque in Agda 2.7 — the constraint solver decomposes it into `foldr _++_ [] (List.map buildU (pdUMany-aux ...))` and tries to unify across all uses simultaneously, causing "Failed to solve the following constraints" errors. When a function returns a type indexed by `parseAll[ r , w ]` (e.g., `>-sorted parseAll[ r , w ]` or `All _ parseAll[ r , w ]`), Agda may fail to infer the implicit `{r} {w}` from context inside nested `where` clauses. Provide them explicitly at the call site:

```agda
-- BAD: {r} {w} not inferred, constraint solver decomposes parseAll
core (parseAll[ r , w ]) refl parseAll-is-greedy parseAll-sound

-- GOOD: explicit implicits anchor the constraint solver
core (parseAll[ r , w ]) refl (parseAll-is-greedy {r} {w}) parseAll-sound
```

This prevents the constraint solver from spinning on unification of decomposed `parseAll` terms.

### 29. Transport Lemma for `parseAll` Word Equality

When you need to transport an `Any` proof across a word equality `w₁ ≡ w₂` inside `parseAll`, define a top-level transport lemma that uses `rewrite`:

```agda
parseAll-subst : ∀ {r : RE} {w₁ w₂ : List Char} {v : U r}
  → w₁ ≡ w₂
  → Any (_≡_ v) parseAll[ r , w₁ ]
  → Any (_≡_ v) parseAll[ r , w₂ ]
parseAll-subst {r} {w₁} {w₂} {v} w₁≡w₂ any
  rewrite w₁≡w₂ = any
```

This works because `rewrite` operates on the goal type directly, avoiding the constraint solver decomposition that `subst` triggers inside `parseAll`.

### 30. Avoid `parseAll` in Type Signatures — Use Explicit Equality Parameter

When `parseAll[ r , w ]` appears in a type signature, Agda 2.7's constraint solver tries to decompose it simultaneously across all call sites. Instead, pass the list as an explicit parameter and thread an equality proof:

```agda
-- BAD: parseAll in type signature triggers constraint decomposition
core : >-sorted parseAll[ r , w ] → All _ parseAll[ r , w ] → ...

-- GOOD: explicit list + equality parameter
core : (us : List (U r))
  → parseAll[ r , w ] ≡ us
  → >-sorted us
  → All _ us
  → ...
```

Call with `core (parseAll[ r , w ]) refl`. The `refl` anchors the equality without triggering decomposition.

### 31. Helper Lemmas Outside `where` Avoid Constraint Solver Issues

When a helper function uses `parseAll[ r , w ]` in its body or type, defining it inside a `where` clause causes the constraint solver to decompose `parseAll` and try to unify with other uses in the same scope. Define the helper at the top level (outside `where`) with explicit `{r} {w}` parameters:

```agda
-- BAD: inside where, parseAll gets decomposed and unified globally
us'-complete u us' eq v v-flat with parseAll-complete v
  ... | wv , any-v = subst (λ w' → Any _ parseAll[ r , w' ]) v-flat any-v

-- GOOD: top-level lemma, explicit implicits, rewrite avoids decomposition
parseAll-subst : ∀ {r : RE} {w₁ w₂ : List Char} {v : U r}
  → w₁ ≡ w₂ → Any (_≡_ v) parseAll[ r , w₁ ] → Any (_≡_ v) parseAll[ r , w₂ ]
parseAll-subst w₁≡w₂ any rewrite w₁≡w₂ = any
```

### 32. `parseAll-complete` Returns Existential — Use `with` to Extract

`parseAll-complete v` returns `∃[ w' ] Any (_≡_ v) parseAll[ r , w' ]`. To use the `Any` proof, pattern-match with `with`:

```agda
f v v-flat with parseAll-complete v
... | wv , any-v = ...
```

The variable `wv` is definitionally `proj₁ (flat v)`. To transport `any-v` to the expected word `w`, combine with `v-flat : proj₁ (flat v) ≡ w` using a transport lemma or `subst`.
