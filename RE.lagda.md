# Certified Bitcoded Greedy Parsing for Regular Expression

## Table of content

1. RE.lagda.md : definitions of RE, non problematic regular expression, nullability tests and properties
2. Word.lagda.md : definitions of word, and w ∈ re relation
3. ParseTree.lagda.md : definitions of parse trees, flattening and unflattening operations, and the properties
4. empty/AllEmptyParseTree.lagda.md : definitions of generating all empty parse trees (mkAllEmptyU) and its soundness and completeness, sub properties such as Flat-[] and flat-[]
5. Different partial derivative implementation for different matching policies. 
  1. Antimirov 
    1. antimirov/PartialDerivative.lagda.md : definitions of partial derivative based on the original Antimriov's; partial derivative with injection functions ; its soundess and compleness properties 
  1. Greedy Matching policy 
    1. greedy/GreedyPartialDerivative.lagda.md definitions of partial derivative implementing the greedy matching by adapting original Antimriov's partial derivative with injection functions ; its soundess and compleness properties
    1. greedy/Greedy.lagda.md : definitions of greedy order.
    1. greedy/ExtendedGreedy.lagmda.md : 

## Why antimirov's orginal partial derivative does not give us greedy matching policy nor POSIX 



## Bibliography

[1] Certified Bit-Coded Regular Expression Parsing, Rodrigo Ribeiro and André Du Bois
[2] Kenny's Draft report (posix-bitcode/main.tex)
[3] Valentin M. Antimirov. Partial derivatives of regular expressions and finite automa-
ton constructions. Theoretical Computer Science, 155(2):291–319, 1996.
[4] Alain Frisch and Luca Cardelli. Greedy regular expression matching. In Proc. of ICALP’04, pages 618– 629. Spinger-Verlag, 2004.


```agda
module cgp.RE where

open import cgp.Utils using ( ¬∷≡[] )

import Data.Char as Char
open Char using (Char)

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; concatMap ; _∷ʳ_  )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-conicalˡ ; ++-conicalʳ )


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)


import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)

import Relation.Nullary as Nullary 
import Relation.Nullary.Negation using (contradiction; contraposition)
open Nullary using (¬_)

import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no )
```


## Regular Expression and Non-problematic regular expression 


### Definition 1 : regular expression

We use the following EBNF to denote regular expression

 r ::= ϕ | ε | ℓ | r ● r  | r + r | r*


where ϕ denotes the empty regular expression which accepts no input,
ε denotes the expression that accepts only the empty sequence,  ℓ denotes a literal.
r ● r denotes a concatenation,  r + r denotes a choice, r* denotes the kleene's star.


### Definition 2 : (non-) nullable regular expressions

The nullablilty of a regular expression is defined inductively

(null-ε) ε ∈ ε     (null-*)  ε ∈ r*


          ε ∈ r₁  ε ∈ r₂
(null-●) --------------
          ε ∈ r₁ ● r₂   

             ε ∈ r₁                      ε ∈ r₂ 
(null-left) ------------   (null-right)---------------
            ε ∈ r₁ + r₂                 ε ∈ r₁ + r₂ 

For the ease of establishing the correctness proof,
unlike [2], we "expand" (null-left) and (null-right) rules into

          ε ∈ r₁  ε ∈ r₂                 ε ∈ r₁ ε ∉ r₂                       ε ∈ r₂  ε ∉ r₁ 
(null-+) ---------------   (null-left*) ----------------        (null-right*)---------------
           ε ∈ r₁ + r₂                   ε ∈ r₁ + r₂                            ε ∈ r₁ + r₂ 


The non-nullability 9of a regular expression is defined inductively

(non-null-ϕ)  ε ∉ ϕ     (non-null-ℓ) ε ∉ ℓ

                   ε ∉ r₁
(non-null-fst) ---------------
                 ε ∉ r₁ ● r₂

                   ε ∉ r₂ 
(non-null-snd) ---------------
                ε ∉ r₁ ● r₂ 

               ε ∉ r₁   ε ∉ r₂ 
(non-null-+)  -----------------
                ε ∉ r₁ + r₂ 

### Definition 3 : (non-) problematic regular expression (Definition 6 from [2])

We say a regular expression r is problematic if there exists some sub expression t* in r such that ε∈t.
We say a regular expression r is non problematic if there exists no sub expression t* in r such that ε∈t.


The non-problematic regular expression, nullability and non-nullability
can be implemented using the following mutually recursive data types in Agda.

> KL: new stuff: added AST location to RE,
> Greedy pd algo requires AST source locations to be annotated to r in postorder traversal.
> as an implication the AST locations are appearing in membership evidence and parse tree U because of the indexed type?! is that a problem? it seems not.

```agda
data RE : Set
data ε∉ : RE → Set 
data ε∈ : RE → Set

data RE where
  ϕ : RE
  ε : RE
  $_`_ : Char → ℕ → RE
  _●_`_ : RE → RE → ℕ → RE
  _+_`_ : RE → RE → ℕ → RE
  _*_`_  : ∀ ( r : RE )  → ( ε∉ r ) → ℕ → RE

data ε∉ where
  ε∉ϕ   : ε∉ ϕ 
  ε∉$   : ∀ { c : Char} { loc : ℕ } → ε∉ ($ c ` loc )
  ε∉fst : ∀ { l r : RE } { loc : ℕ } → ( ε∉ l ) → ( ε∉ (l ● r ` loc) )
  ε∉snd : ∀ { l r : RE } { loc : ℕ } → ( ε∉ r ) → ( ε∉ (l ● r ` loc ) )
  ε∉_+_ : ∀ { l r : RE } { loc : ℕ } → ( ε∉ l ) → ( ε∉ r ) → ( ε∉ (l + r ` loc) )

data ε∈ where 
  ε∈ε   : ε∈ ε
  ε∈_●_ : ∀ { l r : RE } { loc : ℕ } → ( ε∈ l ) → ( ε∈ r ) → ( ε∈ (l ● r ` loc) )
  ε∈_+_ : ∀ { l r : RE } { loc : ℕ } → ( ε∈ l ) → ( ε∈ r ) → ( ε∈ (l + r ` loc ) )
  ε∈_<+_ : ∀ { l r : RE } { loc : ℕ } → ( ε∈ l ) → ( ε∉ r ) → ( ε∈ (l + r ` loc) ) -- can't replace  ε∉ r with ¬ (ε∈ r ), agda complains ε∈ is not strictly positive.
  ε∈_+>_ : ∀ { l r : RE } { loc : ℕ } → ( ε∉ l ) → ( ε∈ r ) → ( ε∈ (l + r ` loc) ) 
  ε∈*   : ∀ { r : RE } { loc : ℕ } { nε : ε∉ r } → ( ε∈ (r * nε ` loc )) -- KL: do we need to distinguish whether r is nullable?

```


### Lemma 4 : non-nullability implies negation of nullability and the converse also holds

```agda
-- → direction
ε∉r→¬ε∈r : ∀ { r : RE } → (ε∉ r) → ( ¬ (ε∈ r) )
ε∉r→¬ε∈r { ϕ } = λ x → λ()
ε∉r→¬ε∈r { ε } = λ()
ε∉r→¬ε∈r { $ c ` loc } = λ x → λ()
ε∉r→¬ε∈r { s ● t ` loc } (ε∉fst ε∉s) (ε∈ ε∈s ● ε∈t ) = (ε∉r→¬ε∈r ε∉s) ε∈s
ε∉r→¬ε∈r { s ● t ` loc } (ε∉snd ε∉t) (ε∈ ε∈s ● ε∈t ) = (ε∉r→¬ε∈r ε∉t) ε∈t
ε∉r→¬ε∈r { s + t ` loc } (ε∉ ε∉s + ε∉t) (ε∈ ε∈s + ε∈t ) = (ε∉r→¬ε∈r ε∉s) ε∈s
ε∉r→¬ε∈r { s + t ` loc } (ε∉ ε∉s + ε∉t) (ε∈ ε∈s <+ _ )  = (ε∉r→¬ε∈r ε∉s) ε∈s
ε∉r→¬ε∈r { s + t ` loc } (ε∉ ε∉s + ε∉t) (ε∈ _ +> ε∈t ) = (ε∉r→¬ε∈r ε∉t) ε∈t
ε∉r→¬ε∈r { s * ε∉s ` loc } = λ()

-- decidability of ε∉ r; which is required for the other direction 
ε∉? : ∀ ( r : RE ) → Dec (ε∉ r)
ε∉? ϕ               = yes ε∉ϕ
ε∉? ε               = no   λ { ε∉ε → (ε∉r→¬ε∈r ε∉ε)  ε∈ε }
ε∉? ( $ c ` loc )   = yes ε∉$
ε∉? ( r * _ ` loc ) = no   λ { ε∉r* → (ε∉r→¬ε∈r ε∉r*) ε∈* }
ε∉? ( l ● r ` loc ) with ε∉? l | ε∉? r
...                     | yes pl | _     = yes (ε∉fst pl)
...                     | no _  | yes pr = yes (ε∉snd pr)
...                     | no npl | no npr = no (λ { (ε∉fst ε∉l) → npl ε∉l  ; (ε∉snd ε∉r) → npr ε∉r })
ε∉? ( l + r ` loc ) with ε∉? l | ε∉? r
...                     | yes pl | yes pr = yes (ε∉ pl + pr)
...                     | no npl | yes pr = no  λ { (ε∉ ε∉l + ε∉r) → npl ε∉l }
...                     | yes pl | no npr = no  λ { (ε∉ ε∉l + ε∉r) → npr ε∉r }
...                     | no npl | no npr = no  λ { (ε∉ ε∉l + ε∉r) → npl ε∉l } 

-- contrapositive of the ← direction 
¬ε∉r→ε∈r : ∀ { r : RE } → ¬ (ε∉ r) → (ε∈ r)
¬ε∉r→ε∈r { ϕ } ¬ε∉r             = Nullary.contradiction ε∉ϕ ¬ε∉r
¬ε∉r→ε∈r { ε } _                 = ε∈ε
¬ε∉r→ε∈r { $ c ` loc } ¬ε∉r     = Nullary.contradiction ε∉$ ¬ε∉r
¬ε∉r→ε∈r { l ● r ` loc } ¬ε∉l●r with ε∉? l   | ε∉? r
...                                  | yes ε∉l | _        = Nullary.contradiction (ε∉fst ε∉l) ¬ε∉l●r
...                                  | _        | yes ε∉r = Nullary.contradiction (ε∉snd ε∉r) ¬ε∉l●r
...                                  | no ¬ε∉l | no ¬ε∉r = ε∈ (¬ε∉r→ε∈r ¬ε∉l) ● (¬ε∉r→ε∈r ¬ε∉r)
¬ε∉r→ε∈r { l + r ` loc } ¬ε∉l+r with ε∉? l   | ε∉? r
...                                  | yes ε∉l | yes ε∉r  = Nullary.contradiction (ε∉ ε∉l + ε∉r) ¬ε∉l+r
...                                  | no ¬ε∉l | yes ε∉r  = ε∈ (¬ε∉r→ε∈r ¬ε∉l) <+ ε∉r
...                                  | yes ε∉l | no ¬ε∉r  = ε∈ ε∉l +> (¬ε∉r→ε∈r ¬ε∉r)
...                                  | no ¬ε∉l | no ¬ε∉r  = ε∈ (¬ε∉r→ε∈r ¬ε∉l)  + (¬ε∉r→ε∈r ¬ε∉r)
¬ε∉r→ε∈r { r * nε ` loc } _     = ε∈*



-- this direction can't be proven? double check
-- KL: updated: it is proven now. 
¬ε∈r→ε∉r : ∀ { r : RE } → ( ¬ (ε∈ r) ) → (ε∉ r)
¬ε∈r→ε∉r { ϕ } = λ x → ε∉ϕ 
¬ε∈r→ε∉r { ε } = λ x → Nullary.contradiction ε∈ε x
¬ε∈r→ε∉r { $ c ` loc } = λ ¬ε∈$c → ε∉$
¬ε∈r→ε∉r { r * nε ` loc } = λ x → Nullary.contradiction ε∈* x
¬ε∈r→ε∉r { s + t ` loc } ¬ε∈s+t with ε∉? s   | ε∉? t
...                                  | yes ε∉s | yes ε∉t =  ε∉ ε∉s + ε∉t
...                                  | no ¬ε∉s | yes ε∉t =  Nullary.contradiction (ε∈ (¬ε∉r→ε∈r ¬ε∉s) <+ ε∉t ) ¬ε∈s+t
...                                  | yes ε∉s | no ¬ε∉t =  Nullary.contradiction (ε∈ ε∉s +> (¬ε∉r→ε∈r ¬ε∉t) ) ¬ε∈s+t
...                                  | no ¬ε∉s | no ¬ε∉t =   Nullary.contradiction (ε∈ (¬ε∉r→ε∈r ¬ε∉s) + (¬ε∉r→ε∈r ¬ε∉t) ) ¬ε∈s+t
¬ε∈r→ε∉r { s ● t ` loc }  ¬ε∈s●t with ε∉? s   | ε∉? t
...                                  | yes ε∉s  | _        =  ε∉fst ε∉s
...                                  | _         | yes ε∉t =  ε∉snd ε∉t
...                                  | no ¬ε∉s  | no  ¬ε∉t = Nullary.contradiction (ε∈ (¬ε∉r→ε∈r ¬ε∉s) ● (¬ε∉r→ε∈r ¬ε∉t) ) ¬ε∈s●t


-- decidability of ε∈ r as a collary of the ← direction 
-- KL: this is proven now. 

ε∈? : ∀ ( r : RE ) → Dec (ε∈ r)
ε∈? ϕ              =  no (ε∉r→¬ε∈r ε∉ϕ)
ε∈? ε              =  yes (ε∈ε)
ε∈? ($ c ` _)      =  no (ε∉r→¬ε∈r ε∉$)
ε∈? (r * _ ` _ )   =  yes (ε∈*)
ε∈? (l ● r ` loc ) with ε∈? l   | ε∈? r
...                    | yes ε∈l | yes ε∈r   = yes (ε∈ ε∈l  ● ε∈r)
...                    | no ¬ε∈l | _         = no λ { (ε∈ ε∈l ● ε∈r ) →  ¬ε∈l ε∈l}
...                    | _        | no ¬ε∈r  = no λ { (ε∈ ε∈l ● ε∈r ) →  ¬ε∈r ε∈r}
ε∈? (l + r ` loc ) with ε∈? l   | ε∈? r
...                    | yes ε∈l | yes ε∈r  = yes (ε∈ ε∈l + ε∈r )
...                    | no ¬ε∈l | no ¬ε∈r  = no λ { (ε∈ ε∈l + ε∈r ) → ¬ε∈l ε∈l
                                                    ; (ε∈ ε∈l <+ _   ) → ¬ε∈l ε∈l
                                                    ; (ε∈ _   +> ε∈r ) → ¬ε∈r ε∈r }
...                    | yes ε∈l | no ¬ε∈r  = yes (ε∈ ε∈l <+  ¬ε∈r→ε∉r ¬ε∈r )
...                    | no ¬ε∈l | yes ε∈r  = yes (ε∈ ¬ε∈r→ε∉r ¬ε∈l +> ε∈r )


```


More sub lemmas required by sub lemmas in ParseTree.lagda.md 

```agda
inv-ε∉l+r : ∀ { l r : RE } { loc : ℕ } → ε∉ (l + r ` loc) → ( ε∉ l ) × (ε∉ r )
inv-ε∉l+r {l} {r} {loc} (ε∉ ε∉l + ε∉r ) =  ε∉l , ε∉r

inv-¬ε∈l+r : ∀ { l r : RE } { loc : ℕ } → ¬ ( ε∈ (l + r ` loc) ) → ( ¬ ε∈ l ) × ( ¬ ε∈ r )
inv-¬ε∈l+r {l} {r} {loc} ¬ε∈l+r =
  let ε∉l+r    = ¬ε∈r→ε∉r ¬ε∈l+r
      ε∉l×ε∉r = inv-ε∉l+r ε∉l+r
      ε∉l      = proj₁ ε∉l×ε∉r
      ε∉r      = proj₂ ε∉l×ε∉r
  in ( ε∉r→¬ε∈r ε∉l ) , ( ε∉r→¬ε∈r ε∉r )




```


#### ϕ testing and decidability

```agda
data ϕ≡ :  RE → Set where 
  ϕ≡ϕ   : ϕ≡ ϕ
  ϕ≡_+_ : ∀ { l r : RE } { loc : ℕ }
    → ϕ≡ l
    → ϕ≡ r
    ---------------------
    → ϕ≡ ( l + r ` loc )
  ϕ≡fst  : ∀ { l r : RE } { loc : ℕ }
    → ϕ≡ l
    ----------------------
    → ϕ≡ ( l ● r ` loc )
  ϕ≡snd  : ∀ { l r : RE } { loc : ℕ }
    → ϕ≡ r
    ----------------------
    → ϕ≡ ( l ● r ` loc )


ϕ≡? : ∀ ( r : RE ) → Dec (ϕ≡ r)
ϕ≡? ϕ = yes ϕ≡ϕ
ϕ≡? ε = no λ()
ϕ≡? ($ c ` loc) = no λ()
ϕ≡? (l * _ ` _) = no λ()
ϕ≡? (l + r ` loc) with ϕ≡? l | ϕ≡? r
... | yes ϕ≡l | yes ϕ≡r = yes (ϕ≡ ϕ≡l + ϕ≡r)
... | no ¬ϕ≡l | _       = no (λ { ( ϕ≡ ϕ≡l + ϕ≡r ) → ¬ϕ≡l ϕ≡l } )
... | yes ϕ≡l | no ¬ϕ≡r = no (λ { ( ϕ≡ ϕ≡l + ϕ≡r ) → ¬ϕ≡r ϕ≡r } )
ϕ≡? (l ● r ` loc) with ϕ≡? l | ϕ≡? r
... | yes ϕ≡l | _       = yes (ϕ≡fst ϕ≡l)
... | no ¬ϕ≡l | yes ϕ≡r = yes (ϕ≡snd ϕ≡r)
... | no ¬ϕ≡l | no ¬ϕ≡r = no (λ { ( ϕ≡fst ϕ≡l ) → ¬ϕ≡l ϕ≡l
                                ; ( ϕ≡snd ϕ≡r ) → ¬ϕ≡r ϕ≡r } )
                                


data ϕ≢ :  RE → Set where 
  ϕ≢ε   : ϕ≢ ε
  ϕ≢$   : ∀ { c : Char } { loc : ℕ }
    -----------------------------------
    → ϕ≢ ($ c ` loc)
    
  ϕ≢left : ∀ { l r : RE } { loc : ℕ }
    → ϕ≢ l
    → ϕ≡ r
    ---------------------
    → ϕ≢ ( l + r ` loc )

  ϕ≢right : ∀ { l r : RE } { loc : ℕ }
    → ϕ≡ l 
    → ϕ≢ r
    ---------------------
    → ϕ≢ ( l + r ` loc )

  ϕ≢left-right : ∀ { l r : RE } { loc : ℕ }
    → ϕ≢ l
    → ϕ≢ r    
    ---------------------
    → ϕ≢ ( l + r ` loc )

  ϕ≢_●_  : ∀ { l r : RE } { loc : ℕ }
    → ϕ≢ l
    → ϕ≢ r    
    ----------------------
    → ϕ≢ ( l ● r ` loc )
  ϕ≢*  : ∀ { l : RE } {ε∉l : ε∉ l} { loc : ℕ }
    ----------------------
    → ϕ≢ ( l * ε∉l ` loc )


¬ϕ≡r→ϕ≢r : ∀ { r : RE }
  → ( ¬ ϕ≡ r )
  ----------------
  → ϕ≢ r
¬ϕ≡r→ϕ≢r {ϕ} ¬ϕ≡ϕ = Nullary.contradiction ϕ≡ϕ ¬ϕ≡ϕ
¬ϕ≡r→ϕ≢r {ε} _    = ϕ≢ε
¬ϕ≡r→ϕ≢r {$ c ` loc} _ = ϕ≢$
¬ϕ≡r→ϕ≢r {l * ε∉l ` loc} _ = ϕ≢*
¬ϕ≡r→ϕ≢r {l ● s ` loc} ¬ϕ≡l●s
  with ϕ≡? l  | ϕ≡? s
... | yes ϕ≡l | _       = Nullary.contradiction (ϕ≡fst ϕ≡l) ¬ϕ≡l●s
... | _       | yes ϕ≡s = Nullary.contradiction (ϕ≡snd ϕ≡s) ¬ϕ≡l●s
... | no ¬ϕ≡l | no ¬ϕ≡s = ϕ≢ (¬ϕ≡r→ϕ≢r ¬ϕ≡l) ● (¬ϕ≡r→ϕ≢r ¬ϕ≡s)
¬ϕ≡r→ϕ≢r {l + s ` loc} ¬ϕ≡l+s
  with ϕ≡? l  | ϕ≡? s
... | yes ϕ≡l | yes ϕ≡s = Nullary.contradiction (ϕ≡ ϕ≡l + ϕ≡s) ¬ϕ≡l+s
... | no ¬ϕ≡l | no ¬ϕ≡s = ϕ≢left-right (¬ϕ≡r→ϕ≢r ¬ϕ≡l) (¬ϕ≡r→ϕ≢r ¬ϕ≡s)
... | no ¬ϕ≡l | yes ϕ≡s = ϕ≢left (¬ϕ≡r→ϕ≢r ¬ϕ≡l) ϕ≡s
... | yes ϕ≡l | no ¬ϕ≡s = ϕ≢right ϕ≡l (¬ϕ≡r→ϕ≢r ¬ϕ≡s)


ϕ≢r→¬ϕ≡r : ∀ { r : RE }
  → ϕ≢ r
  ----------------
  → ( ¬ ϕ≡ r )  
ϕ≢r→¬ϕ≡r {ϕ} = λ()
ϕ≢r→¬ϕ≡r {ε} ϕ≢ε = λ()
ϕ≢r→¬ϕ≡r {$ c ` loc} ϕ≢$ = λ()
ϕ≢r→¬ϕ≡r {l * ε∉l ` loc} ϕ≢* = λ()
ϕ≢r→¬ϕ≡r {l ● s ` loc} (ϕ≢ ϕ≢l ● ϕ≢s) = λ { ( ϕ≡fst ϕ≡l ) →  (ϕ≢r→¬ϕ≡r ϕ≢l) ϕ≡l
                                           ; ( ϕ≡snd ϕ≡s ) →  (ϕ≢r→¬ϕ≡r ϕ≢s) ϕ≡s }
ϕ≢r→¬ϕ≡r {l + s ` loc} (ϕ≢left ϕ≢l ϕ≡s) = λ { (ϕ≡ ϕ≡l + ϕ≡s ) → (ϕ≢r→¬ϕ≡r ϕ≢l) ϕ≡l }
ϕ≢r→¬ϕ≡r {l + s ` loc} (ϕ≢right ϕ≡l ϕ≢s ) = λ { (ϕ≡ ϕ≡l + ϕ≡s ) → (ϕ≢r→¬ϕ≡r ϕ≢s) ϕ≡s }
ϕ≢r→¬ϕ≡r {l + s ` loc} (ϕ≢left-right ϕ≢l ϕ≢s ) = λ { (ϕ≡ ϕ≡l + ϕ≡s ) → (ϕ≢r→¬ϕ≡r ϕ≢s) ϕ≡s }





first : RE → List Char
first ϕ = []
first ε = []
first ($ c ` _ ) = [ c ]
first (l + r ` _ ) = first l ++ first r
first (l * ε∉l ` _ ) = first l
first (l ● s ` _ ) with ε∈? l
... | yes ε∈l = first l ++ first s
... | no ¬ε∈l = first l 

ϕ≢-ε∉→¬first≡[] : ∀ { r : RE }
  → ( ϕ≢r : ϕ≢ r )
  → ( ε∉r : ε∉ r ) 
  → ¬ ( first r ≡ [] ) 
ϕ≢-ε∉→¬first≡[] {ϕ}             ϕ≢ϕ   ε∉ϕ   = λ x → ϕ≢r→¬ϕ≡r ϕ≢ϕ ϕ≡ϕ
-- ϕ≢-ε∉→¬first≡[] {ε}             ϕ≢ε   ε∉ε   = λ x → ε∉r→¬ε∈r ε∉ε ε∈ε 
ϕ≢-ε∉→¬first≡[] {$ c ` _ }      ϕ≢$   ε∉$   = λ c∷[]≡[] → ¬∷≡[] c∷[]≡[]
ϕ≢-ε∉→¬first≡[] {l + r ` loc }  (ϕ≢left-right ϕ≢l ϕ≢r) (ε∉ ε∉l + ε∉r) = λ first-l++first-r≡[] → (ϕ≢-ε∉→¬first≡[] ϕ≢l ε∉l) (++-conicalˡ (first l) (first r) first-l++first-r≡[]) 
ϕ≢-ε∉→¬first≡[] {l + r ` loc }  (ϕ≢left ϕ≢l ϕ≡r) (ε∉ ε∉l + ε∉r)       = λ first-l++first-r≡[] → (ϕ≢-ε∉→¬first≡[] ϕ≢l ε∉l) (++-conicalˡ (first l) (first r) first-l++first-r≡[])  
ϕ≢-ε∉→¬first≡[] {l + r ` loc }  (ϕ≢right ϕ≡l ϕ≢r) (ε∉ ε∉l + ε∉r)      = λ first-l++first-r≡[] → (ϕ≢-ε∉→¬first≡[] ϕ≢r ε∉r) (++-conicalʳ (first l) (first r) first-l++first-r≡[])
ϕ≢-ε∉→¬first≡[] {l ● r ` loc }  (ϕ≢ ϕ≢l ● ϕ≢r) (ε∉fst ε∉l) with ε∈? l
... | yes ε∈l = λ first-l++first-r≡[] →  (ε∉r→¬ε∈r ε∉l) ε∈l
... | no ¬εεl = λ first-l≡[] →  ( ϕ≢-ε∉→¬first≡[] ϕ≢l ε∉l) first-l≡[]
ϕ≢-ε∉→¬first≡[] {l ● r ` loc }  (ϕ≢ ϕ≢l ● ϕ≢r) (ε∉snd ε∉r) with ε∈? l
... | yes ε∈l = λ first-l++first-r≡[] →  (ϕ≢-ε∉→¬first≡[] ϕ≢r ε∉r) (++-conicalʳ (first l) (first r) first-l++first-r≡[])
... | no ¬ε∈l = λ first-l≡[] → ( ϕ≢-ε∉→¬first≡[] ϕ≢l (¬ε∈r→ε∉r ¬ε∈l)) first-l≡[] 




ϕ≡r→ε∉r : ∀ { r : RE } ( ϕ≡r : ϕ≡ r )
  →  ε∉ r
ϕ≡r→ε∉r {ϕ} ϕ≡ϕ = ε∉ϕ
ϕ≡r→ε∉r {l + r ` loc } (ϕ≡ ϕ≡l + ϕ≡r) = ε∉ (ϕ≡r→ε∉r ϕ≡l) + ( ϕ≡r→ε∉r ϕ≡r )
ϕ≡r→ε∉r {l ● r ` loc } (ϕ≡fst ϕ≡l) = ε∉fst (ϕ≡r→ε∉r ϕ≡l)
ϕ≡r→ε∉r {l ● r ` loc } (ϕ≡snd ϕ≡r) = ε∉snd (ϕ≡r→ε∉r ϕ≡r)




{-
first-ϕ●r≡[] : ∀ { l r  : RE } { loc : ℕ } { ϕ≡l : ϕ≡ l }
  → first ( l ● r ` loc ) ≡ []
first-ϕ●r≡[]  {ϕ} {r} {loc} {ϕ≡ϕ} = refl
-- first-ϕ●r≡[]  {ε} {r} {loc} {ϕ≡ε} = Nullary.contradiction ϕ≡ε (ϕ≢r→¬ϕ≡r ϕ≢ε)
-- first-ϕ●r≡[]  {$ c ` loc₁} {r} {loc} {ϕ≡$} = Nullary.contradiction ϕ≡$ (ϕ≢r→¬ϕ≡r ϕ≢$)
first-ϕ●r≡[] {l + s ` loc₁} {r} {loc₂} {ϕ≡ ϕ≡l + ϕ≡s} =  {!!}
-} 
  

```
