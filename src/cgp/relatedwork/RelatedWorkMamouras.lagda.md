# RelatedWorkMamouras ( properties )

The base development lives in RelatedWorkMamouras3Base.lagda.md ( checked
once and cached ) . This module contains only the properties : greedyU-prop ,
greedy-max-prop and ←greedy-sound .

```agda
{-# OPTIONS --rewriting --no-positivity-check #-}
module cgp.relatedwork.RelatedWorkMamouras where

import cgp.RE as RE
open RE using (RE; ε ; $_`_ ; _●_`_ ; _+_`_ ; _*_`_ ; ε∉ ; ε∈  ; ε∈_+_  ; ε∈_<+_ ; ε∈_+>_ ; ε∈_●_ ; ε∈*  ; ε∈ε ; ε∉r→¬ε∈r ; ¬ε∈r→ε∉r ;  ε∉fst ; ε∉snd ; ε∉$ ; ε∉_+_ ; ε∉? ; ε∈? )


import cgp.Utils as Utils
open Utils using (foldr++ys-map-λ_→[]-xs≡ys ; all-concat ; ∷-inj  ;
  w₁++w₂≡w₃++w₄len-w₁≡len-w₂→w₁≡w₂×w₂≡w₄ ;
  w₁++w₂≡w₃++w₄len-w₁<len-w₂→∃w₅≢[]w₁w₅≡w₃×w₂≡w₅w₄ ;
  ¬m>n→n≡m⊎n>m ;
  len-w₁++w₃>len-w₂++w₃→len-w₁>len-w₂ ; concatmap-λx→[]-xs≡[] ;
  length≡0→[] ; ¬≡[]→¬length≡0 ;
  dec-elim ; maybe-just-≟ ; n∸0≡n ; dec-∃-range ;
  +-1≡suc ; suc-∸-1 ; ∸-suc-≤ ; ∸-step-≤)


import cgp.Word as Word
open Word using ( _∈⟦_⟧ ; ε ;  $_ ; _+L_ ; _+R_ ; _●_⧺_ ; _* ; []∈⟦r⟧→¬ε∉r )


import cgp.ParseTree as ParseTree
open ParseTree using ( U; EmptyU ; LetterU ;
  LeftU ; RightU ; PairU ; ListU ; flat ; unflat ; unListU ; listU∘unListU ; 
  unflat∘proj₂∘flat ; flat∘unflat ;
  inv-listU ; inv-listU1 ; inv-pairU ; inv-leftU ; inv-rightU ;
  _⊢_≟_  ; ¬|list-u∷us|≡[] ) 

import cgp.empty.AllEmptyParseTree as AllEmptyParseTree
open AllEmptyParseTree using ( mkAllEmptyU ; mkAllEmptyU-sound ; Flat-[] ; flat-[] ;
  proj₁flat-v≡[]→ε∈r ; flat-[]→flat-[]-left ; flat-[]→flat-[]-right ; mkAllEmptyU≢[]  )


import cgp.PDInstance as PDI
open PDI using ( PDInstance ; pdinstance ; PDInstance* ; pdinstance* ;
  pdinstance-left ; pdinstance-right ;
  pdinstance-star ; mkinjList ;
  pdinstance-fst ; mkinjFst ;
  pdinstance-snd ; mkinjSnd ; mk-snd-pdi ;
  concatmap-pdinstance-snd ; zip-es-flat-[]-es ;
  pdinstance-assoc ; mkinjAssoc ; inv-assoc-sound ;
  compose-pdi-with ;
  concatmap-pdinstance-snd-[]≡[] 
  ) 



import cgp.posix.PartialDerivative as PartialDerivative
open PartialDerivative using ( pdU[_,_] ; -- pdUConcat ;
  pdUMany[_,_]; pdUMany-aux ;
  pdinstance-oplus ; fuse ; mkfuseInj ;  mkfuseInjSoundEv ; 
  advance-pdi*-with-c
  )


import cgp.posix.Order as PosixOrder
open PosixOrder using ( _⊢_>_ ; len-≡ ; len-> ;
  _⊢_>ⁱ_ ; seq₁ ; seq₂ ;
  choice-ll ; choice-rr ;
  choice-lr ;
  choice-rl ; star-head ; star-cons-nil ; star-tail ;
  >→¬≡
  )

import cgp.relatedwork.RelatedWorkCUrban as RelatedWorkCUrban
open RelatedWorkCUrban  using ( _,_⇒_ ; p₁ ; pc ; p+l ; p+r ; ps ; p[] ; p* ; ∈⟦→⇒ ; ∈⟦→⇒*-go ; ∈⟦→⇒●-go ; *-fb ; ∈⟦-+-elim ; ∈⟦-●-elim ; ∈⟦-ε-elim ; ∈⟦-decides ; elim-star ; list≡-decides ; ∈⟦-*-empty-r* ; find-longest-split ; NoShorter ; ∈⟦→⇒-ε ; ∈⟦→⇒-$ ; plus-right-member ; plus-right-∈⟦→⇒ ; ⇒-member ; ⇒→>-max ; >-anti-sym ; >-max→⇒ ; intersect-memberʳ ; >→¬< )

import Data.Char as Char
open Char using (Char )

import Data.Nat as Nat
open Nat using ( ℕ ; suc ; zero ; _>_ ; _≥_ ; _≤_  ; _+_  )

import Data.Nat.Properties as NatProperties
open import Data.Nat using (_<_ ; _≤_ ; _≟_ ; _≤?_ ; zero ; suc ; _+_ ; _∸_ ; s<s ; z<s ; z≤n ; s≤s)
open import Data.Empty using (⊥ ; ⊥-elim)
open NatProperties using ( ≤-reflexive ;  <⇒≤ ; ≤-trans ; <-trans ; +-monoʳ-≤ ; ≤-refl ; <-irrefl ; suc-injective ; +-cancelˡ-< ; <⇒≯ ; <⇒≱ ; <-cmp ; +-suc ; +-identityʳ ;
  ≤-antisym ; m∸n≡0⇒m≤n ; n≤1+n ; ≤-step ; m≤n⇒m<n∨m≡n ; ≤-pred ;
  m+[n∸m]≡n ; n∸n≡0 ; +-∸-comm ; ∸-+-assoc ; +-monoʳ-< ; +-monoˡ-≤ ; m≤m+n ;
  ∸-monoˡ-≤ )

import Data.Maybe as Maybe
open Maybe using (Maybe ; just ; nothing )

import Data.List as List
open List using (List ; _∷_ ; [] ; _++_ ; [_]; map; head; tail; concatMap ; _∷ʳ_ ; length ; take ; drop )

import Data.List.Properties
open Data.List.Properties using (  ++-identityʳ ; ++-identityˡ ; ∷ʳ-++ ; ++-cancelˡ ; ++-cancelʳ ; ++-conicalʳ ; ++-conicalˡ ;
  length-++ ; ++-assoc ; ∷-injective ; take-[] ; drop-[] ; drop-drop ; take++drop≡id ;
  length-drop
  -- ; length-++-sucʳ -- this is only available after v2.3
  )

open import Data.List.Membership.Propositional using (_∈_; _∉_)
open import Data.List.Relation.Unary.Any using (here ; there)
open import Data.List.Membership.Propositional.Properties using (∈-++⁻ ; ∈-++⁺ˡ ; ∈-++⁺ʳ)


import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong₂; cong-app; subst; subst₂; inspect; Reveal_·_is_; [_]; _≢_)

open import Relation.Nullary using (¬_)
open Eq.≡-Reasoning using (begin_; step-≡;  step-≡-∣;  step-≡-⟩; _∎)

import Data.Product as Product
open Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_ )
open Σ using (proj₁ ; proj₂)


import Data.Sum as Sum
open Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)




import Relation.Nullary.Decidable as Decidable
open Decidable using
  ( Dec; yes; no; _×-dec_ )

```




```agda


open import cgp.relatedwork.RelatedWorkMamourasBase public

import cgp.greedy.Order as GreedyOrder
open GreedyOrder renaming ( _⊢_>_ to  _⊢_>ᵍ_ )
open GreedyOrder renaming ( _⊢_>ⁱ_ to _⊢_>ᵍⁱ_ )

mutual

  -- more helpers for greedyU-prop -------------------------------------

  -- Purpose : the substring w [ i , j ) of a match span has exactly the
  --           length j ∸ i of that span .
  -- Used in : greedyU-prop ( the U⊨ / PairSplit / ListSplit length side
  --           conditions ) .
  -- Idea    : match→end≤len + ∸-monoˡ-≤ + take≤length ( as in
  --           ←greedy-sound-go ) .
  match-span-len : ( r : RE ) ( i j : ℕ ) ( w : List Char )
    → ( t : r , i , j ⊨ w )
    → length ( take ( j ∸ i ) ( drop i w ) ) ≡ j ∸ i
  match-span-len r i j w t = take≤length ( drop i w ) ( j ∸ i ) j∸i≤len
    where
      j∸i≤len : j ∸ i ≤ length ( drop i w )
      j∸i≤len with m≤n⇒m<n∨m≡n ( rij⊨w→i≤j t )
      ... | inj₁ i<j =
        subst ( λ n → j ∸ i ≤ n )
          ( sym ( length-drop i w ) )
          ( ∸-monoˡ-≤ i ( match→end≤len r i j w i<j t ) )
      ... | inj₂ i≡j rewrite i≡j | n∸n≡0 j = z≤n

  -- Purpose : flat decomposes over LeftU / RightU ( the projection of a
  --           + parse is the projection of its payload ) .
  -- Used in : greedyU-prop ( + cases : transporting the flat condition ) .
  -- Idea    : the with-block in the definition of flat fires on the branch .
  flat-LeftU : ∀ { l r : RE } { loc : ℕ }
    → ( u : U l )
    → proj₁ ( flat ( LeftU { l } { r } { loc } u ) ) ≡ proj₁ ( flat u )
  flat-LeftU u with flat u
  ... | _ , _ = refl

  flat-RightU : ∀ { l r : RE } { loc : ℕ }
    → ( u : U r )
    → proj₁ ( flat ( RightU { l } { r } { loc } u ) ) ≡ proj₁ ( flat u )
  flat-RightU u with flat u
  ... | _ , _ = refl

  -- Purpose : U⊨ instantiated at the canonical take / drop split ( the
  --           match witness of a parse over the substring w [ i , j ) ) .
  -- Used in : greedyU-prop ( + cases ) .
  -- Idea    : one-line instance of U⊨ .
  v⊨ : ( r : RE ) ( i j : ℕ ) ( w : List Char )
    → ( i≤j : i Nat.≤ j )
    → ( v : U r )
    → proj₁ ( flat v ) ≡ take ( j ∸ i ) ( drop i w )
    → length ( take ( j ∸ i ) ( drop i w ) ) ≡ j ∸ i
    → r , i , j ⊨ w
  v⊨ r i j w i≤j v flatv len =
    U⊨ r i j w i≤j v ( take ( j ∸ i ) ( drop i w ) )
      ( drop ( j ∸ i ) ( drop i w ) ) flatv len
      ( take++drop≡id ( j ∸ i ) ( drop i w ) )

  -- Purpose : a PairU parse over the substring w [ i , j ) splits at
  --           s = i + length ( flat u₁ ) into sub-matches and sub-flat
  --           conditions for both halves .
  -- Used in : greedyU-prop ( ● case ) .
  -- Idea    : split-helper + the U⊨ sub-instances of U⊨ ( ● case ) +
  --           prefix→take for the two flat conditions .
  PairSplit : ( l₁ l₂ : RE ) ( loc : ℕ ) ( i j : ℕ ) ( w : List Char )
    → ( i≤j : i Nat.≤ j )
    → ( u₁ : U l₁ ) ( u₂ : U l₂ )
    → proj₁ ( flat ( PairU { l₁ } { l₂ } { loc } u₁ u₂ ) )
        ≡ take ( j ∸ i ) ( drop i w )
    → length ( take ( j ∸ i ) ( drop i w ) ) ≡ j ∸ i
    → ∃[ s ] ( l₁ , i , s ⊨ w ) × ( l₂ , s , j ⊨ w )
             × ( proj₁ ( flat u₁ ) ≡ take ( s ∸ i ) ( drop i w ) )
             × ( proj₁ ( flat u₂ ) ≡ take ( j ∸ s ) ( drop s w ) )
  PairSplit l₁ l₂ loc i j w i≤j u₁ u₂ flatv len =
    s₀ , m₁ , m₂ , fl₁c , fl₂c
    where
      a = proj₁ ( flat u₁ )
      b = proj₁ ( flat u₂ )
      s₀ = i + length a
      ab≡ : a ++ b ≡ take ( j ∸ i ) ( drop i w )
      ab≡ = trans ( flat-PairU { l₁ } { l₂ } { loc } u₁ u₂ ) flatv
      fl' : length ( a ++ b ) ≡ j ∸ i
      fl' = subst ( λ xs → length xs ≡ j ∸ i ) ( sym ab≡ ) len
      fw' : ( a ++ b ) ++ drop ( j ∸ i ) ( drop i w ) ≡ drop i w
      fw' = subst ( λ xs → xs ++ drop ( j ∸ i ) ( drop i w ) ≡ drop i w )
              ( sym ab≡ ) ( take++drop≡id ( j ∸ i ) ( drop i w ) )
      split = split-helper w i j i≤j ( drop ( j ∸ i ) ( drop i w ) ) a b fl' fw'
      i≤s₀ = SplitLemmas.i≤s₀ split
      fl₁ = SplitLemmas.fl₁ split
      fw₁ = SplitLemmas.fw₁ split
      s₀≤j = SplitLemmas.s₀≤j split
      fl₂ = SplitLemmas.fl₂ split
      fw₂ = SplitLemmas.fw₂ split
      m₁ = U⊨ l₁ i s₀ w i≤s₀ u₁ a ( drop s₀ w ) refl fl₁ fw₁
      m₂ = U⊨ l₂ s₀ j w s₀≤j u₂ b ( drop j w ) refl fl₂ fw₂
      fl₁c : a ≡ take ( s₀ ∸ i ) ( drop i w )
      fl₁c = prefix→take a ( drop s₀ w ) ( drop i w ) ( s₀ ∸ i ) fw₁ fl₁
      fl₂c : b ≡ take ( j ∸ s₀ ) ( drop s₀ w )
      fl₂c = trans ( prefix→take b ( drop j w ) ( drop s₀ w ) ( length b ) fw₂ refl )
               ( cong ( λ n → take n ( drop s₀ w ) ) fl₂ )

  -- Purpose : a ListU ( u ∷ us ) parse over the substring w [ i , j )
  --           splits at a head span ( i , s ) with i < s ≤ j into the
  --           head / tail sub-matches and the head / tail flat conditions .
  -- Used in : greedyU-prop ( * case ) .
  -- Idea    : split-helper + the U⊨ sub-instances of U⊨ ( * case ) +
  --           ε∉r→0<flat for i < s + prefix→take for the flat conditions .
  ListSplit : ( r : RE ) ( nε : ε∉ r ) ( loc : ℕ ) ( i j : ℕ ) ( w : List Char )
    → ( i≤j : i Nat.≤ j )
    → ( u : U r ) ( us : List ( U r ) )
    → proj₁ ( flat ( ListU { r } { nε } { loc } ( u ∷ us ) ) )
        ≡ take ( j ∸ i ) ( drop i w )
    → length ( take ( j ∸ i ) ( drop i w ) ) ≡ j ∸ i
    → ∃[ s ] ( i Nat.< s ) × ( s Nat.≤ j ) × ( r , i , s ⊨ w )
             × ( ( r * nε ` loc ) , s , j ⊨ w )
             × ( proj₁ ( flat u ) ≡ take ( s ∸ i ) ( drop i w ) )
             × ( proj₁ ( flat ( ListU { r } { nε } { loc } us ) )
                 ≡ take ( j ∸ s ) ( drop s w ) )
  ListSplit r nε loc i j w i≤j u us flatv len =
    s₀ , i<s₀ , s₀≤j , m₁ , m₂ , fu , fus
    where
      a = proj₁ ( flat u )
      b = proj₁ ( flat ( ListU { r } { nε } { loc } us ) )
      s₀ = i + length a
      ab≡ : a ++ b ≡ take ( j ∸ i ) ( drop i w )
      ab≡ = trans ( flat-ListU-cons { r } { nε } { loc } u us ) flatv
      fl' : length ( a ++ b ) ≡ j ∸ i
      fl' = subst ( λ xs → length xs ≡ j ∸ i ) ( sym ab≡ ) len
      fw' : ( a ++ b ) ++ drop ( j ∸ i ) ( drop i w ) ≡ drop i w
      fw' = subst ( λ xs → xs ++ drop ( j ∸ i ) ( drop i w ) ≡ drop i w )
              ( sym ab≡ ) ( take++drop≡id ( j ∸ i ) ( drop i w ) )
      split = split-helper w i j i≤j ( drop ( j ∸ i ) ( drop i w ) ) a b fl' fw'
      i≤s₀-lem = SplitLemmas.i≤s₀ split
      fl₁ = SplitLemmas.fl₁ split
      fw₁ = SplitLemmas.fw₁ split
      s₀≤j = SplitLemmas.s₀≤j split
      fl₂ = SplitLemmas.fl₂ split
      fw₂ = SplitLemmas.fw₂ split
      i<s₀ = subst ( λ x → x < s₀ ) ( +-identityʳ i )
               ( +-monoʳ-< i ( ε∉r→0<flat r nε u ) )
      m₁ = U⊨ r i s₀ w i≤s₀-lem u a ( drop s₀ w ) refl fl₁ fw₁
      m₂ = U⊨ ( r * nε ` loc ) s₀ j w s₀≤j
             ( ListU { r } { nε } { loc } us ) b ( drop j w ) refl fl₂ fw₂
      fu : a ≡ take ( s₀ ∸ i ) ( drop i w )
      fu = prefix→take a ( drop s₀ w ) ( drop i w ) ( s₀ ∸ i ) fw₁ fl₁
      fus : b ≡ take ( j ∸ s₀ ) ( drop s₀ w )
      fus = trans ( prefix→take b ( drop j w ) ( drop s₀ w ) ( length b ) fw₂ refl )
              ( cong ( λ n → take n ( drop s₀ w ) ) fl₂ )

  -- Purpose : chain a strict comparison of two greedy parses with the
  --           induction hypothesis for the smaller one : the greedy parse
  --           of any evidence of the same span stays above the target .
  -- Used in : greedyU-prop ( ● / * cases : the strict-order branches ) .
  -- Idea    : greedyU-indep transports the left side across the evidence
  --           change ; >-trans chains the strict steps ; an equality IH
  --           is substed into the strict target instead of returned .
  prop-chain : ( l : RE ) ( i j : ℕ ) ( w : List Char )
    → ( t tᵛ : l , i , j ⊨ w ) ( u v : U l )
    → l ⊢ ( greedyU l i j w tᵛ ) >ᵍ u
    → ( l ⊢ u >ᵍ v ) ⊎ ( u ≡ v )
    → l ⊢ greedyU l i j w t >ᵍ v
  prop-chain l i j w t tᵛ u v mid ih = case-⊎
    ( λ h →
        GreedyOrder.>-trans
          ( subst ( λ x → l ⊢ x >ᵍ u ) ( sym g≡ ) mid ) h )
    ( λ h →
        subst ( λ x → l ⊢ greedyU l i j w t >ᵍ x ) h
          ( subst ( λ x → l ⊢ x >ᵍ u ) ( sym g≡ ) mid ) )
    ih
    where
      g≡ : greedyU l i j w t ≡ greedyU l i j w tᵛ
      g≡ = greedyU-indep l i j w t tᵛ

  -- Purpose : ListU is injective on its list payload .
  -- Used in : greedyU-prop ( * case : the all-equal branch ) .
  -- Idea    : matching the equation with refl performs the constructor
  --           index injection .
  ListU-inj : ∀ { r : RE } { nε : ε∉ r } { loc : ℕ }
    → { xs ys : List ( U r ) }
    → ListU { r } { nε } { loc } xs ≡ ListU { r } { nε } { loc } ys
    → xs ≡ ys
  ListU-inj e with e
  ... | refl = refl

  -- Recursion is on the parse tree v , but the recursive calls receive their
  -- match argument through the PairSplit / ListSplit with-abstractions , so
  -- the termination checker cannot see the decrease ( same situation as the
  -- base order 's decision procedures in RelatedWorkMamouras3Base ) .
  {-# TERMINATING #-}
  greedyU-prop : ∀ ( l : RE ) → ( i j : ℕ ) → ( w : List Char )
    → ( t : l , i , j ⊨ w )
    → ( v : U l ) 
    → ( proj₁ (flat v) ) ≡ (take ( j ∸ i ) ( drop i w ) ) 
    → (l ⊢ (greedyU l i j w t) >ᵍ v ) ⊎ ( (greedyU l i j w t) ≡ v )
  greedyU-prop ε i j w t EmptyU flatv with t
  ... | ( ⊨ε _ _ ) = inj₂ refl
  greedyU-prop ( $ c ` loc ) i j w t ( LetterU c ) flatv with t
  ... | ( ⊨$ _ _ _ _ _ ) = inj₂ refl
  greedyU-prop ( l₁ + l₂ ` loc ) i j w t ( LeftU u ) flatv =
    case-⊎
      ( λ h →
          inj₁ ( subst ( λ x → ( l₁ + l₂ ` loc ) ⊢ x >ᵍ LeftU u ) ( sym eq)
                   ( GreedyOrder.sub ( GreedyOrder.choice-ll h ) ) ) )
      ( λ h → inj₂ ( trans eq ( cong LeftU h ) ) )
      ( greedyU-prop l₁ i j w a u flat-u )
    where
      flat-u : proj₁ ( flat u ) ≡ take ( j ∸ i ) ( drop i w )
      flat-u = trans ( sym ( flat-LeftU { l₁ } { l₂ } { loc } u ) ) flatv
      a : l₁ , i , j ⊨ w
      a = v⊨ l₁ i j w ( rij⊨w→i≤j t ) u flat-u
            ( match-span-len ( l₁ + l₂ ` loc ) i j w t )
      eq : greedyU ( l₁ + l₂ ` loc ) i j w t ≡ LeftU ( greedyU l₁ i j w a )
      eq = greedyU-+inl l₁ l₂ loc i j w t a
  greedyU-prop ( l₁ + l₂ ` loc ) i j w t ( RightU u ) flatv
    with ⊨? l₁ i j w
  ... | yes a = inj₁ ( GreedyOrder.sub GreedyOrder.choice-lr )
  ... | no ¬a with t
  ...   | ( ⊨inr _ _ _ _ _ _ b₀ ) =
        case-⊎
          ( λ h →
              inj₁ ( subst ( λ x → ( l₁ + l₂ ` loc ) ⊢ x >ᵍ RightU u ) ( sym eq)
                       ( GreedyOrder.sub ( GreedyOrder.choice-rr h ) ) ) )
          ( λ h → inj₂ ( trans eq ( cong RightU h ) ) )
          ( greedyU-prop l₂ i j w b u flat-u )
        where
          flat-u : proj₁ ( flat u ) ≡ take ( j ∸ i ) ( drop i w )
          flat-u = trans ( sym ( flat-RightU { l₁ } { l₂ } { loc } u ) ) flatv
          b : l₂ , i , j ⊨ w
          b = v⊨ l₂ i j w ( rij⊨w→i≤j t ) u flat-u
                ( match-span-len ( l₁ + l₂ ` loc ) i j w t )
          eq : RightU ( greedyU l₂ i j w b₀ ) ≡ RightU ( greedyU l₂ i j w b )
          eq = cong RightU ( greedyU-indep l₂ i j w b₀ b )
  ...   | ( ⊨inl _ _ _ _ _ _ a₀ ) = ⊥-elim ( ¬a a₀ )
  greedyU-prop ( l₁ ● l₂ ` loc ) i j w t ( PairU u₁ u₂ ) flatv
    with find-<-Min● l₁ l₂ loc w i j t
       | PairSplit l₁ l₂ loc i j w ( rij⊨w→i≤j t ) u₁ u₂ flatv
           ( match-span-len ( l₁ ● l₂ ` loc ) i j w t )
  ... | ( ⊨● _ _ _ _ .j w s₁ _ _ a₁ b₁ , ev₁₀ )
      | ( s₂ , m₁ , m₂ , fl₁c , fl₂c )
    with trichotomy l₁ w i s₁ s₂ a₁ m₁
  ... | inj₁ s₂<s₁ = ⊥-elim ( <-Min●-¬ex ev₁₀ ( s₂ , m₁ , m₂ , s₂<s₁ ) )
  ... | inj₂ ( inj₂ s₁<s₂ ) =
    inj₁ ( GreedyOrder.sub
             ( GreedyOrder.seq₁
                 ( prop-chain l₁ i s₁ w a₁ ( ⊢-t₁ l₁ w i s₁ s₂ s₁<s₂ )
                     ( greedyU l₁ i s₂ w m₁ ) u₁
                     ( go l₁ w i s₁ s₂ s₁<s₂ m₁ )
                     ( greedyU-prop l₁ i s₂ w m₁ u₁ fl₁c ) ) ) )
  ... | inj₂ ( inj₁ s₁≡s₂ ) =
    let a₁s : l₁ , i , s₂ ⊨ w
        a₁s = subst ( λ m → l₁ , i , m ⊨ w ) s₁≡s₂ a₁
        b₁s : l₂ , s₂ , j ⊨ w
        b₁s = subst ( λ m → l₂ , m , j ⊨ w ) s₁≡s₂ b₁
        head-tp : greedyU l₁ i s₁ w a₁ ≡ greedyU l₁ i s₂ w a₁s
        head-tp = greedyU-●-L-transport l₁ i w s₁ s₂ s₁≡s₂ a₁
        tail-tp : greedyU l₂ s₁ j w b₁ ≡ greedyU l₂ s₂ j w b₁s
        tail-tp = greedyU-●-R-transport l₂ j w s₁ s₂ s₁≡s₂ b₁
    in case-⊎
         ( λ h₁ →
             inj₁ ( GreedyOrder.sub
                      ( GreedyOrder.seq₁
                          ( subst ( λ x → l₁ ⊢ x >ᵍ u₁ ) ( sym head-tp ) h₁ ) ) ) )
         ( λ h₁ →
             let head≡ : greedyU l₁ i s₁ w a₁ ≡ u₁
                 head≡ = trans head-tp h₁
             in case-⊎
                  ( λ h₂ →
                      inj₁ ( GreedyOrder.sub
                               ( GreedyOrder.seq₂ head≡
                                   ( subst ( λ x → l₂ ⊢ x >ᵍ u₂ )
                                           ( sym tail-tp ) h₂ ) ) ) )
                  ( λ h₂ →
                      inj₂ ( cong₂ PairU head≡ ( trans tail-tp h₂ ) ) )
                  ( greedyU-prop l₂ s₂ j w b₁s u₂ fl₂c ) )
         ( greedyU-prop l₁ i s₂ w a₁s u₁ fl₁c )
  greedyU-prop ( r₀ * nε ` loc ) i j w t ( ListU [] ) flatv with t
  ... | ( ⊨[] _ _ _ _ _ ) = inj₂ refl
  ... | ( ⊨∷ _ _ _ _ _ _ ( j₁ , i<j₁ , j₁≤j , _ , _ ) ) =
    ⊥-elim ( <-irrefl refl
               ( ≤-trans
                   ( ≤-trans i<j₁ j₁≤j )
                   ( m∸n≡0⇒m≤n
                       ( trans ( sym ( match-span-len ( r₀ * nε ` loc ) i j w t ) )
                               ( cong length ( sym flatv ) ) ) ) ) )
  greedyU-prop ( r₀ * nε ` loc ) i j w t ( ListU ( u ∷ us ) ) flatv
    with find-<-Min* r₀ nε loc w i j t
       | ListSplit r₀ nε loc i j w ( rij⊨w→i≤j t ) u us flatv
           ( match-span-len ( r₀ * nε ` loc ) i j w t )
  ... | ( ⊨[] _ _ _ _ _ , _ )
      | ( s₂ , i<s₂ , s₂≤j , _ , _ , _ , _ ) =
        ⊥-elim ( <-irrefl refl ( ≤-trans i<s₂ s₂≤j ) )
  ... | ( ⊨∷ _ _ _ _ _ _ ( j₁ , i<j₁ , j₁≤j , h₁ , tl₁ )
        , <-min-∷ _ _ _ _ _ _ _ _ _ _ _ _ ¬ex )
      | ( s₂ , i<s₂ , s₂≤j , m₁ , m₂ , fu , fus )
    with trichotomy r₀ w i j₁ s₂ h₁ m₁
  ... | inj₁ s₂<j₁ =
    ⊥-elim ( ¬ex ( s₂ , i<s₂ , s₂≤j , m₁ , m₂ , s₂<j₁ ) )
  ... | inj₂ ( inj₂ j₁<s₂ ) =
    inj₁ ( GreedyOrder.sub
             ( GreedyOrder.star-head
                 ( prop-chain r₀ i j₁ w h₁ ( ⊢-t₁ r₀ w i j₁ s₂ j₁<s₂ )
                     ( greedyU r₀ i s₂ w m₁ ) u
                     ( go r₀ w i j₁ s₂ j₁<s₂ m₁ )
                     ( greedyU-prop r₀ i s₂ w m₁ u fu ) ) ) )
  ... | inj₂ ( inj₁ j₁≡s₂ ) =
    let h₁s : r₀ , i , s₂ ⊨ w
        h₁s = subst ( λ m → r₀ , i , m ⊨ w ) j₁≡s₂ h₁
        tl₁s : ( r₀ * nε ` loc ) , s₂ , j ⊨ w
        tl₁s = subst ( λ m → ( r₀ * nε ` loc ) , m , j ⊨ w ) j₁≡s₂ tl₁
        head-tp : greedyU r₀ i j₁ w h₁ ≡ greedyU r₀ i s₂ w h₁s
        head-tp = greedyU-●-L-transport r₀ i w j₁ s₂ j₁≡s₂ h₁
        tail-tp : greedyU ( r₀ * nε ` loc ) j₁ j w tl₁
                    ≡ greedyU ( r₀ * nε ` loc ) s₂ j w tl₁s
        tail-tp = greedyU-●-R-transport ( r₀ * nε ` loc ) j w j₁ s₂ j₁≡s₂ tl₁
    in case-⊎
         ( λ h →
             inj₁ ( GreedyOrder.sub
                      ( GreedyOrder.star-head
                          ( subst ( λ x → r₀ ⊢ x >ᵍ u ) ( sym head-tp ) h ) ) ) )
         ( λ h →
             let head≡ : greedyU r₀ i j₁ w h₁ ≡ u
                 head≡ = trans head-tp h
             in case-⊎
                  ( λ h₂ →
                      inj₁ ( GreedyOrder.sub
                               ( GreedyOrder.star-tail head≡
                                   ( subst ( λ x → ( r₀ * nε ` loc ) ⊢ x >ᵍ ListU us )
                                           ( sym tail-tp ) h₂ ) ) ) )
                  ( λ h₂ →
                      inj₂ ( cong ( ListU { r₀ } { nε } { loc } )
                             ( cong₂ _∷_ head≡ ( ListU-inj ( trans tail-tp h₂ ) ) ) ) )
                  ( greedyU-prop ( r₀ * nε ` loc ) s₂ j w tl₁s ( ListU us ) fus ) )
         ( greedyU-prop r₀ i s₂ w h₁s u fu )

  greedy-max-prop : ∀ ( l : RE ) → ( i j : ℕ ) → ( w : List Char )
    → ( t : l , i , j ⊨ w )
    → ( v : U l ) 
    → ( proj₁ (flat v) ) ≡ (take ( j ∸ i ) ( drop i w ) ) 
    → (l ⊢ (greedy-max l w i j t) >ᵍ v ) ⊎ ( (greedy-max l w i j t) ≡ v )
  -- Immediate from greedyU-prop : greedy-max is greedyU with its arguments
  -- reordered , so the goal unfolds judgmentally to that of greedyU-prop .
  greedy-max-prop l i j w t v flatv = greedyU-prop l i j w t v flatv



  -- Purpose : extract the RIGHT span-k match evidence carried by a base-order
  --           proof p : r ∣ w ∣ i ⊢ j < k . Every constructor of the base
  --           order stores both match evidences ; ⊢-t₁ takes the left one .
  -- Used in : ←greedy-sound ( the right-hand greedy witness of the k-span ) .
  -- Idea    : three projection clauses , mirroring ⊢-t₁ .
  ⊢-t₂ : ( r : RE ) ( w : List Char ) ( i j k : ℕ )
    → ( p : r ∣ w ∣ i ⊢ j < k )
    → r , i , k ⊨ w
  ⊢-t₂ _ _ _ _ _ ( choice _ _ _ _ t₂ _ ) = t₂
  ⊢-t₂ _ _ _ _ _ ( seq    _ _ _ _ t₂ _ ) = t₂
  ⊢-t₂ _ _ _ _ _ ( star   _ _ _ _ t₂ _ ) = t₂

  ←greedy-sound : ( r : RE ) ( w : List Char ) ( i j k : ℕ )
    → ( p : r ∣ w ∣ i ⊢ j < k )
    → ∃[ u ] ∃[ w₁ ] ∃[ w₂ ]
         ( proj₁ ( flat { r } u ) ≡ w₁
         × w₁ ++ w₂ ≡ drop i w
         × length w₁ ≡ j ∸ i
         × ∀ ( v : U r ) 
           → ( proj₁ (flat v) ) ≡ (take ( k ∸ i ) ( drop i w ) ) 
           → r ⊢ u >ᵍ v )
  -- The ∃ package is exactly ←greedy-sound-go 's : its first three fields
  -- match the goal verbatim , and its ∀ field bounds the k-span greedy
  -- witness greedy-max r w i k t₂ from above ( t₂ = ⊢-t₂ p ) . For the
  -- goal 's ∀ over an arbitrary parse tree v matching the k-span substring ,
  -- greedy-max-prop says that witness is strictly above v ( chain with
  -- GreedyOrder.>-trans ) or equal to v ( transport ) .
  ←greedy-sound r w i j k p with ( ←greedy-sound-go r w i j k p )
  ... | ( u , w₁ , w₂ , ( flat-ev , concat-ev , len-ev , ∀-ev ) )
    = ( u , w₁ , w₂ , ( flat-ev , concat-ev , len-ev , ∀-ev₂ ) )
    where
      t₂ : r , i , k ⊨ w
      t₂ = ⊢-t₂ r w i j k p
      ∀-ev₂ : ∀ ( v : U r )
        → ( proj₁ ( flat v ) ) ≡ ( take ( k ∸ i ) ( drop i w ) )
        → r ⊢ u >ᵍ v
      ∀-ev₂ v flatv = case-⊎
        ( λ g>v → GreedyOrder.>-trans ( ∀-ev t₂ ) g>v )
        ( λ g≡v → subst ( λ x → r ⊢ u >ᵍ x ) g≡v ( ∀-ev t₂ ) )
        ( greedy-max-prop r i k w t₂ v flatv )


  -- ←greedy-complete : ( r : RE ) ( u v : U r )
  --   → ( r ⊢ u >ᵍ v )
  --   -----------------------------------------
  --   → ∃[ w ] ∃[ i ] ∃[ j ] ∃[ k ]
  --     ( ( proj₁ (flat u) ) ≡ (take ( j ∸ i ) ( drop i w ) )
  --     × ( proj₁ (flat v) ) ≡ (take ( k ∸ i ) ( drop i w ) )
  --     × ( r ∣ w ∣ i ⊢ j < k ) )
  -- ←greedy-complete = {!!}
      

```

UNPROVABLE : the goal of ←greedy-complete is refuted by the counterexample
below ( for r-ce = ( 'a' + 'b' ) , u-ce = LeftU ( LetterU 'a' ) ,
v-ce = RightU ( LetterU 'b' ) the premise is inhabited but the ∃ conclusion
fails ; see ¬←greedy-complete-ce ) . The greedy order compares parse trees ,
the base order compares match spans : the conjecture asks every greedy pair
( u >ᵍ v ) to come from one word w and one start index i , which would make
flat u and flat v prefix-comparable ( both are prefixes of drop i w ) . The
greedy order has no such requirement : on a + regex , choice-lr relates ANY
LeftU parse above ANY RightU parse .


```agda
-- the two letters are matched by a + regex , so its two parses are related
-- by the greedy order without any condition on their words .
r-ce : RE
r-ce = ( $ 'a' ` 0 ) + ( $ 'b' ` 1 ) ` 2

u-ce : U r-ce
u-ce = LeftU ( LetterU 'a' )

v-ce : U r-ce
v-ce = RightU ( LetterU 'b' )

-- the premise of ←greedy-complete is inhabited for this pair .
u-ce>ᵍv-ce : r-ce ⊢ u-ce >ᵍ v-ce
u-ce>ᵍv-ce = sub GreedyOrder.choice-lr

flat-u-ce : proj₁ ( flat { r-ce } u-ce ) ≡ 'a' ∷ []
flat-u-ce = refl

flat-v-ce : proj₁ ( flat { r-ce } v-ce ) ≡ 'b' ∷ []
flat-v-ce = refl

-- Purpose : the ∃ conclusion of ←greedy-complete fails for ( r-ce , u-ce , v-ce ) .
-- Used in : ¬←greedy-complete , ←greedy-complete-counterexample .
-- Idea    : take n ws ≡ 'a' ∷ [] fixes the head of ws ( take++drop≡id ) , so
--           the two spans would fix it to 'a' and to 'b' ; ∷-inj turns the two
--           equalities into 'a' ≡ 'b' .
¬←greedy-complete-ce : ¬ ( ∃[ w ] ∃[ i ] ∃[ j ] ∃[ k ]
      ( ( proj₁ ( flat { r-ce } u-ce ) ) ≡ ( take ( j ∸ i ) ( drop i w ) )
      × ( proj₁ ( flat { r-ce } v-ce ) ) ≡ ( take ( k ∸ i ) ( drop i w ) )
      × ( r-ce ∣ w ∣ i ⊢ j < k ) ) )
¬←greedy-complete-ce ( w , i , j , k , ( fu , fv , j<k) ) =
  ⊥-elim ( ¬'a'≡'b'
    ( proj₁ ( ∷-inj { 'a' } { 'b' } { drop ( j ∸ i ) ws } { drop ( k ∸ i ) ws }
                  ( trans p-u (sym p-v) ) ) ) )
  where
    ws : List Char
    ws = drop i w
    -- the u -span fixes the head of ws to 'a' …
    p-u : 'a' ∷ drop ( j ∸ i ) ws ≡ ws
    p-u = trans ( sym ( cong ( λ t → t ++ drop ( j ∸ i ) ws )
                             ( trans ( sym fu ) flat-u-ce ) ) )
                ( take++drop≡id ( j ∸ i ) ws )
    -- … and the v -span fixes it to 'b' .
    p-v : 'b' ∷ drop ( k ∸ i ) ws ≡ ws
    p-v = trans ( sym ( cong ( λ t → t ++ drop ( k ∸ i ) ws )
                             ( trans ( sym fv ) flat-v-ce ) ) )
                ( take++drop≡id ( k ∸ i ) ws )
    ¬'a'≡'b' : ¬ ( 'a' ≡ 'b' )
    ¬'a'≡'b' ()

-- Purpose : ←greedy-complete ( the conjecture , for every r / u / v ) is false .
-- Used in : ←greedy-complete-counterexample .
-- Idea    : instantiate the conjecture at ( r-ce , u-ce , v-ce ) , whose
--           premise is inhabited , and refute its ∃ part .
¬←greedy-complete : ¬ ( ( r : RE ) ( u v : U r )
    → ( r ⊢ u >ᵍ v )
    → ∃[ w ] ∃[ i ] ∃[ j ] ∃[ k ]
        ( ( proj₁ ( flat u ) ) ≡ ( take ( j ∸ i ) ( drop i w ) )
        × ( proj₁ ( flat v ) ) ≡ ( take ( k ∸ i ) ( drop i w ) )
        × ( r ∣ w ∣ i ⊢ j < k ) ) )
¬←greedy-complete H with ( H r-ce u-ce v-ce u-ce>ᵍv-ce )
... | ( w , i , j , k , ( fu , fv , j<k) )
  = ¬←greedy-complete-ce ( w , i , j , k , ( fu , fv , j<k) )

-- the counterexample assembled : the premise holds while the conclusion
-- fails ( cf. the counterexample of ←greedy-sound in RelatedWorkMamouras2 ) .
←greedy-complete-counterexample : ( r-ce ⊢ u-ce >ᵍ v-ce )
  × ¬ ( ∃[ w ] ∃[ i ] ∃[ j ] ∃[ k ]
        ( ( proj₁ ( flat { r-ce } u-ce ) ) ≡ ( take ( j ∸ i ) ( drop i w ) )
        × ( proj₁ ( flat { r-ce } v-ce ) ) ≡ ( take ( k ∸ i ) ( drop i w ) )
        × ( r-ce ∣ w ∣ i ⊢ j < k ) ) )
←greedy-complete-counterexample = u-ce>ᵍv-ce , ¬←greedy-complete-ce
```



```agda

import cgp.posix.Order as POSIXOrder
open POSIXOrder renaming ( _⊢_>_ to  _⊢_>ᵖ_ )
open POSIXOrder renaming ( _⊢_>ⁱ_ to _⊢_>ᵖⁱ_ )


-- Purpose : strictness of truncated subtraction under a span hypothesis :
--           for a start index inside the span ( i ≤ k ) , k < j implies
--           k ∸ i < j ∸ i .
-- Used in : ←posix-sound .
-- Idea    : i ≤ k ≤ j rewrites both sides as i + ( _ ∸ i ) ( m+[n∸m]≡n ) ,
--           and +-cancelˡ-< cancels the common left summand .
∸-<-< : ( i j k : ℕ )
  → ( i≤k : i Nat.≤ k )
  → ( k<j : k Nat.< j )
  → k ∸ i Nat.< j ∸ i
∸-<-< i j k i≤k k<j =
  +-cancelˡ-< i ( k ∸ i ) ( j ∸ i )
    ( subst₂ _<_ ( sym ( m+[n∸m]≡n i≤k ) )
                 ( sym ( m+[n∸m]≡n ( ≤-trans i≤k (<⇒≤ k<j) ) ) )
                 k<j )

←posix-sound : ( r : RE ) ( w : List Char ) ( i j k : ℕ )
  → ( p : r ∣ w ∣ i ⊩ j < k )
  → ∃[ u ] ∃[ w₁ ] ∃[ w₂ ]
         ( proj₁ ( flat { r } u ) ≡ w₁
         × w₁ ++ w₂ ≡ drop i w
         × length w₁ ≡ j ∸ i
         × ∀ ( v : U r ) 
           → ( proj₁ (flat v) ) ≡ (take ( k ∸ i ) ( drop i w ) ) 
           → r ⊢ u >ᵖ v )


-- Purpose : soundness of Mamouras 's POSIX span order ( _∣_∣_⊩_<_ , the
--           leftmost-longest order of section 2.1 ) for the POSIX parse-tree
--           order >ᵖ : when the span ( i , j ) is below the span ( i , k ) ,
--           a witness of the ( i , j ) span is POSIX-above EVERY parse of
--           the ( i , k ) substring .
-- Used in : — ( top-level goal of this file ) .
-- Idea    : the only ⊩ constructor , leftlong , asks j > k : the span order
--           prefers the LONGER span , so the top-level POSIX rule len->
--           ( longer word ⇒ greater ) settles the ∀ part outright , no
--           comparison of the two parse trees is needed . Both lengths are
--           read off by match-span-len : the witness 's via greedyU-flat ,
--           v 's via its own flat equality ; ∸-<-< turns j > k into the
--           strict inequality of the truncated lengths . The witness is
--           greedyU , the same parse ←greedy-sound-go uses , and its three
--           side conditions are greedyU-flat / take++drop≡id /
--           match-span-len .
←posix-sound r w i j k ( leftlong {r} {w} .i .j .k t₁ t₂ j>k )
  = ( greedyU r i j w t₁ , w₁ , w₂ , ( flat-ev , concat-ev , len-ev , ∀-ev ) )
  where
    w₁ : List Char
    w₁ = take ( j ∸ i ) ( drop i w )
    w₂ : List Char
    w₂ = drop ( j ∸ i ) ( drop i w )
    -- the k -span starts at i , so i ≤ k .
    i≤k : i Nat.≤ k
    i≤k = rij⊨w→i≤j t₂
    flat-ev : proj₁ ( flat { r } ( greedyU r i j w t₁ ) ) ≡ w₁
    flat-ev = greedyU-flat r i j w t₁
    concat-ev : w₁ ++ w₂ ≡ drop i w
    concat-ev = take++drop≡id ( j ∸ i ) ( drop i w )
    len-ev : length w₁ ≡ j ∸ i
    len-ev = match-span-len r i j w t₁
    -- the witness 's word length , and the length of any v that matches the
    -- k -span substring .
    len-gu : length ( proj₁ ( flat ( greedyU r i j w t₁ ) ) ) ≡ j ∸ i
    len-gu = trans ( cong length flat-ev ) len-ev
    ∀-ev : ∀ ( v : U r )
      → ( proj₁ ( flat v ) ) ≡ take ( k ∸ i ) ( drop i w )
      → r ⊢ greedyU r i j w t₁ >ᵖ v
    ∀-ev v flatv =
      len-> { r } { greedyU r i j w t₁ } { v }
        ( subst₂ _<_
            ( sym ( trans ( cong length flatv )
                           ( match-span-len r i k w t₂ ) ) )
            ( sym len-gu )
            ( ∸-<-< i j k i≤k j>k ) )

```

UNPROVABLE : the completeness direction for the POSIX order , ←posix-complete ,
is refuted by the counterexample below ( for r-pc = `a* ● a*` , u-pc and v-pc
the two splits of "a" , the premise is inhabited but the ∃ conclusion fails ;
see ¬←posix-complete-pc ) .

The span order `_∣_∣_⊩_<_` compares only the END points of two spans that share
a start ( leftlong : j > k ) , so it cannot say anything about two parses that
span the SAME interval — and that is exactly what the POSIX parse-tree order
does through len-≡ + seq₁ : it compares the SPLIT POINTS of a sequence . For
`a* ● a*` on the word "a" , u-pc gives the letter to the LEFT star ( the
POSIX -maximal split ) and v-pc gives it to the RIGHT star , so r-pc ⊢ u-pc >ᵖ
v-pc holds ; but both parses span the interval ( 0 , 1 ) , while the ∃
conclusion asks for spans ( i , j ) and ( i , k ) of the same word with j > k ,
and match-span-len pins j ∸ i and k ∸ i to the two word lengths , both 1 .

( The other top-level POSIX rule , len-> , is much closer to completeness : if
flat u extends flat v as a proper prefix the conclusion is satisfiable by
i ≡ 0 , w ≡ flat u . It still fails whenever the two words are not
prefix-comparable , for the same head-conflict reason as the ←greedy-complete
counterexample . )


```agda
-- ←posix-complete : ( r : RE ) ( u v : U r )
--   → ( r ⊢ u >ᵖ v )
--   -----------------------------------------
--   → ∃[ w ] ∃[ i ] ∃[ j ] ∃[ k ]
--       ( ( proj₁ (flat u) ) ≡ (take ( j ∸ i ) ( drop i w ) )
--       × ( proj₁ (flat v) ) ≡ (take ( k ∸ i ) ( drop i w ) )
--       × ( r ∣ w ∣ i ⊩ j < k ) )

-- the POSIX -maximal split and a non -maximal one , for `a* ● a*` on "a" .
a₁ : RE
a₁ = $ 'a' ` 1

a*₁ : RE
a*₁ = a₁ * ε∉$ ` 2

a*₂ : RE
a*₂ = ( $ 'a' ` 3 ) * ε∉$ ` 4

r-pc : RE
r-pc = a*₁ ● a*₂ ` 5

u-pc : U r-pc
u-pc = PairU ( ListU ( LetterU 'a' ∷ [] ) ) ( ListU [] )

v-pc : U r-pc
v-pc = PairU ( ListU [] ) ( ListU ( LetterU 'a' ∷ [] ) )

flat-u-pc : proj₁ ( flat { r-pc } u-pc ) ≡ 'a' ∷ []
flat-u-pc = refl

flat-v-pc : proj₁ ( flat { r-pc } v-pc ) ≡ 'a' ∷ []
flat-v-pc = refl

-- the premise : the two total lengths are EQUAL ( len-≡ ) and the left
-- component of the sequence is strictly longer ( seq₁ + len-> ) .
u-pc>ᵖv-pc : r-pc ⊢ u-pc >ᵖ v-pc
u-pc>ᵖv-pc = POSIXOrder.len-≡ refl
               ( POSIXOrder.seq₁ ( POSIXOrder.len-> { a*₁ } ( s<s z≤n) ) )

-- Purpose : the ∃ conclusion of ←posix-complete fails for ( r-pc , u-pc , v-pc ) .
-- Used in : ¬←posix-complete , ←posix-complete-counterexample .
-- Idea    : the ⊩ evidence can only be leftlong , so j > k , and ∸-<-< turns
--           that into k ∸ i < j ∸ i ; but both truncated lengths are 1 ( the
--           two word lengths , by match-span-len and the flat equalities ) ,
--           which is the irreflexive 1 < 1 .
¬←posix-complete-pc : ¬ ( ∃[ w ] ∃[ i ] ∃[ j ] ∃[ k ]
      ( ( proj₁ ( flat { r-pc } u-pc ) ) ≡ ( take ( j ∸ i ) ( drop i w ) )
      × ( proj₁ ( flat { r-pc } v-pc ) ) ≡ ( take ( k ∸ i ) ( drop i w ) )
      × ( r-pc ∣ w ∣ i ⊩ j < k ) ) )
¬←posix-complete-pc ( w , i , j , k , ( fu , fv , leftlong .i .j .k t₁ t₂ j>k ) ) =
  ⊥-elim ( <-irrefl refl
    ( subst₂ _<_ k≡1 j≡1 ( ∸-<-< i j k i≤k j>k ) ) )
  where
    i≤k : i Nat.≤ k
    i≤k = rij⊨w→i≤j t₂
    -- the truncated lengths are the word lengths , and both words are "a" .
    j≡1 : j ∸ i ≡ 1
    j≡1 = trans ( sym ( match-span-len r-pc i j w t₁ ) )
                ( sym ( cong length fu ) )
    k≡1 : k ∸ i ≡ 1
    k≡1 = trans ( sym ( match-span-len r-pc i k w t₂ ) )
                ( sym ( cong length fv ) )

-- Purpose : ←posix-complete ( the conjecture , for every r / u / v ) is false .
-- Used in : ←posix-complete-counterexample .
-- Idea    : instantiate the conjecture at ( r-pc , u-pc , v-pc ) , whose
--           premise is inhabited , and refute its ∃ part .
¬←posix-complete : ¬ ( ( r : RE ) ( u v : U r )
    → ( r ⊢ u >ᵖ v )
    → ∃[ w ] ∃[ i ] ∃[ j ] ∃[ k ]
        ( ( proj₁ ( flat u ) ) ≡ ( take ( j ∸ i ) ( drop i w ) )
        × ( proj₁ ( flat v ) ) ≡ ( take ( k ∸ i ) ( drop i w ) )
        × ( r ∣ w ∣ i ⊩ j < k ) ) )
¬←posix-complete H with ( H r-pc u-pc v-pc u-pc>ᵖv-pc )
... | ( w , i , j , k , ( fu , fv , p< ) )
  = ¬←posix-complete-pc ( w , i , j , k , ( fu , fv , p< ) )

-- the counterexample assembled : the premise holds while the conclusion
-- fails ( cf. ←greedy-complete-counterexample above ) .
←posix-complete-counterexample : ( r-pc ⊢ u-pc >ᵖ v-pc )
  × ¬ ( ∃[ w ] ∃[ i ] ∃[ j ] ∃[ k ]
        ( ( proj₁ ( flat { r-pc } u-pc ) ) ≡ ( take ( j ∸ i ) ( drop i w ) )
        × ( proj₁ ( flat { r-pc } v-pc ) ) ≡ ( take ( k ∸ i ) ( drop i w ) )
        × ( r-pc ∣ w ∣ i ⊩ j < k ) ) )
←posix-complete-counterexample = u-pc>ᵖv-pc , ¬←posix-complete-pc
```
