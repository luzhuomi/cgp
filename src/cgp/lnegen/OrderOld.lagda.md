```agda

{-
data >-maximal : ∀ { r : RE } ( us : List ( U r ) ) → Set where
  >-empty : ∀ { r : RE }  → >-maximal {r} []
  >-join : ∀ { r : RE } 
    → ( top : U r )
    → ( us : List (U r ) )
    → All (λ x → r ⊢ top > x) us 
    -----------------------------------------------
    → >-maximal {r} (top ∷ us )

data >-Max-Preserve : ∀ { r : RE } { c : Char } → PDInstance r c → Set where
  >-pres : ∀ { p r : RE } { c : Char } { inj : U p →  U r }
    { sound-ev : ∀ ( x : U p ) → ( proj₁ ( flat {r} (inj x) ) ≡ c ∷ ( proj₁ (flat {p} x) )) }
    → ( ( us : List (U p) )
        → (w : List Char)
        → All ( λ x → proj₁ (flat {p} x) ≡ w ) us
        → ( us-maximal : >-maximal {p} us ) 
        → ( >-maximal {r} (List.map inj us) ) ) -- preserve ≥-maximality 
    → >-Max-Preserve {r} {c} (pdinstance {p} {r} {c} inj sound-ev)
    
>-max-preserve-left : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( pdi : PDInstance l c )
    → >-Max-Preserve {l} {c} pdi
    → >-Max-Preserve {l + r ` loc} {c} (pdinstance-left pdi) 
>-max-preserve-left {l} {r} {loc} {c} (pdinstance {p} {r} {c} in₁ s-ev₁) (>-pres us→w→|us|≡w→max-us→max-map-in₁-us) =  >-pres prf
  where
    prf : (us : List (U p))
      → (w : List Char)
      → All (λ x → (proj₁ (flat x)) ≡ w) us 
      → >-maximal us
      → >-maximal (List.map (λ u → LeftU {l} {r} {loc} (in₁ u)) us)
    prf [] w [] >-empty = >-empty
    prf ( u ∷ us ) w (|u|≡w ∷ |us|≡w ) m@(>-join .(u) .(us) u≥us) with  us→w→|us|≡w→max-us→max-map-in₁-us (u ∷ us) w  (|u|≡w ∷ |us|≡w ) m
    ... | >-join in₁u map-in₁us all-in₁u>map-in₁us = >-join (LeftU (in₁ u)) (List.map (λ u₁ → LeftU (in₁ u₁)) us) (sub-prf us all-in₁u>map-in₁us ) 
      where
        sub-prf : (vs : List (U p ))
          → All (_⊢_>_ l (in₁ u)) (List.map in₁ vs)
          → All (_⊢_>_ (l + r ` loc) (LeftU (in₁ u)))
                    (List.map (λ u₁ → LeftU (in₁ u₁)) vs)
        sub-prf [] [] = []
        sub-prf (v ∷ vs) ( in₁u>in₁v ∷ xs ) = left-mono in₁u>in₁v  ∷ sub-prf vs  xs 


>-max-preserve-right : ∀ { l r : RE } { loc : ℕ } { c : Char }
    → ( pdi : PDInstance r c )
    → >-Max-Preserve {r} {c} pdi
    → >-Max-Preserve {l + r ` loc} {c} (pdinstance-right pdi) 
>-max-preserve-right {l} {r} {loc} {c} (pdinstance {p} {r} {c} in₁ s-ev₁) (>-pres us→w→|us|≡w→max-us→max-map-in₁-us) =  >-pres prf
  where
    prf : (us : List (U p))
      → (w : List Char)
      → All (λ x → (proj₁ (flat x)) ≡ w) us 
      → >-maximal us
      → >-maximal (List.map (λ u → RightU {l} {r} {loc} (in₁ u)) us)
    prf [] w [] >-empty = >-empty
    prf ( u ∷ us ) w (|u|≡w ∷ |us|≡w ) m@(>-join .(u) .(us) u≥us) with  us→w→|us|≡w→max-us→max-map-in₁-us (u ∷ us) w  (|u|≡w ∷ |us|≡w ) m
    ... | >-join in₁u map-in₁us all-in₁u>map-in₁us = >-join (RightU (in₁ u)) (List.map (λ u₁ → RightU (in₁ u₁)) us) (sub-prf us all-in₁u>map-in₁us ) 
      where
        sub-prf : (vs : List (U p ))
          → All (_⊢_>_ r (in₁ u)) (List.map in₁ vs)
          → All (_⊢_>_ (l + r ` loc) (RightU (in₁ u)))
                    (List.map (λ u₁ → RightU (in₁ u₁)) vs)
        sub-prf [] [] = []
        sub-prf (v ∷ vs) ( in₁u>in₁v ∷ xs ) = right-mono in₁u>in₁v  ∷ sub-prf vs  xs 

-}

```
