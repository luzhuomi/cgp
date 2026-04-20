{-
pdi-∃2 : ∀ { r : RE } { ϕ≢r :  ϕ≢ r } { c : Char }
       → ( pdi : PDInstance r c )
       → Any ( pdi ≡_ ) pdU[ r , c ]
       → ∃[ u ] Recons u pdi

pdi-concat-∃2 : ∀ { l r : RE } { ε∈l : ε∈ l } { loc : ℕ } { ϕ≢l●r :  ϕ≢ (l ● r ` loc) } { c : Char }
        → ( pdi : PDInstance ( l ● r ` loc ) c )
        → pdi ∈ pdUConcat l r ε∈l loc c
        → ∃[ u ] Recons u pdi 


pdi*-∃2 : ∀ { r : RE } { ϕ≢r : ϕ≢ r } { pref : List Char }
        → ( pdi : PDInstance* r pref )
        →  pdi ∈ pdUMany[ r , pref ] 
        → ∃[ u ] Recons* u pdi




pdi-∃2 {ε}  {ϕ≢ε}       {c}  pdi pdi∈pdU-ε-c = Nullary.contradiction pdi∈pdU-ε-c  ¬Any[]
pdi-∃2 {$ c ` loc} {ϕ≢$} {c'} with c Char.≟ c'
... | yes refl = λ { pdi@(pdinstance {ε} {$ c ` loc} {c} inj s-ev) pdi∈pdU-c-c → inj (unflat ε) , recons (inj (unflat ε)) (ε , refl)
                   ; pdi (there pxs) → Nullary.contradiction pxs ¬Any[]  }
... | no ¬c≡c' = λ { pdi pdi∈pdU-c-c' → Nullary.contradiction pdi∈pdU-c-c' ¬Any[] }
pdi-∃2 {l + s ` loc} {ϕ≢left-right ϕ≢l ϕ≢s} {c} pdi@(pdinstance {p} {l + s ` loc}  {c} inj s-ev) pdi∈pdU-l+s-c
  = go pdU[ l , c ] pdU[ s , c ] (xs-all-∈xs pdU[ l , c ]) (xs-all-∈xs pdU[ s , c ]) pdi∈pdU-l+s-c
  where
    go : ( pdisˡ : List ( PDInstance  l  c ) )
       → ( pdisʳ : List ( PDInstance  s  c ) )
       → All ( _∈ pdU[ l , c ] ) pdisˡ  
       → All ( _∈ pdU[ s , c ] ) pdisʳ 
       → Any ( pdi ≡_ ) ((List.map pdinstance-left pdisˡ) ++ (List.map pdinstance-right pdisʳ))
       → ∃[ u ] Recons u pdi
    go []                 []     _  _            pdi∈[]     = Nullary.contradiction pdi∈[] ¬Any[]
    go ( pdiˡ@(pdinstance {p₁} {l} {c}   injˡ s-evˡ) ∷ pdisˡ  )  pdisʳ              ( pdiˡ∈pdu-l-c ∷ pdisˡall-in-pdu-l-c )  pdisʳall-in-pdu-s-c
      with  pdi-∃2 {l} {ϕ≢l} {c} pdiˡ pdiˡ∈pdu-l-c 
    ... |   uˡ , recons {p₃} {l} {c} uˡ ( w∈⟦p₃⟧ , injˡ-unflat-w∈⟦p⟧≡uˡ ) =
      λ { (there pxs) → go pdisˡ pdisʳ pdisˡall-in-pdu-l-c pdisʳall-in-pdu-s-c pxs
        ; (here refl) → (LeftU uˡ) , (recons (LeftU uˡ) (w∈⟦p₃⟧ , left-≡ injˡ-unflat-w∈⟦p⟧≡uˡ))
        }
    go []                 ( pdiʳ@(pdinstance {p₁} {s} {c}   injʳ s-evʳ) ∷ pdisʳ  ) [] ( pdiʳ∈pdu-s-c ∷ pdisʳall-in-pdu-s-c )
      with pdi-∃2 {s} {ϕ≢s} {c} pdiʳ pdiʳ∈pdu-s-c 
    ... |   uʳ , recons {p₃} {s} {c} uʳ ( w∈⟦p₃⟧ , injʳ-unflat-w∈⟦p⟧≡uʳ ) =
      λ { (there pxs) → go [] pdisʳ [] pdisʳall-in-pdu-s-c pxs
        ; (here refl) → (RightU uʳ) , recons (RightU uʳ) (w∈⟦p₃⟧ , right-≡ injʳ-unflat-w∈⟦p⟧≡uʳ) 
        }

pdi-∃2 {l + s ` loc} {ϕ≢left ϕ≢l ϕ≡s} {c} pdi@(pdinstance {p} {l + s ` loc}  {c} inj s-ev) pdi∈pdU-l+s-c
  rewrite ( pdU-ϕ-c≡[] {s} { ϕ≡s } {c}) | ++-identityʳ (List.map (pdinstance-left {l} {s} {loc} {c})  pdU[ l , c ]) = 
     go pdU[ l , c ] (xs-all-∈xs pdU[ l , c ]) pdi∈pdU-l+s-c
  where
    go : ( pdisˡ : List ( PDInstance  l  c ) )
       → All ( _∈ pdU[ l , c ] ) pdisˡ  
       → Any ( pdi ≡_ ) (List.map pdinstance-left pdisˡ)
       → ∃[ u ] Recons u pdi
    go []                                                      []                                      pdi∈[]     = Nullary.contradiction pdi∈[] ¬Any[]
    go ( pdiˡ@(pdinstance {p₁} {l} {c}   injˡ s-evˡ) ∷ pdisˡ  )  ( pdiˡ∈pdu-l-c ∷ pdisˡall-in-pdu-l-c )  
      with  pdi-∃2 {l} {ϕ≢l} {c} pdiˡ pdiˡ∈pdu-l-c 
    ... |   uˡ , recons {p₃} {l} {c} uˡ ( w∈⟦p₃⟧ , injˡ-unflat-w∈⟦p⟧≡uˡ ) =
      λ { (there pxs) → go pdisˡ  pdisˡall-in-pdu-l-c pxs
        ; (here refl) → (LeftU uˡ) , (recons (LeftU uˡ) (w∈⟦p₃⟧ , left-≡ injˡ-unflat-w∈⟦p⟧≡uˡ))
        }
pdi-∃2 {l + s ` loc} {ϕ≢right ϕ≡l ϕ≢s} {c} pdi@(pdinstance {p} {l + s ` loc}  {c} inj s-ev) pdi∈pdU-l+s-c
  rewrite ( pdU-ϕ-c≡[] {l} { ϕ≡l } {c}) | ++-identityˡ (List.map (pdinstance-right {l} {s} {loc} {c})  pdU[ s , c ]) = 
     go pdU[ s , c ] (xs-all-∈xs pdU[ s , c ]) pdi∈pdU-l+s-c
  where
    go : ( pdisˢ : List ( PDInstance  s  c ) )
       → All ( _∈ pdU[ s , c ] ) pdisˢ   
       → Any ( pdi ≡_ ) (List.map pdinstance-right pdisˢ)
       → ∃[ u ] Recons u pdi
    go []                                                      []                                      pdi∈[]     = Nullary.contradiction pdi∈[] ¬Any[]
    go ( pdiˢ@(pdinstance {p₁} {s} {c}   injˢ s-evˢ) ∷ pdisˢ  )  ( pdiˢ∈pdu-s-c ∷ pdisˢall-in-pdu-s-c )  
      with  pdi-∃2 {s} {ϕ≢s} {c} pdiˢ pdiˢ∈pdu-s-c 
    ... |   uˢ , recons {p₃} {s} {c} uˢ ( w∈⟦p₃⟧ , injˢ-unflat-w∈⟦p⟧≡uˢ ) =
      λ { (there pxs) → go pdisˢ  pdisˢall-in-pdu-s-c pxs
        ; (here refl) → (RightU uˢ) , (recons (RightU uˢ) (w∈⟦p₃⟧ , right-≡ injˢ-unflat-w∈⟦p⟧≡uˢ))
        }
pdi-∃2 {l ● s ` loc} {ϕ≢ ϕ≢l ● ϕ≢s } {c} pdi@(pdinstance {p} {l ● s ` loc} {c} inj s-ev) pdi∈pdU-l●s-c with ε∈? l
... | no ¬ε∈l = go pdU[ l , c ] (xs-all-∈xs pdU[ l , c ]) pdi∈pdU-l●s-c 
  where
    go : ( pdisˡ : List ( PDInstance  l  c ) )
       → All ( _∈ pdU[ l , c ] ) pdisˡ  
       → Any ( pdi ≡_ ) (List.map pdinstance-fst pdisˡ)
       → ∃[ u ] Recons u pdi
    go []                                                   []                                   pdi∈map-fst-pdisˡ = Nullary.contradiction pdi∈map-fst-pdisˡ ¬Any[]
    go (pdiˡ@(pdinstance {p₁} {l} {c}   injˡ s-evˡ) ∷ pdisˡ)  (pdiˡ∈pdu-l-c ∷ pdisˡ-all∈pdu-l-c )
      with pdi-∃2 {l} {ϕ≢l} {c} pdiˡ pdiˡ∈pdu-l-c                           | pdi*-∃2 {s} {ϕ≢s} {[]} (pdinstance* {s} {s} {[]} (λ u → u ) (λ u → refl )) (here refl)  -- is this the right ind-hyp? we find uˡ but what about uˢ ? 
    ... | uˡ , recons {p₃} {l} {c} uˡ ( w∈⟦p₃⟧ , injˡ-unflat-w∈⟦p₃⟧≡uˡ ) | uˢ , recons* uˢ ( w∈⟦p₄⟧ ,  injˢ-unflat-w∈⟦p₄⟧≡uˢ )  =
        λ { (there pxs) → go pdisˡ pdisˡ-all∈pdu-l-c pxs
          ; (here refl) → (PairU uˡ uˢ , recons (PairU uˡ uˢ) ((w∈⟦p₃⟧ ● w∈⟦p₄⟧ ⧺ refl) , pair-≡  injˡ-unflat-w∈⟦p₃⟧≡uˡ injˢ-unflat-w∈⟦p₄⟧≡uˢ) ) 
          }
... | yes ε∈l = pdi-concat-∃2 {l} {s} {ε∈l} {loc} {ϕ≢ ϕ≢l ● ϕ≢s } {c}  pdi pdi∈pdU-l●s-c
pdi-∃2 {l * ε∉l ` loc } {ϕ≢*} {c}  pdi@(pdinstance {p} {l * ε∉l ` loc}  {c} inj s-ev) pdi∈pdU-l*-c with ϕ≡? l
... | yes ϕ≡l rewrite (pdU-ϕ*-c≡[] {l} {ε∉l} {loc} {ϕ≡l} {c}) = Nullary.contradiction pdi∈pdU-l*-c ¬Any[] 
... | no ¬ϕ≡l = go pdU[ l , c ] ( xs-all-∈xs pdU[ l , c ]) pdi∈pdU-l*-c
  where
    go : ( pdisˡ : List (PDInstance l c ) )
      → All ( _∈ pdU[ l , c ] ) pdisˡ
      → Any ( pdi ≡_ ) (List.map pdinstance-star pdisˡ)
      → ∃[ u ] Recons u pdi
    go []  [] pdi∈map-star-pdisˡ = Nullary.contradiction pdi∈map-star-pdisˡ ¬Any[] 
    go (pdiˡ@(pdinstance {p₁} {l} {c}   injˡ s-evˡ) ∷ pdisˡ)  (pdiˡ∈pdu-l-c ∷ pdisˡ-all∈pdu-l-c )
      with pdi-∃2 {l} {¬ϕ≡r→ϕ≢r ¬ϕ≡l} {c} pdiˡ pdiˡ∈pdu-l-c
    ... | uˡ , recons  uˡ ( w∈⟦p₃⟧ , injˡ-unflat-w∈⟦p₃⟧≡uˡ ) =
      λ { (there pxs) → go pdisˡ pdisˡ-all∈pdu-l-c pxs
        ; (here refl) → mkinjList injˡ
                         (unflat (w∈⟦p₃⟧ ● ((l ● l * ε∉l ` loc ` loc) +L ε) * ⧺ refl))
                         ,
                         recons
                         (mkinjList injˡ
                          (unflat (w∈⟦p₃⟧ ● ((l ● l * ε∉l ` loc ` loc) +L ε) * ⧺ refl)))
                         ((w∈⟦p₃⟧ ● ((l ● l * ε∉l ` loc ` loc) +L ε) * ⧺ refl) , refl)
        }


{-# TERMINATING #-}
pdi-concat-∃2 {ε} {s} {ε∈ε} {loc} {ϕ≢ ϕ≢ε ● ϕ≢s}  {c} pdi pdi∈pduConcat-ε-s
  rewrite cong (λ x → Any ( _≡_ pdi ) x ) (++-identityʳ (List.map (mk-snd-pdi {ε} {s} {loc} {c} (EmptyU , flat-[] EmptyU refl)) pdU[ s , c ]))
    =  go pdU[ s , c ] ( xs-all-∈xs pdU[ s , c ]) pdi∈pduConcat-ε-s 
  where
    go : (pdisˢ : List (PDInstance s c ) )
      → All ( _∈ pdU[ s , c ] ) pdisˢ
      → Any ( pdi ≡_ ) (List.map (mk-snd-pdi (EmptyU , flat-[] EmptyU refl)) pdisˢ)
      → ∃[ u ] Recons u pdi 
    go []               []                                       pdi∈map-mk-snd-pdisˢ = Nullary.contradiction pdi∈map-mk-snd-pdisˢ ¬Any[]
    go (pdiˢ ∷ pdisˢ)   ( pdiˢ∈pdu-s-c ∷  pdisˢ-all∈pdu-s-c )   (there pxs) =  go pdisˢ pdisˢ-all∈pdu-s-c pxs
    go (pdiˢ@(pdinstance {p₁} {s} {c}   injˢ s-evˢ) ∷ pdisˢ)   ( pdiˢ∈pdu-s-c ∷  pdisˢ-all∈pdu-s-c )   (here refl)
      with  pdi-∃2 {s} {ϕ≢s} {c}  pdiˢ pdiˢ∈pdu-s-c 
    ... | uˢ , recons uˢ ( w∈⟦p⟧ ,  injˢ-unflat-w∈⟦p⟧≡uˢ ) =  (PairU EmptyU uˢ) , recons (PairU EmptyU uˢ) (w∈⟦p⟧ , pair-≡ refl injˢ-unflat-w∈⟦p⟧≡uˢ) 
pdi-concat-∃2 {l * ε∉l ` loc₁} {s} {ε∈*} {loc₂} {(ϕ≢ ϕ≢* ● ϕ≢s)} {c} pdi pdi∈pduConcat-l*-s with ϕ≡? l
... | yes ϕ≡l rewrite (pdU-ϕ*-c≡[] {l} {ε∉l} {loc₁} {ϕ≡l} {c}) | ++-identityʳ (List.map (mk-snd-pdi {l * ε∉l ` loc₁} {s} {loc₂} {c} (ListU {l} {ε∉l} {loc₁} [] , flat-[] (ListU []) refl)) pdU[ s , c ])
  = go pdU[ s , c ] ( xs-all-∈xs pdU[ s , c ] ) pdi∈pduConcat-l*-s
  where
    go : (pdisˢ : List (PDInstance s c ) )
      → All ( _∈ pdU[ s , c ] ) pdisˢ
      → pdi ∈ (List.map (mk-snd-pdi (ListU [] , flat-[] (ListU []) refl)) pdisˢ )
      -----------------------------------------------------------------------------
      → ∃[ u ] Recons u pdi
    go []             []                                  pdi∈cononcat-map-snd-pdisˢ   = Nullary.contradiction pdi∈cononcat-map-snd-pdisˢ ¬Any[]
    go (pdiˢ ∷ pdisˢ) (pdiˢ∈pdu-s-c ∷ pdisˢ-all∈pdu-s-c) (there pxs)                  = go pdisˢ pdisˢ-all∈pdu-s-c pxs
    go (pdiˢ ∷ pdisˢ) (pdiˢ∈pdu-s-c ∷ pdisˢ-all∈pdu-s-c) (here refl)
     with pdi-∃2 {s} {ϕ≢s} {c} pdiˢ pdiˢ∈pdu-s-c
    ... | uˢ , recons uˢ ( w∈⟦p⟧ , injˢ-unflat-w∈⟦p⟧≡uˢ ) = (PairU (ListU []) uˢ) , (recons (PairU (ListU []) uˢ) (w∈⟦p⟧ , pair-≡ refl  injˢ-unflat-w∈⟦p⟧≡uˢ ))
... | no ¬ϕ≡l = go pdU[ l , c ] ( xs-all-∈xs pdU[ l , c ] ) pdU[ s , c ] ( xs-all-∈xs pdU[ s , c ] ) pdi∈pduConcat-l*-s
  where
    go : (pdisˡ : List (PDInstance l c) )
      → All ( _∈ pdU[ l , c ] ) pdisˡ
      → (pdisˢ : List (PDInstance s c ) )
      → All ( _∈ pdU[ s , c ] ) pdisˢ
      → pdi ∈ List.map pdinstance-fst (List.map pdinstance-star pdisˡ ) ++ concatmap-pdinstance-snd {l * ε∉l ` loc₁} {s} {ε∈*} {loc₂} {c} pdisˢ
      -------------------------------------------------------------------------------------------------
      → ∃[ u ] Recons u pdi
    go [] [] []             []                                  pdi∈map-fst-pdisˡ++cononcat-map-snd-pdisˢ        = Nullary.contradiction pdi∈map-fst-pdisˡ++cononcat-map-snd-pdisˢ ¬Any[]
    go [] [] (pdiˢ ∷ pdisˢ) (pdiˢ∈pdu-s-c ∷ pdisˢ-all∈pdu-s-c) (there pxs)                                       = go [] [] pdisˢ pdisˢ-all∈pdu-s-c pxs
    go [] [] (pdiˢ@(pdinstance {p₁} {s} {c}   injˢ s-evˢ) ∷ pdisˢ) (pdiˢ∈pdu-s-c ∷ pdisˢ-all∈pdu-s-c) (here refl)
      with pdi-∃2 {s} {ϕ≢s} {c} pdiˢ pdiˢ∈pdu-s-c
    ... | uˢ , recons uˢ ( w∈⟦p⟧ , injˢ-unflat-w∈⟦p⟧≡uˢ ) = (PairU (ListU []) uˢ) , (recons (PairU (ListU []) uˢ) (w∈⟦p⟧ , pair-≡ refl  injˢ-unflat-w∈⟦p⟧≡uˢ ))
    go (pdiˡ ∷ pdisˡ) (pdiˡ∈pdu-l-c ∷ pdisˡ-all∈pdu-l-c)  pdisˢ pdisˢ-all∈pdu-s-c (there pxs)                    = go pdisˡ pdisˡ-all∈pdu-l-c pdisˢ pdisˢ-all∈pdu-s-c pxs 
    go (pdiˡ@(pdinstance {p₁} {l} {c}   injˡ s-evˡ )  ∷ pdisˡ) (pdiˡ∈pdu-l-c ∷ pdisˡ-all∈pdu-l-c)  pdisˢ pdisˢ-all∈pdu-s-c (here refl)
      with pdi-∃2 {l} {¬ϕ≡r→ϕ≢r ¬ϕ≡l} {c} pdiˡ pdiˡ∈pdu-l-c             | pdi*-∃2 {s} {ϕ≢s} {[]} (pdinstance* {s} {s} {[]} (λ u → u ) (λ u → refl )) (here refl) 
    ... | uˡ , recons uˡ ( w∈⟦p⟧ , injˡ-unflat-w∈⟦p⟧≡uˡ )  | uˢ , recons* uˢ ( w∈⟦p₄⟧ ,  injˢ-unflat-w∈⟦p₄⟧≡uˢ )  =
        PairU (ListU (uˡ ∷ [])) uˢ , recons (PairU (ListU (uˡ ∷ [])) uˢ) (((w∈⟦p⟧ ● ((l ● l * ε∉l ` loc₁ ` loc₁) +L ε) * ⧺ refl) ● w∈⟦p₄⟧ ⧺ refl) , pair-≡ (cong (λ x → ListU ( x ∷ [] ) ) injˡ-unflat-w∈⟦p⟧≡uˡ ) injˢ-unflat-w∈⟦p₄⟧≡uˢ ) 
pdi-concat-∃2 {l + s ` loc₁} {r} {ε∈l+s} {loc₂} {ϕ≢ (ϕ≢left-right ϕ≢l  ϕ≢s) ● ϕ≢r } {c} pdi pdi∈pduConcat-l+s-r = go  pdU[ l ● r ` loc₂ , c ] ( xs-all-∈xs pdU[ l ● r ` loc₂ , c ] )  pdU[ s ● r ` loc₂ , c ] ( xs-all-∈xs pdU[ s ● r ` loc₂ , c ] ) pdi∈pduConcat-l+s-r 
  where
    go : (pdisˡ : List (PDInstance (l ● r ` loc₂) c ) )
      →  (All ( _∈ pdU[ l ● r ` loc₂ , c ] ) pdisˡ)
      →  (pdisˢ : List (PDInstance (s ● r ` loc₂) c ) )
      →  (All ( _∈ pdU[ s ● r ` loc₂ , c ] ) pdisˢ)
      →  pdi ∈ List.map pdinstance-dist ((List.map pdinstance-left pdisˡ ) ++ (List.map pdinstance-right pdisˢ) )
      ---------------------------------------------------------------------------------------------------------
      → ∃[ u ] Recons u pdi
    go [] [] [] [] pdi∈map-dist-map-leftpdisˡ++map-rightpdisʳ  =  Nullary.contradiction  pdi∈map-dist-map-leftpdisˡ++map-rightpdisʳ ¬Any[]
    go [] [] (pdiˢ ∷ pdisˢ) (pdiˢ∈pdu-s-r-c ∷ pdisˢ-all∈pdu-s-r-c) (there pxs) = go [] []  pdisˢ pdisˢ-all∈pdu-s-r-c pxs
    go [] [] (pdiˢ@(pdinstance {p₁} {s ● r ` loc₂} {c}   injˢ s-evˢ) ∷ pdisˢ) (pdiˢ∈pdu-s-r-c ∷ pdisˢ-all∈pdu-s-c) (here refl)
      with  pdi-∃2 {s ● r ` loc₂} {ϕ≢ ϕ≢s ● ϕ≢r } {c} pdiˢ pdiˢ∈pdu-s-r-c
    ... | uˢ , recons uˢ ( w∈⟦p⟧ , injˢ-unflat-w∈⟦p⟧≡uˢ ) = inv-dist (RightU (injˢ (unflat w∈⟦p⟧))) , recons (inv-dist (RightU (injˢ (unflat w∈⟦p⟧)))) (w∈⟦p⟧ , refl) 
    go (pdiˡ ∷ pdisˡ) (pdiˡ∈pdu-l-r-c ∷ pdisˡ-all∈pdu-l-r-c)  pdisˢ pdisˢ-all∈pdu-s-r-c (there pxs)                    = go pdisˡ pdisˡ-all∈pdu-l-r-c pdisˢ pdisˢ-all∈pdu-s-r-c pxs 
    go (pdiˡ@(pdinstance {p₁} {l ● r ` loc₂} {c}   injˡ s-evˡ )  ∷ pdisˡ) (pdiˡ∈pdu-l-r-c ∷ pdisˡ-all∈pdu-l-r-c)  pdisˢ pdisˢ-all∈pdu-s-r-c (here refl)
      with pdi-∃2 {l ● r ` loc₂ } {ϕ≢ ϕ≢l ● ϕ≢r }  {c} pdiˡ pdiˡ∈pdu-l-r-c             
    ... | uˡ , recons uˡ ( w∈⟦p⟧ , injˡ-unflat-w∈⟦p⟧≡uˡ )   =
      inv-dist (LeftU (injˡ (unflat w∈⟦p⟧))) ,   recons (inv-dist (LeftU (injˡ (unflat w∈⟦p⟧)))) (w∈⟦p⟧ , refl)

pdi-concat-∃2 {l + s ` loc₁} {r} {ε∈l+s} {loc₂} {ϕ≢ (ϕ≢left ϕ≢l  ϕ≡s) ● ϕ≢r } {c} pdi pdi∈pduConcat-l+s-r
  rewrite (pdU-ϕ-c≡[] {s ● r ` loc₂}  {ϕ≡fst ϕ≡s} {c}) | ++-identityʳ (List.map (pdinstance-left { l ● r ` loc₂ } {  s ● r ` loc₂ } {loc₁} {c}) pdU[ l ● r ` loc₂ , c ] ) =
   go  pdU[ l ● r ` loc₂ , c ] ( xs-all-∈xs pdU[ l ● r ` loc₂ , c ] ) pdi∈pduConcat-l+s-r
  where
    go : (pdisˡ : List (PDInstance (l ● r ` loc₂) c ) )
      →  (All ( _∈ pdU[ l ● r ` loc₂ , c ] ) pdisˡ )
      →  pdi ∈ List.map pdinstance-dist (List.map pdinstance-left pdisˡ ) 
      ---------------------------------------------------------------------------------------------------------
      → ∃[ u ] Recons u pdi
    go [] [] pdi∈map-dist-map-leftpdisˡ =  Nullary.contradiction  pdi∈map-dist-map-leftpdisˡ ¬Any[]
    go (pdiˡ ∷ pdisˡ) (pdiˡ∈pdu-l-r-c ∷ pdisˡ-all∈pdu-l-r-c)  (there pxs)                    = go pdisˡ pdisˡ-all∈pdu-l-r-c pxs
    go (pdiˡ@(pdinstance {p₁} {l ● r ` loc₂} {c}   injˡ s-evˡ )  ∷ pdisˡ) (pdiˡ∈pdu-l-r-c ∷ pdisˡ-all∈pdu-l-r-c)  (here refl)
      with pdi-∃2 {l ● r ` loc₂ } {ϕ≢ ϕ≢l ● ϕ≢r }  {c} pdiˡ pdiˡ∈pdu-l-r-c             
    ... | uˡ , recons uˡ ( w∈⟦p⟧ , injˡ-unflat-w∈⟦p⟧≡uˡ )   =
      inv-dist (LeftU (injˡ (unflat w∈⟦p⟧))) ,   recons (inv-dist (LeftU (injˡ (unflat w∈⟦p⟧)))) (w∈⟦p⟧ , refl)

pdi-concat-∃2 {l + s ` loc₁} {r} {ε∈l+s} {loc₂} {ϕ≢ (ϕ≢right ϕ≡l  ϕ≢s) ● ϕ≢r } {c} pdi pdi∈pduConcat-l+s-r
  rewrite (pdU-ϕ-c≡[] {l ● r ` loc₂}  {ϕ≡fst ϕ≡l} {c}) | ++-identityˡ (List.map (pdinstance-right { l ● r ` loc₂ } {  s ● r ` loc₂ } {loc₁} {c}) pdU[ s ● r ` loc₂ , c ] ) =
   go  pdU[ s ● r ` loc₂ , c ] ( xs-all-∈xs pdU[ s ● r ` loc₂ , c ] ) pdi∈pduConcat-l+s-r
  where
    go : (pdisˢ : List (PDInstance (s ● r ` loc₂) c ) )
      →  (All ( _∈ pdU[ s ● r ` loc₂ , c ] ) pdisˢ )
      →  pdi ∈ List.map pdinstance-dist (List.map pdinstance-right pdisˢ ) 
      ---------------------------------------------------------------------------------------------------------
      → ∃[ u ] Recons u pdi
    go [] [] pdi∈map-dist-map-rightpdisʳ =  Nullary.contradiction  pdi∈map-dist-map-rightpdisʳ ¬Any[]
    go (pdiˢ ∷ pdisˢ) (pdiˢ∈pdu-s-r-c ∷ pdisˢ-all∈pdu-s-r-c)  (there pxs)                    = go pdisˢ pdisˢ-all∈pdu-s-r-c pxs
    go (pdiˢ@(pdinstance {p₁} {s ● r ` loc₂} {c}   injˢ s-evˢ )  ∷ pdisˢ) (pdiˢ∈pdu-s-r-c ∷ pdisˢ-all∈pdu-s-r-c)  (here refl)
      with pdi-∃2 {s ● r ` loc₂ } {ϕ≢ ϕ≢s ● ϕ≢r }  {c} pdiˢ pdiˢ∈pdu-s-r-c             
    ... | uˢ , recons uˢ ( w∈⟦p⟧ , injˢ-unflat-w∈⟦p⟧≡uˢ )   =
      inv-dist (RightU (injˢ (unflat w∈⟦p⟧))) ,   recons (inv-dist (RightU (injˢ (unflat w∈⟦p⟧)))) (w∈⟦p⟧ , refl)




pdi-concat-∃2 {l ● s ` loc₁} {r} {ε∈l●s} {loc₂} {ϕ≢ (ϕ≢ ϕ≢l ● ϕ≢s ) ● ϕ≢r } {c} pdi pdi∈pduConcat-l●s-r  = go pdU[  l ● ( s ● r ` loc₂ ) ` loc₁ , c ]  ( xs-all-∈xs pdU[  l ● ( s ● r ` loc₂ ) ` loc₁ , c ] ) pdi∈pduConcat-l●s-r  
  where
    go : (pdisˡ : List (PDInstance ( l ● ( s ● r ` loc₂ ) ` loc₁) c ) )
      → (All ( _∈ pdU[  l ● ( s ● r ` loc₂ ) ` loc₁ , c ] ) pdisˡ)
      → pdi ∈ List.map pdinstance-assoc pdisˡ
      ---------------------------------------------------------------------
      → ∃[ u ] Recons u pdi
    go []             []                                           pdi∈map-assoc-pdisˡ = Nullary.contradiction pdi∈map-assoc-pdisˡ ¬Any[]
    go (pdiˡ ∷ pdisˡ) (pdiˡ∈pdu-l-s-r-c ∷ pdisˡ-all∈pdu-l-s-r-c )  (there pxs)         = go  pdisˡ pdisˡ-all∈pdu-l-s-r-c pxs
    go (pdiˡ@(pdinstance {p₁} {( l ● ( s ● r ` loc₂ ) ` loc₁ )} {c}   injˡ s-evˡ )  ∷ pdisˡ) (pdiˡ∈pdu-l-s-r-c ∷ pdisˡ-all∈pdu-l-s-r-c )  (here refl)
       with pdi-∃2 { ( l ● ( s ● r ` loc₂ ) ` loc₁ ) }  {ϕ≢ ϕ≢l ●  (ϕ≢  ϕ≢s  ● ϕ≢r ) }  {c} pdiˡ pdiˡ∈pdu-l-s-r-c
    ... | uˡ ,  recons uˡ ( w∈⟦p⟧ , injˡ-unflat-w∈⟦p⟧≡uˡ )   = inv-assoc (injˡ (unflat w∈⟦p⟧)) , recons (inv-assoc (injˡ (unflat w∈⟦p⟧))) (w∈⟦p⟧ , refl)



pdi*-∃2 {r} {ϕ≢r} {[]} pdi@(pdinstance* inj s-ev)              (there pxs) = Nullary.contradiction pxs ¬Any[] 
pdi*-∃2 {ϕ} {ϕ≢ϕ} {[]} pdi@(pdinstance* {ϕ} {ϕ} {[]} inj s-ev) (here refl) = Nullary.contradiction ϕ≡ϕ (ϕ≢r→¬ϕ≡r ϕ≢ϕ)    
pdi*-∃2 {ε} {ϕ≢ε} {[]} pdi@(pdinstance* inj s-ev) (here refl) = unflat ε , recons* (unflat ε) (ε , refl) 
pdi*-∃2 {$ c ` loc} {ϕ≢$} {[]} pdi@(pdinstance* inj s-ev) (here refl) = unflat ($ c) , recons* (unflat ($ c)) (($ c) , refl) 
pdi*-∃2 {l ● s ` loc} {ϕ≢ ϕ≢l ● ϕ≢s } {[]} pdi@(pdinstance* inj s-ev) (here refl)
  with pdi*-∃2 {l} {ϕ≢l} {[]} (pdinstance* {l} {l} {[]} (λ u → u ) (λ u → refl )) (here refl) |  pdi*-∃2 {s} {ϕ≢s} {[]} (pdinstance* {s} {s} {[]} (λ u → u ) (λ u → refl )) (here refl)
... | uˡ , recons* uˡ ( w∈⟦p⟧ ,  injˡ-unflat-w∈⟦p⟧≡uˡ )  | uˢ , recons* uˢ ( w∈⟦p₂⟧ ,  injˢ-unflat-w∈⟦p₂⟧≡uˢ )  = (PairU uˡ uˢ) , recons* (PairU uˡ uˢ) ((w∈⟦p⟧ ● w∈⟦p₂⟧ ⧺ refl) , pair-≡ injˡ-unflat-w∈⟦p⟧≡uˡ injˢ-unflat-w∈⟦p₂⟧≡uˢ ) 
pdi*-∃2 {l + s ` loc} {ϕ≢left ϕ≢l ϕ≡s } {[]} pdi@(pdinstance* inj s-ev) (here refl)
  with pdi*-∃2 {l} {ϕ≢l} {[]} (pdinstance* {l} {l} {[]} (λ u → u ) (λ u → refl )) (here refl)  -- just pick left
... | uˡ , recons* uˡ ( w∈⟦p⟧ ,  injˡ-unflat-w∈⟦p⟧≡uˡ )  = LeftU uˡ , recons* (LeftU uˡ) ((s +L w∈⟦p⟧) , left-≡ injˡ-unflat-w∈⟦p⟧≡uˡ )
pdi*-∃2 {l + s ` loc} {ϕ≢right ϕ≡l ϕ≢s } {[]} pdi@(pdinstance* inj s-ev) (here refl)
  with pdi*-∃2 {s} {ϕ≢s} {[]} (pdinstance* {s} {s} {[]} (λ u → u ) (λ u → refl )) (here refl)  -- just pick right
... | uˢ , recons* uˢ ( w∈⟦p⟧ ,  injˢ-unflat-w∈⟦p⟧≡uˢ )  = RightU uˢ , recons* (RightU uˢ) ((l +R w∈⟦p⟧) , right-≡ injˢ-unflat-w∈⟦p⟧≡uˢ )
pdi*-∃2 {l + s ` loc} {ϕ≢left-right ϕ≢l ϕ≢s } {[]} pdi@(pdinstance* inj s-ev) (here refl)
  with pdi*-∃2 {l} {ϕ≢l} {[]} (pdinstance* {l} {l} {[]} (λ u → u ) (λ u → refl )) (here refl)  -- just pick left
... | uˡ , recons* uˡ ( w∈⟦p⟧ ,  injˡ-unflat-w∈⟦p⟧≡uˡ )  = LeftU uˡ , recons* (LeftU uˡ) ((s +L w∈⟦p⟧) , left-≡ injˡ-unflat-w∈⟦p⟧≡uˡ )
pdi*-∃2 {l * ε∉l ` loc} {ϕ≢*} {[]} pdi@(pdinstance* inj s-ev) (here refl) = 
  ListU [] , recons* (ListU []) ((((l ● l * ε∉l ` loc ` loc) +L ε) *) , refl)


pdi*-∃2 {r} {ϕ≢r} {c ∷ cs} pdi@(pdinstance* {p} {r} {c ∷ cs}  inj s-ev)           pdi∈pdUMany-r-ccs  with ε∈? p
... |  yes ε∈p with mkAllEmptyU ε∈p in mkAllEmptyU-e∈p-eq 
...              | ( e ∷ es ) = inj e , recons* (inj e) ((proj₂ (flat e)) , prf) -- base case, we don't need   pdi∈pdUMany-r-ccs
  where
    prf  : inj (unflat (Product.proj₂ (flat e))) ≡ inj e
    prf = cong (λ x → inj x ) unflat∘proj₂∘flat
...              | [] = Nullary.contradiction  mkAllEmptyU-e∈p-eq ( mkAllEmptyU≢[] ε∈p)     -- we need to create a contradiction here. mkAllEmptyU is not empty

pdi*-∃2 {r} {ϕ≢r} {c ∷ cs} pdi@(pdinstance* {p} {r} {c ∷ cs}  inj s-ev)           pdi∈pdUMany-r-ccs
   | no ¬ε∈p with ϕ≡? p  -- since r is not phi, p must not be phi, we should be able to find at least one leading letter from p such that
...            | yes ϕ≡p = {!!}  -- we need to create a contradiction  -- how to get ϕ≢ p ? from pdi∈pdUMany-r-ccs ? 
...            | no ¬ϕ≡p with first p in first-p-eq 
...                       |  []  = Nullary.contradiction first-p-eq (ϕ≢-ε∉→¬first≡[] (¬ϕ≡r→ϕ≢r ¬ϕ≡p) (¬ε∈r→ε∉r ¬ε∈p)) 
...                       |  ( d ∷ ds ) with pdU[ p , d ]
...                                       | []  = {!!} -- since d is in first p, pdU[ p , d ] should not be [] 
...                                       | pdi' ∷ _  = {!!}






-- do we need to bake this into the pdinstance construction? definitiely not in pdinstance* 
-- 1. given pdisntance p r c inj s-ev
-- 2.   ind hyp shows exist v and pdi such that : U p, Recons v pdi
-- 3.   inj v : U r, recons (inj v) (pdinstance p r c inj s-ev) 



data Pd¬ϕ :  { r : RE } { c : Char } → PDInstance r c → Set  where 
  pd¬ϕ : ∀ { p r : RE } { c : Char } 
       → ( inj : U p → U r ) -- ^ the injection function 
       → ( s-ev : ∀ ( u : U p ) → ( proj₁ ( flat {r} (inj u) ) ≡ c ∷ ( proj₁ (flat {p} u) )) )
       → ( ϕ≢ p )
       → Pd¬ϕ {r} {c} (pdinstance {p} {r} {c} inj s-ev)
       

pdU-all¬ϕ : ∀ ( r : RE ) → ( c : Char )
  → All Pd¬ϕ pdU[ r , c ]
pdU-all¬ϕ ϕ c = [] 
pdU-all¬ϕ ε c = []
pdU-all¬ϕ ($ c ` _ ) c' with c Char.≟ c'
... | yes refl =  pd¬ϕ (λ u → LetterU c)
                        (λ EmptyU →                 -- ^ soudness ev
                          begin
                            [ c ]
                          ≡⟨⟩
                            c ∷ []
                          ≡⟨ cong ( λ x → ( c ∷  x) ) (sym (flat-Uε≡[] EmptyU)) ⟩
                            c ∷ (proj₁ (flat EmptyU))
                          ∎)
                        ϕ≢ε
                        ∷ [] 
... | no ¬c≡c' = []
-} 
