```agda

{-# OPTIONS --rewriting  #-}
module cgp.robust.GreedyLNE where

-- Shared utilities (flat lemmas, repair helpers, ε≅, etc.)
import cgp.robust.greedylne.GreedyLNEUtils as Utils
open Utils public

-- Iso definition
import cgp.robust.greedylne.Iso as Iso
open Iso public

-- LNN definition and proofs
import cgp.robust.greedylne.LNN as LNN
open LNN public

-- Robust definition and iso→robust
import cgp.robust.greedylne.Robust as Robust
open Robust public

-- RLNN definition, embedding (lnn→rlnn), robustness, counterexample
import cgp.robust.greedylne.RLNN as RLNNMod
open RLNNMod public

-- RLN definition and robustness
import cgp.robust.greedylne.RLN as RLNMod
open RLNMod public
```

-- actually this is order isomorphism, not maximality robustness
### Isomorphic definition

`data Iso` is in `cgp.robust.greedylne.Iso`.

### A sufficient condition, Left-not-nullable form

`data LNN` and LNN proofs are in `cgp.robust.greedylne.LNN`.

### Is LNN necessary?

See `cgp.robust.greedylne.LNN`.

### Definition RLNN

`data RLNN` and counterexample to RLNN implying Iso are in `cgp.robust.greedylne.RLNN`.

### Definition RLN

`data RLN` is in `cgp.robust.greedylne.RLN`.

### RLN Robustness

RLN robustness proofs are in `cgp.robust.greedylne.RLN`.

### RLNN Robustness

RLNN robustness proofs are in `cgp.robust.greedylne.RLNN`.
