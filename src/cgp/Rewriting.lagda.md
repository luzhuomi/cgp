this module stores all the common rewriting pragmas used by multiple modules which will have downstream import effect.



```agda

{-# OPTIONS --rewriting #-}
module cgp.Rewriting where


import Data.List as List
import Data.List.Properties
open Data.List.Properties using ( ∷ʳ-++  )


open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite


{-# REWRITE ∷ʳ-++  #-}


```
