
## Issue: Antimirov's Partial Derivative with list concatenation as set union does not give us greedy nor POSIX matching policy. 

### POSIX matching policy  Sulzmann and Lu (FLOPS 2014) 



r₁ ⊢ v₁ > v₁'
-------------------------------------------- (Seq₁)
r₁ ● r₂ ⊢ PairU v₁ v₂ > PairU v₁' v₂'



v₁ ≡ v₁'  r₂ ⊢ v₂ > v₂'
-------------------------------------------- (Seq₂)
r₁ ● r₂ ⊢ PairU v₁ v₂ > PairU v₁' v₂'


r₁ ⊢ v₁ > v₁'
----------------------------------(ChoiceLL)
r₁ + r₂ ⊢ LeftU v₁ > LeftU v₁' 


r₂ ⊢ v₂ > v₂'
----------------------------------(ChoiceRR)
r₁ + r₂ ⊢ RightU v₂ > RightU v₂' 


len (proj₁ ∘ flat v₁) ≥ len (proj₁ ∘ flat v₂) 
----------------------------------------------(ChoiceLR)
r₁ + r₂ ⊢ LeftU v₁ > RightU v₂ 



len (proj₁ ∘ flat v₂) > len (proj₁ ∘ flat v₁)
----------------------------------------------(ChoiceRL)
r₁ + r₂ ⊢ RightU v₂ > LeftU v₁ 


r ⊢ v₁ > v₂ 
---------------------------------(StarHd)
r* ⊢ ConsU v₁ vs₁ > ConsU v₂ vs₂


v₁ ≡ v₂        r* ⊢ vs₁ > vs₂ 
---------------------------------(StarTl)
r* ⊢ ConsU v₁ vs₁ > ConsU v₂ vs₂



len (proj₁ ∘ flat v) + len (proj₁ ∘ flat vs) = 0
-----------------------------------------------(StarNilCons)
r* ⊢ NilU > ConsU v vs



len (proj₁ ∘ flat v) + len (proj₁ ∘ flat vs) > 0
------------------------------------------------(StarNilCons)
r* ⊢ ConsU v vs > NilU



### Greedy Matching Policy by Frisch and Cardelli


Rules (Seq₁), (Seq₂), (ChoiceLL), (ChoiceRR), (StarHd) and (StarTl) are identical to the POSIX policy.


-------------------------------(ChoiceLR)
r₁ + r₂ ⊢ LeftU v₁ > RightU v₂


------------------------------(StarNilCons)
r* ⊢ ConsU v vs > NilU

Assuming that the regular expression is no problematic.



### Example that shows that pd[ r , c ] do not produce greedy

r = (ε + a) ● (a + ε)                                                 -- (1)
w = a

pd[ (ε + a) ● (a + ε) , a ] =                             
  { p ● ( a + ε ) | p ∈ pd [ ε + a , a ] } ∪ pd[ (a + ε) , a ] =
  { ε ● ( a + ε ) } ∪ { ε }                                          -- (2)

Note { } is implemented as [] and  ∪ is implemented as ++, which fixes an order among partial derivatives.

As we inject the letter a from (2) back to (1) we have

 [ (PairU (RightU a) (RightU EmptyU)) ,
   (PairU (LeftU EmptyU) (LeftU a)) ]

According to greedy matching policy 

(ε + a) ● (a + ε) ⊢ (PairU (LeftU EmptyU) (LeftU a)) > (PairU (RightU a) (RightU EmptyU))


### Exmple that show that pd[ r , c ] do not produce POSIX


r = (a + b + a ● b)*                                        -- (3)
w = ab

pd[ r , a ] =
  { ε ● r } ∪ {} ∪ { ε ● b ● r } =
  { ε ● r } ∪ { ε ● b ● r }                                 -- (4)


pd[ { ε ● r } ∪ { ε ● b ● r } , b ] = { ε ● r } ∪ { ε ● r } -- (5) 

 ∵  pd[ ε ● r , b ] = pd[ ε ● (a + b + a ● b)* , b ]
                   = { } ∪ { ε ● r } 
  
     pd[ ε ● b ● r , b ] = { ε ● r } 
  

1. injecting b into (5) to produce parse trees of (4)
      [ ConsU (RightU (LeftU b)) NilU
       , PairU b NilU ]

2. injecting a into the above to get parse trees of (3)

      [ ConsU (LeftU a) (ConsU (RightU (LeftU b)) NilU)
       , ConsU (RightU (RightU (PairU a b))) NilU ]

According to POSIX matching policy

(a + b + a ● b)* ⊢ ConsU (RightU (RightU (PairU a b))) NilU > ConsU (LeftU a) (ConsU (RightU (LeftU b)) NilU


### The observation:

pd[ϕ, ℓ] = {}   pd[ε, ℓ] = {}    pd[ℓ, ℓ] = {ε}    pd[ℓ', ℓ] = {}

pd[r₁ ● r₂ , ℓ ] =
  if ε ∈ r₁ 
  then { r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] } ∪ {  r₂' ∣ r₂' ∈ pd[ r₂ , ℓ ] }
  else { r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] }

pd[r₁ + r₂ , ℓ ] = pd[ r₁ , ℓ ] ∪ pd[ r₂ , ℓ  ]

pd[r* , ℓ ] = pd[ r' ● r* ∣ r' ∈ pd( r , ℓ ) ]


pd is not greedy because in the case of pd[r₁ ● r₂ , ℓ ], where ε ∈ r₁ , we prioritize the partial derivatives from
{ r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] } over {  r₂' ∣ r₂' ∈ pd[ r₂ , ℓ ] } by putting them closer to the left of the list (ordered set),
ignoring the fact that the r₁ is possessing ε in its left choice, (see the counter example above.)



### Solution 1:

We adapt antimirov's pd[_,_] above by splitting the ε∈ r₁ case further,

pd[r₁ ● r₂ , ℓ ] =
  if ε ∈ r₁
  then if r₁ ≡ s₁ + s₂
       then pd[ s₁ ● r₂ , ℓ ]  ∪ pd [ s₂ ● r₂ , ℓ ]
       else { r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] } ∪ {  r₂' ∣ r₂' ∈ pd[ r₂ , ℓ ] }
  else { r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] }


See in greedy/GreedyPartialDerivativel.lagda.md for proof.


### Solution 2:

We define a new matching policy, let's call it Antimirov's matching


Where we replace rule (Seq₁) from the greedy matching policy with the following rules


r₁ ≡ s₁ + s₂    len (proj₁ ∘ flat v₁) > len (proj₁ ∘ flat v₁')
--------------------------------------------------------------- (SeqChoice₁)
r₁ ● r₂ ⊢ PairU v₁ v₂ > PairU v₁' v₂'


r₁ ≢ s₁ + s₂    r₁ ⊢ v₁ > v₂ 
--------------------------------------------------------------- (SeqOther₁)
r₁ ● r₂ ⊢ PairU v₁ v₂ > PairU v₁' v₂'


Yet to be proven. 
