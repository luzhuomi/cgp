
## Issue: Antimirov's Partial Derivative with list concatenation as set union does not give us greedy nor POSIX matching policy. 

### POSIX matching policy  Sulzmann and Lu (FLOPS 2014) 


```
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


length |v₁| ≥ length |v₂|
----------------------------------------------(ChoiceLR)
r₁ + r₂ ⊢ LeftU v₁ > RightU v₂ 



length |v₂| > length |v₁|
----------------------------------------------(ChoiceRL)
r₁ + r₂ ⊢ RightU v₂ > LeftU v₁ 


r ⊢ v₁ > v₂ 
---------------------------------(StarHd)
r* ⊢ ConsU v₁ vs₁ > ConsU v₂ vs₂


v₁ ≡ v₂        r* ⊢ vs₁ > vs₂ 
---------------------------------(StarTl)
r* ⊢ ConsU v₁ vs₁ > ConsU v₂ vs₂



length |v| + length |vs| == 0
-----------------------------------------------(StarNilCons)
r* ⊢ NilU > ConsU v vs



length |v| + length |vs| > 0
------------------------------------------------(StarNilCons)
r* ⊢ ConsU v vs > NilU
```

where | u | denotes the word obtained by flattening u. i.e. proj₁ ∘ flat u



### Greedy Matching Policy by Frisch and Cardelli (ICALP 2004)


Rules (Seq₁), (Seq₂), (ChoiceLL), (ChoiceRR), (StarHd) and (StarTl) are identical to the POSIX policy.

```

-------------------------------(ChoiceLR)
r₁ + r₂ ⊢ LeftU v₁ > RightU v₂


------------------------------(StarNilCons)
r* ⊢ ConsU v vs > NilU

Assuming that the regular expression is no problematic.


### Partial derivative operation

pd[ϕ, ℓ] = {}   pd[ε, ℓ] = {}    pd[ℓ, ℓ] = {ε}    pd[ℓ', ℓ] = {}

pd[r₁ ● r₂ , ℓ ] =
  if ε ∈ r₁ 
  then { r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] } ∪ {  r₂' ∣ r₂' ∈ pd[ r₂ , ℓ ] }
  else { r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] }

pd[r₁ + r₂ , ℓ ] = pd[ r₁ , ℓ ] ∪ pd[ r₂ , ℓ  ]

pd[r* , ℓ ] = pd[ r' ● r* ∣ r' ∈ pd( r , ℓ ) ]
```

For simplicity, we assume concat ● is right associative, i.e. r ● s ● t is parsed as
r ● ( s ● t ).

Note the set { } is implemented as a list [] and  the set union ∪ is implemented as
list concatenation ++, which fixes an order among partial derivatives.


### Example that shows that pd[ r , c ] do not produce greedy

consider 
```
r = (ε + a) ● (a + ε)                                                -- (1)
w = a

pd[ (ε + a) ● (a + ε) , a ] =                             
  { p ● ( a + ε ) | p ∈ pd [ ε + a , a ] } ∪ pd[ (a + ε) , a ] =
  { ε ● ( a + ε ) } ∪ { ε }                                          -- (2)

```

As we inject the letter a from (2) back to (1) we have

```
 [ (PairU (RightU a) (RightU EmptyU)) , 
   (PairU (LeftU EmptyU) (LeftU a)) ]                                -- (3) 
```

which is the list of all the parse trees produced.

According to greedy matching policy 

(ε + a) ● (a + ε) ⊢ (PairU (LeftU EmptyU) (LeftU a)) > (PairU (RightU a) (RightU EmptyU))

which means that the list (3) produced by pd is not sorted according to the greedy order.


### Exmple that shows that pd[ r , c ] do not produce POSIX

(pointed out Martin and Kenny's FLOPS paper)

Consider 
```
r = (a + b + a ● b)*                                        -- (4)
w = ab

pd[ r , a ] =
  { ε ● r } ∪ {} ∪ { ε ● b ● r } =
  { ε ● r } ∪ { ε ● b ● r }                                 -- (5)


pd[ { ε ● r } ∪ { ε ● b ● r } , b ] = { ε ● r } ∪ { ε ● r } -- (6) 

 ∵  pd[ ε ● r , b ] = pd[ ε ● (a + b + a ● b)* , b ]
                   = { } ∪ { ε ● r } 
  
     pd[ ε ● b ● r , b ] = { ε ● r } 
```  

1. injecting b into (5) to produce parse trees of (5)
      ```
      [ ConsU (RightU (LeftU b)) NilU
       , PairU b NilU ]
      ```

2. injecting a into the above to get the list of  parse trees 

      ```
      [ ConsU (LeftU a) (ConsU (RightU (LeftU b)) NilU)    -- (7)
       , ConsU (RightU (RightU (PairU a b))) NilU ]
      ```



According to POSIX matching policy

```
(a + b + a ● b)* ⊢ ConsU (RightU (RightU (PairU a b))) NilU > ConsU (LeftU a) (ConsU (RightU (LeftU b)) NilU
```

which means the list (7) is not sorted according to the POSIX order.





### The observation:


pd is not greedy because in the case of pd[r₁ ● r₂ , ℓ ], where ε ∈ r₁ , we "prioritize" the partial derivatives generated from

```
{ r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] }
```

over those generated from

```
{  r₂' ∣ r₂' ∈ pd[ r₂ , ℓ ] }
```

by "putting" them closer to the left of the list (ordered set),
ignoring the fact that the r₁ is possessing ε in its left choice,
(see the counter example above.)



### Solution 1: pd + distributivity law gives us greedy matching 

We adapt antimirov's pd[_,_] above by specializing the r₁●r₂ case ,

```
pd[r₁ ● r₂ , ℓ ] =
  if ε ∈ r₁
  then if r₁ ≡ s₁ + s₂
       then pd[ s₁ ● r₂ , ℓ ]  ∪ pd [ s₂ ● r₂ , ℓ ]
       else { r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] } ∪ {  r₂' ∣ r₂' ∈ pd[ r₂ , ℓ ] }
  else { r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] }
```

As a result,

consider the same example 

```
r = (ε + a) ● (a + ε)                                                -- (1)
w = a

pd[ (ε + a) ● (a + ε) , a ] =
  pd[ ε ● (a + ε) , a ] ∪ pd[ a ● ( a + ε ) , a ] =
  { ε }                 ∪ [ ε ● ( a + ε ) ]                          -- (8)
```

As we inject the letter a from (8) back to (1) we have

```
 [ (PairU (LeftU EmptyU) (LeftU a))
 , (PairU (RightU a) (RightU EmptyU)) ]                             -- (9) 
```

which is sorted in greedy order. 


For detail proof, see 

1. `greedy/PartialDerivative.lagda.md`
1. `greedy/Order.lagda.md`
1. `greedy/ExtendedOrder.lagda.md` 


### Solution 2: pd without distributivity law gives us left non-empty matching


We define a new matching policy, let's call it left non-empty (LNE) matching policy


Where we replace rules (ChoiceLL), (ChoiceRR) from the greedy matching policy with the following rules

```
|v₁| = |v₂| = []            l ⊢ v₁ > v₂
-------------------------------------------------------------- (ChoiceLL-bothempty)
l + r  ⊢ LeftU v₁ > LeftU v₂


|v₁| !=[]    |v₂| != []     l ⊢ v₁ > v₂ 
-------------------------------------------------------------- (ChoiceLL-notempty)
l + r  ⊢ LeftU v₁ > LeftU v₂


|v₁| !=[]    |v₂| = [] 
-------------------------------------------------------------- (ChoiceLL-empty)
l + r  ⊢ LeftU v₁ > LeftU v₂


|v₁| = |v₂| = []            r ⊢ v₁ > v₂
-------------------------------------------------------------- (ChoiceRR-bothempty)
l + r  ⊢ RightU v₁ > RightU v₂


|v₁| !=[]    |v₂| != []     r ⊢ v₁ > v₂ 
-------------------------------------------------------------- (ChoiceRR-notempty)
l + r  ⊢ RightU v₁ > RightU v₂


|v₁| !=[]    |v₂| = [] 
-------------------------------------------------------------- (ChoiceRR-empty)
l + r  ⊢ RightU v₁ > RightU v₂


|v₁| = |v₂| = [] 
-------------------------------------------------------------- (ChoiceLR-bothempty)
l + r  ⊢ LeftU v₁ > RightU v₂


|v₁| !=[]    |v₂| != [] 
-------------------------------------------------------------- (ChoiceLR-notempty)
l + r  ⊢ LeftU v₁ > RightU v₂


|v₁| !=[]    |v₂| = [] 
-------------------------------------------------------------- (ChoiceLR-empty)
l + r  ⊢ LeftU v₁ > RightU v₂


|v₁| !=[]    |v₂| = [] 
-------------------------------------------------------------- (ChoiceRL-empty)
l + r  ⊢ RightU v₁ > LeftU v₂
```


Intuitively speaking, when comparing the parse trees of a choice regular expression,

1. we ignore the constructors (regardless left or right) when one of them is flattened to empty word but the other one is not, rules (ChoiceLL-empty), (ChoiceRR-empty), (ChoiceLR-empty) and (ChoiceRL-empty)
2. otherwise, the parse tree with left constructor is always greater than the one with right constructor, rules (ChoiceLR-bothempty) and (ChoiceLR-notempty)
3. otherwise, the parse tree have the same constructor, we compare the underlying parse trees, rules (ChoiceLL-bothempty), (ChoiceLL-notempty),  (ChoiceRR-bothempty) and  (ChoiceRR-notempty) 



As a result,

Recall the list of parse trees  generated from our running example (9),
which is sorted in LNE order. 


For detail proof, refer to 

1. `lne/PartialDerivative.lagda.md`
1. `lne/Order.lagda.md`
1. `lne/ExtendedOrder.lagda.md` 



### Observation:

LNE matching is neither POSIX nor greedy, it is in-between.

It should be cheaper to compute compared to POSIX, in average case, we want non-empty parse tree on the left sub parse tree, which can be tested by traversing down the list of constructors without flattening the entire parse tree.
When we implement it using pd operation, it should be cheaper than greedy as distributivity is not required, (no bit shuffling in bitcoding representation)
