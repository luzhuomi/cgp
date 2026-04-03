
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
------------------------------------------------(StarConsNil)
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
```

Assuming that the regular expression is not problematic.


### Partial derivative operation

```
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

(as reported in Martin and Kenny's FLOPS paper)

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

1. injecting b into (6) to produce parse trees of (5)
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


Where we replace rules (ChoiceLL), (ChoiceRR) and (ChoiceLR) from the greedy matching policy with the following rules

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




## Identifying "lne-greedy-problematic" expression ( also "lne-greedy-robust" expressions as contrapositition )


Definition (robustness)

A regular expressionr is lne-greedy robust iff

  ∀ v₁ v₂ : U r,  r ⊢ v₁ >ᵍ v₂ ⇔ v₁ >ˡ v₂ 

Note that we write v : U r to denote a parse tree v of regular expression r.


Since our `parseAll` functions implemented using partial derivatives are sound and complete, in other words,


A regular expression dr is lne-greedy robust iff

  ∀ w ∈ L( r ),  parseAll_lne(r , w )  ≡ parseAll_greedy(r , w )


We can now observe when the two parseAll functions differ.

The problematic situation arise when we encounter a partial derivative descendant with the shape of  `r₁ ● r₂` and `ε∈ r₁`.

The pd operation without distributivity law produces

```
 { r₁' ● r₂ ∣ r₁' ∈ pd[ r₁ , ℓ ] }    -- (Set₁)
 ∪
 {  r₂' ∣ r₂' ∈ pd[ r₂ , ℓ ] }        -- (Set₂)
```


#### Parse trees generated from (Set₁)

Let

```
inj₁ : U r₁' → U r₁ 

```
be the injection function attached as proof term of `pd[ r₁ , ℓ ]`

Parse trees generated from (Set₁) can be constructed by applying 

```
injFst : (U r₁' → U r₁) → U (r₁' ● r₂) → U (r₁ ● r₂)
injFst inj (Pair v₁ v₂) = Pair (inj v₁) v₂ 
```

to `inj₁`. Note that for any parse tree `v₁` of type `U r₁'`,  `inj₁ v₁` will be flattened to non-empty word.


#### Parse trees generated from (Set₂)


Let

```
mkAllEmptyU : r₁ → ε ∈ r₁ → List [U r₁]
```

be the function that construct all the empty parse trees given an nullable regular expression `r₁`.

The parse trees generated from (Set₂) can be constructed by applying 

```
injSnd : (U r₂' → U r₂) → U r₁ → U r₂' →  U (r₁ ● r₂)
injSnd inj emp₁ v₂ = Pair emp₁ (inj v₂)

```

to `mkAllEmptyU` and `inj₂ : U r₂' → U r₂` where `inj₂` is derived from `pd[ r₂ , ℓ ]`.

Note that `emp₁` is flattened to the empty word.


### The root cause 

In the LNE matching policy,

```
r₁ ● r₂ ⊢ Pair (inj₁ v₁) v₂ >ˡ Pair emp₁ (inj₂ v₃)
```

for any parse tree v₃ of type `U r₂'`, assuming ● is right associative. 


Under the greedy matching policy, the above is not necessarily true. because
only the seq₁ rule, is applicable, which requires

`r₁ ⊢ inj₁ v₁ >ᵍ emp₁`     -- (2)


Let's break down r₁ by cases. Since ε ∈ r₁, r₁ can only be ε , l* , l ● s , or l + s.

case ε : not possible, because pd[ ε , ℓ ] = []

case l*: (2) always true, since (inj₁ v₁) is not flattened the empty word, it must be `ConsU u us` for some u and us.
and `emp₁` must be NilU since we consider non problematic regular expression only.


case l ● s: ε ∈ l ● s implies ε ∈ l and ε ∈ s, emp₁ must be some Pair emp₂ emp₃ where both emp₂ and emp₃ are flattened to the empty word.
We apply "induction" to look at `l ● s` only.

case l + s:
  sub case ε ∉ l and ε ∈ s :  emp₁ must be RightU emp₂ for some emp₂
    (inj₁ v₁) can be LeftU v₁' or RightU v₁'
      sub sub case inj₁ v₁ ≡ LeftU v₁' we apply (choiceLR) rule to verify (2) 
      sub sub case inj₁ v₁ ≡ RightU v₁', we can "inductively" check s ● r.

  sub case ε ∈ l : this is the "problematic" case, since emp₁ must be LeftU emp₂ for some emp₂
    but (there exists) RightU v₁' ≡ inj₁ v₁ that causes (2) to be violated.


In short, we can only allow ε ∈ s to appear at the right most alternative.


### A sufficient condition 


Definition: Left Non Nullable 
A regular expression r is in left non nullable form, iff, forall sub expression (s + t) in r, s is not nullable.

Formally, we say r is LNN iff any of the following holds, 
1) r is ε; 
2) r is l
3) r is l ● s and l is LNN and s is LNN.
4) r is l + s and l is LNN, ε∉ l and s is LNN.
5) r is l * and l is LNN.

    


### Lemma : LNN is a sufficient condition of robustness

Let r be a regular expression in LNN. Then r is lne-greedy robust.

For detail proof, refer to

`robust/GreedyLNE.lagda.md`


### Conjecture : is LNN necessary? 


### How to get POSIX policy? 

#### Updated on Feb 6 2026

The POSIX order defined in FLOPS 2014 is problematic, it is creating a loop among parse trees. 


The main issue lies in the ChoiceLL and ChoiceRR rules 


```
r₁ ⊢ v₁ > v₁'
----------------------------------(ChoiceLL)
r₁ + r₂ ⊢ LeftU v₁ > LeftU v₁' 


r₂ ⊢ v₂ > v₂'
----------------------------------(ChoiceRR)
r₁ + r₂ ⊢ RightU v₂ > RightU v₂' 
```


Consider `r = (a* ● a*) + a*` 

w = `aa`

Let 

```
u₁ = L (Pair [] [a,a])
u₂ = R [a,a]
```
According to ChoiceLR rule, `r ⊢ u₁ > u₂`

Let

w' = `a`
```
u₃ = L (Pair [a] [] )
```
According to ChoiceRL rule, `r ⊢ u₂ > u₃`

According to ChoiceLL rule, `r ⊢ u₃ > u₁`

We have a loop! Why this is bad? consider another regular expression `t = r ● a*`

what is the max value according to the > order?

```
v₁ = Pair u₁ []
v₂ = Pair u₂ []
v₃ = Pair u₃ [a]
```


A proposed solution. refine the ChoiceLL and ChoiceRR to use `length |_| > length |_|` 
instead of `r ⊢ _ > _` only when the length are equal, we break the tie using `r ⊢ _ > _`.


```
length |v₁| = length |v₁'|
r₁ ⊢ v₁ > v₁'
----------------------------------(ChoiceLL-=)
r₁ + r₂ ⊢ LeftU v₁ > LeftU v₁' 


length |v₁| > length |v₁'|
----------------------------------(ChoiceLL->)
r₁ + r₂ ⊢ LeftU v₁ > LeftU v₁' 


length |v₂| = length |v₂'|
r₂ ⊢ v₂ > v₂'
----------------------------------(ChoiceRR-=)
r₁ + r₂ ⊢ RightU v₂ > RightU v₂' 


length |v₂| > length |v₂'|
----------------------------------(ChoiceRR->)
r₁ + r₂ ⊢ RightU v₂ > RightU v₂' 
```

>>> Question: do we need to adjust the Seq and Star rules?
Answer: yes, see below.


#### Updated on Feb 13 2026

to address the above issue mentioned on Feb 6 2026, we introduce a two-level definition for the posix order.

We write r ⊢ v > v' to denote the "top" level order and 
r ⊢ v >ⁱ v' to denote the "internal" or "intermediate" level order. 

There are only two cases for the top level. 

```
len |v₁| ≡ len |v₂|
r ⊢ v₁ >ⁱ v₂
--------------------------------(≡-len)
r ⊢ v₁ > v₂


len |v₁| > len |v₂|
--------------------------------(>-len)
r ⊢ v₁ > v₂
```


We adjust the > from FLOPS 2014 as the internal order by replacing all the inductive premises by top level order.


```

r₁ ⊢ v₁ > v₁'
-------------------------------------------- (Seq₁)
r₁ ● r₂ ⊢ PairU v₁ v₂ >ⁱ PairU v₁' v₂'



v₁ ≡ v₁'  r₂ ⊢ v₂ > v₂'
-------------------------------------------- (Seq₂)
r₁ ● r₂ ⊢ PairU v₁ v₂ >ⁱ PairU v₁' v₂'


r₁ ⊢ v₁ > v₁'
----------------------------------(ChoiceLL)
r₁ + r₂ ⊢ LeftU v₁ >ⁱ LeftU v₁' 


r₂ ⊢ v₂ > v₂'
----------------------------------(ChoiceRR)
r₁ + r₂ ⊢ RightU v₂ >ⁱ RightU v₂' 


length |v₁| ≥ length |v₂| <-- the premise of this rule can be omitted 
----------------------------------------------(ChoiceLR) 
r₁ + r₂ ⊢ LeftU v₁ >ⁱ RightU v₂ 



length |v₂| > length |v₁|
----------------------------------------------(ChoiceRL)  <-- this rule can be omitted 
r₁ + r₂ ⊢ RightU v₂ >ⁱ LeftU v₁ 


r ⊢ v₁ > v₂ 
---------------------------------(StarHd)
r* ⊢ ConsU v₁ vs₁ >ⁱ ConsU v₂ vs₂


v₁ ≡ v₂        r* ⊢ vs₁ > vs₂ 
---------------------------------(StarTl)
r* ⊢ ConsU v₁ vs₁ >ⁱ ConsU v₂ vs₂



length |v| + length |vs| == 0
-------------------------------------------(StarNilCons)  <-- this rule can be omitted 
r* ⊢ NilU >ⁱ ConsU v vs



length |v| + length |vs| > 0
------------------------------------------(StarConsNil)
r* ⊢ ConsU v vs >ⁱ NilU
```


The adjusted ordering is the POSIX ordering.  Some key observations

1. (StarNilCons) rule can be omitted, assuming we are dealing with non problematic regular exprssions.
2. (ChoiceRL) rule can be omitted, assuming we are always starting from the top level.
3. the premise length |v₁| ≥ length |v₂| in the (ChoiceLR) can be dropped, assuming we are always starting from the top level.

As a result, the remaining set of internal rules is the same set for greedy order (Frisch's) modulo the top-level inductive premises.

Hence, we can also adjust the greedy order by introducing an identity top level. 


Adjusted greedy order

```
r ⊢ v₁ >ⁱ v₂
--------------------------------(GreedyTop)
r ⊢ v₁ > v₂
```


```
r₁ ⊢ v₁ > v₁'
-------------------------------------------- (Seq₁)
r₁ ● r₂ ⊢ PairU v₁ v₂ >ⁱ PairU v₁' v₂'


v₁ ≡ v₁'  r₂ ⊢ v₂ > v₂'
-------------------------------------------- (Seq₂)
r₁ ● r₂ ⊢ PairU v₁ v₂ >ⁱ PairU v₁' v₂'


r₁ ⊢ v₁ > v₁'
----------------------------------(ChoiceLL)
r₁ + r₂ ⊢ LeftU v₁ >ⁱ LeftU v₁' 


r₂ ⊢ v₂ > v₂'
----------------------------------(ChoiceRR)
r₁ + r₂ ⊢ RightU v₂ >ⁱ RightU v₂' 


----------------------------------------------(ChoiceLR)             
r₁ + r₂ ⊢ LeftU v₁ >ⁱ RightU v₂ 


r ⊢ v₁ > v₂ 
---------------------------------(StarHd)
r* ⊢ ConsU v₁ vs₁ >ⁱ ConsU v₂ vs₂


v₁ ≡ v₂        r* ⊢ vs₁ > vs₂ 
---------------------------------(StarTl)
r* ⊢ ConsU v₁ vs₁ >ⁱ ConsU v₂ vs₂


length |v| + length |vs| > 0
------------------------------------------------(StarConsNil)
r* ⊢ ConsU v vs >ⁱ NilU

```


This adjustment is minimal, but is insightful, the top level of POSIX order tells us that it is longer the better;
The top level of Greedy tells us that it does not look for longest match, it favors left over right, cons over nil. 


Next question: Can LNE be adjusted in this kind of two level definitions? 

My conjecture: For LNE, we adjust the top level as follows, 


```
len|v₁|=len|v₂|=0
r ⊢  v₁ >ⁱ v₂
--------------------------------(BothEmpty)
r ⊢ v₁ > v₂

len|v₁|>0
len|v₂|>0 
r ⊢ v₁ >ⁱ v₂
--------------------------------(BothNonEmpty)
r ⊢ v₁ > v₂


len|v₁|>0 
len|v₂|=0 
--------------------------------(LeftNonEmpty)
r ⊢ v₁ > v₂
```

The internal rules are identical to the POSIX's and the greedy's. 


What is the advantage of this reformulation? 

1. We have a "plugin-like" matching policy template.
2. Would it make the robustness check easier? 


#### Update on Feb 27 2026


An isomorphism between the new two-level POSIX parse tree order r ⊢ v₁ > v₂ and the POSIX parse tree relation (Urban's definition  w , r ⇒ v ) is established and verified in agda. 

1) => direction:
   Let r be a non problematic regular expression, v be a parse tree of r, and { for any parse tree u of r,  |v| ≡ |u| and  r ⊢ v > u } 
	Then |v| , r ⇒ v.


2) <= direction. 
   Let r be a non problematic regular expression, v be a parse tree of r, and |v| ≡ w. 
   Let w , r ⇒ v. 
   Let u of r such that  ¬ ( v ≡ u ), and |v| ≡ |u|.
   Then  r ⊢ v > u.
    
	
#### Update on 6 March 2026 
POSIX parsing implementation using PD is still in progress. 

What we know so far.

1. we need to use ⊕ to implement  ∪ in all locations and a nil or singleton list [ ] to implement  { }.
i.e. 
pd[ ε , c ]    = []
pd[ $ c ` loc  , c' ] with c Char.≟ c'
...                      | yes refl = [ ε ] 
...                      | no  _    = [] 
pd[ l ● r ` loc , c ] with ε∈? l
...                      | yes ε∈l  = (List.map (λ p → p ● r ` loc ) pd[ l , c ]) ⊕  pd[ r , c ] ` loc
...                      | no ¬ε∈l  = List.map (λ l' → l' ● r ` loc ) pd[ l , c ]
pd[ l + r ` loc , c ]               = pd[ l , c ] ⊕  pd[ r , c ] ` loc 
pd[ r * nε ` loc , c ]              = List.map (λ r' → r' ● ( r * nε ` loc ) ` loc ) pd[ r , c ]

   1.1 kenny tried to relax it by keeping the ++ in concat  l ● r cases, the result is not posix ordered, counter examples were identified, (posix-notworking/PartialDerivative.lagda.md ExampleParseAll.ex_ps) 
	   r = (a* ● (a* ● a )) * 
	   w = aaa
   1.2 constructing the partial deriative with injection, the list of partial derivative is weak singleton,
	   i.e. all the instances share the same partial derivative, but injections are different. e.g.
	   r = (ε + ε) ● a , w = a
	   the list of partial deriative, [ε], but we need two different injection functions, 
	   (λ y → Pair (Left Empty) y ) ∘ (λ x → a) and 
	   (λ y → Pair (Right Empty) y ) ∘ (λ x → a)



### How to establish robustness between POSIX and LNE and Greedy?

We can reverse the approach from CIAA 16 Journal paper?

How did Frisch prove that their NFA construction is greedy?

### Connection to Glushkov
Is Glushkov Greedy or LNE, some paper said PD NFA is a quotient of Glushkov? what does that mean?


### Rust runtime comparison



#### Update on 20 March 2026


Here is the issue:

##### How we proved the correctness of partial derivatives parsing algorithm is greedy (or left non empty, lne)

consider the Antimirov's pd algo with injection function for parse tree , (which gives us left non empty matching)

pdU[ _ , _ ] : RE  → Char → [ (RE , RE → RE) ]
pdU[ ε , c ] = []
pdU[ l , l' ] = if l == l'
  then [ ( ε , λ x → Letter c ) ]
  else []
pdU[ r ● t , l  ] = if ε∈ r
  then [ ( p ● t , mkinjFst inj ) | ( p , inj ) ∈ pdU[ r , l ] ] ++ [ ( p, mkinjSnd e inj) | e ∈ mkEmpty r , (p , inj) ∈ pdU[ t , l ]]
  else [ ( p ● t , mkinjFst inj ) | ( p , inj ) ∈ pdU[ r , l ] ]
pdU[ r + t , l ] = [ ( p , mkinjLeft inj ) | (p , inj) ∈ pdU[ r , l ] ]
                ++ [ ( p , mkinjRight inj) | (p , inj) ∈ pdU[ t , l ] ]
pdU[ r * , l ] =
  [ ( p ● r*  , mkinjStar inj ) | (p , inj) ∈ pdU[ r , l ] ]


where

mkinjFst inj   = λ (Pair x y ) → Pair (inj x) y 
mkinjSnd e inj = λ y → Pair e ( inj y )
mkinjLeft inj  = λ x → Left (inj x)
mkinjRight inj = λ y → Right (inj y)
mkinjStar inj  = λ (Pair v (List vs)) → List ((inj v) ∷ vs)


we omitted mkEmpty : RE → [ U ] for breivity



Using Agda, we have verified the above algorithm is giving us LNE order, which is proven using two sub lemmas.


Defn: (Strict increment)
Let r and p be non problematic regular expressions.  p is a partial derivative of r w.r.t c.
Let inj be an injection function from parse trees of p to ( parse trees of) r.
We say inj is strict incremeantal, written as ">-inc r p inj"
 iff
  ∀ u, v  parse trees of p.  p ⊢ u > v ==> r ⊢ inj u > inj v


Lemma: (All injection functions from pdU are strict incremental)
Let r be a non problematic regular expression. Let c be a character.
Let ( p , inj ) ∈ pdU [ r , c ].
Then >-inc r p inj.

Proven in lne/Order.lagda.md (similarly greedy/Order.lagda.md)


Defn: (Extended order among injection)
Let r , p₁ , p₂  be non problematic regular expression. such that p₁ and p₂ partial derivatives of r w.r.t to character c. 
Let inj₁ and inj₂ be injection functions from p₁ to r and p₂ to r respectively.
We say (p₁, inj₁) >ᵣᶜ (p₂ , inj₂ )
  iff ∀ u₁ and u₂ as parse tree of r. 
      ∃ v₁ a parse tree of p₁, v₂ a parse tree of p₂
        such that inj₁ v₁ = u₁ and inj₂ v₂ = u₂
      Then r ⊢ inj₁ v₁ > inj₂ v₂
	       (in other words, ) r ⊢ u1 > u2
		   
How Frisch proved it?

Lemma: (All partial dervative and injection functions are ordered according to the extended order)

Let pds = pdU[ r , c ]
Then pds is sorted according to the extended order.

Proven in lne/ExtendedOrder.lagda.md  (similarly greedy/ExtendedOrder.lagda.md)


Ultimately, these lemmas (plus the extended results to partial derivative descendants) give us the result that the parse trees produced by the parseAll functions are sorted according to >.



##### Now we consider the Posix order.


Main idea we use ⊕ operator to combine partial derivatives into derivative.


pd[ ε , l ] = []
pd[ l , l' ] = if l == l'
  then [ ( ε , λ e → Letter l )]
  else []
pd[ r + t , l ] = [ ( p , mkinjLeft inj ) | ( p , inj ) ∈ pd[ r , l ] ] ⊕ [ ( p , mkinjRight inj ) | ( p , inj ) ∈ pd[ t , l ] ]
pd[ r ● t , l ] = if ε∈ r
  then [ ( p , mkinjFst inj) | (p , inj ) ∈ pdU[ r , l ] ] ⊕ [ ( p , mkinjSnd e inj) | e ∈ mkEmpty r ,   ( p , inj ) ∈ pdU[ t , l ] ]
  else [ ( p , mkinjFst inj) | (p , inj ) ∈ pdU[ r , l ] ]
pd[ r * , l ] =
  [ ( p ● r * , mkinjStar inj ) | (p , inj) ∈ pdU[ r , l ] ]

where

[] ⊕ ys = ys
xs ⊕ [] = xs
xs ⊕ ys =
  [ ((p + p') , λ { Left x → inj x ; Right y → inj' y } ) | (p , inj ) ∈ xs , (p' , inj' ) ∈ ys ]



Lemma:
We find that the posix adaptation of pdU[ r , l ] is still strict incremental.


Lemma:
In addition, we also verified that all the pds from posix pdU[ r , l ] is homogenous, i.e. all the p are identical.



The extended ordering among injection needs to be altered.
Defn: (Extended ordering among injection)
Let r , p be non problematic regular expressions, such that p is a derivative of r w.r.t character c. 
Let inj₁ and inj₂ be injection functions from p to r.
We say (p, inj₁) >ᵣᶜ (p , inj₂ )
  iff
    ∀ v₁ v₂ parse trees of p, such that p ⊢ v₁ > v₂
    Then r ⊢ inj₁ v₁ > inj₂ v₂


Conjecture
We want to show that pds = pdU[ r , c ] are ordered according to >ᵣᶜ.

However this conjecture is not valid. >ᵣᶜ is a partial order, not a total order.

Counter example below.

Let r = ( (ε + ε ) ● a) +  ( (ε + ε) ● a ) 

pdU[ r , a ] = ps ⊕ qs
  where
    ps = [ ( p, mkinjLeft inj) | ( p , inj) ∈ pdU[ ( ε + ε ) ● r , a ] ] -- (1)
    qs = [ ( q, mkinjRight inj) | ( q , inj) ∈ pdU[ ( ε + ε ) ● r , a ] ] -- (2)


then the sub call (1)

pdU [ ( ε + ε ) ● a , a ] =
  [ ( ε , λ x → (Left Empty , Letter a) )      -- inj₁₁
  , ( ε , λ y → (Right Empty , Letter a) ) ]   -- inj₁₂


and the sub call (2)

pdU [ ( ε + ε ) ● a , a ] =
  [ ( ε , λ x → (Left Empty , Letter a) )      -- inj₂₁
  , ( ε , λ y → (Right Empty , Letter a) ) ]   -- inj₂₂


Substituting the above into ps and qs

ps = [ ( ε, λ x → Left (Left Empty , Letter a))
     , ( ε, λ y → Left (Right Empty , Letter a ))
     ]


qs = [ ( ε, λ x → Right (Left Empty , Letter a))
     , ( ε, λ y → Right (Right Empty , Letter a ))
     ]


Finally

ps ⊕ qs = [ ( ε + ε , λ { Left e → Left (Left Empty , Letter a )
                         ; Right e → Right (Left Empty , Letter a ) } )  -- inj₁
           , ( ε + ε , λ { Left e → Left (Left Empty, Letter a )
                         ; Right e → Right (Right Empty, Letter a ) } )  -- inj₂
           , ( ε + ε , λ { Left e → Left (Right Empty, Letter a )
                         ; Right e → Right (Left Empty, Letter a ) } )   -- inj₃
           , ( ε + ε , λ { Left e → Left (Right Empty, Letter a )
                         ; Right e → Right (Right Empty, Letter a ) } )  -- inj₄ 
           ]

based on our definition of >ᵣᶜ

inj₁ >ᵣᶜ inj₂
inj₁ >ᵣᶜ inj₃
inj₃ >ᵣᶜ inj₄

but we have neither inj₂ >ᵣᶜ  inj₃ nor inj₃ >ᵣᶜ inj₂ 

Proposition
We want to show that pds = pdU[ r , c ] forms a complete lattice with the left most injection function is the meet, the right most is the join. 


buildU ( p , inj ) = if ε∈p then map inj (mkAllEmptyU ε∈p) 
                     else [] 


parseAllU r [a] = concatMap buildU pdU[ r . a ] 
                = concatMap buildU [ ( ε + ε ,  inj₁ )  , ( ε + ε,  inj₂ ) , ( ε + ε , inj₃ ) , ( ε + ε.  inj₄)  ]  -- (1) 

  since mkAllEmptyU (ε + ε) = [ Left Empty , Right Empty ] 

            (1) = (map inj₁ [ Left Empty , Right Empty ] ) ++ 
			      (map inj₂ [ Left Empty , Right Empty ] ) ++ 
			      (map inj₃ [ Left Empty , Right Empty ] ) ++ 
			      (map  inj₄ [ Left Empty , Right Empty ] ) 
	            = [ Left (Left Empty , Letter a )  -- (same; top)
				  , Right (Left Empty , Letter a ) 
				  , Left (Left Empty, Letter a )   -- (same; top)
				  , Right (Right Empty, Letter a ) 
				  , Left (Right Empty, Letter a ) 
				  , Right (Left Empty, Letter a )
				  , Left (Right Empty, Letter a )
				  , Right (Right Empty, Letter a ) ]

what about ?
parseAllU r [a] = app buildU pdU[ r . a ] 
                = concatMap ( \e -> map (\f -> f e ) [  inj₁ , inj₂ , inj₃ , inj₄ ]  ) ( mkAllEmpty ε + ε ) 
				= [ inj1 (Left Empty) , inj2 (Left Empty) , inj3 (Left Empty), inj4 (Left Empty)
				  , inj1 (Right Empty) , inj2 (Right Empty) , inj3 (Right Empty), inj4 (Right Empty) ]

                = [ Left (Left Empty , Letter a )  -- (same; top)
				  , Left (Left Empty, Letter a )   -- (same; top)
				  , Left (Right Empty, Letter a ) 
				  , Left (Right Empty, Letter a )
				  , Right (Left Empty , Letter a ) 
				  , Right (Right Empty, Letter a )  -- not sorted
				  , Right (Left Empty, Letter a )   -- not sorted
				  , Right (Right Empty, Letter a ) ]
				 
