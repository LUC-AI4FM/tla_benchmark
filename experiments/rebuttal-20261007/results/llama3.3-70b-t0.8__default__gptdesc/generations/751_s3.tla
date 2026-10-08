```
MODULE Smokers
EXTENDS Integers, FiniteSets

CONSTANTS SmokerSet, IngredientSet
ASSUME /\
  SmokerSet \subseteq IngredientSet /\ 
  Cardinality(SmokerSet) = 3 /\ 
  Cardinality(IngredientSet) = 3

VARIABLES smoking, offer

Init == /\ 
  smoking = [s \in SmokerSet |-> FALSE] /\ 
  offer \in {<<i1, i2>> : i1 \in IngredientSet, i2 \in IngredientSet | i1 # i2}

Next == 
  (\E s \in SmokerSet : 
    /\ offer = <<t1, t2>> 
    /\ (s = i1 /\ t1 = i2) \/ (s = i2 /\ t1 = i3) \/ (s = i3 /\ t1 = i1)
    /\ smoking' = [smoking EXCEPT ![s] = TRUE]
    /\ offer' \in {<<i1, i2>> : i1 \in IngredientSet, i2 \in IngredientSet | i1 # i2}
  ) \/ 
  (\E s \in SmokerSet :
    /\ smoking[s] 
    /\ smoking' = [smoking EXCEPT ![s] = FALSE]
    /\ offer' = offer
  )

AtMostOne == \A s, t \in SmokerSet : 
  ~/ (smoking[s] /\ smoking[t])

Spec == Init /\ [][Next]_<<smoking, offer>>
FairSpec == Spec /\ WF_vars(Next)

THEOREM Spec => []AtMostOne
```