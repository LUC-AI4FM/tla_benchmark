```
MODULE SmokersProblem
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Smokers
VARIABLES smoking, offer

Init ==
  /\ smoking = [s \in Smokers |-> FALSE]
  /\ offer = {}

Next ==
  \/ \E s \in Smokers :
      /\ offer = (Ingredients \ {s})
      /\ smoking' = [smoking EXCEPT ![s] = TRUE]
      /\ offer' = {}
  \/ \E S \subseteq Ingredients :
      /\ offer = S
      /\ ~(\E s \in Smokers : S = (Ingredients \ {s}))
      /\ smoking' = smoking
      /\ offer' = (Ingredients \ {CHOOSE x \in Ingredients : x \notin S})

Spec == Init /\ [][Next]_vars

AtMostOne ==
  \A t \in Nat :
    Spec(t) => Cardinality({s \in Smokers : smoking[s]}) <= 1

FairSpec == Spec /\ WF_vars(Next)

THEOREM Spec => []AtMostOne
THEOREM FairSpec => <>[]~(\E s \in Smokers : smoking[s])
```
Note: The `CHOOSE` operator is used to select an arbitrary element from a non-empty set. This specification assumes that the sets of smokers and ingredients are finite and non-empty, which is in line with the standard formulation of the cigarette smokers problem.