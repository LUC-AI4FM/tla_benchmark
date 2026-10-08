```
MODULE Smokers
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Smokers
VARIABLES smoking, offer

Init == (
  /\ smoking = [s \in Smokers |-> FALSE]
  /\ offer = {}
)

Next == 
  /\ (EIF s \in Smokers :
      /\ ~smoking[s]
      /\ offer = Ingredients \ {i \in Ingredients : i = s}
      /\ smoking' = [smoking EXCEPT ![s] = TRUE]
      /\ offer' = {}
    ELSE
      /\ smoking' = smoking
      /\ offer' = {i \in Ingredients : i /= s}
  )

AtMostOne == 
  /\ \A s1, s2 \in Smokers : 
      ~(smoking[s1] /\ smoking[s2])

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

THEOREM Spec => []AtMostOne
THEOREM FairSpec => <><smoking[s]>(~smoking[s]) /\ AtMostOne
```
Note: `EIF` is used to represent "if there exists", and `[s \in Smokers |-> FALSE]` represents a function that maps each smoker to `FALSE`. The `AtMostOne` invariant asserts that no more than one smoker can be smoking at any time. The `FairSpec` includes weak fairness for the `Next` action, ensuring that if the system is in a state where a smoker can smoke, it will eventually do so.