```
MODULE CigaretteSmokers
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers
VARIABLES smokers, dealer

Init ==
  /\ smokers \in [Ingredients -> [{smoking : BOOLEAN, done : BOOLEAN}]]
  /\ dealer \in Offers \cup {{}}
  /\ ∀ i ∈ Ingredients : smokers[i] = [smoking |-> FALSE, done |-> FALSE]
  /\ dealer ≠ {}

Next ==
  \/ ∃ i ∈ Ingredients :
      /\ dealer ∈ Offers
      /\ ∀ j ∈ Ingredients : j ≠ i ⇒ i ∉ dealer
      /\ smokers' = [smokers EXCEPT ![i].smoking = TRUE]
      /\ dealer' = {}
  \/ ∃ i ∈ Ingredients :
      /\ dealer = {}
      /\ smokers[i].smoking
      /\ smokers' = [smokers EXCEPT ![i].smoking = FALSE, ![i].done = TRUE]
      /\ dealer' ∈ Offers

Spec == Init ∧ [][Next]_<<smokers, dealer>>
FairSpec == Spec ∧ WF_<<smokers, dealer>>(Next)

TypeOK ==
  /\ smokers \in [Ingredients -> [{smoking : BOOLEAN, done : BOOLEAN}]]
  /\ dealer \in Offers \cup {{}}

AtMostOne ==
  ∀ s1, s2 ∈ Ingredients :
    ¬(s1 ≠ s2 ∧ smokers[s1].smoking ∧ smokers[s2].smoking)

THEOREM Spec => []TypeOK
THEOREM Spec => []AtMostOne

```
Note: The `WF_` operator is used to specify weak fairness. It ensures that if the `Next` action is continuously enabled, it will eventually occur.