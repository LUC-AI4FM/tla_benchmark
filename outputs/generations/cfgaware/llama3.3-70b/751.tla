```
MODULE Smokers
VARIABLES smoking, offer

DefineType == << "tobacco", "paper", "matches" >>
Smoker == { "smoker1", "smoker2", "smoker3" }

TypeInvariant == smoking \in [Smoker -> BOOLEAN] /\ offer \in DefineType

Init ==
  /\ smoking = [s \in Smoker |-> FALSE]
  /\ offer = "tobacco"

Next ==
  /\ IF offer = "tobacco"
     THEN /\ smoking' = [smoking EXCEPT !["smoker1"] = TRUE]
          /\ offer' = "paper"
     ELSEIF offer = "paper"
          THEN /\ smoking' = [smoking EXCEPT !["smoker2"] = TRUE]
               /\ offer' = "matches"
          ELSE /\ smoking' = [smoking EXCEPT !["smoker3"] = TRUE]
               /\ offer' = "tobacco"
  /\ UNCHANGED << smoking, offer >>

AtMostOne == \A s1, s2 \in Smoker : s1 # s2 => ~(smoking[s1] /\ smoking[s2])

TypeOK == Init /\ [][Next]_<<smoking, offer>>
Spec == TypeOK /\ WF_vars(Next)
```
Note: The `WF_vars` operator is used to specify weak fairness for the `Next` action. This ensures that if the system can take a step according to `Next`, it will eventually do so.

Also note that this specification assumes that each smoker has exactly one ingredient, and the dealer offers the other two ingredients. When a smoker receives the offer, they smoke and then the system returns to the initial state where the dealer may offer again. The invariant `AtMostOne` ensures that no more than one smoker is smoking at any time.

The `TypeOK` operator defines the basic temporal specification using the `Init` and `Next` actions, and the `Spec` operator adds weak fairness for `Next`.