```
---------------------------- MODULE Consensus ----------------------------
EXTENDS Integers

CONSTANT Values
VARIABLE chosen

Init == (chosen = << >>)

Propose(v) == (chosen = << >>) /\ (v \in Values)
                  /\ (chosen' = IF << >> \in chosen THEN chosen ELSE {v})

Learn(v) == (v \in chosen)
             /\ (chosen' = chosen)

Next == (\E v \in Values : Propose(v)) \/ Learn(chosen)

Spec == Init /\ [][Next]_chosen

Validity == []((chosen \subseteq Values) /\ (Cardinality(chosen) <= 1))
Agreement == [](Cardinality(chosen) <= 1)
Integrity == [](~(chosen \subset chosen'))

EventualChoice == <>(<>(\E v \in Values : Propose(v)))
NonTriviality == []((chosen = << >>) => (<>(~(\E v \in Values : Propose(v)))))

LiveSpec == Spec /\ WF_var(Next)
---------------------------- END MODULE ----------------------------
```