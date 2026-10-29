---- MODULE ProcAB ----
EXTENDS Naturals, TLC

VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"A", "B"}

Init == /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "a1"
                                        [] self = "B" -> "b1"]

a1 == /\ pc["A"] = "a1"
      /\ x' = x + 1
      /\ pc' = [pc EXCEPT !["A"] = "Done"]

ProcA == a1

b1 == /\ pc["B"] = "b1"
      /\ x' = x + 1
      /\ pc' = [pc EXCEPT !["B"] = "Done"]

ProcB == b1

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == ProcA \/ ProcB \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

====