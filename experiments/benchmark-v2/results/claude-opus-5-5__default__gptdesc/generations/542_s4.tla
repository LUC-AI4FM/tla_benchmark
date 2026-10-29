---- MODULE TwoProcIncrement ----
EXTENDS Naturals, TLC

VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"ProcA", "ProcB"}

Init == /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = "ProcA" -> "a"
                                        [] self = "ProcB" -> "b"]

a == /\ pc["ProcA"] = "a"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

ProcA == a

b == /\ pc["ProcB"] = "b"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

ProcB == b

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == ProcA \/ ProcB \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ProcA)
        /\ WF_vars(ProcB)

TypeOK == /\ x \in 0..2
          /\ pc \in [ProcSet -> {"a", "b", "Done"}]

FinalValue == (\A self \in ProcSet : pc[self] = "Done") => x = 2

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

====