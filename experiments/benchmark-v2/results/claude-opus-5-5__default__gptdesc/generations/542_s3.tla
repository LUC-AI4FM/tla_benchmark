---- MODULE TwoProcIncrement ----
EXTENDS Integers, TLC

VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"ProcA", "ProcB"}

Init == /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = "ProcA" -> "IncA"
                                        [] self = "ProcB" -> "IncB"]

IncA == /\ pc["ProcA"] = "IncA"
        /\ x' = x + 1
        /\ pc' = [pc EXCEPT !["ProcA"] = "Done"]

ProcA == IncA

IncB == /\ pc["ProcB"] = "IncB"
        /\ x' = x + 1
        /\ pc' = [pc EXCEPT !["ProcB"] = "Done"]

ProcB == IncB

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == ProcA \/ ProcB \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ProcA)
        /\ WF_vars(ProcB)

TypeOK == /\ x \in 0..2
          /\ pc \in [ProcSet -> {"IncA", "IncB", "Done"}]

FinalValue == (\A self \in ProcSet : pc[self] = "Done") => x = 2

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

====