---- MODULE TwoProcIncrement ----
EXTENDS Integers, TLC

VARIABLES x, pc

vars == << x, pc >>

ProcSet == {"A", "B"}

Init == /\ x = 0
        /\ pc = [self \in ProcSet |-> CASE self = "A" -> "a"
                                       [] self = "B" -> "b"]

a == /\ pc["A"] = "a"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT !["A"] = "Done"]

ProcA == a

b == /\ pc["B"] = "b"
     /\ x' = x + 1
     /\ pc' = [pc EXCEPT !["B"] = "Done"]

ProcB == b

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == ProcA \/ ProcB \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(ProcA)
        /\ WF_vars(ProcB)

TypeOK == /\ x \in 0..2
          /\ pc \in [ProcSet -> {"a", "b", "Done"}]

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

FinalValue == (\A self \in ProcSet : pc[self] = "Done") => x = 2

====