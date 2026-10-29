---- MODULE ConcurrentIncrement ----
EXTENDS Naturals, TLC

VARIABLES x, pc

vars == << x, pc >>

ProcSet == {1, 2}

Init == /\ x = 0
        /\ pc = [self \in ProcSet |-> "Inc"]

Inc(self) == /\ pc[self] = "Inc"
             /\ x' = x + 1
             /\ pc' = [pc EXCEPT ![self] = "Done"]

proc(self) == Inc(self)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet : proc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ProcSet : WF_vars(proc(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

TypeOK == /\ x \in 0..2
          /\ pc \in [ProcSet -> {"Inc", "Done"}]

====