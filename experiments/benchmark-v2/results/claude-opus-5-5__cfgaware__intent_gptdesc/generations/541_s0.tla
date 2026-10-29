---------------------------- MODULE ConcurrentAdd ----------------------------
EXTENDS Naturals

VARIABLES x, pc

vars == << x, pc >>

ProcSet == {1, 2}

Init == /\ x = 0
        /\ pc = [p \in ProcSet |-> "Add"]

\* Each process atomically increments the shared variable, then terminates.
Add(self) == /\ pc[self] = "Add"
             /\ x' = x + 1
             /\ pc' = [pc EXCEPT ![self] = "Done"]

proc(self) == Add(self)

\* Allows infinite stuttering once both processes have terminated.
Terminating == /\ \A p \in ProcSet : pc[p] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet : proc(self))
        \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in ProcSet : WF_vars(proc(self))

TypeOK == /\ x \in Nat
          /\ pc \in [ProcSet -> {"Add", "Done"}]

\* Safety: when both processes have terminated, x must equal 2.
AddCorrect == (\A p \in ProcSet : pc[p] = "Done") => (x = 2)

\* Liveness: every fair execution eventually terminates.
Termination == <>(\A p \in ProcSet : pc[p] = "Done")

=============================================================================