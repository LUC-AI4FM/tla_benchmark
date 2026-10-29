---------------------------- MODULE Simple ----------------------------
EXTENDS Integers, TLC

CONSTANT N

ASSUME NAssump == (N \in Nat) /\ (N > 0)

VARIABLES x, y, pc

vars == << x, y, pc >>

ProcSet == 0..(N-1)

Init == /\ x = [i \in ProcSet |-> 0]
        /\ y = [i \in ProcSet |-> 0]
        /\ pc = [self \in ProcSet |-> "a"]

a(self) == /\ pc[self] = "a"
           /\ x' = [x EXCEPT ![self] = 1]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ y' = y

b(self) == /\ pc[self] = "b"
           /\ y' = [y EXCEPT ![self] = x[(self - 1) % N]]
           /\ pc' = [pc EXCEPT ![self] = "Done"]
           /\ x' = x

proc(self) == a(self) \/ b(self)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet : proc(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ProcSet : WF_vars(proc(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

-----------------------------------------------------------------------------

PCorrect == (\A i \in ProcSet : pc[i] = "Done") =>
                (\E i \in ProcSet : y[i] = 1)

TypeOK == /\ x \in [ProcSet -> {0, 1}]
          /\ y \in [ProcSet -> {0, 1}]
          /\ pc \in [ProcSet -> {"a", "b", "Done"}]

Inv == /\ TypeOK
       /\ \A i \in ProcSet : (pc[i] \in {"b", "Done"}) => (x[i] = 1)
       /\ \/ \E i \in ProcSet : pc[i] /= "Done"
          \/ \E i \in ProcSet : y[i] = 1

=============================================================================