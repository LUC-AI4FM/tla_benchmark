---------------------------- MODULE SemaphoreCounter ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES x, sem, pc, t

vars == << x, sem, pc, t >>

ProcSet == 1..N

Init == /\ x = 0
        /\ sem = 1
        /\ t = [self \in ProcSet |-> 0]
        /\ pc = [self \in ProcSet |-> "p1"]

\* Acquire the binary semaphore (blocking) and read the shared counter
p1(self) == /\ pc[self] = "p1"
            /\ sem = 1
            /\ sem' = 0
            /\ t' = [t EXCEPT ![self] = x]
            /\ pc' = [pc EXCEPT ![self] = "p2"]
            /\ x' = x

\* Write back the incremented value and release the semaphore
p2(self) == /\ pc[self] = "p2"
            /\ x' = t[self] + 1
            /\ sem' = 1
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ t' = t

Proc(self) == p1(self) \/ p2(self)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet : Proc(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ProcSet : WF_vars(Proc(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

TypeOK == /\ x \in Nat
          /\ sem \in {0, 1}
          /\ t \in [ProcSet -> Nat]
          /\ pc \in [ProcSet -> {"p1", "p2", "Done"}]

MutualExclusion == \A i, j \in ProcSet :
                      (i # j) => ~(pc[i] = "p2" /\ pc[j] = "p2")

SemaphoreConsistent == (sem = 0) <=> (\E self \in ProcSet : pc[self] = "p2")

Correctness == (\A self \in ProcSet : pc[self] = "Done") => (x = N)

=============================================================================