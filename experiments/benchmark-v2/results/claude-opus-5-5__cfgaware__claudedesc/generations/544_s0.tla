---------------------------- MODULE Increment ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLES x, sem, pc, t

vars == << x, sem, pc, t >>

ProcSet == 1..N

Init ==
    /\ x = 0
    /\ sem = 1
    /\ t = [self \in ProcSet |-> 0]
    /\ pc = [self \in ProcSet |-> "p1"]

\* Acquire the lock: wait until sem = 1, then atomically set it to 0
p1(self) ==
    /\ pc[self] = "p1"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![self] = "p2"]
    /\ UNCHANGED << x, t >>

\* Read x into local t
p2(self) ==
    /\ pc[self] = "p2"
    /\ t' = [t EXCEPT ![self] = x]
    /\ pc' = [pc EXCEPT ![self] = "p3"]
    /\ UNCHANGED << x, sem >>

\* Write t + 1 back to x
p3(self) ==
    /\ pc[self] = "p3"
    /\ x' = t[self] + 1
    /\ pc' = [pc EXCEPT ![self] = "p4"]
    /\ UNCHANGED << sem, t >>

\* Release the lock
p4(self) ==
    /\ pc[self] = "p4"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << x, t >>

proc(self) == p1(self) \/ p2(self) \/ p3(self) \/ p4(self)

\* Allow infinite stuttering to prevent deadlock on termination
Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E self \in ProcSet : proc(self)
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

\* Useful properties
MutualExclusion ==
    \A i, j \in ProcSet :
        (i # j) => ~(pc[i] \in {"p2", "p3", "p4"} /\ pc[j] \in {"p2", "p3", "p4"})

TypeOK ==
    /\ x \in Nat
    /\ sem \in {0, 1}
    /\ pc \in [ProcSet -> {"p1", "p2", "p3", "p4", "Done"}]
    /\ t \in [ProcSet -> Nat]

Correctness ==
    (\A self \in ProcSet : pc[self] = "Done") => x = N

=============================================================================