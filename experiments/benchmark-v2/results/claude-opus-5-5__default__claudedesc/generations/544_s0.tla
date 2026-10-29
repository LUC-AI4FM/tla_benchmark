---- MODULE ConcurrentIncrementSemaphore ----
EXTENDS Naturals, Integers, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs == 1..N

VARIABLES x, sem, t, pc

vars == << x, sem, t, pc >>

Init ==
    /\ x = 0
    /\ sem = 1
    /\ t = [p \in Procs |-> 0]
    /\ pc = [p \in Procs |-> "acquire"]

Acquire(p) ==
    /\ pc[p] = "acquire"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![p] = "read"]
    /\ UNCHANGED << x, t >>

Read(p) ==
    /\ pc[p] = "read"
    /\ t' = [t EXCEPT ![p] = x]
    /\ pc' = [pc EXCEPT ![p] = "write"]
    /\ UNCHANGED << x, sem >>

Write(p) ==
    /\ pc[p] = "write"
    /\ x' = t[p] + 1
    /\ pc' = [pc EXCEPT ![p] = "release"]
    /\ UNCHANGED << sem, t >>

Release(p) ==
    /\ pc[p] = "release"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED << x, t >>

proc(p) == Acquire(p) \/ Read(p) \/ Write(p) \/ Release(p)

Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : proc(p)
    \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A p \in Procs : pc[p] = "Done")

TypeOK ==
    /\ x \in Nat
    /\ sem \in {0, 1}
    /\ t \in [Procs -> Nat]
    /\ pc \in [Procs -> {"acquire", "read", "write", "release", "Done"}]

InCS(p) == pc[p] \in {"read", "write", "release"}

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(InCS(p) /\ InCS(q))

SemaphoreConsistent ==
    (sem = 0) <=> (\E p \in Procs : InCS(p))

Correctness ==
    (\A p \in Procs : pc[p] = "Done") => x = N

====