---------------------------- MODULE Session7fg ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ConstN == 5

ASSUME N \in Nat \ {0}

Procs == 1..N

VARIABLES x, t, pc, lock

vars == << x, t, pc, lock >>

Init ==
    /\ x = 0
    /\ t = [p \in Procs |-> -1]
    /\ pc = [p \in Procs |-> "p0"]
    /\ lock = 0

\* Acquire the lock (await lock = 0)
p0(self) ==
    /\ pc[self] = "p0"
    /\ lock = 0
    /\ lock' = self
    /\ pc' = [pc EXCEPT ![self] = "p1"]
    /\ UNCHANGED << x, t >>

\* Read the shared variable
p1(self) ==
    /\ pc[self] = "p1"
    /\ t' = [t EXCEPT ![self] = x]
    /\ pc' = [pc EXCEPT ![self] = "p2"]
    /\ UNCHANGED << x, lock >>

\* Write back the incremented value
p2(self) ==
    /\ pc[self] = "p2"
    /\ x' = t[self] + 1
    /\ pc' = [pc EXCEPT ![self] = "p3"]
    /\ UNCHANGED << t, lock >>

\* Release the lock
p3(self) ==
    /\ pc[self] = "p3"
    /\ lock' = 0
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << x, t >>

proc(self) == p0(self) \/ p1(self) \/ p2(self) \/ p3(self)

Terminating ==
    /\ \A self \in Procs : pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Procs : proc(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

Termination == <>(\A self \in Procs : pc[self] = "Done")

-----------------------------------------------------------------------------

TypeOK ==
    /\ x \in 0..N
    /\ t \in [Procs -> {-1} \cup (0..(N-1))]

AddCorrect ==
    (\A p \in Procs : pc[p] = "Done") => x = N

CriticalSecInv ==
    \A p, q \in Procs :
        (p # q) => ~(pc[p] \in {"p1", "p2"} /\ pc[q] \in {"p1", "p2"})

=============================================================================