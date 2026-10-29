----------------------------- MODULE Session7fg -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs == 1..N

VARIABLES x, lock, t, pc

vars == << x, lock, t, pc >>

Init ==
    /\ x = 0
    /\ lock = FALSE
    /\ t = [p \in Procs |-> -1]
    /\ pc = [p \in Procs |-> "p0"]

\* Acquire the lock (entry into the critical section)
p0(self) ==
    /\ pc[self] = "p0"
    /\ lock = FALSE
    /\ lock' = TRUE
    /\ pc' = [pc EXCEPT ![self] = "p1"]
    /\ UNCHANGED << x, t >>

\* Read the shared variable into the local variable
p1(self) ==
    /\ pc[self] = "p1"
    /\ t' = [t EXCEPT ![self] = x]
    /\ pc' = [pc EXCEPT ![self] = "p2"]
    /\ UNCHANGED << x, lock >>

\* Write back the incremented value and release the lock
p2(self) ==
    /\ pc[self] = "p2"
    /\ x' = t[self] + 1
    /\ lock' = FALSE
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED << t >>

proc(self) == p0(self) \/ p1(self) \/ p2(self)

\* Allow infinite stuttering once all processes have terminated
Terminating ==
    /\ \A self \in Procs : pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Procs : proc(self)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))

-----------------------------------------------------------------------------
\* Invariants

TypeOK ==
    /\ x \in 0..N
    /\ t \in [Procs -> {-1} \cup (0..(N-1))]

AddCorrect ==
    (\A p \in Procs : pc[p] = "Done") => (x = N)

InCS(p) == pc[p] \in {"p1", "p2"}

CriticalSecInv ==
    \A p, q \in Procs : (p # q) => ~(InCS(p) /\ InCS(q))

-----------------------------------------------------------------------------
\* Liveness

Termination == <>(\A p \in Procs : pc[p] = "Done")

=============================================================================