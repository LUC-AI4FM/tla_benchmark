------------------------------- MODULE Increment -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES x, sem, pc, t

vars == << x, sem, pc, t >>

ProcSet == 1..N

Init ==
    /\ x = 0
    /\ sem = 1
    /\ t = [self \in ProcSet |-> 0]
    /\ pc = [self \in ProcSet |-> "p1"]

\* p1: acquire the semaphore (only when free) and read the counter into t
p1(self) ==
    /\ pc[self] = "p1"
    /\ sem = 1
    /\ sem' = 0
    /\ t' = [t EXCEPT ![self] = x]
    /\ pc' = [pc EXCEPT ![self] = "p2"]
    /\ x' = x

\* p2: write t + 1 back to the counter and release the semaphore
p2(self) ==
    /\ pc[self] = "p2"
    /\ x' = t[self] + 1
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ t' = t

Proc(self) == p1(self) \/ p2(self)

Terminating ==
    /\ \A self \in ProcSet : pc[self] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E self \in ProcSet : Proc(self)
    \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in ProcSet : SF_vars(Proc(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

-----------------------------------------------------------------------------
\* Correctness properties

TypeOK ==
    /\ x \in Nat
    /\ sem \in {0, 1}
    /\ t \in [ProcSet -> Nat]
    /\ pc \in [ProcSet -> {"p1", "p2", "Done"}]

InCS == {self \in ProcSet : pc[self] = "p2"}

MutualExclusion ==
    /\ Cardinality(InCS) <= 1
    /\ (sem = 0) <=> (Cardinality(InCS) = 1)

Completed == {self \in ProcSet : pc[self] = "Done"}

CounterCorrect == x = Cardinality(Completed)

Correctness == (\A self \in ProcSet : pc[self] = "Done") => x = N

Inv == TypeOK /\ MutualExclusion /\ CounterCorrect /\ Correctness

NoStarvation ==
    \A self \in ProcSet : (pc[self] = "p1") ~> (pc[self] = "Done")

AllTerminate == <>[](\A self \in ProcSet : pc[self] = "Done")

=============================================================================