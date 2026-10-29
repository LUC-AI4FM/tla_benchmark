---------------------------- MODULE BinarySemaphore ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES sem, pc

vars == <<sem, pc>>

TypeOK ==
    /\ sem \in {0, 1}
    /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

Init ==
    /\ sem = 1
    /\ pc = [p \in Procs |-> "ncs"]

ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED sem

enter(self) ==
    /\ pc[self] = "enter"
    /\ sem = 1
    /\ sem' = 0
    /\ pc' = [pc EXCEPT ![self] = "cs"]

cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED sem

exit(self) ==
    /\ pc[self] = "exit"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![self] = "ncs"]

proc(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : proc(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs : WF_vars(proc(self))
    /\ \A self \in Procs : SF_vars(enter(self))

-----------------------------------------------------------------------------

InCS(p) == pc[p] \in {"cs", "exit"}

MutualExclusion ==
    \A p, q \in Procs : (pc[p] = "cs" /\ pc[q] = "cs") => p = q

AtMostOneHolder ==
    Cardinality({p \in Procs : InCS(p)}) <= 1

SemaphoreAccurate ==
    (sem = 0) <=> (\E p \in Procs : InCS(p))

Invariant ==
    /\ TypeOK
    /\ MutualExclusion
    /\ AtMostOneHolder
    /\ SemaphoreAccurate

StarvationFreedom ==
    \A p \in Procs : (pc[p] = "enter") ~> (pc[p] = "cs")

NoPermanentLock ==
    []<>(sem = 1)

Repetition ==
    \A p \in Procs : []<>(pc[p] = "ncs")

Liveness == StarvationFreedom /\ NoPermanentLock /\ Repetition

=============================================================================