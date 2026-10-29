---- MODULE SemaphoreMutex ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

Procs == 0..(N-1)

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

p(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exit(self)

Next == \E self \in Procs : p(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs :
           /\ WF_vars((pc[self] # "ncs") /\ p(self))
           /\ SF_vars(enter(self))

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

StarvationFreedom ==
    \A self \in Procs : (pc[self] = "enter") ~> (pc[self] = "cs")

====