---------------------------- MODULE SemaphoreMutex ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES sem, pc

vars == << sem, pc >>

TypeOK ==
    /\ sem \in {0, 1}
    /\ pc \in [Procs -> {"ncs", "enter", "cs", "exit"}]

Init ==
    /\ sem = 1
    /\ pc = [self \in Procs |-> "ncs"]

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

exitCS(self) ==
    /\ pc[self] = "exit"
    /\ sem' = 1
    /\ pc' = [pc EXCEPT ![self] = "ncs"]

P(self) == ncs(self) \/ enter(self) \/ cs(self) \/ exitCS(self)

Next == \E self \in Procs : P(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs :
          /\ WF_vars((pc[self] # "ncs") /\ P(self))
          /\ SF_vars(enter(self))

MutualExclusion ==
    \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

StarvationFree ==
    \A i \in Procs : (pc[i] = "enter") ~> (pc[i] = "cs")

=============================================================================