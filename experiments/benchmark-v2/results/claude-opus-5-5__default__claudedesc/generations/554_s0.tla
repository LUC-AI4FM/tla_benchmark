---------------------------- MODULE PetersonN ----------------------------
EXTENDS Integers

CONSTANT N

ASSUME NAssump == N \in Nat \ {0}

Procs  == 0 .. (N - 1)
Levels == 0 .. (N - 2)

VARIABLES level, last_to_enter, pc, i

vars == << level, last_to_enter, pc, i >>

TypeOK ==
    /\ level \in [Procs -> -1 .. (N - 2)]
    /\ last_to_enter \in [Levels -> Procs]
    /\ pc \in [Procs -> {"ncs", "enter", "setlevel", "setlast", "wait", "cs", "exit"}]
    /\ i \in [Procs -> 0 .. (N - 1)]

Init ==
    /\ level = [p \in Procs |-> -1]
    /\ last_to_enter = [l \in Levels |-> 0]
    /\ pc = [p \in Procs |-> "ncs"]
    /\ i = [p \in Procs |-> 0]

\* Non-critical section: process may stay here forever (no fairness)
NCS(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ i' = [i EXCEPT ![self] = 0]
    /\ UNCHANGED << level, last_to_enter >>

\* Loop test of the filter: pass N-1 levels before entering the CS
Enter(self) ==
    /\ pc[self] = "enter"
    /\ IF i[self] < N - 1
          THEN pc' = [pc EXCEPT ![self] = "setlevel"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED << level, last_to_enter, i >>

\* Announce presence at the current level
SetLevel(self) ==
    /\ pc[self] = "setlevel"
    /\ level' = [level EXCEPT ![self] = i[self]]
    /\ pc' = [pc EXCEPT ![self] = "setlast"]
    /\ UNCHANGED << last_to_enter, i >>

\* Mark self as last to enter the current level
SetLast(self) ==
    /\ pc[self] = "setlast"
    /\ last_to_enter' = [last_to_enter EXCEPT ![i[self]] = self]
    /\ pc' = [pc EXCEPT ![self] = "wait"]
    /\ UNCHANGED << level, i >>

\* Wait while another process is at or above this level and self was last to arrive
Wait(self) ==
    /\ pc[self] = "wait"
    /\ \/ last_to_enter[i[self]] # self
       \/ \A k \in Procs \ {self} : level[k] < i[self]
    /\ i' = [i EXCEPT ![self] = i[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED << level, last_to_enter >>

\* Critical section
CS(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << level, last_to_enter, i >>

\* Exit protocol
Exit(self) ==
    /\ pc[self] = "exit"
    /\ level' = [level EXCEPT ![self] = -1]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED << last_to_enter, i >>

\* All process actions except the non-critical section
FairActions(self) ==
    \/ Enter(self)
    \/ SetLevel(self)
    \/ SetLast(self)
    \/ Wait(self)
    \/ CS(self)
    \/ Exit(self)

proc(self) == NCS(self) \/ FairActions(self)

Next == \E self \in Procs : proc(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs : WF_vars(FairActions(self))

=============================================================================