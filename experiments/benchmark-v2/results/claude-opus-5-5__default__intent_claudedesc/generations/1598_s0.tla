---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Proc == 1..N

VARIABLES x, y, b, pc, j

vars == <<x, y, b, pc, j>>

Labels == {"start", "l1", "l2", "l3", "l4", "l5", "l6", "l7", "l8",
           "cs", "l9", "l10"}

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [Proc -> BOOLEAN]
    /\ pc \in [Proc -> Labels]
    /\ j \in [Proc -> 1..(N+1)]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Proc |-> FALSE]
    /\ pc = [i \in Proc |-> "start"]
    /\ j = [i \in Proc |-> 1]

\* Signal intent
start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "l1"]
    /\ UNCHANGED <<x, y, j>>

\* Write identity to x
l1(self) ==
    /\ pc[self] = "l1"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "l2"]
    /\ UNCHANGED <<y, b, j>>

\* First contention check: examine y
l2(self) ==
    /\ pc[self] = "l2"
    /\ IF y # 0
          THEN /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "l3"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
               /\ b' = b
    /\ UNCHANGED <<x, y, j>>

\* Back off: wait until y is clear, then retry
l3(self) ==
    /\ pc[self] = "l3"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, j>>

\* Write identity to y
l4(self) ==
    /\ pc[self] = "l4"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED <<x, b, j>>

\* Second contention check: examine x
l5(self) ==
    /\ pc[self] = "l5"
    /\ IF x # self
          THEN /\ b' = [b EXCEPT ![self] = FALSE]
               /\ j' = [j EXCEPT ![self] = 1]
               /\ pc' = [pc EXCEPT ![self] = "l6"]
          ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
               /\ UNCHANGED <<b, j>>
    /\ UNCHANGED <<x, y>>

\* Slow path: wait for every flag to be cleared
l6(self) ==
    /\ pc[self] = "l6"
    /\ IF j[self] <= N
          THEN /\ ~b[j[self]]
               /\ j' = [j EXCEPT ![self] = j[self] + 1]
               /\ pc' = pc
          ELSE /\ pc' = [pc EXCEPT ![self] = "l7"]
               /\ j' = j
    /\ UNCHANGED <<x, y, b>>

\* Slow path: check whether we still own y
l7(self) ==
    /\ pc[self] = "l7"
    /\ IF y # self
          THEN pc' = [pc EXCEPT ![self] = "l8"]
          ELSE pc' = [pc EXCEPT ![self] = "cs"]
    /\ UNCHANGED <<x, y, b, j>>

\* Back off: wait until y is clear, then retry
l8(self) ==
    /\ pc[self] = "l8"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, j>>

\* Critical section
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "l9"]
    /\ UNCHANGED <<x, y, b, j>>

\* Exit: clear y
l9(self) ==
    /\ pc[self] = "l9"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![self] = "l10"]
    /\ UNCHANGED <<x, b, j>>

\* Exit: clear own flag and loop
l10(self) ==
    /\ pc[self] = "l10"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, j>>

proc(self) ==
    \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self) \/ l4(self)
    \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
    \/ cs(self) \/ l9(self) \/ l10(self)

Next == \E self \in Proc : proc(self)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A self \in Proc : WF_vars(proc(self))

-----------------------------------------------------------------------------

\* Safety: no two distinct processes are in the critical section simultaneously
MutualExclusion ==
    \A i, k \in Proc : (i # k) => ~(pc[i] = "cs" /\ pc[k] = "cs")

\* Liveness: some process enters the critical section infinitely often
Liveness == []<>(\E i \in Proc : pc[i] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => Liveness
=============================================================================