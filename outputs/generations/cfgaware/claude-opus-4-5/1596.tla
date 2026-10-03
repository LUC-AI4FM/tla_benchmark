---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANTS M, N

ASSUME 1 <= M /\ M < N

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

Procs1 == 1..M
Procs2 == (M+1)..N
Procs == Procs1 \cup Procs2

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]

\* Process class 1: processes 1..M

ncs1(self) ==
    /\ self \in Procs1
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start1"]
    /\ UNCHANGED <<x, y, b>>

start1(self) ==
    /\ self \in Procs1
    /\ pc[self] = "start1"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "check1_1"]
    /\ UNCHANGED y

check1_1(self) ==
    /\ self \in Procs1
    /\ pc[self] = "check1_1"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "wait1_1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "setY1"]
            /\ UNCHANGED b
    /\ UNCHANGED <<x, y>>

wait1_1(self) ==
    /\ self \in Procs1
    /\ pc[self] = "wait1_1"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start1"]
    /\ UNCHANGED <<x, y, b>>

setY1(self) ==
    /\ self \in Procs1
    /\ pc[self] = "setY1"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "check2_1"]
    /\ UNCHANGED <<x, b>>

check2_1(self) ==
    /\ self \in Procs1
    /\ pc[self] = "check2_1"
    /\ IF x /= self
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "wait2_1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs1"]
            /\ UNCHANGED b
    /\ UNCHANGED <<x, y>>

wait2_1(self) ==
    /\ self \in Procs1
    /\ pc[self] = "wait2_1"
    /\ \A j \in Procs : ~b[j]
    /\ pc' = [pc EXCEPT ![self] = "check3_1"]
    /\ UNCHANGED <<x, y, b>>

check3_1(self) ==
    /\ self \in Procs1
    /\ pc[self] = "check3_1"
    /\ IF y /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "start1"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs1"]
    /\ UNCHANGED <<x, y, b>>

cs1(self) ==
    /\ self \in Procs1
    /\ pc[self] = "cs1"
    /\ pc' = [pc EXCEPT ![self] = "exit1"]
    /\ UNCHANGED <<x, y, b>>

exit1(self) ==
    /\ self \in Procs1
    /\ pc[self] = "exit1"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED x

proc1(self) ==
    \/ ncs1(self)
    \/ start1(self)
    \/ check1_1(self)
    \/ wait1_1(self)
    \/ setY1(self)
    \/ check2_1(self)
    \/ wait2_1(self)
    \/ check3_1(self)
    \/ cs1(self)
    \/ exit1(self)

\* Process class 2: processes (M+1)..N

ncs2(self) ==
    /\ self \in Procs2
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start2"]
    /\ UNCHANGED <<x, y, b>>

start2(self) ==
    /\ self \in Procs2
    /\ pc[self] = "start2"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "check1_2"]
    /\ UNCHANGED y

check1_2(self) ==
    /\ self \in Procs2
    /\ pc[self] = "check1_2"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "wait1_2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "setY2"]
            /\ UNCHANGED b
    /\ UNCHANGED <<x, y>>

wait1_2(self) ==
    /\ self \in Procs2
    /\ pc[self] = "wait1_2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start2"]
    /\ UNCHANGED <<x, y, b>>

setY2(self) ==
    /\ self \in Procs2
    /\ pc[self] = "setY2"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "check2_2"]
    /\ UNCHANGED <<x, b>>

check2_2(self) ==
    /\ self \in Procs2
    /\ pc[self] = "check2_2"
    /\ IF x /= self
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "wait2_2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
            /\ UNCHANGED b
    /\ UNCHANGED <<x, y>>

wait2_2(self) ==
    /\ self \in Procs2
    /\ pc[self] = "wait2_2"
    /\ \A j \in Procs : ~b[j]
    /\ pc' = [pc EXCEPT ![self] = "check3_2"]
    /\ UNCHANGED <<x, y, b>>

check3_2(self) ==
    /\ self \in Procs2
    /\ pc[self] = "check3_2"
    /\ IF y /= self
       THEN /\ pc' = [pc EXCEPT ![self] = "start2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
    /\ UNCHANGED <<x, y, b>>

cs2(self) ==
    /\ self \in Procs2
    /\ pc[self] = "cs2"
    /\ pc' = [pc EXCEPT ![self] = "exit2"]
    /\ UNCHANGED <<x, y, b>>

exit2(self) ==
    /\ self \in Procs2
    /\ pc[self] = "exit2"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED x

proc2(self) ==
    \/ ncs2(self)
    \/ start2(self)
    \/ check1_2(self)
    \/ wait1_2(self)
    \/ setY2(self)
    \/ check2_2(self)
    \/ wait2_2(self)
    \/ check3_2(self)
    \/ cs2(self)
    \/ exit2(self)

Next ==
    \/ \E self \in Procs1 : proc1(self)
    \/ \E self \in Procs2 : proc2(self)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A self \in Procs1 : WF_vars(proc1(self))
    /\ \A self \in Procs2 : WF_vars(proc2(self))

InCS(i) ==
    \/ (i \in Procs1 /\ pc[i] = "cs1")
    \/ (i \in Procs2 /\ pc[i] = "cs2")

Invariant ==
    \A i, j \in Procs : (i /= j) => ~(InCS(i) /\ InCS(j))

Liveness ==
    []<>(\E i \in Procs : InCS(i))

=============================================================================