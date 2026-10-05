---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLAPS

CONSTANTS M, N

ASSUME MN == M \in Nat /\ N \in Nat /\ M < N /\ M > 0

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

Procs1 == 1..M
Procs2 == (M+1)..N
Procs == Procs1 \cup Procs2

Init == /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]
        /\ pc = [i \in Procs |-> "ncs"]

\* Process class 1: processes 1..M

ncs1(self) == /\ self \in Procs1
              /\ pc[self] = "ncs"
              /\ pc' = [pc EXCEPT ![self] = "start1"]
              /\ UNCHANGED <<x, y, b>>

start1(self) == /\ self \in Procs1
                /\ pc[self] = "start1"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ x' = self
                /\ pc' = [pc EXCEPT ![self] = "check1_y1"]
                /\ UNCHANGED y

check1_y1(self) == /\ self \in Procs1
                   /\ pc[self] = "check1_y1"
                   /\ IF y /= 0
                      THEN /\ b' = [b EXCEPT ![self] = FALSE]
                           /\ pc' = [pc EXCEPT ![self] = "wait1_y1"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "set1_y1"]
                           /\ b' = b
                   /\ UNCHANGED <<x, y>>

wait1_y1(self) == /\ self \in Procs1
                  /\ pc[self] = "wait1_y1"
                  /\ y = 0
                  /\ pc' = [pc EXCEPT ![self] = "start1"]
                  /\ UNCHANGED <<x, y, b>>

set1_y1(self) == /\ self \in Procs1
                 /\ pc[self] = "set1_y1"
                 /\ y' = self
                 /\ pc' = [pc EXCEPT ![self] = "check1_x1"]
                 /\ UNCHANGED <<x, b>>

check1_x1(self) == /\ self \in Procs1
                   /\ pc[self] = "check1_x1"
                   /\ IF x /= self
                      THEN /\ b' = [b EXCEPT ![self] = FALSE]
                           /\ pc' = [pc EXCEPT ![self] = "wait1_b1"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "cs1"]
                           /\ b' = b
                   /\ UNCHANGED <<x, y>>

wait1_b1(self) == /\ self \in Procs1
                  /\ pc[self] = "wait1_b1"
                  /\ \A j \in Procs : ~b[j]
                  /\ pc' = [pc EXCEPT ![self] = "check1_y2"]
                  /\ UNCHANGED <<x, y, b>>

check1_y2(self) == /\ self \in Procs1
                   /\ pc[self] = "check1_y2"
                   /\ IF y = self
                      THEN /\ pc' = [pc EXCEPT ![self] = "cs1"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "wait1_y2"]
                   /\ UNCHANGED <<x, y, b>>

wait1_y2(self) == /\ self \in Procs1
                  /\ pc[self] = "wait1_y2"
                  /\ y = 0
                  /\ pc' = [pc EXCEPT ![self] = "start1"]
                  /\ UNCHANGED <<x, y, b>>

cs1(self) == /\ self \in Procs1
             /\ pc[self] = "cs1"
             /\ pc' = [pc EXCEPT ![self] = "exit1"]
             /\ UNCHANGED <<x, y, b>>

exit1(self) == /\ self \in Procs1
               /\ pc[self] = "exit1"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
               /\ UNCHANGED x

proc1(self) == ncs1(self) \/ start1(self) \/ check1_y1(self) \/ wait1_y1(self)
               \/ set1_y1(self) \/ check1_x1(self) \/ wait1_b1(self)
               \/ check1_y2(self) \/ wait1_y2(self) \/ cs1(self) \/ exit1(self)

\* Process class 2: processes (M+1)..N

ncs2(self) == /\ self \in Procs2
              /\ pc[self] = "ncs"
              /\ pc' = [pc EXCEPT ![self] = "start2"]
              /\ UNCHANGED <<x, y, b>>

start2(self) == /\ self \in Procs2
                /\ pc[self] = "start2"
                /\ b' = [b EXCEPT ![self] = TRUE]
                /\ x' = self
                /\ pc' = [pc EXCEPT ![self] = "check2_y1"]
                /\ UNCHANGED y

check2_y1(self) == /\ self \in Procs2
                   /\ pc[self] = "check2_y1"
                   /\ IF y /= 0
                      THEN /\ b' = [b EXCEPT ![self] = FALSE]
                           /\ pc' = [pc EXCEPT ![self] = "wait2_y1"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "set2_y1"]
                           /\ b' = b
                   /\ UNCHANGED <<x, y>>

wait2_y1(self) == /\ self \in Procs2
                  /\ pc[self] = "wait2_y1"
                  /\ y = 0
                  /\ pc' = [pc EXCEPT ![self] = "start2"]
                  /\ UNCHANGED <<x, y, b>>

set2_y1(self) == /\ self \in Procs2
                 /\ pc[self] = "set2_y1"
                 /\ y' = self
                 /\ pc' = [pc EXCEPT ![self] = "check2_x1"]
                 /\ UNCHANGED <<x, b>>

check2_x1(self) == /\ self \in Procs2
                   /\ pc[self] = "check2_x1"
                   /\ IF x /= self
                      THEN /\ b' = [b EXCEPT ![self] = FALSE]
                           /\ pc' = [pc EXCEPT ![self] = "wait2_b1"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "cs2"]
                           /\ b' = b
                   /\ UNCHANGED <<x, y>>

wait2_b1(self) == /\ self \in Procs2
                  /\ pc[self] = "wait2_b1"
                  /\ \A j \in Procs : ~b[j]
                  /\ pc' = [pc EXCEPT ![self] = "check2_y2"]
                  /\ UNCHANGED <<x, y, b>>

check2_y2(self) == /\ self \in Procs2
                   /\ pc[self] = "check2_y2"
                   /\ IF y = self
                      THEN /\ pc' = [pc EXCEPT ![self] = "cs2"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "wait2_y2"]
                   /\ UNCHANGED <<x, y, b>>

wait2_y2(self) == /\ self \in Procs2
                  /\ pc[self] = "wait2_y2"
                  /\ y = 0
                  /\ pc' = [pc EXCEPT ![self] = "start2"]
                  /\ UNCHANGED <<x, y, b>>

cs2(self) == /\ self \in Procs2
             /\ pc[self] = "cs2"
             /\ pc' = [pc EXCEPT ![self] = "exit2"]
             /\ UNCHANGED <<x, y, b>>

exit2(self) == /\ self \in Procs2
               /\ pc[self] = "exit2"
               /\ y' = 0
               /\ b' = [b EXCEPT ![self] = FALSE]
               /\ pc' = [pc EXCEPT ![self] = "ncs"]
               /\ UNCHANGED x

proc2(self) == ncs2(self) \/ start2(self) \/ check2_y1(self) \/ wait2_y1(self)
               \/ set2_y1(self) \/ check2_x1(self) \/ wait2_b1(self)
               \/ check2_y2(self) \/ wait2_y2(self) \/ cs2(self) \/ exit2(self)

\* Overall next-state relation

Next == \/ \E self \in Procs1 : proc1(self)
        \/ \E self \in Procs2 : proc2(self)

\* Specification with weak fairness for each process class

Fairness == /\ \A self \in Procs1 : WF_vars(proc1(self))
            /\ \A self \in Procs2 : WF_vars(proc2(self))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Type invariant

TypeOK == /\ x \in Procs \cup {0}
          /\ y \in Procs \cup {0}
          /\ b \in [Procs -> BOOLEAN]
          /\ pc \in [Procs -> {"ncs", "start1", "check1_y1", "wait1_y1", "set1_y1",
                               "check1_x1", "wait1_b1", "check1_y2", "wait1_y2",
                               "cs1", "exit1", "start2", "check2_y1", "wait2_y1",
                               "set2_y1", "check2_x1", "wait2_b1", "check2_y2",
                               "wait2_y2", "cs2", "exit2"}]

\* Safety: Mutual exclusion invariant

InCS(i) == pc[i] \in {"cs1", "cs2"}

MutualExclusion == \A i, j \in Procs : (i /= j) => ~(InCS(i) /\ InCS(j))

\* Liveness: Some process enters the critical section infinitely often

Liveness == []<>(\E i \in Procs : InCS(i))

==========================================================================