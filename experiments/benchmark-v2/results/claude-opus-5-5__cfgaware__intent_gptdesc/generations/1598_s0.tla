---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES x, y, b, pc, j

vars == <<x, y, b, pc, j>>

Labels == {"ncs", "start", "l1", "l2", "l3", "l4", "l5", "l6", "l7",
           "l8", "l9", "l10", "cs", "l11", "l12"}

TypeOK ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [Procs -> BOOLEAN]
  /\ pc \in [Procs -> Labels]
  /\ j \in [Procs -> 1..(N+1)]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Procs |-> FALSE]
  /\ pc = [i \in Procs |-> "ncs"]
  /\ j = [i \in Procs |-> 1]

Goto(self, lbl) == pc' = [pc EXCEPT ![self] = lbl]

\* noncritical section: decide to try entering
ncs(self) ==
  /\ pc[self] = "ncs"
  /\ Goto(self, "start")
  /\ UNCHANGED <<x, y, b, j>>

\* set intent flag
start(self) ==
  /\ pc[self] = "start"
  /\ b' = [b EXCEPT ![self] = TRUE]
  /\ Goto(self, "l1")
  /\ UNCHANGED <<x, y, j>>

\* write first tour register
l1(self) ==
  /\ pc[self] = "l1"
  /\ x' = self
  /\ Goto(self, "l2")
  /\ UNCHANGED <<y, b, j>>

\* read second tour register
l2(self) ==
  /\ pc[self] = "l2"
  /\ IF y # 0 THEN Goto(self, "l3") ELSE Goto(self, "l5")
  /\ UNCHANGED <<x, y, b, j>>

\* withdraw intent (contention detected)
l3(self) ==
  /\ pc[self] = "l3"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ Goto(self, "l4")
  /\ UNCHANGED <<x, y, j>>

\* back off: wait until y = 0, then retry
l4(self) ==
  /\ pc[self] = "l4"
  /\ y = 0
  /\ Goto(self, "start")
  /\ UNCHANGED <<x, y, b, j>>

\* write second tour register
l5(self) ==
  /\ pc[self] = "l5"
  /\ y' = self
  /\ Goto(self, "l6")
  /\ UNCHANGED <<x, b, j>>

\* fast path check
l6(self) ==
  /\ pc[self] = "l6"
  /\ IF x # self THEN Goto(self, "l7") ELSE Goto(self, "cs")
  /\ UNCHANGED <<x, y, b, j>>

\* slow path: withdraw intent and prepare to scan flags
l7(self) ==
  /\ pc[self] = "l7"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ j' = [j EXCEPT ![self] = 1]
  /\ Goto(self, "l8")
  /\ UNCHANGED <<x, y>>

\* spin on other processes' flags
l8(self) ==
  /\ pc[self] = "l8"
  /\ IF j[self] <= N
       THEN /\ ~b[j[self]]
            /\ j' = [j EXCEPT ![self] = j[self] + 1]
            /\ Goto(self, "l8")
       ELSE /\ Goto(self, "l9")
            /\ UNCHANGED j
  /\ UNCHANGED <<x, y, b>>

\* check whether we still own y
l9(self) ==
  /\ pc[self] = "l9"
  /\ IF y # self THEN Goto(self, "l10") ELSE Goto(self, "cs")
  /\ UNCHANGED <<x, y, b, j>>

\* lost: wait until y = 0, then retry
l10(self) ==
  /\ pc[self] = "l10"
  /\ y = 0
  /\ Goto(self, "start")
  /\ UNCHANGED <<x, y, b, j>>

\* critical section
cs(self) ==
  /\ pc[self] = "cs"
  /\ Goto(self, "l11")
  /\ UNCHANGED <<x, y, b, j>>

\* cleanup: reset y
l11(self) ==
  /\ pc[self] = "l11"
  /\ y' = 0
  /\ Goto(self, "l12")
  /\ UNCHANGED <<x, b, j>>

\* cleanup: reset intent flag and restart loop
l12(self) ==
  /\ pc[self] = "l12"
  /\ b' = [b EXCEPT ![self] = FALSE]
  /\ Goto(self, "ncs")
  /\ UNCHANGED <<x, y, j>>

Proc(self) ==
  \/ ncs(self) \/ start(self) \/ l1(self) \/ l2(self) \/ l3(self)
  \/ l4(self) \/ l5(self) \/ l6(self) \/ l7(self) \/ l8(self)
  \/ l9(self) \/ l10(self) \/ cs(self) \/ l11(self) \/ l12(self)

Next == \E self \in Procs : Proc(self)

Spec == Init /\ [][Next]_vars /\ \A self \in Procs : WF_vars(Proc(self))

MutualExclusion ==
  \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Invariant == TypeOK /\ MutualExclusion

\* Deadlock freedom: if some process is trying to enter, eventually some
\* process enters the critical section.
DeadlockFreedom ==
  \A i \in Procs :
    (pc[i] \notin {"ncs", "cs", "l11", "l12"}) ~> (\E k \in Procs : pc[k] = "cs")

\* System-wide progress: infinitely often some process is in its CS.
InfinitelyOftenCS == []<>(\E k \in Procs : pc[k] = "cs")

Liveness == DeadlockFreedom /\ InfinitelyOftenCS

=============================================================================