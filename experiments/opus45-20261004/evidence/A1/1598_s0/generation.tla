---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, S, pc

vars == <<x, y, b, S, pc>>

Procs == 1..N

Labels == {"ncs", "start", "l1", "l2", "l3", "l4", "l5", "cs", "l6", "l7"}

TypeOK ==
    /\ x \in Procs \cup {0}
    /\ y \in Procs \cup {0}
    /\ b \in [Procs -> BOOLEAN]
    /\ S \in [Procs -> SUBSET Procs]
    /\ pc \in [Procs -> Labels]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ S = [i \in Procs |-> {}]
    /\ pc = [i \in Procs |-> "ncs"]

(* Non-critical section - process decides to enter critical section *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

(* Start of fast path - set own flag *)
start(self) ==
    /\ pc[self] = "start"
    /\ b' = [b EXCEPT ![self] = TRUE]
    /\ pc' = [pc EXCEPT ![self] = "l1"]
    /\ UNCHANGED <<x, y, S>>

(* Set x to self *)
l1(self) ==
    /\ pc[self] = "l1"
    /\ x' = self
    /\ pc' = [pc EXCEPT ![self] = "l2"]
    /\ UNCHANGED <<y, b, S>>

(* Check if y is 0; if not, reset flag and go to slow path *)
l2(self) ==
    /\ pc[self] = "l2"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ b' = b
    /\ UNCHANGED <<x, y, S>>

(* Slow path: wait until y becomes 0 *)
l3(self) ==
    /\ pc[self] = "l3"
    /\ IF y /= 0
       THEN /\ pc' = [pc EXCEPT ![self] = "l3"]
            /\ UNCHANGED <<x, y, b, S>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "start"]
            /\ UNCHANGED <<x, y, b, S>>

(* Set y to self *)
l4(self) ==
    /\ pc[self] = "l4"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED <<x, b, S>>

(* Check if x equals self (fast path success) *)
l5(self) ==
    /\ pc[self] = "l5"
    /\ IF x /= self
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ S' = [S EXCEPT ![self] = Procs]
            /\ pc' = [pc EXCEPT ![self] = "l6"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED <<b, S>>
    /\ UNCHANGED <<x, y>>

(* Wait for all other processes to have b[j] = FALSE *)
l6(self) ==
    /\ pc[self] = "l6"
    /\ IF S[self] /= {}
       THEN \E j \in S[self]:
            /\ b[j] = FALSE
            /\ S' = [S EXCEPT ![self] = S[self] \ {j}]
            /\ pc' = pc
            /\ UNCHANGED <<x, y, b>>
       ELSE /\ pc' = [pc EXCEPT ![self] = "l7"]
            /\ UNCHANGED <<x, y, b, S>>

(* Check if y still equals self *)
l7(self) ==
    /\ pc[self] = "l7"
    /\ IF y = self
       THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

(* Critical section - then exit *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, S>>

(* Per-process action *)
proc(self) ==
    \/ ncs(self)
    \/ start(self)
    \/ l1(self)
    \/ l2(self)
    \/ l3(self)
    \/ l4(self)
    \/ l5(self)
    \/ l6(self)
    \/ l7(self)
    \/ cs(self)

Next == \E self \in Procs: proc(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Mutual exclusion: no two distinct processes in critical section *)
MutualExclusion == \A i, j \in Procs: (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Invariant == MutualExclusion

(* Liveness: infinitely often some process is in the critical section *)
Liveness == []<>(\E i \in Procs: pc[i] = "cs")

==========================================================================