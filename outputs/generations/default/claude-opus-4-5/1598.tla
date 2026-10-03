---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES x, y, b, S, pc

vars == <<x, y, b, S, pc>>

Labels == {"ncs", "start", "l1", "l2", "l3", "l4", "l5", "l6", "cs", "l7", "l8"}

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

(* Non-critical section - process decides to try entering CS *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

(* Start of fast path - set b[self] to TRUE *)
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

(* Check if y is 0, if not reset b and wait *)
l2(self) ==
    /\ pc[self] = "l2"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![self] = FALSE]
            /\ pc' = [pc EXCEPT ![self] = "l3"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "l4"]
            /\ UNCHANGED b
    /\ UNCHANGED <<x, y, S>>

(* Wait until y = 0, then restart *)
l3(self) ==
    /\ pc[self] = "l3"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

(* Set y to self (claiming the lock) *)
l4(self) ==
    /\ pc[self] = "l4"
    /\ y' = self
    /\ pc' = [pc EXCEPT ![self] = "l5"]
    /\ UNCHANGED <<x, b, S>>

(* Check if x = self (fast path succeeded) *)
l5(self) ==
    /\ pc[self] = "l5"
    /\ IF x = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "l6"]
    /\ UNCHANGED <<x, y, b, S>>

(* Slow path - set b[self] to FALSE and collect waiting processes *)
l6(self) ==
    /\ pc[self] = "l6"
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ S' = [S EXCEPT ![self] = {j \in Procs : b[j]}]
    /\ pc' = [pc EXCEPT ![self] = "l7"]
    /\ UNCHANGED <<x, y>>

(* Wait for all processes in S to leave, check if y = self *)
l7(self) ==
    /\ pc[self] = "l7"
    /\ \A j \in S[self] : ~b[j]
    /\ IF y = self
       THEN pc' = [pc EXCEPT ![self] = "cs"]
       ELSE pc' = [pc EXCEPT ![self] = "l8"]
    /\ UNCHANGED <<x, y, b, S>>

(* Wait until y = 0, then restart *)
l8(self) ==
    /\ pc[self] = "l8"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![self] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

(* Critical section - proceed to exit *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ y' = 0
    /\ b' = [b EXCEPT ![self] = FALSE]
    /\ pc' = [pc EXCEPT ![self] = "ncs"]
    /\ UNCHANGED <<x, S>>

(* Process action *)
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
    \/ l8(self)
    \/ cs(self)

Next == \E self \in Procs : proc(self)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety: Mutual Exclusion - no two distinct processes in CS simultaneously *)
MutualExclusion ==
    \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness: Infinitely often some process is in CS *)
Liveness == []<>(\E self \in Procs : pc[self] = "cs")

==========================================================================