---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES pc, x, y, b, S

vars == <<pc, x, y, b, S>>

Labels == {"ncs", "start", "l1", "l2", "l3", "l4", "l5", "l6", "cs", "l7", "l8"}

TypeOK ==
    /\ pc \in [Procs -> Labels]
    /\ x \in Procs \cup {0}
    /\ y \in Procs \cup {0}
    /\ b \in [Procs -> BOOLEAN]
    /\ S \in [Procs -> SUBSET Procs]

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ x = 0
    /\ y = 0
    /\ b = [p \in Procs |-> FALSE]
    /\ S = [p \in Procs |-> {}]

(* Non-critical section - process decides to enter critical section *)
ncs(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

(* Start of algorithm - set b[p] to TRUE *)
start(p) ==
    /\ pc[p] = "start"
    /\ b' = [b EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "l1"]
    /\ UNCHANGED <<x, y, S>>

(* l1: Set x to p *)
l1(p) ==
    /\ pc[p] = "l1"
    /\ x' = p
    /\ pc' = [pc EXCEPT ![p] = "l2"]
    /\ UNCHANGED <<y, b, S>>

(* l2: Check if y is 0, if not go back to start after setting b[p] to FALSE *)
l2(p) ==
    /\ pc[p] = "l2"
    /\ IF y /= 0
       THEN /\ b' = [b EXCEPT ![p] = FALSE]
            /\ pc' = [pc EXCEPT ![p] = "l3"]
            /\ UNCHANGED <<x, y, S>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "l4"]
            /\ UNCHANGED <<x, y, b, S>>

(* l3: Wait until y = 0, then restart *)
l3(p) ==
    /\ pc[p] = "l3"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![p] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

(* l4: Set y to p *)
l4(p) ==
    /\ pc[p] = "l4"
    /\ y' = p
    /\ pc' = [pc EXCEPT ![p] = "l5"]
    /\ UNCHANGED <<x, b, S>>

(* l5: Check if x = p *)
l5(p) ==
    /\ pc[p] = "l5"
    /\ IF x /= p
       THEN /\ b' = [b EXCEPT ![p] = FALSE]
            /\ pc' = [pc EXCEPT ![p] = "l6"]
            /\ UNCHANGED <<x, y, S>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
            /\ UNCHANGED <<x, y, b, S>>

(* l6: Collect all processes q where b[q] is TRUE into S[p], then check if y = p *)
l6(p) ==
    /\ pc[p] = "l6"
    /\ S' = [S EXCEPT ![p] = {q \in Procs : b[q]}]
    /\ IF y /= p
       THEN /\ pc' = [pc EXCEPT ![p] = "l3"]
            /\ UNCHANGED <<x, y, b>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "l7"]
            /\ UNCHANGED <<x, y, b>>

(* l7: Wait until all processes in S[p] have b[q] = FALSE *)
l7(p) ==
    /\ pc[p] = "l7"
    /\ \A q \in S[p] : ~b[q]
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<x, y, b, S>>

(* Critical section - process is in CS *)
cs(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "l8"]
    /\ UNCHANGED <<x, y, b, S>>

(* l8: Exit protocol - set y to 0 and b[p] to FALSE *)
l8(p) ==
    /\ pc[p] = "l8"
    /\ y' = 0
    /\ b' = [b EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED <<x, S>>

(* Process p takes a step *)
proc(p) ==
    \/ ncs(p)
    \/ start(p)
    \/ l1(p)
    \/ l2(p)
    \/ l3(p)
    \/ l4(p)
    \/ l5(p)
    \/ l6(p)
    \/ l7(p)
    \/ cs(p)
    \/ l8(p)

Next == \E p \in Procs : proc(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety: Mutual exclusion - no two distinct processes in CS simultaneously *)
MutualExclusion == \A p, q \in Procs : (p /= q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Liveness: Infinitely often some process is in the critical section *)
Liveness == []<>(\E p \in Procs : pc[p] = "cs")

==========================================================================