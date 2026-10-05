---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES pc, x, y, b, S

vars == <<pc, x, y, b, S>>

Labels == {"ncs", "start", "l1", "l2", "l3", "l4", "l5", "l6", "cs", "l7", "l8"}

TypeOK == /\ pc \in [Procs -> Labels]
          /\ x \in Procs \cup {0}
          /\ y \in Procs \cup {0}
          /\ b \in [Procs -> BOOLEAN]
          /\ S \in [Procs -> SUBSET Procs]

Init == /\ pc = [p \in Procs |-> "ncs"]
        /\ x = 0
        /\ y = 0
        /\ b = [p \in Procs |-> FALSE]
        /\ S = [p \in Procs |-> {}]

(* Non-critical section - process decides to enter *)
ncs(p) == /\ pc[p] = "ncs"
          /\ pc' = [pc EXCEPT ![p] = "start"]
          /\ UNCHANGED <<x, y, b, S>>

(* Start: set b[p] to TRUE *)
start(p) == /\ pc[p] = "start"
            /\ b' = [b EXCEPT ![p] = TRUE]
            /\ pc' = [pc EXCEPT ![p] = "l1"]
            /\ UNCHANGED <<x, y, S>>

(* l1: set x to p *)
l1(p) == /\ pc[p] = "l1"
         /\ x' = p
         /\ pc' = [pc EXCEPT ![p] = "l2"]
         /\ UNCHANGED <<y, b, S>>

(* l2: check if y != 0 *)
l2(p) == /\ pc[p] = "l2"
         /\ IF y /= 0
            THEN /\ b' = [b EXCEPT ![p] = FALSE]
                 /\ pc' = [pc EXCEPT ![p] = "l3"]
            ELSE /\ pc' = [pc EXCEPT ![p] = "l4"]
                 /\ UNCHANGED b
         /\ UNCHANGED <<x, y, S>>

(* l3: wait until y = 0, then restart *)
l3(p) == /\ pc[p] = "l3"
         /\ y = 0
         /\ pc' = [pc EXCEPT ![p] = "start"]
         /\ UNCHANGED <<x, y, b, S>>

(* l4: set y to p *)
l4(p) == /\ pc[p] = "l4"
         /\ y' = p
         /\ pc' = [pc EXCEPT ![p] = "l5"]
         /\ UNCHANGED <<x, b, S>>

(* l5: check if x = p *)
l5(p) == /\ pc[p] = "l5"
         /\ IF x /= p
            THEN /\ b' = [b EXCEPT ![p] = FALSE]
                 /\ S' = [S EXCEPT ![p] = {q \in Procs : b[q]}]
                 /\ pc' = [pc EXCEPT ![p] = "l6"]
            ELSE /\ pc' = [pc EXCEPT ![p] = "cs"]
                 /\ UNCHANGED <<b, S>>
         /\ UNCHANGED <<x, y>>

(* l6: wait for all processes in S[p] to have b = FALSE, then check y *)
l6(p) == /\ pc[p] = "l6"
         /\ \A q \in S[p] : ~b[q]
         /\ IF y = p
            THEN pc' = [pc EXCEPT ![p] = "cs"]
            ELSE pc' = [pc EXCEPT ![p] = "l3"]
         /\ UNCHANGED <<x, y, b, S>>

(* Critical section *)
cs(p) == /\ pc[p] = "cs"
         /\ pc' = [pc EXCEPT ![p] = "l7"]
         /\ UNCHANGED <<x, y, b, S>>

(* l7: set y to 0 *)
l7(p) == /\ pc[p] = "l7"
         /\ y' = 0
         /\ pc' = [pc EXCEPT ![p] = "l8"]
         /\ UNCHANGED <<x, b, S>>

(* l8: set b[p] to FALSE and return to ncs *)
l8(p) == /\ pc[p] = "l8"
         /\ b' = [b EXCEPT ![p] = FALSE]
         /\ pc' = [pc EXCEPT ![p] = "ncs"]
         /\ UNCHANGED <<x, y, S>>

(* Process p takes a step *)
proc(p) == \/ ncs(p)
           \/ start(p)
           \/ l1(p)
           \/ l2(p)
           \/ l3(p)
           \/ l4(p)
           \/ l5(p)
           \/ l6(p)
           \/ cs(p)
           \/ l7(p)
           \/ l8(p)

Next == \E p \in Procs : proc(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety: Mutual Exclusion - no two distinct processes are simultaneously in cs *)
MutualExclusion == \A p, q \in Procs : (p /= q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Liveness: Infinitely often some process is in the critical section *)
Liveness == []<>(\E p \in Procs : pc[p] = "cs")

=============================================================================