-------------------------------- MODULE FastMutex --------------------------------
EXTENDS Integers, FiniteSets, TLAPS

CONSTANTS N

ASSUME NAssumption == N \in Nat \ {0}

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

(* Start of protocol - set b[p] to TRUE *)
start(p) ==
    /\ pc[p] = "start"
    /\ b' = [b EXCEPT ![p] = TRUE]
    /\ pc' = [pc EXCEPT ![p] = "l1"]
    /\ UNCHANGED <<x, y, S>>

(* l1: Read x and check if 0 *)
l1(p) ==
    /\ pc[p] = "l1"
    /\ x = 0
    /\ x' = p
    /\ pc' = [pc EXCEPT ![p] = "l2"]
    /\ UNCHANGED <<y, b, S>>

l1_retry(p) ==
    /\ pc[p] = "l1"
    /\ x /= 0
    /\ pc' = [pc EXCEPT ![p] = "l5"]
    /\ UNCHANGED <<x, y, b, S>>

(* l2: Check if y is 0 *)
l2(p) ==
    /\ pc[p] = "l2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![p] = "l3"]
    /\ UNCHANGED <<x, y, b, S>>

l2_wait(p) ==
    /\ pc[p] = "l2"
    /\ y /= 0
    /\ pc' = [pc EXCEPT ![p] = "l5"]
    /\ UNCHANGED <<x, y, b, S>>

(* l3: Set y to p *)
l3(p) ==
    /\ pc[p] = "l3"
    /\ y' = p
    /\ pc' = [pc EXCEPT ![p] = "l4"]
    /\ UNCHANGED <<x, b, S>>

(* l4: Check if x = p, if so enter CS, else go to slow path *)
l4_fast(p) ==
    /\ pc[p] = "l4"
    /\ x = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED <<x, y, b, S>>

l4_slow(p) ==
    /\ pc[p] = "l4"
    /\ x /= p
    /\ pc' = [pc EXCEPT ![p] = "l5"]
    /\ UNCHANGED <<x, y, b, S>>

(* l5: Set b[p] to FALSE and collect waiting set *)
l5(p) ==
    /\ pc[p] = "l5"
    /\ b' = [b EXCEPT ![p] = FALSE]
    /\ S' = [S EXCEPT ![p] = {q \in Procs : b[q]}]
    /\ pc' = [pc EXCEPT ![p] = "l6"]
    /\ UNCHANGED <<x, y>>

(* l6: Wait for all processes in S to have b = FALSE, then check y *)
l6_wait(p) ==
    /\ pc[p] = "l6"
    /\ \E q \in S[p] : b[q]
    /\ S' = [S EXCEPT ![p] = {q \in S[p] : b[q]}]
    /\ UNCHANGED <<pc, x, y, b>>

l6_check(p) ==
    /\ pc[p] = "l6"
    /\ \A q \in S[p] : ~b[q]
    /\ IF y = p
       THEN pc' = [pc EXCEPT ![p] = "cs"]
       ELSE pc' = [pc EXCEPT ![p] = "start"]
    /\ UNCHANGED <<x, y, b, S>>

(* Critical section - process is in CS *)
cs(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "l7"]
    /\ UNCHANGED <<x, y, b, S>>

(* l7: Set y to 0 when leaving CS *)
l7(p) ==
    /\ pc[p] = "l7"
    /\ y' = 0
    /\ pc' = [pc EXCEPT ![p] = "l8"]
    /\ UNCHANGED <<x, b, S>>

(* l8: Set b[p] to FALSE and return to ncs *)
l8(p) ==
    /\ pc[p] = "l8"
    /\ b' = [b EXCEPT ![p] = FALSE]
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED <<x, y, S>>

(* Process action - all possible actions for process p *)
proc(p) ==
    \/ ncs(p)
    \/ start(p)
    \/ l1(p)
    \/ l1_retry(p)
    \/ l2(p)
    \/ l2_wait(p)
    \/ l3(p)
    \/ l4_fast(p)
    \/ l4_slow(p)
    \/ l5(p)
    \/ l6_wait(p)
    \/ l6_check(p)
    \/ cs(p)
    \/ l7(p)
    \/ l8(p)

Next == \E p \in Procs : proc(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety: Mutual Exclusion - no two distinct processes in CS simultaneously *)
MutualExclusion ==
    \A p, q \in Procs : (p /= q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Liveness: Infinitely often some process is in the critical section *)
Liveness == []<>(\E p \in Procs : pc[p] = "cs")

================================================================================