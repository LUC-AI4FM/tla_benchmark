---------------------------- MODULE CBakery ----------------------------
EXTENDS Integers, Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum

ASSUME NumProcs \in Nat /\ NumProcs > 0
ASSUME MaxNum \in Nat /\ MaxNum > 0

Procs == 1..NumProcs

VARIABLES pc, num, choosing, read, max, nxt

vars == <<pc, num, choosing, read, max, nxt>>

Labels == {"d1", "d2", "d3", "w1", "w2", "cs", "exit"}

TypeOK ==
    /\ pc \in [Procs -> Labels]
    /\ num \in [Procs -> Nat]
    /\ choosing \in [Procs -> BOOLEAN]
    /\ read \in [Procs -> Procs \cup {0}]
    /\ max \in [Procs -> Nat]
    /\ nxt \in [Procs -> Procs \cup {0}]

Init ==
    /\ pc = [p \in Procs |-> "d1"]
    /\ num = [p \in Procs |-> 0]
    /\ choosing = [p \in Procs |-> FALSE]
    /\ read = [p \in Procs |-> 0]
    /\ max = [p \in Procs |-> 0]
    /\ nxt = [p \in Procs |-> 0]

(* d1: Start choosing - set choosing to TRUE and initialize read and max *)
d1(self) ==
    /\ pc[self] = "d1"
    /\ choosing' = [choosing EXCEPT ![self] = TRUE]
    /\ read' = [read EXCEPT ![self] = 1]
    /\ max' = [max EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "d2"]
    /\ UNCHANGED <<num, nxt>>

(* d2: Scan all processes to find maximum ticket number *)
d2(self) ==
    /\ pc[self] = "d2"
    /\ IF read[self] <= NumProcs
       THEN /\ max' = [max EXCEPT ![self] = IF num[read[self]] > max[self] 
                                            THEN num[read[self]] 
                                            ELSE max[self]]
            /\ read' = [read EXCEPT ![self] = read[self] + 1]
            /\ pc' = [pc EXCEPT ![self] = "d2"]
       ELSE /\ pc' = [pc EXCEPT ![self] = "d3"]
            /\ UNCHANGED <<max, read>>
    /\ UNCHANGED <<num, choosing, nxt>>

(* d3: Pick number (max + 1) and clear choosing flag *)
d3(self) ==
    /\ pc[self] = "d3"
    /\ num' = [num EXCEPT ![self] = max[self] + 1]
    /\ choosing' = [choosing EXCEPT ![self] = FALSE]
    /\ nxt' = [nxt EXCEPT ![self] = 1]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED <<read, max>>

(* w1: Wait loop - check if done with all processes or wait for next *)
w1(self) ==
    /\ pc[self] = "w1"
    /\ IF nxt[self] <= NumProcs
       THEN /\ IF nxt[self] = self
               THEN /\ nxt' = [nxt EXCEPT ![self] = nxt[self] + 1]
                    /\ pc' = [pc EXCEPT ![self] = "w1"]
               ELSE /\ pc' = [pc EXCEPT ![self] = "w2"]
                    /\ UNCHANGED nxt
       ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
            /\ UNCHANGED nxt
    /\ UNCHANGED <<num, choosing, read, max>>

(* w2: Wait until other process is not choosing and has lower priority *)
w2(self) ==
    /\ pc[self] = "w2"
    /\ ~choosing[nxt[self]]
    /\ \/ num[nxt[self]] = 0
       \/ num[nxt[self]] > num[self]
       \/ (num[nxt[self]] = num[self] /\ nxt[self] > self)
    /\ nxt' = [nxt EXCEPT ![self] = nxt[self] + 1]
    /\ pc' = [pc EXCEPT ![self] = "w1"]
    /\ UNCHANGED <<num, choosing, read, max>>

(* cs: Critical section *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED <<num, choosing, read, max, nxt>>

(* exit: Leave critical section and reset ticket *)
exit(self) ==
    /\ pc[self] = "exit"
    /\ num' = [num EXCEPT ![self] = 0]
    /\ pc' = [pc EXCEPT ![self] = "d1"]
    /\ UNCHANGED <<choosing, read, max, nxt>>

(* Process action *)
Process(self) ==
    \/ d1(self)
    \/ d2(self)
    \/ d3(self)
    \/ w1(self)
    \/ w2(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in Procs : Process(self)

(* State constraint for model checking *)
StateConstraint == \A p \in Procs : num[p] <= MaxNum

(* Mutual exclusion invariant *)
Invariant == \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* Specification - safety only, no fairness *)
Spec == Init /\ [][Next]_vars

==========================================================================