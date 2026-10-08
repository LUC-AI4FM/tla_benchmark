----------------------------- MODULE MutualExclusion -----------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

Procs == 1..N

(* Process states/labels *)
Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "start"]

(* Process i sets its flag and writes to x *)
Start(i) ==
    /\ pc[i] = "start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "check_y1"]
    /\ y' = y

(* Process i checks if y is nonzero (contention check 1) *)
CheckY1(i) ==
    /\ pc[i] = "check_y1"
    /\ IF y /= 0
       THEN pc' = [pc EXCEPT ![i] = "backoff"]
       ELSE pc' = [pc EXCEPT ![i] = "set_y"]
    /\ UNCHANGED <<x, y, b>>

(* Process i sets y to its identity *)
SetY(i) ==
    /\ pc[i] = "set_y"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "check_x"]
    /\ UNCHANGED <<x, b>>

(* Process i checks if x still equals i *)
CheckX(i) ==
    /\ pc[i] = "check_x"
    /\ IF x /= i
       THEN pc' = [pc EXCEPT ![i] = "backoff"]
       ELSE pc' = [pc EXCEPT ![i] = "check_y2"]
    /\ UNCHANGED <<x, y, b>>

(* Process i checks y again before entering CS *)
CheckY2(i) ==
    /\ pc[i] = "check_y2"
    /\ IF y /= i
       THEN pc' = [pc EXCEPT ![i] = "backoff"]
       ELSE pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, b>>

(* Backoff: clear flag *)
Backoff(i) ==
    /\ pc[i] = "backoff"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "wait_y"]
    /\ UNCHANGED <<x, y>>

(* Wait until y is clear before retrying *)
WaitY(i) ==
    /\ pc[i] = "wait_y"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x, y, b>>

(* Critical section: process i is in CS *)
CS(i) ==
    /\ pc[i] = "cs"
    /\ pc' = [pc EXCEPT ![i] = "exit"]
    /\ UNCHANGED <<x, y, b>>

(* Exit: clear y and flag, return to start *)
Exit(i) ==
    /\ pc[i] = "exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "start"]
    /\ UNCHANGED <<x>>

(* All actions for process i *)
Step(i) ==
    \/ Start(i)
    \/ CheckY1(i)
    \/ SetY(i)
    \/ CheckX(i)
    \/ CheckY2(i)
    \/ Backoff(i)
    \/ WaitY(i)
    \/ CS(i)
    \/ Exit(i)

(* Next state relation *)
Next == \E i \in Procs : Step(i)

(* Fairness: weak fairness for all process steps *)
Fairness == \A i \in Procs : WF_vars(Step(i))

(* Complete specification *)
Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety: Mutual exclusion - no two distinct processes in CS simultaneously *)
MutualExclusion ==
    \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Invariant == MutualExclusion

(* Liveness: Some process enters CS infinitely often *)
Liveness == []<>(\E i \in Procs : pc[i] = "cs")

=============================================================================