-------------------------- MODULE LamportFast --------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANT N
ASSUME N \in Nat \ {0, 1}

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>
ProcSet == 1..N
PCStates == {"Start", "CheckY1", "AwaitY1", "CheckX", "AwaitB", "CheckY2", "AwaitY2", "CS"}

TypeOK ==
    /\ x \in ProcSet
    /\ y \in 0..N
    /\ b \in [ProcSet -> BOOLEAN]
    /\ pc \in [ProcSet -> PCStates]

Init ==
    /\ x = 1
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ pc = [i \in ProcSet |-> "Start"]

(* Actions for process i *)

(* b[i] := TRUE; x := i; *)
P1(i) ==
    /\ pc[i] = "Start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "CheckY1"]
    /\ UNCHANGED <<y>>

(* if y /= 0 then b[i] := FALSE; goto AwaitY1 *)
P2(i) ==
    /\ pc[i] = "CheckY1"
    /\ y /= 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "AwaitY1"]
    /\ UNCHANGED <<x, y>>

(* else y := i; goto CheckX *)
P3(i) ==
    /\ pc[i] = "CheckY1"
    /\ y = 0
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "CheckX"]
    /\ UNCHANGED <<x, b>>

(* await y = 0; goto Start *)
P4(i) ==
    /\ pc[i] = "AwaitY1"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<x, y, b>>

(* if x /= i then b[i] := FALSE; goto AwaitB (slow path) *)
P5(i) ==
    /\ pc[i] = "CheckX"
    /\ x /= i
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "AwaitB"]
    /\ UNCHANGED <<x, y>>

(* else goto CS (fast path) *)
P6(i) ==
    /\ pc[i] = "CheckX"
    /\ x = i
    /\ pc' = [pc EXCEPT ![i] = "CS"]
    /\ UNCHANGED <<x, y, b>>

(* await (\A j \in ProcSet : b[j] = FALSE) *)
P7(i) ==
    /\ pc[i] = "AwaitB"
    /\ \A j \in ProcSet : b[j] = FALSE
    /\ pc' = [pc EXCEPT ![i] = "CheckY2"]
    /\ UNCHANGED <<x, y, b>>

(* if y /= i then goto AwaitY2 *)
P8(i) ==
    /\ pc[i] = "CheckY2"
    /\ y /= i
    /\ pc' = [pc EXCEPT ![i] = "AwaitY2"]
    /\ UNCHANGED <<x, y, b>>

(* else goto CS *)
P9(i) ==
    /\ pc[i] = "CheckY2"
    /\ y = i
    /\ pc' = [pc EXCEPT ![i] = "CS"]
    /\ UNCHANGED <<x, y, b>>

(* await y = 0; goto Start *)
P10(i) ==
    /\ pc[i] = "AwaitY2"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<x, y, b>>

(* Critical Section & Exit: y := 0; b[i] := FALSE; *)
P11(i) ==
    /\ pc[i] = "CS"
    /\ y' = 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<x>>

P(i) == P1(i) \/ P2(i) \/ P3(i) \/ P4(i) \/ P5(i) \/ P6(i) \/ P7(i) \/ P8(i) \/ P9(i) \/ P10(i) \/ P11(i)

Next == \E i \in ProcSet : P(i)

Fairness == \A i \in ProcSet : WF_vars(P(i))

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion == \A i, j \in ProcSet : (i /= j) => ~(pc[i] = "CS" /\ pc[j] = "CS")

Invariant == TypeOK /\ MutualExclusion

Liveness == []<>(\E i \in ProcSet : pc[i] = "CS")

=============================================================================