------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals, TLC

CONSTANT N \* number of processes

VARIABLES flags, tour1, tour2, procState

(* ------------------------------------------------------------------ *)
(* Initial state: all intent flags are FALSE, registers are 0,
   and every process is in the idle state. *)
Init == /\ flags = [i ∈ 1..N |-> FALSE]
        /\ tour1 = 0
        /\ tour2 = 0
        /\ procState = [i ∈ 1..N |-> "idle"]

(* ------------------------------------------------------------------ *)
(* Actions for a single process i *)

SetIntent(i) ==
    /\ i ∈ 1..N
    /\ procState[i] = "idle"
    /\ flags' = [flags EXCEPT ![i] = TRUE]
    /\ procState' = [procState EXCEPT ![i] = "intentSet"]
    /\ UNCHANGED <<tour1, tour2>>

WriteTour1(i) ==
    /\ i ∈ 1..N
    /\ procState[i] = "intentSet"
    /\ tour1' = i
    /\ procState' = [procState EXCEPT ![i] = "writeTour1"]
    /\ UNCHANGED <<flags, tour2>>

ReadTour2(i) ==
    /\ i ∈ 1..N
    /\ procState[i] = "writeTour1"
    /\ tour2' = tour1
    /\ procState' = [procState EXCEPT ![i] = "readTour2"]
    /\ UNCHANGED <<flags, tour1>>

CheckEntry(i) ==
    /\ i ∈ 1..N
    /\ procState[i] = "readTour2"
    /\ tour2 = i
    /\ \A j ∈ 1..N : (j = i \/ flags[j] = FALSE)
    /\ procState' = [procState EXCEPT ![i] = "critical"]
    /\ UNCHANGED <<flags, tour1, tour2>>

Abort(i) ==
    /\ i ∈ 1..N
    /\ procState[i] = "readTour2"
    /\ (tour2 /= i \/ \E j ∈ 1..N : (j ≠ i /\ flags[j]))
    /\ flags' = [flags EXCEPT ![i] = FALSE]
    /\ procState' = [procState EXCEPT ![i] = "idle"]
    /\ UNCHANGED <<tour1, tour2>>

ExitCS(i) ==
    /\ i ∈ 1..N
    /\ procState[i] = "critical"
    /\ flags' = [flags EXCEPT ![i] = FALSE]
    /\ tour1' = 0
    /\ tour2' = 0
    /\ procState' = [procState EXCEPT ![i] = "idle"]

(* ------------------------------------------------------------------ *)
(* Next-state relation: any process may perform one of its actions. *)
Next == \E i ∈ 1..N :
          SetIntent(i) \/ WriteTour1(i) \/ ReadTour2(i)
        \/ CheckEntry(i) \/ Abort(i) \/ ExitCS(i)

Spec == Init /\ [][Next]_<<flags, tour1, tour2, procState>>

(* ------------------------------------------------------------------ *)
(* Safety property: mutual exclusion. *)
Invariant ==
    \A i, j ∈ 1..N :
        (i # j) => ~(procState[i] = "critical" /\ procState[j] = "critical")

(* ------------------------------------------------------------------ *)
(* Liveness property: infinitely often some process enters the CS. *)
Liveness == □◇(∃ i ∈ 1..N : procState[i] = "critical")
=============================================================================