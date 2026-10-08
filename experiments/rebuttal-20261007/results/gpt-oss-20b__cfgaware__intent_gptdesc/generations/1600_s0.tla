------------------------------ MODULE MutualExclusionProtocol ------------------------------

EXTENDS Naturals, Sequences, TemporalOperators

CONSTANTS N, defaultInitValue

VARIABLES owner, flag

(* --------------------------------------------------------------------------- *)
(*  Process set and variable declaration                                       *)
(* --------------------------------------------------------------------------- *)

ProcSet == 1..N
vars    == <<owner, flag>>

(* --------------------------------------------------------------------------- *)
(*  Initial state                                                              *)
(* --------------------------------------------------------------------------- *)

Init ==
  owner = defaultInitValue
  /\ \A i \in ProcSet : flag[i] = FALSE

(* --------------------------------------------------------------------------- *)
(*  Actions for a single process i                                           *)
(* --------------------------------------------------------------------------- *)

ExpressIntent(i) ==
  flag[i] = FALSE
  /\ owner' = owner
  /\ flag'  = [flag EXCEPT ![i] = TRUE]

FastAttemptSuccess(i) ==
  flag[i] = TRUE
  /\ owner   = 0
  /\ \A j \in ProcSet : (j # i => flag[j] = FALSE)
  /\ owner' = i
  /\ flag'  = flag

FastAttemptFailure(i) ==
  flag[i] = TRUE
  /\ (owner # 0 \/ \E j \in ProcSet : (j # i /\ flag[j]))
  /\ owner' = owner
  /\ flag'  = [flag EXCEPT ![i] = FALSE]

WaitAndReattempt(i) ==
  flag[i] = FALSE
  /\ \A j \in ProcSet : flag[j] = FALSE
  /\ owner' = owner
  /\ flag'  = [flag EXCEPT ![i] = TRUE]

ExitCS(i) ==
  owner   = i
  /\ flag[i] = TRUE
  /\ owner' = 0
  /\ flag'  = [flag EXCEPT ![i] = FALSE]

(* --------------------------------------------------------------------------- *)
(*  Next-state relation (one process acts per step)                           *)
(* --------------------------------------------------------------------------- *)

Next ==
  \E i \in ProcSet :
    ( ExpressIntent(i)
      \/ FastAttemptSuccess(i)
      \/ FastAttemptFailure(i)
      \/ WaitAndReattempt(i)
      \/ ExitCS(i) )

(* --------------------------------------------------------------------------- *)
(*  Fairness assumption                                                       *)
(* --------------------------------------------------------------------------- *)

Fairness == WF_vars(Next)

(* --------------------------------------------------------------------------- *)
(*  Specification                                                            *)
(* --------------------------------------------------------------------------- *)

Spec == Init /\ [][Next]_vars /\ Fairness

(* --------------------------------------------------------------------------- *)
(*  Safety property: mutual exclusion                                         *)
(* --------------------------------------------------------------------------- *)

Invariant ==
  (owner = 0)
  \/ (\E i \in ProcSet : owner = i /\ flag[i])

(* --------------------------------------------------------------------------- *)
(*  Liveness property: global progress                                       *)
(* --------------------------------------------------------------------------- *)

Liveness == []<>(\E i \in ProcSet : owner = i)

=============================================================================