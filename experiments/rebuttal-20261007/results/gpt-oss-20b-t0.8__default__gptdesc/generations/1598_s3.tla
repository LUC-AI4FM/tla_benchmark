------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES x, y, b, S, inCS

(* ------------------------------------------------------------------------ *)
(*  The set of process identifiers                                         *)
ProcSet == 1 .. N

(* ------------------------------------------------------------------------ *)
(*  State variables                                                          *)
Vars == <<x, y, b, S, inCS>>

(* ------------------------------------------------------------------------ *)
(*  Initial state                                                            *)
Init ==
  /\ x = 0
  /\ y = 0
  /\ b \in [1..N -> BOOLEAN]
  /\ S \in [1..N -> SUBSET 1..N]
  /\ inCS \in [1..N -> BOOLEAN]
  /\ \A i \in ProcSet : b[i] = FALSE
  /\ \A i \in ProcSet : S[i] = {}
  /\ \A i \in ProcSet : inCS[i] = FALSE

(* ------------------------------------------------------------------------ *)
(*  Request entry: set flag, update Y and waiting set                       *)
Request(i) ==
  /\ i \in ProcSet
  /\ b[i] = FALSE
  /\ b'   = [b EXCEPT ![i] = TRUE]
  /\ y'   = i
  /\ S'   = [S EXCEPT ![i] =
              { j \in ProcSet : b[j] /\ j # i }]
  /\ x'   = x
  /\ inCS'= inCS

(* ------------------------------------------------------------------------ *)
(*  Enter critical section: if X is free, acquire it                       *)
EnterCS(i) ==
  /\ i \in ProcSet
  /\ b[i] = TRUE
  /\ x = 0
  /\ inCS[i] = FALSE
  /\ x'   = i
  /\ inCS'= [inCS EXCEPT ![i] = TRUE]
  /\ y'   = y
  /\ b'   = b
  /\ S'   = S

(* ------------------------------------------------------------------------ *)
(*  Exit critical section: release X, clear flag and waiting set           *)
ExitCS(i) ==
  /\ i \in ProcSet
  /\ inCS[i] = TRUE
  /\ inCS'= [inCS EXCEPT ![i] = FALSE]
  /\ x'   = 0
  /\ b'   = [b EXCEPT ![i] = FALSE]
  /\ S'   = [S EXCEPT ![i] = {}]
  /\ y'   = y

(* ------------------------------------------------------------------------ *)
(*  Next-state relation: any process may request, enter or exit CS         *)
Next ==
  \E i \in ProcSet :
    (Request(i) \/ EnterCS(i) \/ ExitCS(i))

(* ------------------------------------------------------------------------ *)
(*  Safety invariant: no two distinct processes in critical section       *)
NoTwoInCS ==
  \A i j \in ProcSet : i # j => ~(inCS[i] /\ inCS[j])

(* ------------------------------------------------------------------------ *)
(*  Liveness property: infinitely often some process is in CS             *)
Liveliness ==
  []( <> (\E i \in ProcSet : inCS[i]))

(* ------------------------------------------------------------------------ *)
Spec == Init
      /\ [][Next]_Vars
      /\ WF/PR_Next

=============================================================================