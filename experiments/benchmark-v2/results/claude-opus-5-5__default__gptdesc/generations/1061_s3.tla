---------------------- MODULE APSyncTerminationDetection ----------------------
(***************************************************************************)
(* Thin wrapper around SyncTerminationDetection that attaches Apalache     *)
(* type annotations to the constants and variables without modifying the   *)
(* original specification. Init, Next, Spec, the invariants and the        *)
(* liveness properties are obtained through the INSTANCE statement.        *)
(*                                                                         *)
(* The underlying module is provided inline as a nested module so that     *)
(* this file is self-contained for the SANY parser.                        *)
(***************************************************************************)
EXTENDS Naturals

  ------------------- MODULE SyncTerminationDetection -------------------
  EXTENDS Naturals

  CONSTANT N

  ASSUME NIsPosNat == N \in Nat \ {0}

  Node == 0 .. N-1

  VARIABLES active, terminationDetected

  vars == <<active, terminationDetected>>

  TypeOK ==
      /\ active \in [Node -> BOOLEAN]
      /\ terminationDetected \in BOOLEAN

  terminated == \A n \in Node : ~ active[n]

  Init ==
      /\ active \in [Node -> BOOLEAN]
      /\ terminationDetected \in {FALSE, terminated}

  Terminate(i) ==
      /\ active[i]
      /\ active' = [active EXCEPT ![i] = FALSE]
      /\ terminationDetected' \in {terminationDetected, terminated'}

  Wakeup(i, j) ==
      /\ active[i]
      /\ ~ active[j]
      /\ active' = [active EXCEPT ![j] = TRUE]
      /\ UNCHANGED terminationDetected

  DetectTermination ==
      /\ terminated
      /\ ~ terminationDetected
      /\ terminationDetected' = TRUE
      /\ UNCHANGED active

  Next ==
      \/ \E i \in Node : Terminate(i)
      \/ \E i, j \in Node : Wakeup(i, j)
      \/ DetectTermination

  Spec == Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

  TDCorrect == terminationDetected => terminated

  Stable == [](terminated => []terminated)

  Liveness == terminated ~> terminationDetected
  =======================================================================