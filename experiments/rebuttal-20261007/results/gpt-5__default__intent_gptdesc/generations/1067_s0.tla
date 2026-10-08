----------------------------- MODULE TerminationDetectionRing -----------------------------

EXTENDS Naturals

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Proc == 0..(N - 1)

Succ(i) == IF i < N - 1 THEN i + 1 ELSE 0

VARIABLES active, detected

vars == <<active, detected>>

AllInactive == \A p \in Proc : ~active[p]

Init ==
  /\ active \in [Proc -> BOOLEAN]
  /\ detected = FALSE

Deactivate(p) ==
  /\ p \in Proc
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ UNCHANGED detected

Activate(p, q) ==
  /\ p \in Proc
  /\ q \in Proc
  /\ p # q
  /\ active[p]
  /\ active' = [active EXCEPT ![q] = TRUE]
  /\ UNCHANGED detected

Detect ==
  /\ ~detected
  /\ AllInactive
  /\ detected' = TRUE
  /\ UNCHANGED active

Next ==
  \/ \E p \in Proc : Deactivate(p)
  \/ \E p \in Proc, q \in Proc : Activate(p, q)
  \/ Detect

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Detect)

(*
 Safety: once termination is declared, the system state is quiescent.
*)
TerminationSafety ==
  [] (detected => AllInactive)

(*
 Quiescence persistence: once all processes are inactive, they remain inactive thereafter.
*)
QuiescencePersistence ==
  [] (AllInactive => AllInactive')

(*
 Liveness: whenever the system is quiescent, termination detection will eventually be raised.
*)
TerminationLiveness ==
  [] (AllInactive => <> detected)

===========================================================================================