---- MODULE TerminationRing ----
EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N > 0

(*
  Processes are arranged in a logical ring: Proc = 1..N with wraparound successor.
  We model synchronous delivery by having activation take effect in the same step.
*)
Proc == 1..N
NextProc(p) == IF p = N THEN 1 ELSE p + 1

VARIABLES active, detected
vars == << active, detected >>

TypeOK == active \subseteq Proc /\ detected \in BOOLEAN
Quiescent == active = {}

Init ==
  /\ active \subseteq Proc
  /\ detected = FALSE

(*
  A local computation that deactivates an active process.
*)
LocalStop ==
  \E i \in active:
    /\ active' = active \ {i}
    /\ UNCHANGED detected

(*
  A local computation by some active process i that activates another process j.
  This can reawaken an inactive process. It is disabled in quiescent states.
*)
Activate ==
  \E i \in active:
    \E j \in Proc \ {i}:
      /\ j \notin active
      /\ active' = active \cup {j}
      /\ UNCHANGED detected

(*
  Global termination detection event. It can occur only in truly quiescent states.
  Detection is latched (once TRUE, it remains TRUE).
*)
Detect ==
  /\ Quiescent
  /\ ~detected
  /\ detected' = TRUE
  /\ UNCHANGED active

Next == LocalStop \/ Activate \/ Detect

Spec == Init /\ [][Next]_vars /\ WF_vars(Detect)

(*
  Required properties (for reference; they follow from Spec):
  - Safety (soundness of detection): once detection is declared, the system is quiescent.
  - Quiescence persistence: once all processes are inactive, they remain inactive thereafter.
  - Liveness: whenever the system is quiescent, detection will eventually be raised.
*)
TerminationSoundness == [](detected => Quiescent)
QuiescencePersistence == [](Quiescent => Quiescent')
TerminationLiveness == [](Quiescent => <> detected)

====