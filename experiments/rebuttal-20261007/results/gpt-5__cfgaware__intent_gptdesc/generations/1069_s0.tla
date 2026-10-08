------------------------------ MODULE TerminationDetection ------------------------------

EXTENDS Naturals

CONSTANTS Proc, MaxMsgs

(*
  Assumptions for model instantiation:
  - Proc is a nonempty finite set of process identifiers.
  - MaxMsgs is a natural bound on the number of in-flight messages per sender/receiver pair.
*)
ASSUME /\ Proc # {}
       /\ MaxMsgs \in Nat

VARIABLES
  active,    \* [Proc -> BOOLEAN], whether a process is active
  inFlight,  \* [Proc -> [Proc -> 0..MaxMsgs]], counts of in-transit messages from i to j
  Detected   \* BOOLEAN, global termination-detected flag

vars == << active, inFlight, Detected >>

(*
  Typing and boundedness constraints (state invariant).
*)
TypeOK ==
  /\ active \in [Proc -> BOOLEAN]
  /\ inFlight \in [Proc -> [Proc -> 0..MaxMsgs]]
  /\ Detected \in BOOLEAN

(*
  Initial states: arbitrary well-typed active set and message multiset; detection not yet claimed.
*)
Init ==
  /\ TypeOK
  /\ Detected = FALSE

(*
  Global termination: no active processes and no in-transit messages.
*)
Terminated ==
  /\ \A p \in Proc: ~active[p]
  /\ \A i \in Proc: \A j \in Proc: inFlight[i][j] = 0

(*
  Abstract actions:
    - Send: an active process sends a message to any process, increasing the in-flight count.
    - Receive: a message is delivered to its destination, reactivating it.
    - Deactivate: an active process becomes inactive (e.g., local work complete).
    - DetectAction: the detector may set Detected to TRUE, but only when Terminated holds.
  After global termination holds, only DetectAction (and stuttering) may occur.
*)

Send(p, q) ==
  /\ ~Terminated
  /\ p \in Proc /\ q \in Proc
  /\ active[p] = TRUE
  /\ inFlight[p][q] < MaxMsgs
  /\ active'   = [active EXCEPT ![p] = TRUE]
  /\ inFlight' = [inFlight EXCEPT ![p][q] = @ + 1]
  /\ Detected' = Detected

Receive(p, q) ==
  /\ ~Terminated
  /\ p \in Proc /\ q \in Proc
  /\ inFlight[p][q] > 0
  /\ inFlight' = [inFlight EXCEPT ![p][q] = @ - 1]
  /\ active'   = [active EXCEPT ![q] = TRUE]
  /\ Detected' = Detected

Deactivate(p) ==
  /\ ~Terminated
  /\ p \in Proc
  /\ active[p] = TRUE
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ UNCHANGED << inFlight, Detected >>

DetectAction ==
  /\ Terminated
  /\ ~Detected
  /\ Detected' = TRUE
  /\ UNCHANGED << active, inFlight >>

Next ==
  \/ \E p \in Proc: \E q \in Proc: Send(p, q)
  \/ \E p \in Proc: \E q \in Proc: Receive(p, q)
  \/ \E p \in Proc: Deactivate(p)
  \/ DetectAction

(*
  System specification with weak fairness on DetectAction to ensure eventual detection
  once global termination is reached (and remains, by construction).
*)
Spec == Init /\ [][Next]_vars /\ WF_vars(DetectAction)

(*
  Properties for model checking:
  - Safety: the detector never claims termination unless global termination actually holds.
  - Quiescence/Stability: once termination holds, it holds forever.
  - Liveness: if the system ever reaches global termination, detection eventually occurs.
*)
Safety == [](Detected => Terminated)

Quiescence == [](Terminated => []Terminated)

Liveness == (<>Terminated) => (<>Detected)

=============================================================================