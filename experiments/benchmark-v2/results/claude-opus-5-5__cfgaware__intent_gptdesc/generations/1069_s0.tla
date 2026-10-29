------------------------- MODULE TerminationDetection -------------------------
(***************************************************************************)
(* Abstract model of asynchronous termination detection.                   *)
(*                                                                         *)
(* N processes, each either active or inactive.  Messages in transit are   *)
(* counted per destination process.  Delivery is asynchronous, reliable,   *)
(* and unordered.  An abstract detector may set terminationDetected only   *)
(* when global termination actually holds, and may delay doing so.         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssump == N \in Nat /\ N >= 1

Procs == 1 .. N

\* Finite bound on in-transit messages per process, for model checking.
MaxMsgs == 2

VARIABLES active,               \* active[i] : process i is executing
          pending,              \* pending[i] : messages in transit to i
          terminationDetected   \* detector has announced termination

vars == << active, pending, terminationDetected >>

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ pending \in [Procs -> Nat]
    /\ terminationDetected \in BOOLEAN

\* Global termination: all processes idle and no messages in transit.
Terminated ==
    /\ \A i \in Procs : ~active[i]
    /\ \A i \in Procs : pending[i] = 0

-----------------------------------------------------------------------------

Init ==
    /\ active \in [Procs -> BOOLEAN]
    /\ pending = [i \in Procs |-> 0]
    /\ terminationDetected = FALSE

\* An active process sends a message to some process j.
SendMsg(i, j) ==
    /\ active[i]
    /\ pending[j] < MaxMsgs
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED << active, terminationDetected >>

\* Process i consumes a message, which (re)activates it.
RcvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED terminationDetected

\* An active process finishes its local work and becomes idle.
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << pending, terminationDetected >>

\* The abstract detector announces termination; only allowed when it holds.
DetectTermination ==
    /\ Terminated
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED << active, pending >>

\* Final stuttering once termination has been detected (avoids deadlock).
Done ==
    /\ terminationDetected
    /\ UNCHANGED vars

Next ==
    \/ \E i, j \in Procs : SendMsg(i, j)
    \/ \E i \in Procs : RcvMsg(i)
    \/ \E i \in Procs : Deactivate(i)
    \/ DetectTermination
    \/ Done

Fairness == WF_vars(DetectTermination)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

\* Safety: detection is never claimed unless global termination holds.
Safe == terminationDetected => Terminated

\* Stability: once terminated, the system remains terminated.
Quiescence == [][Terminated => Terminated']_vars

\* Liveness: global termination is eventually detected.
Live == Terminated ~> terminationDetected

\* Bounds for model checking.
StateConstraint == \A i \in Procs : pending[i] <= MaxMsgs

=============================================================================