------------------------- MODULE AsyncTerminationDetection -------------------------
(***************************************************************************)
(* Abstract model of asynchronous termination detection.                   *)
(*                                                                         *)
(* A fixed, finite set of N processes is connected in a fully connected    *)
(* topology, which subsumes a ring and any other connected topology.       *)
(* Each process is either active or inactive.                              *)
(*                                                                         *)
(* In-transit messages are counted per destination process. Delivery is   *)
(* asynchronous, reliable, and unordered. Messages are never lost or       *)
(* duplicated, and there are no timing assumptions.                        *)
(*                                                                         *)
(* No particular detection algorithm is prescribed. The Detect action is   *)
(* an abstract oracle. It may fire only when global termination actually   *)
(* holds, and it may be delayed arbitrarily long.                          *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    N,          \* number of processes
    MaxMsgs     \* model-checking bound on in-transit messages per process

ASSUME NAssump       == N \in Nat \ {0}
ASSUME MaxMsgsAssump == MaxMsgs \in Nat

Procs == 1 .. N

VARIABLES
    active,                 \* active[p] = TRUE iff process p is active
    pending,                \* pending[p] = number of in-transit messages to p
    terminationDetected     \* global detection predicate

vars == << active, pending, terminationDetected >>

---------------------------------------------------------------------------
(* Global termination: all processes idle and no messages in transit. *)
Terminated ==
    /\ \A p \in Procs : ~active[p]
    /\ \A p \in Procs : pending[p] = 0

---------------------------------------------------------------------------
TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ pending \in [Procs -> 0 .. MaxMsgs]
    /\ terminationDetected \in BOOLEAN

Init ==
    /\ active \in [Procs -> BOOLEAN]
    /\ pending \in [Procs -> 0 .. MaxMsgs]
    /\ terminationDetected = FALSE

---------------------------------------------------------------------------
(* An active process i sends a message to process j.              *)
(* The guard pending[j] < MaxMsgs is a model-checking bound only. *)
SendMsg(i, j) ==
    /\ active[i]
    /\ pending[j] < MaxMsgs
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ UNCHANGED << active, terminationDetected >>

(* Process i consumes one incoming message.            *)
(* Receiving a message (re)activates the process.       *)
RcvMsg(i) ==
    /\ pending[i] > 0
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ active' = [active EXCEPT ![i] = TRUE]
    /\ UNCHANGED terminationDetected

(* An active process voluntarily finishes its local work. *)
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << pending, terminationDetected >>

(* Abstract detector.                                              *)
(* It may claim termination only when global termination holds.    *)
(* The action is optional at every step, so it may be delayed.     *)
DetectTermination ==
    /\ Terminated
    /\ ~terminationDetected
    /\ terminationDetected' = TRUE
    /\ UNCHANGED << active, pending >>

(* Explicit stuttering once everything is finished.          *)
(* This avoids spurious deadlock reports from the model checker. *)
Done ==
    /\ Terminated
    /\ terminationDetected
    /\ UNCHANGED vars

Next ==
    \/ \E i, j \in Procs : SendMsg(i, j)
    \/ \E i \in Procs : RcvMsg(i)
    \/ \E i \in Procs : Deactivate(i)
    \/ DetectTermination
    \/ Done

(* Fair scheduling assumption: detection is weakly fair. *)
Fairness == WF_vars(DetectTermination)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(*************************** Correctness properties ***********************)

(* Safety: the detector never claims termination unless it really holds. *)
TDCorrect == terminationDetected => Terminated

(* The detection predicate is stable once set. *)
DetectionStable == [][terminationDetected => terminationDetected']_vars

(* Quiescence: once global termination holds, it holds forever. *)
TerminationStable == [][Terminated => Terminated']_vars

(* Liveness: global termination is eventually detected. *)
TDLiveness == Terminated ~> terminationDetected

---------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []TDCorrect
THEOREM Spec => TerminationStable
THEOREM Spec => DetectionStable
THEOREM Spec => TDLiveness
=============================================================================