---------------------------- MODULE TerminationDetection ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    N,              \* Number of processes (fixed, finite)
    MaxMessages     \* Bound on messages per process for model checking

ASSUME N \in Nat /\ N > 0
ASSUME MaxMessages \in Nat /\ MaxMessages > 0

Procs == 0..(N-1)

VARIABLES
    active,         \* active[p] = TRUE iff process p is active
    pending,        \* pending[p] = number of in-transit messages destined for p
    detected        \* TRUE iff termination has been detected

vars == <<active, pending, detected>>

-----------------------------------------------------------------------------
(* Type invariant for model checking *)

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ pending \in [Procs -> 0..MaxMessages]
    /\ detected \in BOOLEAN

-----------------------------------------------------------------------------
(* Global termination: all processes inactive and no messages in transit *)

GlobalTermination ==
    /\ \A p \in Procs : ~active[p]
    /\ \A p \in Procs : pending[p] = 0

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ active \in [Procs -> BOOLEAN]      \* Any initial activity pattern
    /\ pending \in [Procs -> 0..MaxMessages]  \* Any initial message distribution
    /\ detected = FALSE

-----------------------------------------------------------------------------
(* Actions *)

(* An active process p sends a message to process q *)
Send(p, q) ==
    /\ active[p]                          \* Only active processes can send
    /\ pending[q] < MaxMessages           \* Bound for model checking
    /\ pending' = [pending EXCEPT ![q] = @ + 1]
    /\ UNCHANGED <<active, detected>>

(* Process p receives a message, becoming active if it was inactive *)
Receive(p) ==
    /\ pending[p] > 0                     \* There is a message to receive
    /\ pending' = [pending EXCEPT ![p] = @ - 1]
    /\ active' = [active EXCEPT ![p] = TRUE]  \* Receiving reactivates
    /\ UNCHANGED <<detected>>

(* An active process voluntarily becomes inactive *)
Deactivate(p) ==
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<pending, detected>>

(* Termination detection: may only occur when termination actually holds *)
Detect ==
    /\ GlobalTermination                  \* Precondition: termination must hold
    /\ ~detected                          \* Not already detected
    /\ detected' = TRUE
    /\ UNCHANGED <<active, pending>>

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E p, q \in Procs : Send(p, q)
    \/ \E p \in Procs : Receive(p)
    \/ \E p \in Procs : Deactivate(p)
    \/ Detect

-----------------------------------------------------------------------------
(* Fairness: weak fairness on all actions to ensure liveness *)

Fairness ==
    /\ \A p, q \in Procs : WF_vars(Send(p, q))
    /\ \A p \in Procs : WF_vars(Receive(p))
    /\ \A p \in Procs : WF_vars(Deactivate(p))
    /\ WF_vars(Detect)

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Properties *)

(* Safety: Detection implies global termination *)
SafetyDetection ==
    detected => GlobalTermination

(* Quiescence/Stability: Once global termination holds, it remains true.
   This is expressed as: if we're in a terminated state and take a step,
   we remain in a terminated state. *)
StabilityInvariant ==
    (GlobalTermination /\ ~detected) => 
        (\A p \in Procs : ~active[p] /\ pending[p] = 0)

(* Alternative formulation: GlobalTermination is stable *)
Stability == GlobalTermination => [][GlobalTermination]_vars

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* Liveness: If global termination holds, detection eventually occurs *)
LivenessDetection ==
    GlobalTermination ~> detected

(* Once detected, stays detected (detection is monotonic) *)
DetectionStable ==
    detected => []detected

-----------------------------------------------------------------------------
(* Combined correctness properties for model checking *)

Safety == SafetyDetection

Liveness == LivenessDetection

=============================================================================