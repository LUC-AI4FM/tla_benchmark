----------------------------- MODULE TerminationRing -----------------------------
EXTENDS Naturals, TLC

CONSTANTS
    N,            \* Number of nodes in the ring (N \in Nat, N > 0)
    MaxPending,   \* Upper bound on per-node pending message count (Nat)
    MaxSteps      \* Upper bound on number of non-stuttering steps (Nat)

(*
  High-level overview:
  - Nodes are arranged in a ring: Nodes == 0 .. (N-1).
  - active[i] indicates whether node i is active.
  - pending[i] is the count of messages pending for node i.
  - detected indicates whether global termination has been detected.
  - step counts the number of non-stuttering steps; used for bounded model checking.
*)

VARIABLES
    active,       \* [Nodes -> BOOLEAN]
    pending,      \* [Nodes -> 0..MaxPending]
    detected,     \* BOOLEAN
    step          \* 0..MaxSteps

vars == << active, pending, detected, step >>

ASSUME N \in Nat /\ N > 0 /\ MaxPending \in Nat /\ MaxSteps \in Nat

Nodes == 0 .. (N - 1)

NextNode(i) == IF i = N - 1 THEN 0 ELSE i + 1

AllInactive == \A i \in Nodes: ~active[i]
NoPending  == \A i \in Nodes: pending[i] = 0
Terminated == AllInactive /\ NoPending
Detected   == detected

TypeOK ==
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending \in [Nodes -> 0..MaxPending]
    /\ detected \in BOOLEAN
    /\ step \in 0..MaxSteps

StateConstraint == step < MaxSteps

Init ==
    /\ TypeOK
    /\ active \in [Nodes -> BOOLEAN]
    /\ pending = [i \in Nodes |-> 0]
    /\ detected = FALSE
    /\ step = 0

TerminateNode(i) ==
    /\ i \in Nodes
    /\ active[i]
    /\ StateConstraint
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ pending' = pending
    /\ detected' = detected
    /\ step' = step + 1

Send(i) ==
    /\ i \in Nodes
    /\ active[i]
    /\ LET j == NextNode(i) IN pending[j] < MaxPending
    /\ StateConstraint
    /\ active' = active
    /\ LET j == NextNode(i) IN pending' = [pending EXCEPT ![j] = @ + 1]
    /\ detected' = detected
    /\ step' = step + 1

Receive(i) ==
    /\ i \in Nodes
    /\ pending[i] > 0
    /\ StateConstraint
    /\ active'  = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ detected' = detected
    /\ step' = step + 1

DetectTermination ==
    /\ ~detected
    /\ Terminated
    /\ StateConstraint
    /\ active'  = active
    /\ pending' = pending
    /\ detected' = TRUE
    /\ step' = step + 1

Next ==
    \E i \in Nodes:
        TerminateNode(i)
      \/ Send(i)
      \/ Receive(i)
  \/ DetectTermination

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

(*
  Safety properties (state and temporal):
  - Detected implies actual termination.
  - Termination is stable once reached.
*)
InvDetectedSound ==
    detected => Terminated

SafetyDetectedImpliesActual ==
    [] (detected => Terminated)

SafetyTerminationStable ==
    [] (Terminated => Terminated')

(*
  Liveness property under WF on DetectTermination:
  - If actual termination holds at some point, then detection eventually occurs.
*)
LivenessEventualDetection ==
    [] (Terminated => <> detected)

=============================================================================