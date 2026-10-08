------------------------------ MODULE TerminationDetection ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

(*
  Nodes are arranged conceptually in a ring 0..N-1.
  The ring topology is abstracted away, as messages may be sent to any destination.
*)
Nodes == 0..(N - 1)

VARIABLES
  active,               \* [i \in Nodes -> BOOLEAN]
  pending,              \* [i \in Nodes -> Nat], number of messages destined to i
  terminationDetected   \* BOOLEAN

vars == << active, pending, terminationDetected >>

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ pending \in [Nodes -> Nat]
  /\ terminationDetected \in BOOLEAN

AllInactive == \A i \in Nodes: ~active[i]
NoMsgs      == \A i \in Nodes: pending[i] = 0
TrulyTerminated == AllInactive /\ NoMsgs

Init ==
  /\ TypeOK
  /\ pending = [i \in Nodes |-> 0]
  /\ terminationDetected \in BOOLEAN
  /\ terminationDetected => TrulyTerminated

Terminate ==
  \E i \in Nodes:
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ pending' = pending
    /\ IF TrulyTerminated'
       THEN terminationDetected' \in {terminationDetected, TRUE}
       ELSE terminationDetected' = terminationDetected

SendMsg ==
  \E i \in Nodes:
    /\ active[i]
    /\ \E j \in Nodes:
         /\ pending' = [pending EXCEPT ![j] = @ + 1]
         /\ active' = active
         /\ terminationDetected' = terminationDetected

RcvMsg ==
  \E j \in Nodes:
    /\ pending[j] > 0
    /\ pending' = [pending EXCEPT ![j] = @ - 1]
    /\ active' = [active EXCEPT ![j] = TRUE]
    /\ terminationDetected' = terminationDetected

DetectTermination ==
  /\ TrulyTerminated
  /\ terminationDetected' = TRUE
  /\ active' = active
  /\ pending' = pending

Next ==
  \/ Terminate
  \/ SendMsg
  \/ RcvMsg
  \/ DetectTermination
  \/ UNCHANGED vars  \* Always-enabled stuttering step

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(DetectTermination)

\* State predicate for safety
Safe == terminationDetected => TrulyTerminated

\* Liveness: once truly terminated, detection eventually occurs
Live == [] (TrulyTerminated => <> terminationDetected)

\* Quiescence: once terminated, it remains terminated
Quiescence == [] (TrulyTerminated => [] TrulyTerminated)

\* Inductive invariant for Apalache: typing + safety
IndInv == TypeOK /\ Safe

\* Action-formula variants of quiescence (useful for symbolic tools)
KeepsTerminated(A) == TrulyTerminated /\ A => TrulyTerminated'
QuiescenceAct == TrulyTerminated /\ Next => TrulyTerminated'
Qt_Terminate == KeepsTerminated(Terminate)
Qt_SendMsg == KeepsTerminated(SendMsg)
Qt_RcvMsg == KeepsTerminated(RcvMsg)
Qt_DetectTermination == KeepsTerminated(DetectTermination)

\* State constraint used in the model: bound pending counts
PendingBound == \A i \in Nodes: pending[i] <= 3

==============================