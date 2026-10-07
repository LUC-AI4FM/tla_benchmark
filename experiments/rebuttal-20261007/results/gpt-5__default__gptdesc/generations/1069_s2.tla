----------------------------- MODULE TerminationDetectionRing -----------------------------

EXTENDS Naturals

CONSTANTS N, MSG_BOUND

ASSUME N \in Nat /\ N >= 1 /\ MSG_BOUND \in Nat

VARIABLES active, msgs, detected

NodeSet == 1..N

Succ(i) == IF i = N THEN 1 ELSE i + 1

TypeOK ==
  /\ active \in [NodeSet -> BOOLEAN]
  /\ msgs \in [NodeSet -> Nat]
  /\ detected \in BOOLEAN

Terminated ==
  /\ \A i \in NodeSet: ~active[i]
  /\ \A i \in NodeSet: msgs[i] = 0

RECURSIVE SumPendingSet(_)
SumPendingSet(S) ==
  IF S = {} THEN 0
  ELSE
    LET i == CHOOSE x \in S: TRUE IN
      msgs[i] + SumPendingSet(S \ {i})

TotalPending == SumPendingSet(NodeSet)

StateConstraint == TotalPending <= MSG_BOUND

Init ==
  /\ TypeOK
  /\ detected = FALSE
  /\ StateConstraint

Send(i) ==
  /\ i \in NodeSet
  /\ ~detected
  /\ ~Terminated
  /\ active[i]
  /\ TotalPending < MSG_BOUND
  /\ msgs' = [msgs EXCEPT ![Succ(i)] = @ + 1]
  /\ UNCHANGED <<active, detected>>

Receive(i) ==
  /\ i \in NodeSet
  /\ ~detected
  /\ ~Terminated
  /\ msgs[i] > 0
  /\ msgs' = [msgs EXCEPT ![i] = @ - 1]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ UNCHANGED detected

TerminateNode(i) ==
  /\ i \in NodeSet
  /\ ~detected
  /\ ~Terminated
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<msgs, detected>>

DetectTermination ==
  /\ ~detected
  /\ Terminated
  /\ detected' = TRUE
  /\ UNCHANGED <<active, msgs>>

Stutter ==
  UNCHANGED <<active, msgs, detected>>

Next0 ==
  \/ \E i \in NodeSet: Send(i)
  \/ \E i \in NodeSet: Receive(i)
  \/ \E i \in NodeSet: TerminateNode(i)
  \/ DetectTermination
  \/ Stutter

Next == Next0 /\ StateConstraint'

vars == <<active, msgs, detected>>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(DetectTermination)

(*
  Safety invariants and liveness properties to be checked:
*)

DetectionSoundness == [](detected => Terminated)

TerminationStability == [](Terminated => Terminated')

EventualDetection == (Terminated ~> detected)

AuxTypeInvariant == [](TypeOK)

AuxBoundInvariant == [](StateConstraint)

==========================================================================================