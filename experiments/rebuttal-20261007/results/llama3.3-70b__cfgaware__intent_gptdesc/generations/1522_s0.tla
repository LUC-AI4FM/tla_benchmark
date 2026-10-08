---------------------------- MODULE WeightedTerminationDetection ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT Processes, Leader
VARIABLES State, Messages, Weights

Weights == [p \in Processes |-> 0]
State == [p \in Processes |-> IF p = Leader THEN "active" ELSE "idle" ]
Messages == {}

TypeInvariant == 
  /\ Processes \subseteq STRING
  /\ Leader \in Processes
  /\ State \in [Processes -> {"active", "idle"}]
  /\ Messages \in SUBSET (Processes \X Processes \X (1..10))
  /\ Weights \in [Processes -> (0..10)]

Init == 
  /\ TypeInvariant
  /\ State = [p \in Processes |-> IF p = Leader THEN "active" ELSE "idle" ]
  /\ Messages = {}
  /\ Weights = [Leader |-> 1] @ [p \in (Processes \ {Leader}) |-> 0]

BecomeActive(p) == 
  /\ p \in Processes
  /\ State[p] = "idle"
  /\ State' = [State EXCEPT ![p] = "active"]
  /\ Messages' = Messages
  /\ Weights' = Weights

SendWeight(p, q, w) == 
  /\ p \in Processes
  /\ q \in Processes
  /\ p /= q
  /\ State[p] = "active"
  /\ w > 0
  /\ w <= Weights[p]
  /\ Messages' = Messages \cup {(p, q, w)}
  /\ Weights' = [Weights EXCEPT ![p] = @ - w]
  /\ State' = State

ReceiveWeight(p, q, w) == 
  /\ (p, q, w) \in Messages
  /\ p \in Processes
  /\ q \in Processes
  /\ p /= q
  /\ State[p] = "active"
  /\ Weights' = [Weights EXCEPT ![p] = @ + w]
  /\ Messages' = Messages \ { (p, q, w) }
  /\ State' = State

BecomeIdle(p) == 
  /\ p \in Processes
  /\ State[p] = "active"
  /\ IF p = Leader THEN 
      /\ Weights[p] = 1
      /\ Messages' = Messages
    ELSE 
      /\ \E q \in Processes : SendWeight(p, q, Weights[p])
  /\ State' = [State EXCEPT ![p] = "idle"]
  /\ Weights' = IF p = Leader THEN Weights ELSE [Weights EXCEPT ![p] = 0]

Next == 
  \/ \E p \in Processes : BecomeActive(p)
  \/ \E p \in Processes, q \in Processes, w \in (1..10) : SendWeight(p, q, w)
  \/ \E p \in Processes, q \in Processes, w \in (1..10) : ReceiveWeight(p, q, w)
  \/ \E p \in Processes : BecomeIdle(p)

Spec == Init /\ [][Next]_State

THEOREM Spec => []TypeInvariant
=============================================================================