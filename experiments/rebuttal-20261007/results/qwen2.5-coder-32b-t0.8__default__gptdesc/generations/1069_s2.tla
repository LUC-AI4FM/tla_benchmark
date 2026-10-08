------------------------------- MODULE AsyncTermDetect --------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N \* Number of nodes

VARIABLES active, pending, detected \* active: set of active nodes, pending: function from nodes to natural numbers, detected: boolean

Init == 
  /\ active = {1..N}
  /\ pending \in [1..N -> {0}]
  /\ detected = FALSE

Next ==
  \/ \E n \in active : (* Node n sends a message *)
     \/ /\ pending[n] > 0
        /\ pending' = [pending EXCEPT ![n] = pending[n] - 1]
        /\ active' = active
        /\ detected' = detected
  \/ \E n \notin active : (* Node n receives a message *)
     \/ /\ pending[n] < N
        /\ pending' = [pending EXCEPT ![n] = pending[n] + 1]
        /\ active' = active
        /\ detected' = detected
  \/ \E n \in active : (* Node n terminates *)
     \/ /\ pending[n] = 0
        /\ pending' = pending
        /\ active' = active \ {n}
        /\ detected' = detected
  \/ \A n \notin active : (* Detection occurs if all nodes are inactive and have no pending messages *)
     \/ /\ active = {}
        /\ pending = [1..N -> {0}]
        /\ detected
        /\ detected' = TRUE

Spec == 
  /\ Init
  /\ [][Next]_<<active, pending, detected>>
  /\ WF_[Next]_<<DetectTermination>>

DetectTermination ==
  \/ detected = FALSE
     /\ active = {}
     /\ pending = [1..N -> {0}]
     /\ detected' = TRUE

\* Safety properties
DetectedImpliesActualTermination == 
  G(detected => (active = {} /\ pending = [1..N -> {0}]))

StableDetection ==
  [](detected => []<>(detected))

\* Liveness property
EventualDetection ==
  <>(/\ active = {}
      /\ pending = [1..N -> {0}]
      /\ detected)

StateConstraint ==
  /\ pending \in [1..N -> Nat]
  /\ detected \in BOOLEAN

Properties == 
  /\ DetectedImpliesActualTermination
  /\ StableDetection
  /\ EventualDetection

=============================================================================