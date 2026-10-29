------------------------------- MODULE MCEcho -------------------------------
EXTENDS Naturals, FiniteSets, TLC

-------------------------------- MODULE Echo --------------------------------
(***************************************************************************)
(* The echo algorithm: the initiator floods a message to its neighbors.   *)
(* Each node adopts the sender of the first message it receives as its    *)
(* parent and forwards the message to all its other neighbors. Once a     *)
(* node has heard from all its neighbors, it echoes back to its parent.   *)
(* The algorithm terminates when the initiator has heard from all its     *)
(* neighbors. At that point, the parent pointers form a spanning tree.    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Node, initiator, R

VARIABLES inbox, rcvd, parent

vars == <<inbox, rcvd, parent>>

nbrs(n) == {m \in Node : R[m, n]}

NoNode == CHOOSE x : x \notin Node

TypeOK ==
  /\ inbox \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> SUBSET Node]
  /\ parent \in [Node -> Node \cup {NoNode}]

Init ==
  /\ inbox = [n \in Node |-> IF initiator \in nbrs(n) THEN {initiator} ELSE {}]
  /\ rcvd = [n \in Node |-> {}]
  /\ parent = [n \in Node |-> IF n = initiator THEN initiator ELSE NoNode]

Receive(n, m) ==
  /\ m \in inbox[n]
  /\ LET newR   == rcvd[n] \cup {m}
         first  == parent[n] = NoNode
         par    == IF first THEN m ELSE parent[n]
         toSend == (IF first THEN nbrs(n) \ {m} ELSE {})
                   \cup (IF newR = nbrs(n) /\ n # initiator THEN {par} ELSE {})
     IN /\ rcvd' = [rcvd EXCEPT ![n] = newR]
        /\ parent' = [parent EXCEPT ![n] = par]
        /\ inbox' = [k \in Node |->
                       IF k = n THEN inbox[n] \ {m}
                       ELSE IF k \in toSend THEN inbox[k] \cup {n}
                       ELSE inbox[k]]

Done == rcvd[initiator] = nbrs(initiator)

Terminated == Done /\ UNCHANGED vars

Next == (\E n \in Node, m \in Node : Receive(n, m)) \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(\E n \in Node, m \in Node : Receive(n, m))

(* Safety: parents are always neighbors *)
ParentsAreNeighbors ==
  \A n \in Node \ {initiator} : parent[n] # NoNode => R[n, parent[n]]

(* Safety: upon termination every node has a parent and no messages remain *)
Correctness ==
  Done => /\ \A n \in Node : parent[n] # NoNode
          /\ \A n \in Node : inbox[n] = {}
          /\ \A n \in Node \ {initiator} : R[n, parent[n]]

(* Liveness: the algorithm eventually terminates *)
Termination == <>Done
=============================================================================