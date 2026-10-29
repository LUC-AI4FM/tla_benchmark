-------------------------------- MODULE Echo --------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, initiator, R, NoNode

-----------------------------------------------------------------------------
(* Concrete instances used by the model-checking configuration.             *)
N1 == {"n1", "n2", "n3", "n4"}
I1 == "n1"
E1 == { <<"n1","n2">>, <<"n2","n1">>,
        <<"n2","n3">>, <<"n3","n2">>,
        <<"n1","n3">>, <<"n3","n1">>,
        <<"n3","n4">>, <<"n4","n3">> }
R1 == [e \in N1 \X N1 |-> e \in E1]

-----------------------------------------------------------------------------
(* Graph utilities                                                          *)
Compose(S) == { p \in Node \X Node :
                  \E b \in Node : <<p[1], b>> \in S /\ <<b, p[2]>> \in S }

RECURSIVE Iterate(_, _)
Iterate(S, k) == IF k = 0 THEN S ELSE Iterate(S \cup Compose(S), k - 1)

TransitiveClosure(S) == Iterate(S, Cardinality(Node))

EdgeSet == { p \in Node \X Node : R[p[1], p[2]] }

neighbors(n) == { m \in Node : R[n, m] }

(* Network assumptions: symmetric, irreflexive, connected.                  *)
ASSUME /\ IsFiniteSet(Node)
       /\ initiator \in Node
       /\ NoNode \notin Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ \A n \in Node : ~ R[n, n]
       /\ \A m, n \in Node : R[m, n] = R[n, m]
       /\ \A m, n \in Node :
             m # n => <<m, n>> \in TransitiveClosure(EdgeSet)

-----------------------------------------------------------------------------
Msg == [from : Node, id : Node]

VARIABLES
  leader,     \* leader[n]: identity n believes is the initiator (or NoNode)
  parent,     \* parent[n]: node from which n first learned the identity
  inbox,      \* inbox[n]: set of messages in transit to n (asynchronous, lossless)
  nbrs,       \* nbrs[n]: neighbors to which n still has to forward the identity
  forwarded,  \* forwarded[n]: n has forwarded the identity to all its neighbors
  rcvd,       \* rcvd[n]: number of messages received by n
  echoed      \* echoed[n]: n has sent its echo back to its parent

vars == <<leader, parent, inbox, nbrs, forwarded, rcvd, echoed>>

TypeOK ==
  /\ leader \in [Node -> Node \cup {NoNode}]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ inbox \in [Node -> SUBSET Msg]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ forwarded \in [Node -> BOOLEAN]
  /\ rcvd \in [Node -> 0 .. Cardinality(Node)]
  /\ echoed \in [Node -> BOOLEAN]

Init ==
  /\ leader = [n \in Node |-> NoNode]
  /\ parent = [n \in Node |-> NoNode]
  /\ inbox = [n \in Node |-> {}]
  /\ nbrs = [n \in Node |-> {}]
  /\ forwarded = [n \in Node |-> FALSE]
  /\ rcvd = [n \in Node |-> 0]
  /\ echoed = [n \in Node |-> FALSE]

(* The initiator wakes up spontaneously and starts flooding its identity.   *)
Start ==
  /\ leader[initiator] = NoNode
  /\ leader' = [leader EXCEPT ![initiator] = initiator]
  /\ nbrs' = [nbrs EXCEPT ![initiator] = neighbors(initiator)]
  /\ forwarded' = [forwarded EXCEPT ![initiator] = (neighbors(initiator) = {})]
  /\ UNCHANGED <<parent, inbox, rcvd, echoed>>

(* Node n forwards the identity it believes in to some neighbor m.          *)
Forward(n, m) ==
  /\ leader[n] # NoNode
  /\ m \in nbrs[n]
  /\ inbox' = [inbox EXCEPT ![m] = @ \cup {[from |-> n, id |-> leader[n]]}]
  /\ nbrs' = [nbrs EXCEPT ![n] = @ \ {m}]
  /\ forwarded' = [forwarded EXCEPT ![n] = (nbrs[n] \ {m} = {})]
  /\ UNCHANGED <<leader, parent, rcvd, echoed>>

(* Node n receives a message (arbitrary order, arbitrary delay).            *)
Receive(n, msg) ==
  /\ msg \in inbox[n]
  /\ inbox' = [inbox EXCEPT ![n] = @ \ {msg}]
  /\ rcvd' = [rcvd EXCEPT ![n] = @ + 1]
  /\ IF leader[n] = NoNode
       THEN LET rest == neighbors(n) \ {msg.from}
            IN  /\ leader' = [leader EXCEPT ![n] = msg.id]
                /\ parent' = [parent EXCEPT ![n] = msg.from]
                /\ nbrs' = [nbrs EXCEPT ![n] = rest]
                /\ forwarded' = [forwarded EXCEPT ![n] = (rest = {})]
       ELSE UNCHANGED <<leader, parent, nbrs, forwarded>>
  /\ UNCHANGED echoed

(* A non-initiator that has forwarded to all neighbors and heard from all  *)
(* of them echoes back to its parent.                                       *)
Echo(n) ==
  /\ n # initiator
  /\ leader[n] # NoNode
  /\ forwarded[n]
  /\ ~ echoed[n]
  /\ rcvd[n] = Cardinality(neighbors(n))
  /\ inbox' = [inbox EXCEPT ![parent[n]] =
                  @ \cup {[from |-> n, id |-> leader[n]]}]
  /\ echoed' = [echoed EXCEPT ![n] = TRUE]
  /\ UNCHANGED <<leader, parent, nbrs, forwarded, rcvd>>

Terminated ==
  /\ \A n \in Node : leader[n] = initiator /\ inbox[n] = {}
  /\ rcvd[initiator] = Cardinality(neighbors(initiator))

Done == Terminated /\ UNCHANGED vars

Next ==
  \/ Start
  \/ \E n \in Node, m \in Node : Forward(n, m)
  \/ \E n \in Node : \E msg \in inbox[n] : Receive(n, msg)
  \/ \E n \in Node : Echo(n)
  \/ Done

Fairness ==
  /\ WF_vars(Start)
  /\ \A n, m \in Node : WF_vars(Forward(n, m))
  /\ \A n \in Node : WF_vars(\E msg \in inbox[n] : Receive(n, msg))
  /\ \A n \in Node : WF_vars(Echo(n))

Spec == Init /\ [][Next]_vars /\ Fairness

TestSpec == Spec

-----------------------------------------------------------------------------
(* Properties                                                               *)

ParentRel == { p \in Node \X Node : parent[p[1]] = p[2] }
AncRel == TransitiveClosure(ParentRel)

(* The parent pointers form a tree rooted at the initiator over activated   *)
(* nodes: every activated non-initiator has the initiator as an ancestor,   *)
(* no node is its own ancestor, parents are neighbors, and only the         *)
(* initiator's identity is ever believed.                                   *)
AncestorProperties ==
  /\ \A n \in Node : leader[n] \in {NoNode, initiator}
  /\ parent[initiator] = NoNode
  /\ \A n \in Node :
       /\ (leader[n] # NoNode /\ n # initiator) =>
              /\ parent[n] \in Node
              /\ R[n, parent[n]]
              /\ leader[parent[n]] = leader[n]
              /\ <<n, initiator>> \in AncRel
       /\ <<n, n>> \notin AncRel
  /\ \A n \in Node : \A msg \in inbox[n] : msg.id = initiator

(* Safety: only the initiator's identity is ever adopted.                   *)
OnlyInitiator == \A n \in Node : leader[n] \in {NoNode, initiator}

(* Safety: once adopted, the identity never changes.                        *)
LeaderStable ==
  [][\A n \in Node : leader[n] # NoNode => leader'[n] = leader[n]]_vars

(* No duplication / monotonicity of forwarding.                             *)
ForwardMonotone ==
  [][\A n \in Node :
       /\ forwarded[n] => forwarded'[n]
       /\ forwarded[n] => leader'[n] = leader[n]
       /\ echoed[n] => echoed'[n]]_vars

NoDuplicateForward ==
  \A n \in Node : \A msg \in inbox[n] : msg.id = leader[msg.from]

(* Liveness: flooding terminates with all nodes knowing the initiator.      *)
EventuallyAllKnow == <>(\A n \in Node : leader[n] = initiator)
Termination == <>[]Terminated

=============================================================================