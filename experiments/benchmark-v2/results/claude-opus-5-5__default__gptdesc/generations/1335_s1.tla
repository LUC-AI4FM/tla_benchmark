------------------------------- MODULE Echo -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node,      \* set of nodes
          initiator, \* single initiator, root of the spanning tree
          R          \* neighborhood relation, a Boolean function over Node \X Node

\* Graph properties, defined locally
IsIrreflexive(rel, S) == \A x \in S : ~ rel[x, x]
IsSymmetric(rel, S)   == \A x, y \in S : rel[x, y] <=> rel[y, x]

RECURSIVE Reach(_, _)
Reach(S, k) ==
    IF k = 0 THEN S
    ELSE Reach(S \cup {m \in Node : \E s \in S : R[s, m]}, k - 1)

IsConnected(rel, S) == \A m, n \in S : n \in Reach({m}, Cardinality(S))

ASSUME /\ IsFiniteSet(Node)
       /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)   \* no self loops
       /\ IsSymmetric(R, Node)     \* undirected graph
       /\ IsConnected(R, Node)     \* graph is connected

NoNode == CHOOSE x : x \notin Node

neighbors(n) == { m \in Node : R[m, n] }

Message == [kind : {"m1", "m2"}, sndr : Node]

(***************************************************************************
--algorithm Echo {
    variable inbox = [n \in Node |-> {}];
    define {
        send(box, n, msg) == [box EXCEPT ![n] = @ \cup {msg}]
        multicast(box, n, exceptional) ==
            [m \in Node |-> IF R[n, m] /\ m # exceptional
                            THEN box[m] \cup {[kind |-> "m1", sndr |-> n]}
                            ELSE box[m]]
    }
    process (node \in Node)
      variables parent = NoNode, children = {}, rcvd = 0, nbrs = neighbors(self);
    {
    n0: if (self = initiator) { inbox := multicast(inbox, self, NoNode) };
    n1: while (rcvd < Cardinality(nbrs)) {
          with (msg \in inbox[self], net = [inbox EXCEPT ![self] = @ \ {msg}]) {
            rcvd := rcvd + 1;
            if (self # initiator /\ rcvd = 1) {
               assert(msg.kind = "m1");
               parent := msg.sndr;
               inbox := multicast(net, self, msg.sndr)
            } else if (msg.kind = "m2") {
               children := children \cup {msg.sndr};
               inbox := net
            } else { inbox := net }
          }
        };
    n2: if (self # initiator) {
          assert(parent \in nbrs);
          inbox := send(inbox, parent, [kind |-> "m2", sndr |-> self])
        }
    }
}
***************************************************************************)

VARIABLES inbox, pc, parent, children, rcvd, nbrs

send(box, n, msg) == [box EXCEPT ![n] = @ \cup {msg}]

multicast(box, n, exceptional) ==
    [m \in Node |-> IF R[n, m] /\ m # exceptional
                    THEN box[m] \cup {[kind |-> "m1", sndr |-> n]}
                    ELSE box[m]]

vars == << inbox, pc, parent, children, rcvd, nbrs >>

ProcSet == Node

Init == /\ inbox = [n \in Node |-> {}]
        /\ parent = [self \in Node |-> NoNode]
        /\ children = [self \in Node |-> {}]
        /\ rcvd = [self \in Node |-> 0]
        /\ nbrs = [self \in Node |-> neighbors(self)]
        /\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
            /\ IF self = initiator
                  THEN inbox' = multicast(inbox, self, NoNode)
                  ELSE UNCHANGED inbox
            /\ pc' = [pc EXCEPT ![self] = "n1"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

n1(self) == /\ pc[self] = "n1"
            /\ IF rcvd[self] < Cardinality(nbrs[self])
                  THEN /\ \E msg \in inbox[self] :
                            LET net == [inbox EXCEPT ![self] = @ \ {msg}] IN
                            /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
                            /\ IF self # initiator /\ rcvd'[self] = 1
                                  THEN /\ Assert(msg.kind = "m1",
                                                 "Failure of assertion: first message must be m1")
                                       /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                                       /\ inbox' = multicast(net, self, msg.sndr)
                                       /\ UNCHANGED children
                                  ELSE /\ IF msg.kind = "m2"
                                             THEN /\ children' = [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
                                                  /\ inbox' = net
                                             ELSE /\ inbox' = net
                                                  /\ UNCHANGED children
                                       /\ UNCHANGED parent
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
                       /\ UNCHANGED << inbox, parent, children, rcvd >>
            /\ UNCHANGED nbrs

n2(self) == /\ pc[self] = "n2"
            /\ IF self # initiator
                  THEN /\ Assert(parent[self] \in nbrs[self],
                                 "Failure of assertion: parent must be a neighbor")
                       /\ inbox' = send(inbox, parent[self], [kind |-> "m2", sndr |-> self])
                  ELSE UNCHANGED inbox
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << parent, children, rcvd, nbrs >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

\* Allow infinite stuttering to prevent deadlock on termination.
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self))
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

-----------------------------------------------------------------------------
(* Correctness properties *)

TypeOK ==
    /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
    /\ inbox \in [Node -> SUBSET Message]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]
    /\ nbrs \in [Node -> SUBSET Node]
    /\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])
    \* Initiator never sends m2 messages / never gets a parent
    /\ \A n \in Node : \A msg \in inbox[n] : msg.kind = "m2" => msg.sndr # initiator

\* The initiator never has a parent.
InitiatorNoParent == parent[initiator] = NoNode

\* Parent and children relations are consistent.
ParentChild ==
    \A m, n \in Node :
        /\ n \in children[m] => m = parent[n]
        /\ m = parent[n] /\ pc[m] = "Done" => n \in children[m]

\* Parent of a node is always a neighbor.
ParentIsNeighbor ==
    \A n \in Node : parent[n] # NoNode => parent[n] \in neighbors(n)

\* Following parent pointers from any node with a parent leads to the
\* initiator within |Node| steps (hence no cycles).
RECURSIVE LeadsToRoot(_, _)
LeadsToRoot(n, k) ==
    IF n = initiator THEN TRUE
    ELSE IF k = 0 \/ parent[n] = NoNode THEN FALSE
    ELSE LeadsToRoot(parent[n], k - 1)

Acyclic ==
    \A n \in Node : parent[n] # NoNode => LeadsToRoot(n, Cardinality(Node))

\* Upon termination, the parent relation forms a spanning tree rooted at the initiator.
SpanningTree ==
    (\A n \in Node : pc[n] = "Done") =>
        /\ \A n \in Node \ {initiator} : parent[n] \in neighbors(n)
        /\ \A n \in Node : LeadsToRoot(n, Cardinality(Node))
        /\ \A n \in Node : inbox[n] = {}

\* Liveness: all nodes eventually terminate.
Termination == <>(\A n \in Node : pc[n] = "Done")

THEOREM Spec => [](TypeOK /\ InitiatorNoParent /\ ParentChild /\ ParentIsNeighbor
                   /\ Acyclic /\ SpanningTree)
THEOREM Spec => Termination
=============================================================================