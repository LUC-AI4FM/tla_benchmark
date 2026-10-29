------------------------------- MODULE Echo -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Node

ASSUME Node # {} /\ IsFiniteSet(Node)

initiator == CHOOSE n \in Node : TRUE

R == [p \in Node \X Node |-> p[1] # p[2]]

IsIrreflexive(Rel, S) == \A a \in S : ~Rel[a, a]
IsSymmetric(Rel, S)   == \A a, b \in S : Rel[a, b] => Rel[b, a]

RECURSIVE Reach(_, _)
Reach(S, k) ==
    IF k = 0 THEN S
    ELSE Reach(S \cup {m \in Node : \E s \in S : R[<<s, m>>]}, k - 1)

IsConnected(Rel, S) == \A a \in S : Reach({a}, Cardinality(S)) = S

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ IsIrreflexive(R, Node)
       /\ IsSymmetric(R, Node)
       /\ IsConnected(R, Node)

NoNode == CHOOSE x : x \notin Node

neighbors(n) == { m \in Node : R[<<m, n>>] }

Message == [kind : {"m", "c"}, sndr : Node]

send(box, i, j, msg) ==
    [box EXCEPT ![j] = @ \cup {[kind |-> msg, sndr |-> i]}]

multicast(box, i, S, msg) ==
    [m \in Node |-> IF m \in S
                    THEN box[m] \cup {[kind |-> msg, sndr |-> i]}
                    ELSE box[m]]

VARIABLES inbox, pc, parent, children, rcvd

vars == <<inbox, pc, parent, children, rcvd>>

Init ==
    /\ inbox = [n \in Node |-> {}]
    /\ pc = [n \in Node |-> "n0"]
    /\ parent = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ rcvd = [n \in Node |-> 0]

n0(self) ==
    /\ pc[self] = "n0"
    /\ inbox' = IF self = initiator
                THEN multicast(inbox, self, neighbors(self), "m")
                ELSE inbox
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED <<parent, children, rcvd>>

n1Receive(self) ==
    /\ pc[self] = "n1"
    /\ rcvd[self] < Cardinality(neighbors(self))
    /\ \E msg \in inbox[self] :
         /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
         /\ IF self # initiator /\ rcvd[self] + 1 = 1
              THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                   /\ inbox' = multicast([inbox EXCEPT ![self] = @ \ {msg}],
                                         self, neighbors(self) \ {msg.sndr}, "m")
              ELSE /\ inbox' = [inbox EXCEPT ![self] = @ \ {msg}]
                   /\ UNCHANGED parent
         /\ children' = IF msg.kind = "c"
                        THEN [children EXCEPT ![self] = @ \cup {msg.sndr}]
                        ELSE children
    /\ UNCHANGED pc

n1Exit(self) ==
    /\ pc[self] = "n1"
    /\ rcvd[self] >= Cardinality(neighbors(self))
    /\ pc' = [pc EXCEPT ![self] = "n2"]
    /\ UNCHANGED <<inbox, parent, children, rcvd>>

n2(self) ==
    /\ pc[self] = "n2"
    /\ inbox' = IF self # initiator
                THEN send(inbox, self, parent[self], "c")
                ELSE inbox
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<parent, children, rcvd>>

node(self) == n0(self) \/ n1Receive(self) \/ n1Exit(self) \/ n2(self)

Terminating == /\ \A n \in Node : pc[n] = "Done"
               /\ UNCHANGED vars

Next == (\E n \in Node : node(n)) \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A n \in Node : WF_vars(node(n))

----------------------------------------------------------------------------
(* Correctness properties *)

TypeOK ==
    /\ inbox \in [Node -> SUBSET Message]
    /\ \A n \in Node : \A msg \in inbox[n] : msg.sndr \in neighbors(n)
    /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ \A n \in Node : children[n] \subseteq neighbors(n)
    /\ rcvd \in [Node -> 0..Cardinality(Node)]
    /\ \A n \in Node : rcvd[n] <= Cardinality(neighbors(n))
    /\ \A n \in Node : neighbors(n) \subseteq Node /\ n \notin neighbors(n)

ParentNeighbor ==
    /\ parent[initiator] = NoNode
    /\ \A n \in Node : parent[n] \in neighbors(n) \cup {NoNode}

Finished == \A n \in Node : pc[n] = "Done"

ParentChild ==
    \A m, n \in Node : (parent[n] = m) ~> (n \in children[m])

ChildParent ==
    <>[](\A m, n \in Node : n \in children[m] <=> parent[n] = m)

Termination == <>Finished

RECURSIVE Up(_, _)
Up(n, k) ==
    IF k = 0 THEN n
    ELSE IF n \in Node THEN Up(parent[n], k - 1)
    ELSE NoNode

IsAncestor(a, n) == \E k \in 1..Cardinality(Node) : Up(n, k) = a

AncestorProperties ==
    Finished =>
      /\ parent[initiator] = NoNode
      /\ \A n \in Node \ {initiator} :
            /\ parent[n] \in neighbors(n)
            /\ IsAncestor(initiator, n)
      /\ \A n \in Node : ~IsAncestor(n, n)

=============================================================================