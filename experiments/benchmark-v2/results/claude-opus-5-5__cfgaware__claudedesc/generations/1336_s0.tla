---------------------------- MODULE MCEcho ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, initiator, R, NoNode

VARIABLES inbox, pc, parent, children, rcvd

vars == <<inbox, pc, parent, children, rcvd>>

(***************************************************************************)
(* Concrete instance used for model checking                               *)
(***************************************************************************)
N1 == {"a", "b", "c"}

I1 == CHOOSE n \in N1 : TRUE

\* Fully connected mesh without self-loops
R1 == [e \in N1 \X N1 |-> e[1] # e[2]]

(***************************************************************************)
(* Alternative definition: any graph that is connected, symmetric and      *)
(* irreflexive could be chosen as follows:                                 *)
(*                                                                         *)
(*   R1 == CHOOSE r \in [N1 \X N1 -> BOOLEAN] :                            *)
(*            /\ \A n \in N1 : ~ r[n,n]                  \* irreflexive    *)
(*            /\ \A m,n \in N1 : r[m,n] = r[n,m]         \* symmetric      *)
(*            /\ IsConnected(r)                          \* connected      *)
(***************************************************************************)

ASSUME NoNode \notin Node
ASSUME initiator \in Node
ASSUME R \in [Node \X Node -> BOOLEAN]

(***************************************************************************)
(* Echo algorithm                                                          *)
(***************************************************************************)
neighbors(n) == {m \in Node : R[m, n]}

Message == [kind : {"m", "c"}, sndr : Node]

multicast(ib, snd, rcvrs, k) ==
    [m \in Node |-> IF m \in rcvrs
                      THEN ib[m] \cup {[kind |-> k, sndr |-> snd]}
                      ELSE ib[m]]

Init ==
    /\ inbox = [n \in Node |-> {}]
    /\ pc = [n \in Node |-> "n0"]
    /\ parent = [n \in Node |-> NoNode]
    /\ children = [n \in Node |-> {}]
    /\ rcvd = [n \in Node |-> 0]

n0(self) ==
    /\ pc[self] = "n0"
    /\ IF self = initiator
         THEN inbox' = multicast(inbox, self, neighbors(self), "m")
         ELSE UNCHANGED inbox
    /\ pc' = [pc EXCEPT ![self] = "n1"]
    /\ UNCHANGED <<parent, children, rcvd>>

n1(self) ==
    /\ pc[self] = "n1"
    /\ IF rcvd[self] < Cardinality(neighbors(self))
         THEN \E msg \in inbox[self] :
                LET ib1 == [inbox EXCEPT ![self] = @ \ {msg}] IN
                /\ IF msg.kind = "m" /\ rcvd[self] = 0 /\ self # initiator
                     THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                          /\ inbox' = multicast(ib1, self,
                                                neighbors(self) \ {msg.sndr}, "m")
                          /\ UNCHANGED children
                     ELSE IF msg.kind = "c"
                            THEN /\ children' = [children EXCEPT ![self] = @ \cup {msg.sndr}]
                                 /\ inbox' = ib1
                                 /\ UNCHANGED parent
                            ELSE /\ inbox' = ib1
                                 /\ UNCHANGED <<parent, children>>
                /\ rcvd' = [rcvd EXCEPT ![self] = @ + 1]
                /\ UNCHANGED pc
         ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
              /\ UNCHANGED <<inbox, parent, children, rcvd>>

n2(self) ==
    /\ pc[self] = "n2"
    /\ IF self # initiator
         THEN inbox' = multicast(inbox, self, {parent[self]}, "c")
         ELSE UNCHANGED inbox
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<parent, children, rcvd>>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminating ==
    /\ \A self \in Node : pc[self] = "Done"
    /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
    /\ inbox \in [Node -> SUBSET Message]
    /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
    /\ parent \in [Node -> Node \cup {NoNode}]
    /\ children \in [Node -> SUBSET Node]
    /\ rcvd \in [Node -> Nat]

RECURSIVE Anc(_, _)
Anc(n, k) ==
    IF k = 0 \/ parent[n] = NoNode
      THEN {}
      ELSE {parent[n]} \cup Anc(parent[n], k - 1)

ancestors(n) == Anc(n, Cardinality(Node) + 1)

AncestorProperties ==
    /\ parent[initiator] = NoNode
    /\ \A n \in Node :
         /\ n \notin ancestors(n)
         /\ parent[n] # NoNode => initiator \in ancestors(n)
         /\ parent[n] # NoNode => parent[n] \in neighbors(n)

(***************************************************************************)
(* Model-checking wrappers                                                 *)
(***************************************************************************)
TestSpec == PrintT(<<"R", R>>) /\ Spec

View == <<inbox, pc, parent, children, rcvd>>

PostCondition ==
    PrintT(<<"generated states", TLCGet("stats").generated>>)

=============================================================================