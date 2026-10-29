------------------------------- MODULE Echo -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Node, initiator, R

NoNode == CHOOSE x : x \notin Node

(***************************************************************************)
(* Transitive closure of a binary relation given as a set of pairs.        *)
(***************************************************************************)
TC(Rel) ==
  LET S == {r[1] : r \in Rel} \cup {r[2] : r \in Rel}
      RECURSIVE TCR(_)
      TCR(T) == IF T = {}
                THEN Rel
                ELSE LET r  == CHOOSE s \in T : TRUE
                         RR == TCR(T \ {r})
                     IN  RR \cup {<<s, t>> \in S \X S :
                                    <<s, r>> \in RR /\ <<r, t>> \in RR}
  IN  TCR(S)

EdgeSet == {<<m, n>> \in Node \X Node : R[m, n]}

ASSUME /\ initiator \in Node
       /\ R \in [Node \X Node -> BOOLEAN]
       /\ \A n \in Node : ~ R[n, n]
       /\ \A m, n \in Node : R[m, n] = R[n, m]
       /\ \A m, n \in Node : m # n => <<m, n>> \in TC(EdgeSet)

neighbors(n) == {m \in Node : R[m, n]}

Message == [kind : {"m", "c"}, sndr : Node]

VARIABLES inbox, parent, children, rcvd, nbrs, pc

vars == <<inbox, parent, children, rcvd, nbrs, pc>>

ProcSet == Node

Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> 0]
  /\ nbrs = [n \in Node |-> neighbors(n)]
  /\ pc = [n \in Node |-> "n0"]

n0(self) ==
  /\ pc[self] = "n0"
  /\ IF self = initiator
       THEN inbox' = [n \in Node |->
                        IF n \in nbrs[self]
                        THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                        ELSE inbox[n]]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "n1"]
  /\ UNCHANGED <<parent, children, rcvd, nbrs>>

n1(self) ==
  /\ pc[self] = "n1"
  /\ IF rcvd[self] < Cardinality(nbrs[self])
       THEN /\ \E msg \in inbox[self] :
                 IF msg.kind = "m"
                 THEN IF rcvd[self] = 0 /\ self # initiator
                      THEN /\ parent' = [parent EXCEPT ![self] = msg.sndr]
                           /\ inbox' = [n \in Node |->
                                 IF n = self
                                 THEN inbox[self] \ {msg}
                                 ELSE IF n \in nbrs[self] \ {msg.sndr}
                                      THEN inbox[n] \cup {[kind |-> "m", sndr |-> self]}
                                      ELSE inbox[n]]
                           /\ UNCHANGED children
                      ELSE /\ inbox' = [inbox EXCEPT ![self] = inbox[self] \ {msg}]
                           /\ UNCHANGED <<parent, children>>
                 ELSE /\ children' = [children EXCEPT ![self] = children[self] \cup {msg.sndr}]
                      /\ inbox' = [inbox EXCEPT ![self] = inbox[self] \ {msg}]
                      /\ UNCHANGED parent
            /\ rcvd' = [rcvd EXCEPT ![self] = rcvd[self] + 1]
            /\ pc' = pc
       ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
            /\ UNCHANGED <<inbox, parent, children, rcvd>>
  /\ UNCHANGED nbrs

n2(self) ==
  /\ pc[self] = "n2"
  /\ IF self # initiator
       THEN inbox' = [inbox EXCEPT ![parent[self]] =
                        inbox[parent[self]] \cup {[kind |-> "c", sndr |-> self]}]
       ELSE UNCHANGED inbox
  /\ pc' = [pc EXCEPT ![self] = "Done"]
  /\ UNCHANGED <<parent, children, rcvd, nbrs>>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in Node : node(self)) \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

-----------------------------------------------------------------------------

TypeOK ==
  /\ inbox \in [Node -> SUBSET Message]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ rcvd \in [Node -> Nat]
  /\ nbrs \in [Node -> SUBSET Node]
  /\ \A n \in Node : nbrs[n] = neighbors(n) /\ rcvd[n] <= Cardinality(nbrs[n])
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]

InitiatorNoParent == parent[initiator] = NoNode

ParentIsNeighbor == \A n \in Node : parent[n] # NoNode => parent[n] \in neighbors(n)

ParentChildConsistent == \A m, n \in Node : n \in children[m] => parent[n] = m

ParentRel == {<<parent[n], n>> : n \in {m \in Node : parent[m] \in Node}}

AncestorProperties ==
  (\A n \in Node : pc[n] = "Done") =>
     LET anc == TC(ParentRel)
     IN  /\ \A n \in Node \ {initiator} : <<initiator, n>> \in anc
         /\ \A n \in Node : <<n, n>> \notin anc

=============================================================================