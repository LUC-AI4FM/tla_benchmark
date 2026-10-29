------------------------------- MODULE EchoSpanningTree -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Node,       \* set of nodes (processes)
          initiator,  \* the single designated initiator
          R           \* undirected neighbor relation, a set of ordered pairs

-----------------------------------------------------------------------------
(* Transitive closure of a binary relation given as a set of pairs *)
TC(Rel) ==
  LET S == {r[1] : r \in Rel} \cup {r[2] : r \in Rel}
      RECURSIVE Close(_)
      Close(T) ==
        LET T2 == T \cup {<<s, t>> \in S \X S :
                            \E u \in S : <<s, u>> \in T /\ <<u, t>> \in T}
        IN IF T2 = T THEN T ELSE Close(T2)
  IN Close(Rel)

ASSUME /\ initiator \in Node
       /\ R \subseteq Node \X Node
       /\ \A n \in Node : <<n, n>> \notin R                         \* no self loops
       /\ \A n, m \in Node : <<n, m>> \in R => <<m, n>> \in R      \* undirected
       /\ \A n \in Node : n # initiator => <<initiator, n>> \in TC(R) \* connected

Nbrs(n) == {m \in Node : <<n, m>> \in R}

NoNode == CHOOSE x : x \notin Node

Msg == [kind : {"probe", "echo"}, from : Node]

-----------------------------------------------------------------------------
VARIABLES inbox,     \* inbox[n] : set of messages in transit to n
          rcvd,      \* rcvd[n]  : set of neighbors n has received a message from
          parent,    \* parent[n]: parent of n, or NoNode
          children,  \* children[n]: neighbors that sent n an echo (acknowledgment)
          phase      \* phase[n] \in {"idle", "active", "done"}

vars == <<inbox, rcvd, parent, children, phase>>

TypeOK ==
  /\ inbox \in [Node -> SUBSET Msg]
  /\ rcvd \in [Node -> SUBSET Node]
  /\ parent \in [Node -> Node \cup {NoNode}]
  /\ children \in [Node -> SUBSET Node]
  /\ phase \in [Node -> {"idle", "active", "done"}]
  /\ \A n \in Node : rcvd[n] \subseteq Nbrs(n) /\ children[n] \subseteq Nbrs(n)
  /\ \A n \in Node : \A m \in inbox[n] : m.from \in Nbrs(n)

-----------------------------------------------------------------------------
Init ==
  /\ inbox = [n \in Node |-> {}]
  /\ rcvd = [n \in Node |-> {}]
  /\ parent = [n \in Node |-> NoNode]
  /\ children = [n \in Node |-> {}]
  /\ phase = [n \in Node |-> "idle"]

(* The initiator starts the wave by probing all its neighbors *)
Start ==
  /\ phase[initiator] = "idle"
  /\ phase' = [phase EXCEPT ![initiator] = "active"]
  /\ inbox' = [k \in Node |->
                 IF k \in Nbrs(initiator)
                   THEN inbox[k] \cup {[kind |-> "probe", from |-> initiator]}
                   ELSE inbox[k]]
  /\ UNCHANGED <<rcvd, parent, children>>

(* Node n receives some message in arbitrary order *)
Receive(n) ==
  \E msg \in inbox[n] :
    LET m == msg.from
        first == /\ n # initiator
                 /\ phase[n] = "idle"
                 /\ msg.kind = "probe"
    IN /\ rcvd' = [rcvd EXCEPT ![n] = @ \cup {m}]
       /\ IF first
            THEN /\ parent' = [parent EXCEPT ![n] = m]
                 /\ phase' = [phase EXCEPT ![n] = "active"]
                 /\ inbox' = [k \in Node |->
                                IF k = n THEN inbox[n] \ {msg}
                                ELSE IF k \in Nbrs(n) \ {m}
                                  THEN inbox[k] \cup {[kind |-> "probe", from |-> n]}
                                  ELSE inbox[k]]
                 /\ UNCHANGED children
            ELSE /\ inbox' = [inbox EXCEPT ![n] = @ \ {msg}]
                 /\ children' = IF msg.kind = "echo"
                                  THEN [children EXCEPT ![n] = @ \cup {m}]
                                  ELSE children
                 /\ UNCHANGED <<parent, phase>>

(* After hearing from all neighbors, a node completes; non-initiators echo to parent *)
Finish(n) ==
  /\ phase[n] = "active"
  /\ rcvd[n] = Nbrs(n)
  /\ phase' = [phase EXCEPT ![n] = "done"]
  /\ IF n # initiator
       THEN inbox' = [inbox EXCEPT ![parent[n]] = @ \cup {[kind |-> "echo", from |-> n]}]
       ELSE UNCHANGED inbox
  /\ UNCHANGED <<rcvd, parent, children>>

AllDone == \A n \in Node : phase[n] = "done"

Terminating == AllDone /\ \A n \in Node : inbox[n] = {} /\ UNCHANGED vars

Next ==
  \/ Start
  \/ \E n \in Node : Receive(n) \/ Finish(n)
  \/ Terminating

Fairness ==
  /\ WF_vars(Start)
  /\ \A n \in Node : WF_vars(Receive(n))
  /\ \A n \in Node : WF_vars(Finish(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

ParentIsNeighbor ==
  \A n \in Node : parent[n] # NoNode => parent[n] \in Nbrs(n)

InitiatorNoParent == parent[initiator] = NoNode

\* No duplication / spontaneous creation: each neighbor sends at most one message to n
NoDuplicates ==
  \A n \in Node : \A msg \in inbox[n] :
     /\ msg.from \in Nbrs(n)
     /\ msg.from \notin rcvd[n]
     /\ \A msg2 \in inbox[n] : msg2.from = msg.from => msg2 = msg

\* Every recorded child relation corresponds to the child having informed its parent
ChildImpliesParent ==
  \A m, n \in Node : n \in children[m] => /\ parent[n] = m
                                          /\ phase[n] = "done"

ParentRel == {<<n, parent[n]>> : n \in {k \in Node : parent[k] # NoNode}}

Ancestor == TC(ParentRel)

SpanningTree ==
  AllDone =>
    /\ parent[initiator] = NoNode
    /\ \A n \in Node \ {initiator} : parent[n] \in Nbrs(n)
    /\ \A n \in Node : <<n, n>> \notin Ancestor                 \* irreflexive / acyclic
    /\ \A n \in Node \ {initiator} : <<n, initiator>> \in Ancestor \* unique root
    /\ \A n \in Node : children[n] = {k \in Node : parent[k] = n}

Inv ==
  /\ TypeOK
  /\ ParentIsNeighbor
  /\ InitiatorNoParent
  /\ NoDuplicates
  /\ ChildImpliesParent
  /\ SpanningTree

-----------------------------------------------------------------------------
(* Liveness properties *)

ParentChildConsistency ==
  \A n, m \in Node : (parent[n] = m) ~> (n \in children[m])

Termination == <>AllDone

EventuallyTree == <>(AllDone /\ SpanningTree)

THEOREM Spec => []Inv
THEOREM Spec => ParentChildConsistency /\ Termination /\ EventuallyTree
=============================================================================