---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,      \* the set of processes (graph nodes)
          Nbrs,      \* Nbrs[p] is the set of neighbors of process p
          root       \* the distinguished root process

ASSUME /\ root \in Proc
       /\ Nbrs \in [Proc -> SUBSET Proc]
       /\ \A p \in Proc : p \notin Nbrs[p]

NoParent == CHOOSE x : x \notin Proc

VARIABLES parent,    \* parent[p] is p's parent, or NoParent
          reported,  \* set of processes that have reported
          msgs       \* set of sent messages, each a pair <<from, to>>

vars == <<parent, reported, msgs>>

Msg == Proc \X Proc

TypeOK ==
  /\ parent \in [Proc -> Proc \cup {NoParent}]
  /\ reported \subseteq Proc
  /\ msgs \subseteq Msg

Init ==
  /\ parent = [p \in Proc |-> NoParent]
  /\ reported = {}
  /\ msgs = {}

\* A process may send to a neighbor if it is the root or already has a parent
SendMsg(p, q) ==
  /\ q \in Nbrs[p]
  /\ \/ p = root
     \/ parent[p] # NoParent
  /\ msgs' = msgs \cup {<<p, q>>}
  /\ UNCHANGED <<parent, reported>>

\* An unparented non-root process adopts as parent a sender it received from
Parent(p) ==
  /\ p # root
  /\ parent[p] = NoParent
  /\ \E q \in Proc :
        /\ <<q, p>> \in msgs
        /\ parent' = [parent EXCEPT ![p] = q]
  /\ UNCHANGED <<reported, msgs>>

Next ==
  \/ \E p \in Proc : \E q \in Nbrs[p] : SendMsg(p, q)
  \/ \E p \in Proc : Parent(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Termination: eventually every non-root process has a parent
Terminates == <>(\A p \in Proc \ {root} : parent[p] # NoParent)

\* Once a parent is assigned it never changes
ParentStable ==
  \A p \in Proc : \A q \in Proc :
     [](parent[p] = q => [](parent[p] = q))

THEOREM Spec => []TypeOK
THEOREM Spec => ParentStable
THEOREM Spec => Terminates
=============================================================================