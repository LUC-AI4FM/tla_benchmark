---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,    \* the set of processes (graph nodes)
          Edges,   \* the set of undirected edges, each a 2-element subset of Proc
          root     \* the distinguished root process

ASSUME /\ root \in Proc
       /\ \A e \in Edges : e \subseteq Proc /\ Cardinality(e) = 2

NoParent == CHOOSE v : v \notin Proc

Nbrs(p) == {q \in Proc : {p, q} \in Edges}

VARIABLES parent,    \* parent[p] is p's parent, or NoParent
          reported,  \* the set of processes that have reported
          msgs       \* the set of sent messages, each a pair <<sender, receiver>>

vars == <<parent, reported, msgs>>

TypeOK ==
  /\ parent \in [Proc -> Proc \cup {NoParent}]
  /\ reported \subseteq Proc
  /\ msgs \subseteq (Proc \X Proc)

Init ==
  /\ parent = [p \in Proc |-> NoParent]
  /\ reported = {}
  /\ msgs = {}

\* Process p sends a message to neighbor q, provided p is the root
\* or already has a parent.
SendMsg(p, q) ==
  /\ q \in Nbrs(p)
  /\ (p = root \/ parent[p] # NoParent)
  /\ <<p, q>> \notin msgs
  /\ msgs' = msgs \cup {<<p, q>>}
  /\ UNCHANGED <<parent, reported>>

\* An unparented non-root process p adopts as parent a process q
\* from which it has received a message.
Adopt(p, q) ==
  /\ p # root
  /\ parent[p] = NoParent
  /\ <<q, p>> \in msgs
  /\ parent' = [parent EXCEPT ![p] = q]
  /\ UNCHANGED <<reported, msgs>>

Next ==
  \E p \in Proc :
     \E q \in Proc : SendMsg(p, q) \/ Adopt(p, q)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Properties

\* Every non-root process eventually gets a parent.
Termination ==
  <>(\A p \in Proc \ {root} : parent[p] # NoParent)

\* Once a parent is assigned, it never changes.
ParentStable ==
  \A p \in Proc, q \in Proc :
     [](parent[p] = q => [](parent[p] = q))

ParentStableAction ==
  [][\A p \in Proc : parent[p] # NoParent => parent'[p] = parent[p]]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => ParentStable
=============================================================================