---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,      \* set of processes
          Nbrs,      \* Nbrs[p] is the set of neighbors of process p
          root       \* the distinguished root process

ASSUME /\ root \in Proc
       /\ Nbrs \in [Proc -> SUBSET Proc]

NoParent == CHOOSE n : n \notin Proc

VARIABLES parent,    \* parent[p] is p's parent, or NoParent
          reported,  \* reported[p] is TRUE iff p has reported
          msgs       \* set of sent messages <<sender, receiver>>

vars == <<parent, reported, msgs>>

TypeOK ==
  /\ parent \in [Proc -> Proc \cup {NoParent}]
  /\ reported \in [Proc -> BOOLEAN]
  /\ msgs \subseteq (Proc \X Proc)

Init ==
  /\ parent = [p \in Proc |-> NoParent]
  /\ reported = [p \in Proc |-> FALSE]
  /\ msgs = {}

\* Process p sends a message to neighbor q, allowed if p is the root
\* or p already has a parent.
Send(p, q) ==
  /\ q \in Nbrs[p]
  /\ \/ p = root
     \/ parent[p] # NoParent
  /\ msgs' = msgs \cup {<<p, q>>}
  /\ UNCHANGED <<parent, reported>>

\* An unparented non-root process p adopts as parent some process q
\* from which it has received a message.
Adopt(p, q) ==
  /\ p # root
  /\ parent[p] = NoParent
  /\ <<q, p>> \in msgs
  /\ parent' = [parent EXCEPT ![p] = q]
  /\ UNCHANGED <<reported, msgs>>

Next ==
  \/ \E p \in Proc : \E q \in Proc : Send(p, q)
  \/ \E p \in Proc : \E q \in Proc : Adopt(p, q)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Termination: every non-root process eventually gets a parent.
Termination ==
  <>(\A p \in Proc \ {root} : parent[p] # NoParent)

\* Once a parent is assigned, it never changes.
ParentStable ==
  \A p \in Proc : \A q \in Proc :
     [](parent[p] = q => [](parent[p] = q))

THEOREM Spec => []TypeOK
THEOREM Spec => Termination
THEOREM Spec => ParentStable
=============================================================================