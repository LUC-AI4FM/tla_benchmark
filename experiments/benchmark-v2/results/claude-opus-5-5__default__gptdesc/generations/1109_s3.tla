------------------------------ MODULE SpanningTree ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,      \* set of processes
          Nbrs,      \* Nbrs[p] is the set of neighbors of process p
          root,      \* the distinguished root process
          NoPrnt     \* value indicating "no parent"

ASSUME /\ root \in Proc
       /\ NoPrnt \notin Proc
       /\ Nbrs \in [Proc -> SUBSET Proc]
       /\ \A p \in Proc : p \notin Nbrs[p]
       /\ \A p, q \in Proc : (q \in Nbrs[p]) <=> (p \in Nbrs[q])

VARIABLES parent,    \* parent[p] is p's parent, or NoPrnt
          reported,  \* set of processes that have reported
          msgs       \* set of sent messages <<sender, receiver>>

vars == <<parent, reported, msgs>>

Edges == {<<p, q>> \in Proc \X Proc : q \in Nbrs[p]}

TypeOK ==
  /\ parent \in [Proc -> Proc \cup {NoPrnt}]
  /\ reported \subseteq Proc
  /\ msgs \subseteq Edges

Init ==
  /\ parent = [p \in Proc |-> NoPrnt]
  /\ reported = {}
  /\ msgs = {}

\* Process p sends a message to neighbor q.
Send(p, q) ==
  /\ q \in Nbrs[p]
  /\ (p = root) \/ (parent[p] # NoPrnt)
  /\ msgs' = msgs \cup {<<p, q>>}
  /\ UNCHANGED <<parent, reported>>

\* Unparented non-root process p adopts sender q as its parent.
SetParent(p, q) ==
  /\ p # root
  /\ parent[p] = NoPrnt
  /\ <<q, p>> \in msgs
  /\ parent' = [parent EXCEPT ![p] = q]
  /\ UNCHANGED <<reported, msgs>>

Next ==
  \E p \in Proc :
     \E q \in Proc :
        \/ Send(p, q)
        \/ SetParent(p, q)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Properties

Termination ==
  <>(\A p \in Proc \ {root} : parent[p] # NoPrnt)

ParentStable ==
  \A p \in Proc :
     [][parent[p] # NoPrnt => parent'[p] = parent[p]]_parent

THEOREM Spec => []TypeOK
THEOREM Spec => Termination
THEOREM Spec => ParentStable
=============================================================================