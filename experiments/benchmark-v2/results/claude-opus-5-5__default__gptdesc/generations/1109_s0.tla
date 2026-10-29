---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,      \* the set of processes (graph nodes)
          Nbrs,      \* Nbrs[p] is the set of neighbors of process p
          root,      \* the distinguished root process
          NoPrnt     \* value denoting "no parent"

ASSUME RootInProc   == root \in Proc
ASSUME NoPrntNotProc == NoPrnt \notin Proc
ASSUME NbrsType     == Nbrs \in [Proc -> SUBSET Proc]
ASSUME NbrsSymmetric == \A p, q \in Proc : (q \in Nbrs[p]) <=> (p \in Nbrs[q])

VARIABLES parent,    \* parent[p] is p's parent, or NoPrnt
          reported,  \* reported[p] is TRUE iff p has reported
          msgs       \* set of sent messages, each a pair <<sender, receiver>>

vars == <<parent, reported, msgs>>

Msgs == Proc \X Proc

TypeOK ==
    /\ parent \in [Proc -> Proc \cup {NoPrnt}]
    /\ reported \in [Proc -> BOOLEAN]
    /\ msgs \subseteq Msgs

Init ==
    /\ parent = [p \in Proc |-> NoPrnt]
    /\ reported = [p \in Proc |-> FALSE]
    /\ msgs = {}

\* Process p sends a message to neighbor q, allowed if p is the root
\* or p already has a parent.
SendMsg(p, q) ==
    /\ q \in Nbrs[p]
    /\ (p = root) \/ (parent[p] # NoPrnt)
    /\ msgs' = msgs \cup {<<p, q>>}
    /\ UNCHANGED <<parent, reported>>

\* An unparented non-root process p adopts as parent a process q
\* from which it has received a message.
Parent(p, q) ==
    /\ p # root
    /\ parent[p] = NoPrnt
    /\ <<q, p>> \in msgs
    /\ parent' = [parent EXCEPT ![p] = q]
    /\ UNCHANGED <<reported, msgs>>

Next ==
    \E p \in Proc, q \in Proc :
        \/ SendMsg(p, q)
        \/ Parent(p, q)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* Properties

\* Every non-root process eventually gets a parent.
Termination ==
    <>(\A p \in Proc \ {root} : parent[p] # NoPrnt)

\* Once a parent is assigned, it never changes.
ParentStable ==
    \A p \in Proc :
        [][parent[p] # NoPrnt => parent'[p] = parent[p]]_parent

THEOREM Spec => []TypeOK
THEOREM Spec => ParentStable
=============================================================================