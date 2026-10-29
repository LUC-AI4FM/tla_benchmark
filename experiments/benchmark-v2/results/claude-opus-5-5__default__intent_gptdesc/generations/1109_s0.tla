---------------------------- MODULE SpanningTree ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,     \* set of processes
          Edges,    \* set of directed pairs; symmetric, so the network is undirected
          root      \* designated root process

NoParent == CHOOSE v : v \notin Proc

Nbrs(p) == {q \in Proc : <<p, q>> \in Edges}

RECURSIVE ReachN(_, _)
ReachN(S, n) ==
    IF n = 0 THEN S
    ELSE ReachN(S \cup {q \in Proc : \E p \in S : <<p, q>> \in Edges}, n - 1)

ASSUME RootInProc   == root \in Proc
ASSUME ProcFinite   == IsFiniteSet(Proc)
ASSUME EdgesType    == Edges \subseteq Proc \X Proc
ASSUME Undirected   == \A p, q \in Proc : <<p, q>> \in Edges => <<q, p>> \in Edges
ASSUME NoSelfLoops  == \A p \in Proc : <<p, p>> \notin Edges
ASSUME Connected    == ReachN({root}, Cardinality(Proc)) = Proc

VARIABLES parent,   \* parent[p] \in Proc \cup {NoParent}
          msgs,     \* set of sent messages <<sender, receiver>>
          ack       \* ack[p] = TRUE iff p has acknowledged (adopted) a parent

vars == <<parent, msgs, ack>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ parent \in [Proc -> Proc \cup {NoParent}]
    /\ msgs \subseteq Proc \X Proc
    /\ ack \in [Proc -> BOOLEAN]

MsgTypeOK == \A m \in msgs : m \in Proc \X Proc

Init ==
    /\ parent = [p \in Proc |-> NoParent]
    /\ msgs = {}
    /\ ack = [p \in Proc |-> FALSE]

CanSend(p) == p = root \/ parent[p] # NoParent

\* Process p sends a message to its neighbor q (may be repeated)
Send(p, q) ==
    /\ CanSend(p)
    /\ q \in Nbrs(p)
    /\ msgs' = msgs \cup {<<p, q>>}
    /\ UNCHANGED <<parent, ack>>

\* Unparented non-root process p receives a message from neighbor q and adopts q
Receive(p, q) ==
    /\ p # root
    /\ parent[p] = NoParent
    /\ <<q, p>> \in msgs
    /\ parent' = [parent EXCEPT ![p] = q]
    /\ ack' = [ack EXCEPT ![p] = TRUE]
    /\ UNCHANGED msgs

Next ==
    \E p, q \in Proc : Send(p, q) \/ Receive(p, q)

Fairness ==
    /\ \A p, q \in Proc : WF_vars(Send(p, q))
    /\ \A p, q \in Proc : WF_vars(Receive(p, q))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety (1): parent pointers are NoParent or a neighbor
ParentIsNeighbor ==
    \A p \in Proc : parent[p] = NoParent \/ parent[p] \in Nbrs(p)

\* The root never acquires a parent
RootHasNoParent == parent[root] = NoParent

\* Acknowledgement status is consistent with parent status
AckConsistent == \A p \in Proc : ack[p] <=> (parent[p] # NoParent)

\* Safety (3): every sent message comes from the root or a parented process
NoUnparentedSenderInv ==
    \A m \in msgs : m[1] = root \/ parent[m[1]] # NoParent

\* Messages only travel over existing links
MsgsOnLinks == msgs \subseteq Edges

\* Safety (2): once set, a parent value never changes
ParentStable ==
    [][\A p \in Proc : parent[p] # NoParent => parent'[p] = parent[p]]_vars

\* Safety (3), action form: no unparented non-root process sends
NoUnparentedSend ==
    [][\A p, q \in Proc :
          (<<p, q>> \in msgs' /\ <<p, q>> \notin msgs) => CanSend(p)]_vars

Invariants ==
    /\ TypeOK
    /\ MsgTypeOK
    /\ ParentIsNeighbor
    /\ RootHasNoParent
    /\ AckConsistent
    /\ NoUnparentedSenderInv
    /\ MsgsOnLinks

-----------------------------------------------------------------------------
\* Liveness: every non-root process eventually becomes parented
EventuallyParented ==
    \A p \in Proc \ {root} : <>(parent[p] # NoParent)

\* Termination: eventually and forever, every non-root process has a neighbor as parent
Termination ==
    <>[](\A p \in Proc \ {root} : parent[p] \in Nbrs(p))

THEOREM Spec => []Invariants
THEOREM Spec => ParentStable /\ NoUnparentedSend
THEOREM Spec => EventuallyParented /\ Termination
=============================================================================