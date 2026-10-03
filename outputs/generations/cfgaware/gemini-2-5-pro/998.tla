-------------------------- MODULE ResourceAllocator --------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT Client, Resource
CONSTANT Precedes

ASSUME Precedes \in [Client -> SUBSET Client]

\* Precedence is irreflexive and transitive (a DAG).
ASSUME \A c \in Client : c \notin Precedes[c]
ASSUME \A a,b,c \in Client : (b \in Precedes[a] /\ c \in Precedes[b]) => c \in Precedes[a]

VARIABLES requests, held, satisfied

vars == <<requests, held, satisfied>>

TypeOK == /\ requests \in [Client -> SUBSET Resource]
          /\ held \in [Client -> SUBSET Resource]
          /\ satisfied \in [Client -> BOOLEAN]

Init == /\ requests = [c \in Client |-> {}]
        /\ held = [c \in Client |-> {}]
        /\ satisfied = [c \in Client |-> FALSE]

\* A client c requests a non-empty set of resources R.
\* Enabled only when the client has no active request and holds no resources.
Request(c, R) ==
    /\ requests[c] = {}
    /\ held[c] = {}
    /\ R \subseteq Resource /\ R # {}
    /\ requests' = [requests EXCEPT ![c] = R]
    /\ satisfied' = [satisfied EXCEPT ![c] = FALSE]
    /\ UNCHANGED held

\* The allocator grants an available resource r to client c.
\* Enabled only if c requested r, doesn't hold it yet, r is free,
\* and all preceding clients' requests are satisfied or non-existent.
Allocate(c, r) ==
    /\ r \in requests[c] \setminus held[c]
    /\ r \notin \bigcup {held[cl] : cl \in Client}
    /\ \A p \in {p \in Client : c \in Precedes[p]} :
          requests[p] = {} \/ satisfied[p]
    /\ held' = [held EXCEPT ![c] = @ \cup {r}]
    /\ satisfied' = [satisfied EXCEPT ![c] = IF \neg satisfied[c] /\ requests[c] = (held[c] \cup {r})
                                            THEN TRUE
                                            ELSE @]
    /\ UNCHANGED requests

\* Client c returns a non-empty set of its held resources R.
Return(c, R) ==
    /\ R \subseteq held[c] /\ R # {}
    /\ held' = [held EXCEPT ![c] = @ \setminus R]
    /\ UNCHANGED <<requests, satisfied>>

\* Client c resets its request after it was satisfied and all resources returned.
\* This allows the client to make a new request.
Reset(c) ==
    /\ requests[c] # {}
    /\ satisfied[c]
    /\ held[c] = {}
    /\ requests' = [requests EXCEPT ![c] = {}]
    /\ satisfied' = [satisfied EXCEPT ![c] = FALSE]
    /\ UNCHANGED held

Next == \/ \E c \in Client, R \in SUBSET Resource: Request(c, R)
        \/ \E c \in Client, r \in Resource: Allocate(c, r)
        \/ \E c \in Client, R \in SUBSET Resource: Return(c, R)
        \/ \E c \in Client: Reset(c)

\* Fairness assumptions to ensure progress.
Fairness == /\ \A c \in Client : WF_vars(\E R \in SUBSET Resource: Request(c, R))
           /\ \A c \in Client : WF_vars(\E r \in Resource: Allocate(c, r))
           /\ \A c \in Client : WF_vars(\E R \in SUBSET Resource: Return(c, R))
           /\ \A c \in Client : WF_vars(Reset(c))

Spec == Init /\ [][Next]_vars /\ Fairness

=============================================================================