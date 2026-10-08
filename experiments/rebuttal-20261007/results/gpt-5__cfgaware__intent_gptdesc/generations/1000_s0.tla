--------------------------- MODULE ResourceAllocator ---------------------------

CONSTANTS CLIENTS, RESOURCES

VARIABLES held, req

AllHeld == UNION { held[c] : c \in CLIENTS }
Free    == RESOURCES \ AllHeld

TypeOK ==
  /\ held \in [CLIENTS -> SUBSET RESOURCES]
  /\ req  \in [CLIENTS -> SUBSET RESOURCES]

Exclusive ==
  \A c1, c2 \in CLIENTS :
    (c1 # c2) => (held[c1] \cap held[c2] = {})

Init ==
  /\ TypeOK
  /\ \A c \in CLIENTS : /\ held[c] = {}
                         /\ req[c]  = {}

Request(c) ==
  /\ c \in CLIENTS
  /\ held[c] = {}
  /\ req[c]  = {}
  /\ \E S \in SUBSET RESOURCES :
       /\ S # {}
       /\ held' = held
       /\ req'  = [req EXCEPT ![c] = S]

Return(c) ==
  /\ c \in CLIENTS
  /\ \E R \in SUBSET held[c] :
       /\ R # {}
       /\ held' = [held EXCEPT ![c] = held[c] \ R]
       /\ req'  = req

Grant(c) ==
  /\ c \in CLIENTS
  /\ \E G \in SUBSET (req[c] \cap Free) :
       /\ G # {}
       /\ held' = [held EXCEPT ![c] = held[c] \cup G]
       /\ req'  = [req  EXCEPT ![c] = req[c] \ G]

Next ==
  \/ \E c \in CLIENTS : Request(c)
  \/ \E c \in CLIENTS : Grant(c)
  \/ \E c \in CLIENTS : Return(c)

Spec == Init /\ [][Next]_<<held, req>>

\* Safety: well-formed state and resource exclusivity always hold.
Safety == [](TypeOK /\ Exclusive)

\* Liveness obligations:

\* 1) If a resource is in a client's outstanding request, that resource is
\*    eventually allocated to that client.
AllocateEventually ==
  \A c \in CLIENTS : \A r \in RESOURCES :
    []( r \in req[c] => <> (r \in held[c]) )

\* 2) Once a client's outstanding request is empty, the client eventually
\*    returns all resources it holds.
ReturnEventually ==
  \A c \in CLIENTS :
    []( req[c] = {} => <> (held[c] = {}) )

\* 3) Each client's outstanding request is satisfied infinitely often
\*    (the client repeatedly reaches states with no outstanding request).
SatisfiedInfOften ==
  \A c \in CLIENTS : []<>(req[c] = {})

Liveness == AllocateEventually /\ ReturnEventually /\ SatisfiedInfOften

=============================================================================