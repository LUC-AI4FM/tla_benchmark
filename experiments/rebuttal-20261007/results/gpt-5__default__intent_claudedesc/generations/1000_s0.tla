---------------------------- MODULE ResourceAllocator ----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  Clients, \* nonempty fixed set of clients
  Resources \* nonempty fixed set of resources

ASSUME Clients # {} /\ Resources # {}

VARIABLES
  Held, \* Held[c] is the set of resources currently held by client c
  Dem,  \* Dem[c] is the (current) demand set most recently requested by client c
  Pend  \* Pend[c] = TRUE iff client c has an outstanding request (may be satisfied or not)

vars == << Held, Dem, Pend >>

AllHeld == UNION { Held[c] : c \in Clients }
Available == Resources \ AllHeld

Full(c) == Pend[c] /\ Dem[c] \subseteq Held[c]
Outstanding(c) == Pend[c]

TypeInv ==
  /\ Held \in [Clients -> SUBSET Resources]
  /\ Dem  \in [Clients -> SUBSET Resources]
  /\ Pend \in [Clients -> BOOLEAN]

MutualExclusion ==
  \A c1, c2 \in Clients : c1 # c2 => Held[c1] \cap Held[c2] = {}

HoldsWithinDemand ==
  \A c \in Clients : Held[c] \subseteq Dem[c]

Init ==
  /\ Held = [c \in Clients |-> {}]
  /\ Dem  = [c \in Clients |-> {}]
  /\ Pend = [c \in Clients |-> FALSE]

Submit(c) ==
  \E S \in SUBSET Resources :
    /\ S # {}
    /\ ~Pend[c]
    /\ Held[c] = {}
    /\ Held' = Held
    /\ Dem'  = [Dem EXCEPT ![c] = S]
    /\ Pend' = [Pend EXCEPT ![c] = TRUE]

Alloc(c) ==
  LET Want == Dem[c] \ Held[c]
      Free == Resources \ UNION { Held[d] : d \in Clients }
  IN /\ Pend[c]
     /\ Want # {}
     /\ \E A \in SUBSET Want :
          /\ A # {}
          /\ A \subseteq Free
          /\ Held' = [Held EXCEPT ![c] = @ \cup A]
          /\ Dem'  = Dem
          /\ Pend' = Pend

ReturnSome(c) ==
  \E A \in SUBSET Held[c] :
    /\ A # {}
    /\ Held' = [Held EXCEPT ![c] = @ \ A]
    /\ Dem'  = Dem
    /\ Pend' = Pend

ReturnAllAndClear(c) ==
  /\ Pend[c]
  /\ Dem[c] \subseteq Held[c]
  /\ Held[c] # {}
  /\ Held' = [Held EXCEPT ![c] = {}]
  /\ Dem'  = [Dem  EXCEPT ![c] = {}]
  /\ Pend' = [Pend EXCEPT ![c] = FALSE]

Next ==
  \/ \E c \in Clients : Submit(c)
  \/ \E c \in Clients : Alloc(c)
  \/ \E c \in Clients : ReturnSome(c)
  \/ \E c \in Clients : ReturnAllAndClear(c)
  \/ UNCHANGED vars

\* Liveness properties required by the description

EvReturn ==
  \A c \in Clients : [](~Pend[c] => <>(Held[c] = {}))

EvAllocationPerResource ==
  \A c \in Clients : \A r \in Resources : []((Pend[c] /\ r \in Dem[c]) => <>(r \in Held[c]))

EvFullSatisfaction ==
  \A c \in Clients : [](Pend[c] => <>Full(c))

InfinitelyOftenSatisfiable ==
  \A c \in Clients : (<>[]FALSE \/ ([]<>(Pend[c]) => []<>(Full(c))))
  \* Equivalent to: if c has an outstanding request infinitely often, then it is fully satisfied infinitely often.
  \* The disjunct <>[]FALSE is a tautology used only to keep the formula purely temporal without free-state predicates.

\* Safety invariants collected
SafetyInv == TypeInv /\ MutualExclusion /\ HoldsWithinDemand

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : SF_vars(Alloc(c))           \* strong fairness for allocator allocations
  /\ \A c \in Clients : WF_vars(ReturnAllAndClear(c)) \* weak fairness for clients returning all once fully satisfied

=============================================================================