---- MODULE ResourceAllocator ----
EXTENDS TLA

CONSTANTS Clients, Resources

VARIABLES held, outReq

vars == << held, outReq >>

TypeOK ==
  /\ held \in [Clients -> SUBSET Resources]
  /\ outReq \in [Clients -> SUBSET Resources]

Init ==
  /\ TypeOK
  /\ held = [c \in Clients |-> {}]
  /\ outReq = [c \in Clients |-> {}]

Available(r) == \A d \in Clients: r \notin held[d]

FullySatisfied(c) == outReq[c] \subseteq held[c]

Satisfied(c) == outReq[c] # {} /\ FullySatisfied(c)

Submit(c, S) ==
  /\ c \in Clients
  /\ S \subseteq Resources /\ S # {}
  /\ outReq[c] = {}
  /\ held[c] = {}
  /\ outReq' = [outReq EXCEPT ![c] = S]
  /\ held' = held

Alloc(c, r) ==
  /\ c \in Clients /\ r \in Resources
  /\ r \in outReq[c]
  /\ r \notin held[c]
  /\ Available(r)
  /\ held' = [held EXCEPT ![c] = @ \cup {r}]
  /\ outReq' = outReq

ReturnSome(c, X) ==
  /\ c \in Clients
  /\ X \subseteq held[c] /\ X # {}
  /\ held' = [held EXCEPT ![c] = @ \ X]
  /\ outReq' = outReq

ReturnAllSatisfied(c) ==
  /\ c \in Clients
  /\ FullySatisfied(c)
  /\ held[c] # {}
  /\ held' = [held EXCEPT ![c] = {}]
  /\ outReq' = [outReq EXCEPT ![c] = {}]

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources: Submit(c, S)
  \/ \E c \in Clients, r \in Resources: Alloc(c, r)
  \/ \E c \in Clients, X \in SUBSET Resources: ReturnSome(c, X)
  \/ \E c \in Clients: ReturnAllSatisfied(c)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A c \in Clients: WF_vars(ReturnAllSatisfied(c)))
  /\ (\A c \in Clients: \A r \in Resources: SF_vars(Alloc(c, r)))

MutualExclusion ==
  [](\A c \in Clients: \A d \in Clients: c # d => held[c] \cap held[d] = {})

EventualReturn ==
  \A c \in Clients: [](outReq[c] = {} => <>(held[c] = {}))

EventualAllocation ==
  \A c \in Clients: \A r \in Resources: [](r \in outReq[c] => <>(r \in held[c]))

InfiniteSatisfiability ==
  \A c \in Clients: ([]<>(outReq[c] # {})) => ([]<>(Satisfied(c)))

====