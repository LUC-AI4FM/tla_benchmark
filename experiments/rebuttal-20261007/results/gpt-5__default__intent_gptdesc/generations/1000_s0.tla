----------------------------- MODULE ResourceAllocator -----------------------------

EXTENDS FiniteSets

CONSTANTS Clients, Resources

ASSUME
  /\ IsFiniteSet(Clients) /\ Clients /= {}
  /\ IsFiniteSet(Resources) /\ Resources /= {}

VARIABLES Hold, Req

vars == << Hold, Req >>

TypeOK ==
  /\ Hold \in [Clients -> SUBSET Resources]
  /\ Req \in [Clients -> SUBSET Resources]

Free ==
  Resources \ UNION { Hold[c] : c \in Clients }

Init ==
  /\ TypeOK
  /\ \A c \in Clients: Hold[c] = {} /\ Req[c] = {}

Request(c, S) ==
  /\ c \in Clients
  /\ Hold[c] = {} /\ Req[c] = {}
  /\ S \in SUBSET Resources
  /\ S /= {}
  /\ Hold' = Hold
  /\ Req' = [Req EXCEPT ![c] = S]

Grant(c, G) ==
  /\ c \in Clients
  /\ Req[c] /= {}
  /\ G \in SUBSET (Req[c] \cap Free)
  /\ G /= {}
  /\ Hold' = [Hold EXCEPT ![c] = Hold[c] \cup G]
  /\ Req' = [Req EXCEPT ![c] = Req[c] \ G]

Return(c, T) ==
  /\ c \in Clients
  /\ T \in SUBSET Hold[c]
  /\ T /= {}
  /\ Hold' = [Hold EXCEPT ![c] = Hold[c] \ T]
  /\ Req' = Req

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources: Request(c, S)
  \/ \E c \in Clients, G \in SUBSET Resources: Grant(c, G)
  \/ \E c \in Clients, T \in SUBSET Resources: Return(c, T)

Spec ==
  Init /\ [][Next]_vars /\ Liveness

Exclusive ==
  \A c1 \in Clients: \A c2 \in Clients:
    c1 = c2 \/ Hold[c1] \cap Hold[c2] = {}

Safety ==
  []TypeOK /\ []Exclusive

PerResourceGrant ==
  \A c \in Clients: \A r \in Resources:
    [](r \in Req[c] => <> (r \in Hold[c]))

ReturnAfterFulfillment ==
  \A c \in Clients:
    [](Req[c] = {} => <> (Hold[c] = {}))

RepeatSatisfaction ==
  \A c \in Clients: []<>(Req[c] = {})

Liveness ==
  PerResourceGrant /\ ReturnAfterFulfillment /\ RepeatSatisfaction

=============================================================================