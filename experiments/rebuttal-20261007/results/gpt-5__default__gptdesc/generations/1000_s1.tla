------------------------------ MODULE ResourceAllocator ------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS CLIENTS, RESOURCES, Nil

ASSUME /\ Nil \notin CLIENTS \cup RESOURCES
       /\ (CLIENTS \cap RESOURCES) = {}
       /\ IsFiniteSet(RESOURCES)

VARIABLES owner, request

vars == << owner, request >>

Universe == CLIENTS \cup RESOURCES \cup {Nil}

Holds(c) == { r \in RESOURCES : owner[r] = c }
Unsat(c) == request[c] \ Holds(c)
NoUnsat(c) == Unsat(c) = {}

TypeInv ==
  /\ owner \in [RESOURCES -> CLIENTS \cup {Nil}]
  /\ request \in [CLIENTS -> SUBSET RESOURCES]

MutualExclusion ==
  \A r \in RESOURCES:
    \A c1, c2 \in CLIENTS:
      c1 # c2 => ~(owner[r] = c1 /\ owner[r] = c2)

Init ==
  /\ TypeInv
  /\ owner = [r \in RESOURCES |-> Nil]
  /\ request = [c \in CLIENTS |-> {}]

Grant(c, r) ==
  /\ c \in CLIENTS
  /\ r \in RESOURCES
  /\ owner[r] = Nil
  /\ r \in request[c]
  /\ owner' = [owner EXCEPT ![r] = c]
  /\ UNCHANGED request

Return(c, r) ==
  /\ c \in CLIENTS
  /\ r \in RESOURCES
  /\ owner[r] = c
  /\ owner' = [owner EXCEPT ![r] = Nil]
  /\ UNCHANGED request

ClearReq(c) ==
  /\ c \in CLIENTS
  /\ Unsat(c) = {}
  /\ request' = [request EXCEPT ![c] = {}]
  /\ UNCHANGED owner

Issue(c, S) ==
  /\ c \in CLIENTS
  /\ S \in SUBSET RESOURCES
  /\ Holds(c) = {}
  /\ Unsat(c) = {}
  /\ request' = [request EXCEPT ![c] = S]
  /\ UNCHANGED owner

Next ==
  \/ \E c \in CLIENTS:
       \E r \in RESOURCES: Grant(c, r)
  \/ \E c \in CLIENTS:
       \E r \in RESOURCES: Return(c, r)
  \/ \E c \in CLIENTS: ClearReq(c)
  \/ \E c \in CLIENTS:
       \E S \in SUBSET RESOURCES: Issue(c, S)

FairGrants ==
  \A c \in CLIENTS:
    \A r \in RESOURCES: WF_vars(Grant(c, r))

FairReturns ==
  \A c \in CLIENTS:
    \A r \in RESOURCES: WF_vars(Return(c, r))

FairClear ==
  \A c \in CLIENTS: WF_vars(ClearReq(c))

SpecGrantOnly ==
  Init /\ [][Next]_vars /\ FairGrants

SpecGrantReturnClear ==
  Init /\ [][Next]_vars /\ FairGrants /\ FairReturns /\ FairClear

Spec == SpecGrantOnly

EventualReturn ==
  \A c \in CLIENTS:
    \A r \in RESOURCES:
      [](owner[r] = c => <> owner[r] = Nil)

EventualGrantWhenEnabled ==
  \A c \in CLIENTS:
    \A r \in RESOURCES:
      [](ENABLED Grant(c, r) ~> owner[r] = c)

InfOftenNoUnsat ==
  \A c \in CLIENTS: []<>(NoUnsat(c))

THEOREM SpecGrantOnly => []TypeInv
THEOREM SpecGrantOnly => []MutualExclusion
THEOREM SpecGrantOnly => EventualGrantWhenEnabled

THEOREM SpecGrantReturnClear => []TypeInv
THEOREM SpecGrantReturnClear => []MutualExclusion
THEOREM SpecGrantReturnClear => EventualReturn
THEOREM SpecGrantReturnClear => InfOftenNoUnsat

IsBijOn(S, p) ==
  /\ p \in [S -> S]
  /\ \A x \in S: \E! y \in S: p[y] = x

Symmetry ==
  { p \in [Universe -> Universe] :
      /\ IsBijOn(CLIENTS, [x \in CLIENTS |-> p[x]])
      /\ \A x \in Universe \ CLIENTS: p[x] = x }

CEX_CLIENTS == {"c1", "c2"}
CEX_RESOURCES == {"r1", "r2"}
CEX_Nil == "nil"

==============================