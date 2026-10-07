----------------------------- MODULE ResourceAllocator -----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS CLIENTS, RESOURCES

(*
  State variables:
    - hold[c] is the set of resources currently held by client c
    - need[c] is the set of resources still needed to complete c's current request
    - want[c] is the original set of resources requested by c for the current request
    - owner[r] is the current owner client of resource r, or Nil if free
*)

VARIABLES hold, need, want, owner

Vars == << hold, need, want, owner >>

TypeOK ==
  /\ hold \in [CLIENTS -> SUBSET RESOURCES]
  /\ need \in [CLIENTS -> SUBSET RESOURCES]
  /\ want \in [CLIENTS -> SUBSET RESOURCES]
  /\ owner \in [RESOURCES -> (CLIENTS \cup {Nil})]

(*
  Basic consistency between owner and hold, and request discipline relations.
*)
Consistency ==
  /\ \A r \in RESOURCES:
        (owner[r] = Nil) <=> (\A c \in CLIENTS: r \notin hold[c])
  /\ \A c \in CLIENTS:
        /\ hold[c] \subseteq want[c]
        /\ need[c] \subseteq want[c]

(*
  Mutual exclusion of resource ownership (no resource is shared).
*)
Mutex ==
  \A c1, c2 \in CLIENTS:
    c1 # c2 => hold[c1] \cap hold[c2] = {}

UniqueOwner ==
  \A r \in RESOURCES:
    owner[r] = Nil
    \/ (\E c \in CLIENTS:
          /\ owner[r] = c
          /\ \A d \in CLIENTS: owner[r] = d => d = c)

Free(r) == owner[r] = Nil

(*
  Initialization: no client holds or needs anything; no outstanding wants; all resources free.
*)
Init ==
  /\ hold = [c \in CLIENTS |-> {}]
  /\ need = [c \in CLIENTS |-> {}]
  /\ want = [c \in CLIENTS |-> {}]
  /\ owner = [r \in RESOURCES |-> Nil]

(*
  Request: a client issues a request S only when idle: currently holds nothing and has no unsatisfied request.
  The request can be partially satisfied over time.
*)
Request(c, S) ==
  /\ c \in CLIENTS
  /\ S \subseteq RESOURCES
  /\ hold[c] = {}
  /\ need[c] = {}
  /\ want' = [want EXCEPT ![c] = S]
  /\ need' = [need EXCEPT ![c] = S]
  /\ UNCHANGED << hold, owner >>

(*
  Serve: grant a resource r to client c if r is free and c still needs it.
*)
Serve(c, r) ==
  /\ c \in CLIENTS
  /\ r \in RESOURCES
  /\ r \in need[c]
  /\ Free(r)
  /\ owner' = [owner EXCEPT ![r] = c]
  /\ hold' = [hold EXCEPT ![c] = hold[c] \cup {r}]
  /\ need' = [need EXCEPT ![c] = need[c] \ {r}]
  /\ UNCHANGED want

(*
  Return: client c returns some non-empty subset X of resources it currently holds.
  Returns can happen even before the current request is fully satisfied.
*)
ReturnSome(c) ==
  /\ c \in CLIENTS
  /\ hold[c] # {}
  /\ \E X \in SUBSET hold[c]:
        /\ X # {}
        /\ owner' = [r \in RESOURCES |-> IF r \in X THEN Nil ELSE owner[r]]
        /\ hold'  = [hold EXCEPT ![c] = hold[c] \ X]
        /\ UNCHANGED << need, want >>

RequestA == \E c \in CLIENTS: \E S \in SUBSET RESOURCES: Request(c, S)
ServeA   == \E c \in CLIENTS: \E r \in RESOURCES:         Serve(c, r)
ReturnA  == \E c \in CLIENTS:                              ReturnSome(c)

Next == RequestA \/ ServeA \/ ReturnA

(*
  Two temporal specifications with distinct fairness assumptions:
    - SpecWF: weak fairness for returns only
    - SpecSF: weak fairness for returns and strong fairness for each Serve(c, r)
*)
SpecWF ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A c \in CLIENTS: WF_Vars(ReturnSome(c))

SpecSF ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A c \in CLIENTS: WF_Vars(ReturnSome(c))
  /\ \A c \in CLIENTS: \A r \in RESOURCES: SF_Vars(Serve(c, r))

(*
  Default Spec alias (can be overridden by a TLC config if desired).
*)
Spec == SpecWF

(*
  Liveness predicates of interest.
*)
NoHoldInfOften(c) == []<>(hold[c] = {})
NoUnsatInfOften(c) == []<>(need[c] = {})

(*
  Under strong fairness on Serve, any individual needed resource is eventually either obtained or no longer needed.
*)
AcquireEventuallySF ==
  \A c \in CLIENTS: \A r \in RESOURCES:
    (r \in need[c]) ~> (owner[r] = c \/ r \notin need[c])

(*
  Theorems (stated as proof obligations; proofs omitted).
*)
THEOREM SpecWF => []TypeOK
THEOREM SpecWF => []Consistency
THEOREM SpecWF => []Mutex
THEOREM SpecWF => []UniqueOwner
THEOREM SpecWF => \A c \in CLIENTS: NoHoldInfOften(c)

THEOREM SpecSF => []TypeOK
THEOREM SpecSF => []Consistency
THEOREM SpecSF => []Mutex
THEOREM SpecSF => []UniqueOwner
THEOREM SpecSF => \A c \in CLIENTS: NoHoldInfOften(c)
THEOREM SpecSF => \A c \in CLIENTS: NoUnsatInfOften(c)
THEOREM SpecSF => AcquireEventuallySF

(*
  Symmetry expression (for TLC symmetry reduction).
  The set of all permutations over CLIENTS.
*)
Symmetry ==
  { pi \in [CLIENTS -> CLIENTS] :
      /\ \A x \in CLIENTS: pi[x] \in CLIENTS
      /\ \A x, y \in CLIENTS: x # y => pi[x] # pi[y]
      /\ \A y \in CLIENTS: \E x \in CLIENTS: pi[x] = y
  }

(*
  A concrete counterexample value structure:
  With two clients and a single resource, under SpecWF (no fairness on Serve),
  a behavior can avoid serving one client forever, demonstrating that "eventual obtainment"
  need not hold without strong fairness.
*)
CEXValues ==
  [ CLIENTS |-> {"c1", "c2"},
    RESOURCES |-> {"r1"} ]

=============================================================================