----------------------------- MODULE ResourceAllocator -----------------------------

EXTENDS Naturals

CONSTANTS
  Clients,      \* finite, nonempty set of clients
  Resources,    \* finite, nonempty set of resources
  None          \* distinguished value not in Clients denoting a free resource

ASSUME /\ Clients # {}
       /\ Resources # {}
       /\ None \notin Clients

VARIABLES
  owner,   \* function Resources -> Clients \cup {None}
  desired  \* function Clients -> SUBSET Resources (active target set for current request)

Vars == << owner, desired >>

HeldOf(c) == { r \in Resources : owner[r] = c }
Unsatisfied(c) == desired[c] \ HeldOf(c)
NoUnsat(c) == Unsatisfied(c) = {}

TypeOK ==
  /\ owner \in [Resources -> (Clients \cup {None})]
  /\ desired \in [Clients -> SUBSET Resources]

HeldSetsDisjoint ==
  \A c1 \in Clients: \A c2 \in Clients:
    c1 # c2 => HeldOf(c1) \cap HeldOf(c2) = {}

AtMostOneOwner ==
  \A r \in Resources:
    \A c1 \in Clients: \A c2 \in Clients:
      (owner[r] = c1 /\ owner[r] = c2) => c1 = c2

SafetyInv == TypeOK /\ HeldSetsDisjoint /\ AtMostOneOwner

Init ==
  /\ owner = [r \in Resources |-> None]
  /\ desired = [c \in Clients  |-> {}]

Request(c, D) ==
  /\ c \in Clients
  /\ D \subseteq Resources
  /\ desired[c] = {}
  /\ HeldOf(c) = {}
  /\ desired' = [desired EXCEPT ![c] = D]
  /\ UNCHANGED owner

Grant(c, r) ==
  /\ c \in Clients
  /\ r \in Resources
  /\ r \in desired[c]
  /\ owner[r] = None
  /\ owner' = [owner EXCEPT ![r] = c]
  /\ UNCHANGED desired

ReturnOne(c, r) ==
  /\ c \in Clients
  /\ r \in Resources
  /\ owner[r] = c
  /\ owner' = [owner EXCEPT ![r] = None]
  /\ UNCHANGED desired

Complete(c) ==
  /\ c \in Clients
  /\ Unsatisfied(c) = {}
  /\ desired' = [desired EXCEPT ![c] = {}]
  /\ UNCHANGED owner

Next ==
  \E c \in Clients, D \in SUBSET Resources: Request(c, D)
  \/ \E c \in Clients, r \in Resources: Grant(c, r)
  \/ \E c \in Clients, r \in Resources: ReturnOne(c, r)
  \/ \E c \in Clients: Complete(c)

\* Weak-fairness-based system: grants are weakly fair.
SpecWeak ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A c \in Clients: \A r \in Resources: WF_Vars(Grant(c, r))

\* Stronger fairness system: grants strongly fair, returns weakly fair.
SpecStrong ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A c \in Clients: \A r \in Resources:
        SF_Vars(Grant(c, r)) /\ WF_Vars(ReturnOne(c, r))

\* Default Spec alias (may be switched as needed).
Spec == SpecWeak

\* Liveness properties of interest

\* Eventual return: any held resource is eventually returned (at least once).
EventualReturn ==
  \A c \in Clients: \A r \in Resources: [](owner[r] = c => <> owner[r] = None)

\* Eventual obtainment: any requested resource is eventually either granted or no longer requested.
EventualObtainment ==
  \A c \in Clients: \A r \in Resources:
    [] (r \in desired[c] => <> (owner[r] = c \/ r \notin desired[c]))

\* Infinitely often, a client has no outstanding unsatisfied request.
InfOftenNoUnsat ==
  \A c \in Clients: []<> NoUnsat(c)

\* Symmetry expression (client permutations)
IsBijection(S, T, f) ==
  /\ f \in [S -> T]
  /\ \A x \in S: \A y \in S: x # y => f[x] # f[y]
  /\ \A t \in T: \E s \in S: f[s] = t

ClientSymmetry ==
  { pi \in [Clients -> Clients] : IsBijection(Clients, Clients, pi) }

Symmetry == ClientSymmetry

\* A concrete counterexample value structure (example constant assignment record)
CEX ==
  [ Clients   |-> {"c1", "c2"},
    Resources |-> {"r1", "r2"},
    None      |-> "none" ]

=============================================================================