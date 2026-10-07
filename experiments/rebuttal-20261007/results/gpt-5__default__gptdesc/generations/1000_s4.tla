------------------------------- MODULE ResourceAllocator -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
    Clients,        \* Finite, nonempty set of clients
    Resources,      \* Finite, nonempty set of resources
    None            \* Distinguished non-client denoting "unowned"

ASSUME
    /\ None \notin Clients
    /\ Finite(Clients) /\ Clients # {}
    /\ Finite(Resources) /\ Resources # {}

VARIABLES
    owner,          \* function Resources -> (Clients \cup {None})
    req             \* function Clients -> SUBSET Resources (the client's current request)

vars == << owner, req >>

\* Derived state functions
Hold(c)  == { r \in Resources : owner[r] = c }
Unsat(c) == req[c] \ Hold(c)

\* Type correctness
TypeOK ==
    /\ owner \in [Resources -> (Clients \cup {None})]
    /\ req   \in [Clients  -> SUBSET Resources]

\* Initial state: no ownership, no requests
Init ==
    /\ owner = [r \in Resources |-> None]
    /\ req   = [c \in Clients  |-> {}]
    /\ TypeOK

\* Actions
IssueReq(c) ==
    /\ c \in Clients
    /\ Hold(c) = {}
    /\ Unsat(c) = {}
    /\ \E S \in SUBSET Resources :
         /\ S # {}
         /\ req' = [req EXCEPT ![c] = S]
    /\ UNCHANGED owner

ClearReq(c) ==
    /\ c \in Clients
    /\ Unsat(c) = {}
    /\ req[c] # {}
    /\ req' = [req EXCEPT ![c] = {}]
    /\ UNCHANGED owner

GrantOne(c, r) ==
    /\ c \in Clients /\ r \in Resources
    /\ r \in req[c]
    /\ owner[r] = None
    /\ owner' = [owner EXCEPT ![r] = c]
    /\ UNCHANGED req

ReturnOne(c, r) ==
    /\ c \in Clients /\ r \in Resources
    /\ owner[r] = c
    /\ owner' = [owner EXCEPT ![r] = None]
    /\ UNCHANGED req

Next ==
    \/ \E c \in Clients : IssueReq(c)
    \/ \E c \in Clients : ClearReq(c)
    \/ \E c \in Clients : \E r \in Resources : GrantOne(c, r)
    \/ \E c \in Clients : \E r \in Resources : ReturnOne(c, r)

\* Safety invariants
MutualExcl ==
    \A c \in Clients : \A d \in Clients :
        c # d => Hold(c) \cap Hold(d) = {}

\* Liveness properties
EventuallyReturned ==
    \A c \in Clients : \A r \in Resources :
        [](owner[r] = c => <> (owner[r] = None))

EventuallyObtained ==
    \A c \in Clients : \A r \in Resources :
        [](r \in req[c] => <> (owner[r] = c))

InfOftenNoUnsat ==
    []<>(\A c \in Clients : Unsat(c) = {})

\* Two temporal system specifications with different fairness assumptions
FairWeak ==
    \A c \in Clients : \A r \in Resources : WF_vars(ReturnOne(c, r))

FairStrong ==
    /\ \A c \in Clients : \A r \in Resources : WF_vars(ReturnOne(c, r))
    /\ \A c \in Clients : \A r \in Resources : SF_vars(GrantOne(c, r))

SpecWeak  == Init /\ [][Next]_vars /\ FairWeak
SpecStrong == Init /\ [][Next]_vars /\ FairStrong

\* Theorems to be checked (by TLC or proved in TLAPS)
THEOREM SpecWeak => []TypeOK
THEOREM SpecWeak => []MutualExcl
THEOREM SpecWeak => EventuallyReturned

THEOREM SpecStrong => []TypeOK
THEOREM SpecStrong => []MutualExcl
THEOREM SpecStrong => EventuallyReturned
THEOREM SpecStrong => EventuallyObtained
THEOREM SpecStrong => InfOftenNoUnsat

\* A symmetry expression (set of permutations of Clients)
IsPermutation(p) ==
    /\ p \in [Clients -> Clients]
    /\ \A c1 \in Clients : \A c2 \in Clients :
         c1 # c2 => p[c1] # p[c2]
    /\ \A d \in Clients : \E c \in Clients : p[c] = d

SymmetryPerms == { p \in [Clients -> Clients] : IsPermutation(p) }

\* A concrete counterexample value structure (not binding the constants)
CE_Clients   == {"A", "B"}
CE_Resources == {"r"}
CE_None      == "None"
CEX == [Clients |-> CE_Clients, Resources |-> CE_Resources, None |-> CE_None]

\* Default exported specification (choose one in the model or config)
Spec == SpecWeak

=============================================================================