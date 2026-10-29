------------------------------- MODULE MC -------------------------------
EXTENDS Naturals, FiniteSets, TLC

\* Model parameter: the set of user identifiers
const_17385913267612000 == 1..2

Users == const_17385913267612000

VARIABLES pc, owner

vars == <<pc, owner>>

States == {"idle", "waiting", "critical"}

\* ------------------------------------------------------------------
\* Multi-user system: users compete for a single shared resource
\* ------------------------------------------------------------------

TypeOK ==
    /\ pc \in [Users -> States]
    /\ owner \in Users \cup {0}

Init ==
    /\ pc = [u \in Users |-> "idle"]
    /\ owner = 0

Request(u) ==
    /\ pc[u] = "idle"
    /\ pc' = [pc EXCEPT ![u] = "waiting"]
    /\ UNCHANGED owner

Enter(u) ==
    /\ pc[u] = "waiting"
    /\ owner = 0
    /\ pc' = [pc EXCEPT ![u] = "critical"]
    /\ owner' = u

Exit(u) ==
    /\ pc[u] = "critical"
    /\ pc' = [pc EXCEPT ![u] = "idle"]
    /\ owner' = 0

Next == \E u \in Users : Request(u) \/ Enter(u) \/ Exit(u)

Fairness ==
    \A u \in Users : /\ WF_vars(Exit(u))
                     /\ SF_vars(Enter(u))

Spec == Init /\ [][Next]_vars /\ Fairness

\* ------------------------------------------------------------------
\* Safety invariants
\* ------------------------------------------------------------------

MutualExclusion ==
    \A u, v \in Users : (pc[u] = "critical" /\ pc[v] = "critical") => u = v

OwnerConsistent ==
    \A u \in Users : (pc[u] = "critical") <=> (owner = u)

\* ------------------------------------------------------------------
\* Single-user views (parameterized by user identifier p)
\* ------------------------------------------------------------------

SingleUserPInit(p) == pc[p] = "idle"

SingleUserPNext(p) ==
    \/ (pc[p] = "idle"     /\ pc'[p] = "waiting")
    \/ (pc[p] = "waiting"  /\ pc'[p] = "critical")
    \/ (pc[p] = "critical" /\ pc'[p] = "idle")

SingleUserPLiveness(p) ==
    /\ (pc[p] = "waiting")  ~> (pc[p] = "critical")
    /\ (pc[p] = "critical") ~> (pc[p] = "idle")

SingleUserPSpec(p) ==
    /\ SingleUserPInit(p)
    /\ [][SingleUserPNext(p)]_(pc[p])
    /\ SingleUserPLiveness(p)

\* SingleUser2: the single-user view for user 2
SingleUser2Spec == SingleUserPSpec(2)

\* SingleUser3: a coarser single-user view (busy / not busy) for user 2
Busy(p) == pc[p] # "idle"

SingleUser3Spec ==
    /\ ~Busy(2)
    /\ [][Busy(2)' # Busy(2)]_(Busy(2))
    /\ []<>(~Busy(2))

\* ------------------------------------------------------------------
\* Properties checked by the model
\* ------------------------------------------------------------------

prop_SingleUser2 == SingleUser2Spec

prop_SingleUser3 == SingleUser3Spec

prop_SingleUserP2 == SingleUserPSpec(2)

prop_SingleUserP_Forall2 == \A p \in {2} : SingleUserPSpec(p)

prop_SingleUserP_Forall1 == \A p \in {1} : SingleUserPSpec(p)

StarvationFreedom ==
    \A u \in Users : (pc[u] = "waiting") ~> (pc[u] = "critical")

=============================================================================