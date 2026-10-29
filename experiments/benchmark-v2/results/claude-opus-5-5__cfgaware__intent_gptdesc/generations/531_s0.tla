---------------------------- MODULE SessionManager ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MSet,   \* finite set of clients
          NSet    \* fixed universe of session identifiers

\* Concrete values used by the model-checking configuration
ConstMSet == {"c1", "c2", "c3"}
ConstNSet == {"s1", "s2"}

None == "none"

ASSUME None \notin MSet /\ None \notin NSet

VARIABLES owner,   \* owner[s] : client holding session s, or None
          pc,      \* pc[c]    : control state of client c
          sess     \* sess[c]  : session held by client c, or None

vars == <<owner, pc, sess>>

States == {"idle", "waiting", "holding", "done"}

TypeOK ==
    /\ owner \in [NSet -> MSet \cup {None}]
    /\ pc \in [MSet -> States]
    /\ sess \in [MSet -> NSet \cup {None}]

Init ==
    /\ owner = [s \in NSet |-> None]
    /\ pc = [c \in MSet |-> "idle"]
    /\ sess = [c \in MSet |-> None]

FreeSessions == {s \in NSet : owner[s] = None}
HeldSessions == {s \in NSet : owner[s] # None}

\* Nondeterministic request arrival
Request(c) ==
    /\ pc[c] = "idle"
    /\ pc' = [pc EXCEPT ![c] = "waiting"]
    /\ UNCHANGED <<owner, sess>>

\* Grant a free session to a waiting client
Acquire(c, s) ==
    /\ pc[c] = "waiting"
    /\ owner[s] = None
    /\ owner' = [owner EXCEPT ![s] = c]
    /\ sess' = [sess EXCEPT ![c] = s]
    /\ pc' = [pc EXCEPT ![c] = "holding"]

AcquireAny(c) == \E s \in NSet : Acquire(c, s)

\* Client uses the session and signals completion
Use(c) ==
    /\ pc[c] = "holding"
    /\ pc' = [pc EXCEPT ![c] = "done"]
    /\ UNCHANGED <<owner, sess>>

\* Session returns to the pool for reuse
Release(c) ==
    /\ pc[c] = "done"
    /\ sess[c] # None
    /\ owner' = [owner EXCEPT ![sess[c]] = None]
    /\ sess' = [sess EXCEPT ![c] = None]
    /\ pc' = [pc EXCEPT ![c] = "idle"]

Next ==
    \E c \in MSet :
        \/ Request(c)
        \/ AcquireAny(c)
        \/ Use(c)
        \/ Release(c)

Fairness ==
    \A c \in MSet :
        /\ SF_vars(AcquireAny(c))
        /\ WF_vars(Use(c))
        /\ WF_vars(Release(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

MutualExclusion ==
    \A c1, c2 \in MSet :
        (c1 # c2 /\ sess[c1] # None) => sess[c1] # sess[c2]

Validity ==
    /\ \A c \in MSet : sess[c] \in NSet \cup {None}
    /\ \A s \in NSet : owner[s] \in MSet \cup {None}

NoDuplication ==
    /\ HeldSessions \subseteq NSet
    /\ \A s \in NSet : owner[s] # None => sess[owner[s]] = s
    /\ \A c \in MSet : sess[c] # None => owner[sess[c]] = c

CardinalityBound ==
    /\ Cardinality(HeldSessions) <= Cardinality(NSet)
    /\ Cardinality({c \in MSet : sess[c] # None}) = Cardinality(HeldSessions)

Consistency ==
    \A c \in MSet : (pc[c] \in {"holding", "done"}) <=> (sess[c] # None)

DeadlockFree == ENABLED Next

Inv ==
    /\ TypeOK
    /\ MutualExclusion
    /\ Validity
    /\ NoDuplication
    /\ CardinalityBound
    /\ Consistency

-----------------------------------------------------------------------------
\* Liveness properties

Progress ==
    \A c \in MSet : (pc[c] = "waiting") ~> (pc[c] = "holding")

Reusability ==
    \A s \in NSet : (owner[s] # None) ~> (owner[s] = None)

=============================================================================