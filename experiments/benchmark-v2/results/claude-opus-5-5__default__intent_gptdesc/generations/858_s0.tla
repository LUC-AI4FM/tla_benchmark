---------------------------- MODULE ReadersWriters ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Actors

ASSUME ActorsFinite == IsFiniteSet(Actors) /\ Actors # {}

VARIABLES
    requests,
    waiting,
    readers,
    writers

vars == <<requests, waiting, readers, writers>>

Modes      == {"read", "write"}
NoRequest  == "none"

WaitingSet == { waiting[i] : i \in 1..Len(waiting) }
Holders    == readers \cup writers
Requesters == { a \in Actors : requests[a] # NoRequest }

-----------------------------------------------------------------------------
TypeOK ==
    /\ requests \in [Actors -> Modes \cup {NoRequest}]
    /\ waiting \in Seq(Actors)
    /\ Len(waiting) <= Cardinality(Actors)
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors

-----------------------------------------------------------------------------
Init ==
    /\ requests = [a \in Actors |-> NoRequest]
    /\ waiting  = << >>
    /\ readers  = {}
    /\ writers  = {}

Request(a, m) ==
    /\ requests[a] = NoRequest
    /\ a \notin Holders
    /\ a \notin WaitingSet
    /\ requests' = [requests EXCEPT ![a] = m]
    /\ waiting'  = Append(waiting, a)
    /\ UNCHANGED <<readers, writers>>

GrantRead ==
    /\ waiting # << >>
    /\ LET a == Head(waiting) IN
         /\ requests[a] = "read"
         /\ writers = {}
         /\ readers' = readers \cup {a}
         /\ waiting' = Tail(waiting)
    /\ UNCHANGED <<requests, writers>>

GrantWrite ==
    /\ waiting # << >>
    /\ LET a == Head(waiting) IN
         /\ requests[a] = "write"
         /\ readers = {}
         /\ writers = {}
         /\ writers' = {a}
         /\ waiting' = Tail(waiting)
    /\ UNCHANGED <<requests, readers>>

ReleaseRead(a) ==
    /\ a \in readers
    /\ readers'  = readers \ {a}
    /\ requests' = [requests EXCEPT ![a] = NoRequest]
    /\ UNCHANGED <<waiting, writers>>

ReleaseWrite(a) ==
    /\ a \in writers
    /\ writers'  = writers \ {a}
    /\ requests' = [requests EXCEPT ![a] = NoRequest]
    /\ UNCHANGED <<waiting, readers>>

Next ==
    \/ \E a \in Actors, m \in Modes : Request(a, m)
    \/ GrantRead
    \/ GrantWrite
    \/ \E a \in Actors : ReleaseRead(a)
    \/ \E a \in Actors : ReleaseWrite(a)

Fairness ==
    /\ WF_vars(GrantRead)
    /\ WF_vars(GrantWrite)
    /\ \A a \in Actors : WF_vars(ReleaseRead(a))
    /\ \A a \in Actors : WF_vars(ReleaseWrite(a))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

WriterMutualExclusion == Cardinality(writers) <= 1

WriterExclusivity == writers # {} => readers = {}

HoldersSubsetRequests == Holders \subseteq Requesters

CountsConsistent ==
    /\ \A a \in readers : requests[a] = "read"
    /\ \A a \in writers : requests[a] = "write"
    /\ readers \cap writers = {}
    /\ Cardinality(Holders) = Cardinality(readers) + Cardinality(writers)
    /\ Cardinality(writers) = 1 => Cardinality(Holders) = 1

WaitingConsistent ==
    /\ \A i, j \in 1..Len(waiting) : waiting[i] = waiting[j] => i = j
    /\ WaitingSet \cap Holders = {}
    /\ WaitingSet \subseteq Requesters
    /\ Requesters = WaitingSet \cup Holders

KnownActorsOnly ==
    /\ Holders \subseteq Actors
    /\ WaitingSet \subseteq Actors
    /\ Requesters \subseteq Actors

SafetyInvariant ==
    /\ TypeOK
    /\ WriterMutualExclusion
    /\ WriterExclusivity
    /\ HoldersSubsetRequests
    /\ CountsConsistent
    /\ WaitingConsistent
    /\ KnownActorsOnly

-----------------------------------------------------------------------------
\* Liveness properties

Progress ==
    (Holders = {} /\ waiting # << >>) ~> (Holders # {})

StarvationFreedom ==
    \A a \in Actors : (a \in WaitingSet) ~> (a \in Holders)

EventualRelease ==
    \A a \in Actors : (a \in Holders) ~> (a \notin Holders)

-----------------------------------------------------------------------------
THEOREM Spec => []SafetyInvariant
THEOREM Spec => Progress /\ StarvationFreedom /\ EventualRelease

=============================================================================