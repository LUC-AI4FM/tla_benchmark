---------------------------- MODULE ReadersWriters ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

ASSUME NumActorsAssumption == NumActors \in Nat /\ NumActors >= 1

Actors == 1..NumActors

Modes == {"none", "read", "write"}

VARIABLES
    req,      \* req[a] : current request mode of actor a ("none" if idle)
    waiting,  \* queue of actors whose requests are pending
    readers,  \* set of actors currently holding read access
    writers   \* set of actors currently holding write access

vars == <<req, waiting, readers, writers>>

-----------------------------------------------------------------------------
Holders == readers \cup writers

WaitingSet == { waiting[i] : i \in 1..Len(waiting) }

Requesters == { a \in Actors : req[a] /= "none" }

RemoveFromSeq(s, x) ==
    SelectSeq(s, LAMBDA y : y /= x)

-----------------------------------------------------------------------------
TypeOK ==
    /\ req \in [Actors -> Modes]
    /\ waiting \in Seq(Actors)
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors

Init ==
    /\ req = [a \in Actors |-> "none"]
    /\ waiting = << >>
    /\ readers = {}
    /\ writers = {}

\* An idle actor issues a new read or write request; it joins the waiting queue.
Request(a, m) ==
    /\ m \in {"read", "write"}
    /\ req[a] = "none"
    /\ a \notin Holders
    /\ a \notin WaitingSet
    /\ req' = [req EXCEPT ![a] = m]
    /\ waiting' = Append(waiting, a)
    /\ UNCHANGED <<readers, writers>>

\* The request at the head of the queue is granted when compatible.
GrantRead ==
    /\ waiting /= << >>
    /\ LET a == Head(waiting) IN
         /\ req[a] = "read"
         /\ writers = {}
         /\ readers' = readers \cup {a}
         /\ waiting' = Tail(waiting)
         /\ UNCHANGED <<req, writers>>

GrantWrite ==
    /\ waiting /= << >>
    /\ LET a == Head(waiting) IN
         /\ req[a] = "write"
         /\ writers = {}
         /\ readers = {}
         /\ writers' = {a}
         /\ waiting' = Tail(waiting)
         /\ UNCHANGED <<req, readers>>

Grant == GrantRead \/ GrantWrite

\* A holder releases the resource and becomes idle (it may later reissue).
Release(a) ==
    /\ a \in Holders
    /\ readers' = readers \ {a}
    /\ writers' = writers \ {a}
    /\ req' = [req EXCEPT ![a] = "none"]
    /\ UNCHANGED waiting

Next ==
    \/ \E a \in Actors, m \in {"read", "write"} : Request(a, m)
    \/ Grant
    \/ \E a \in Actors : Release(a)

Fairness ==
    /\ WF_vars(Grant)
    /\ \A a \in Actors : WF_vars(Release(a))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety properties

WriterMutex == Cardinality(writers) <= 1

WriterExclusive == writers = {} \/ readers = {}

HoldersAreRequesters == Holders \subseteq Requesters

ModeConsistency ==
    /\ \A a \in readers : req[a] = "read"
    /\ \A a \in writers : req[a] = "write"
    /\ Cardinality(Holders) = Cardinality(readers) + Cardinality(writers)
    /\ readers \cap writers = {}

CountConsistency ==
    /\ Cardinality(writers) > 0 => Cardinality(Holders) = 1
    /\ Cardinality(Holders) <= NumActors

KnownActors ==
    /\ Holders \subseteq Actors
    /\ WaitingSet \subseteq Actors
    /\ DOMAIN req = Actors

WaitingConsistency ==
    /\ \A a \in WaitingSet : req[a] /= "none" /\ a \notin Holders
    /\ Len(waiting) = Cardinality(WaitingSet)
    /\ \A a \in Actors : req[a] /= "none" => (a \in WaitingSet \/ a \in Holders)

Safety ==
    /\ TypeOK
    /\ WriterMutex
    /\ WriterExclusive
    /\ HoldersAreRequesters
    /\ ModeConsistency
    /\ CountConsistency
    /\ KnownActors
    /\ WaitingConsistency

-----------------------------------------------------------------------------
\* Liveness properties

Progress ==
    (Holders = {} /\ WaitingSet /= {}) ~> (Holders /= {})

StarvationFreedom ==
    \A a \in Actors : (a \in WaitingSet) ~> (a \in Holders)

EventualRelease ==
    \A a \in Actors : (a \in Holders) ~> (a \notin Holders)

Liveness == Progress /\ StarvationFreedom /\ EventualRelease

THEOREM Spec => []Safety
=============================================================================