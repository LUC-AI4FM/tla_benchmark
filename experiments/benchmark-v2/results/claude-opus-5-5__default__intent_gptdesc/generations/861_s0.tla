------------------------------ MODULE FairReadersWriters ------------------------------
(***************************************************************************)
(* A fair (FIFO-served) readers-writers access-control system for a       *)
(* single shared resource. A fixed finite set of actors may request read  *)
(* or write access. Requests are appended to a FIFO queue, and only the    *)
(* request at the front of the queue is considered for service.           *)
(*                                                                         *)
(*  - Several readers may hold the resource at the same time.             *)
(*  - A writer has exclusive access to the resource.                      *)
(*  - A writer is started only when no readers and no writer are active.  *)
(*  - A read request at the front is granted when no writer is active.    *)
(*    Granting it again exposes the next queued request, so a run of      *)
(*    consecutive read requests can be granted one after another, as long *)
(*    as no writer has been started.                                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT Actors

ASSUME ActorsFinite == IsFiniteSet(Actors) /\ Actors # {}

VARIABLES
    readers,   \* set of actors currently reading the resource
    writers,   \* set of actors currently writing the resource
    waiting    \* FIFO queue of pending requests <<kind, actor>>

vars == <<readers, writers, waiting>>

-----------------------------------------------------------------------------
(* Helper definitions                                                      *)
-----------------------------------------------------------------------------
Kinds    == {"read", "write"}
Requests == Kinds \X Actors

Range(s) == { s[i] : i \in DOMAIN s }

\* Read requests that are currently pending in the queue
WaitingToRead  == { p[2] : p \in { r \in Range(waiting) : r[1] = "read"  } }
\* Write requests that are currently pending in the queue
WaitingToWrite == { p[2] : p \in { r \in Range(waiting) : r[1] = "write" } }

Active == readers \cup writers

-----------------------------------------------------------------------------
(* Initial state                                                           *)
-----------------------------------------------------------------------------
Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = << >>

-----------------------------------------------------------------------------
(* Actions                                                                 *)
-----------------------------------------------------------------------------

(* Actor a asks for read access. Its request is appended to the queue.    *)
(* An actor that is active, or that already has the same request pending, *)
(* cannot enqueue it again.                                               *)
TryRead(a) ==
    /\ a \notin Active
    /\ <<"read", a>> \notin Range(waiting)
    /\ waiting' = Append(waiting, <<"read", a>>)
    /\ UNCHANGED <<readers, writers>>

(* Actor a asks for write access. The same restrictions apply.            *)
TryWrite(a) ==
    /\ a \notin Active
    /\ <<"write", a>> \notin Range(waiting)
    /\ waiting' = Append(waiting, <<"write", a>>)
    /\ UNCHANGED <<readers, writers>>

(* Grant the read request at the front of the queue. This needs no active *)
(* writer. Applying this action repeatedly grants consecutive read        *)
(* requests at the front of the queue.                                    *)
Read ==
    /\ waiting # << >>
    /\ Head(waiting)[1] = "read"
    /\ writers = {}
    /\ readers' = readers \cup {Head(waiting)[2]}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

(* Grant the write request at the front of the queue. This needs no       *)
(* active reader and no active writer.                                    *)
Write ==
    /\ waiting # << >>
    /\ Head(waiting)[1] = "write"
    /\ readers = {}
    /\ writers = {}
    /\ writers' = {Head(waiting)[2]}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

(* Serve the front of the queue. Only the front request is ever served.   *)
ServeFront == Read \/ Write

(* Actor a releases the resource.                                         *)
StopActivity(a) ==
    /\ a \in Active
    /\ readers' = readers \ {a}
    /\ writers' = writers \ {a}
    /\ UNCHANGED waiting

Next ==
    \/ \E a \in Actors : TryRead(a) \/ TryWrite(a)
    \/ ServeFront
    \/ \E a \in Actors : StopActivity(a)

-----------------------------------------------------------------------------
(* Fairness                                                                *)
(*  - Every actor holding the resource eventually releases it.            *)
(*  - The front of the queue is eventually served whenever it stays       *)
(*    servable.                                                           *)
(* Together these rule out starvation. A write request at the front       *)
(* blocks new read grants, so the active readers drain, and the write     *)
(* then becomes continuously enabled.                                     *)
-----------------------------------------------------------------------------
Fairness ==
    /\ \A a \in Actors : WF_vars(StopActivity(a))
    /\ WF_vars(ServeFront)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Type and well-formedness invariants                                    *)
-----------------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq(Requests)

\* The queue contains no duplicate entries.
QueueNoDuplicates ==
    \A i, j \in DOMAIN waiting : (i # j) => (waiting[i] # waiting[j])

\* The queue length is bounded by the number of possible distinct requests.
QueueBounded ==
    Len(waiting) <= 2 * Cardinality(Actors)

\* No active actor has a pending request.
NoActiveWaiting ==
    \A r \in Range(waiting) : r[2] \notin Active

QueueWellFormed ==
    /\ QueueNoDuplicates
    /\ QueueBounded
    /\ NoActiveWaiting

-----------------------------------------------------------------------------
(* Safety properties                                                       *)
-----------------------------------------------------------------------------
\* Readers and writers never hold the resource at the same time.
NoReadWriteConflict == ~(readers # {} /\ writers # {})

\* At most one writer holds the resource at a time.
AtMostOneWriter == Cardinality(writers) <= 1

Safety ==
    /\ TypeOK
    /\ QueueWellFormed
    /\ NoReadWriteConflict
    /\ AtMostOneWriter

-----------------------------------------------------------------------------
(* Liveness properties                                                     *)
-----------------------------------------------------------------------------

\* Every pending request eventually reaches the front of the queue.
EveryRequestReachesFront ==
    \A r \in Requests :
        (r \in Range(waiting)) ~> (waiting # << >> /\ Head(waiting) = r)

\* Every pending read request is eventually granted.
ReadersEventuallyRead ==
    \A a \in Actors : (a \in WaitingToRead) ~> (a \in readers)

\* Every pending write request is eventually granted.
WritersEventuallyWrite ==
    \A a \in Actors : (a \in WaitingToWrite) ~> (a \in writers)

\* Every actor that holds the resource eventually releases it.
EventuallyRelease ==
    \A a \in Actors : (a \in Active) ~> (a \notin Active)

\* No starvation: an actor that requests access infinitely often is
\* granted access infinitely often.
NoStarvation ==
    \A a \in Actors :
        ([]<>(a \in WaitingToRead \cup WaitingToWrite)) => ([]<>(a \in Active))

Liveness ==
    /\ EveryRequestReachesFront
    /\ ReadersEventuallyRead
    /\ WritersEventuallyWrite
    /\ EventuallyRelease
    /\ NoStarvation

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Liveness
=============================================================================