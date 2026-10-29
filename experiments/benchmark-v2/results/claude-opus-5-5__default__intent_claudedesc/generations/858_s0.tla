---------------------------- MODULE ReadersWriters ----------------------------
(***************************************************************************)
(* Readers-writers synchronization.  A fixed number of actors request read *)
(* or write access to a shared resource.  Requests are placed in a FIFO    *)
(* queue, and only the request at the head of the queue may be granted,    *)
(* which keeps ordering fair and prevents starvation.  Any number of       *)
(* readers may hold the resource at once.  A writer holds it exclusively.  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

ASSUME NumActorsAssumption == NumActors \in Nat \ {0}

VARIABLES
    readers,   \* set of actors currently reading
    writers,   \* set of actors currently writing
    waiting    \* FIFO queue of <<"read"|"write", actor>> requests

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

ToSet(s) == { s[i] : i \in DOMAIN s }

IsRead(r)  == r[1] = "read"
IsWrite(r) == r[1] = "write"

WaitingToRead  == { r[2] : r \in ToSet(SelectSeq(waiting, IsRead)) }
WaitingToWrite == { r[2] : r \in ToSet(SelectSeq(waiting, IsWrite)) }
Waiting        == WaitingToRead \cup WaitingToWrite

Active == readers \cup writers

Idle(actor) == actor \notin Active /\ actor \notin Waiting

-----------------------------------------------------------------------------
TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \X Actors)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

-----------------------------------------------------------------------------
(* An idle actor requests read access by joining the end of the queue.     *)
TryRead(actor) ==
    /\ Idle(actor)
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

(* An idle actor requests write access by joining the end of the queue.    *)
TryWrite(actor) ==
    /\ Idle(actor)
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

(* Grant read access to the actor at the head of the queue.                *)
Read(actor) ==
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

(* Grant write access to the actor at the head of the queue.               *)
Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

(* Process the request at the head of the queue (FIFO ordering).           *)
ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET req   == Head(waiting)
           actor == req[2]
       IN  CASE req[1] = "read"  -> Read(actor)
             [] req[1] = "write" -> Write(actor)

(* An active actor releases its access.                                    *)
StopReading(actor) ==
    /\ actor \in readers
    /\ readers' = readers \ {actor}
    /\ UNCHANGED <<writers, waiting>>

StopWriting(actor) ==
    /\ actor \in writers
    /\ writers' = writers \ {actor}
    /\ UNCHANGED <<readers, waiting>>

Stop(actor) == StopReading(actor) \/ StopWriting(actor)

-----------------------------------------------------------------------------
Next ==
    \/ \E actor \in Actors : TryRead(actor) \/ TryWrite(actor)
    \/ ReadOrWrite
    \/ \E actor \in Actors : Stop(actor)

Fairness ==
    /\ WF_vars(ReadOrWrite)
    /\ \A actor \in Actors : WF_vars(Stop(actor))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties                                                       *)

\* Readers and writers never hold the resource at the same time.
Safety == ~(readers /= {} /\ writers /= {})

\* At most one writer holds the resource at any time.
WriterExclusivity == Cardinality(writers) <= 1

\* A writer excludes every other actor.
WriterExclusive ==
    \A w \in writers : Active = {w}

\* No actor is both waiting and active, and no actor waits twice.
WellFormedQueue ==
    /\ Waiting \cap Active = {}
    /\ WaitingToRead \cap WaitingToWrite = {}
    /\ \A i, j \in DOMAIN waiting : i /= j => waiting[i][2] /= waiting[j][2]

\* The system never deadlocks: some step is always possible.
DeadlockFree == ENABLED Next

Invariants ==
    /\ TypeOK
    /\ Safety
    /\ WriterExclusivity
    /\ WriterExclusive
    /\ WellFormedQueue

-----------------------------------------------------------------------------
(* Liveness properties                                                     *)

\* Every actor that requests access is eventually granted it.
NoStarvationReaders ==
    \A actor \in Actors : (actor \in WaitingToRead) ~> (actor \in readers)

NoStarvationWriters ==
    \A actor \in Actors : (actor \in WaitingToWrite) ~> (actor \in writers)

NoStarvation == NoStarvationReaders /\ NoStarvationWriters

\* The queue is always processed: a non-empty queue eventually shrinks
\* by serving its head, and every active actor eventually releases access.
Progress ==
    /\ \A actor \in Actors : (actor \in Waiting) ~> (actor \in Active)
    /\ \A actor \in Actors : (actor \in Active) ~> (actor \notin Active)

Liveness == NoStarvation /\ Progress

THEOREM Spec => []Invariants
THEOREM Spec => Liveness
=============================================================================