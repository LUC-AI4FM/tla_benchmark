---------------------------- MODULE ReadersWriters ----------------------------
(***************************************************************************)
(* Readers-writers synchronization.                                        *)
(*                                                                         *)
(* Processes request read or write access to a shared resource. Each       *)
(* request joins a single FIFO waiting queue. The request at the head of   *)
(* the queue is granted when that is safe:                                 *)
(*   - a read request is granted if no writer is active;                   *)
(*   - a write request is granted if no reader and no writer is active.    *)
(* An active process eventually releases the resource.                     *)
(*                                                                         *)
(* A process is in at most one place at a time: idle, waiting, reading,    *)
(* or writing.                                                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

ASSUME NumActorsAssump == NumActors \in Nat \ {0}

VARIABLES
    readers,   \* set of processes currently reading
    writers,   \* set of processes currently writing
    waiting    \* FIFO queue of requests <<"read" | "write", process>>

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

Requests == {"read", "write"} \X Actors

-----------------------------------------------------------------------------
(* Helpers *)

ToSet(s) == { s[i] : i \in DOMAIN s }

WaitingToRead  == { waiting[i][2] : i \in { j \in DOMAIN waiting : waiting[j][1] = "read" } }
WaitingToWrite == { waiting[i][2] : i \in { j \in DOMAIN waiting : waiting[j][1] = "write" } }

Waiting == WaitingToRead \cup WaitingToWrite

Active == readers \cup writers

Idle == Actors \ (Active \cup Waiting)

-----------------------------------------------------------------------------
(* Actions *)

\* An idle process requests read access.
TryRead(actor) ==
    /\ actor \in Idle
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

\* An idle process requests write access.
TryWrite(actor) ==
    /\ actor \in Idle
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

\* Grant read access to the process at the head of the queue.
Read(actor) ==
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

\* Grant write access to the process at the head of the queue.
Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

\* Serve the request at the head of the queue if it is safe to do so.
ReadOrWrite ==
    /\ waiting /= << >>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN  CASE pair[1] = "read"  -> Read(actor)
             [] pair[1] = "write" -> Write(actor)

\* An active process releases the resource.
StopActivity(actor) ==
    /\ actor \in Active
    /\ IF actor \in readers
          THEN /\ readers' = readers \ {actor}
               /\ UNCHANGED writers
          ELSE /\ writers' = writers \ {actor}
               /\ UNCHANGED readers
    /\ UNCHANGED waiting

Stop == \E actor \in Actors : StopActivity(actor)

-----------------------------------------------------------------------------
(* Specification *)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = << >>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

\* Fairness: queued requests are served when possible, and every active
\* process eventually releases the resource.
Fairness ==
    /\ WF_vars(ReadOrWrite)
    /\ \A actor \in Actors : WF_vars(StopActivity(actor))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq(Requests)
    /\ Len(waiting) <= NumActors

\* At most one writer at a time.
WriterMutex == Cardinality(writers) <= 1

\* No reader is active while a writer is active.
ReaderWriterExclusion == writers /= {} => readers = {}

\* A process is never both a reader and a writer.
NoDualRole == readers \cap writers = {}

\* A process has at most one outstanding request and is not waiting while active.
WellFormedQueue ==
    /\ \A i, j \in DOMAIN waiting : i /= j => waiting[i][2] /= waiting[j][2]
    /\ Waiting \cap Active = {}

Safety ==
    /\ TypeOK
    /\ WriterMutex
    /\ ReaderWriterExclusion
    /\ NoDualRole
    /\ WellFormedQueue

THEOREM Spec => []Safety

-----------------------------------------------------------------------------
(* Liveness properties (under Fairness) *)

\* Every process waiting to read eventually reads.
ReadersEventuallyRead ==
    \A actor \in Actors : (actor \in WaitingToRead) ~> (actor \in readers)

\* Every process waiting to write eventually writes.
WritersEventuallyWrite ==
    \A actor \in Actors : (actor \in WaitingToWrite) ~> (actor \in writers)

\* Every active process eventually releases the resource.
EventuallyRelease ==
    \A actor \in Actors : (actor \in Active) ~> (actor \notin Active)

Liveness ==
    /\ ReadersEventuallyRead
    /\ WritersEventuallyWrite
    /\ EventuallyRelease

THEOREM Spec => Liveness

-----------------------------------------------------------------------------
(* Exploration predicates.                                                 *)
(* Check the negations as invariants in TLC to obtain witness traces,      *)
(* e.g. INVARIANT NotAllReading produces a trace where all processes read. *)

AllReading        == readers = Actors
AllWaitingToWrite == WaitingToWrite = Actors
ReadersAndWritersWaiting == WaitingToRead /= {} /\ WaitingToWrite /= {}
MultipleReaders   == Cardinality(readers) > 1

NotAllReading        == ~AllReading
NotAllWaitingToWrite == ~AllWaitingToWrite
NotMixedWaiting      == ~ReadersAndWritersWaiting
NotMultipleReaders   == ~MultipleReaders

=============================================================================