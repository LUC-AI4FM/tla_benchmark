------------------------------ MODULE ReadersWriters ------------------------------
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT NumActors

ASSUME NumActors \in Nat \ {0}

VARIABLES
    readers,   \* set of actors currently reading
    writers,   \* set of actors currently writing
    waiting    \* FIFO queue of pending requests <<kind, actor>>

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

ToSet(s) == { s[i] : i \in DOMAIN s }

read(s)  == s[1] = "read"
write(s) == s[1] = "write"

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

-----------------------------------------------------------------------------

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \X Actors)

\* Queue well-formedness: no duplicate identical requests in the queue
QueueOK ==
    \A i, j \in DOMAIN waiting : (i # j) => waiting[i] # waiting[j]

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

-----------------------------------------------------------------------------
\* Actions

TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

Read(actor) ==
    /\ readers' = readers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

\* Serve the front of the queue. Consecutive read requests at the front can be
\* granted by repeated steps as long as no writer is active.
ReadOrWrite ==
    /\ waiting # <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN CASE pair[1] = "read"  -> Read(actor)
            [] pair[1] = "write" -> Write(actor)

StopActivity(actor) ==
    /\ actor \in readers \union writers
    /\ IF actor \in readers
       THEN /\ readers' = readers \ {actor}
            /\ UNCHANGED <<writers, waiting>>
       ELSE /\ writers' = writers \ {actor}
            /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in readers \union writers : StopActivity(actor)

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

-----------------------------------------------------------------------------

Fairness ==
    /\ \A actor \in Actors : SF_vars(TryRead(actor))
    /\ \A actor \in Actors : SF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ \A actor \in Actors : WF_vars(StopActivity(actor))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Properties

Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

\* Every pending request is eventually served (no starvation)
NoStarvation ==
    \A actor \in Actors :
        /\ (actor \in WaitingToRead)  ~> (actor \in readers)
        /\ (actor \in WaitingToWrite) ~> (actor \in writers)

=============================================================================