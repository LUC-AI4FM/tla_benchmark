--------------------------- MODULE ReadersWriters ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

ASSUME NumActorsAssumption == NumActors \in Nat \ {0}

VARIABLES readers,  \* set of actors currently reading
          writers,  \* set of actors currently writing
          waiting   \* queue of <<kind, actor>> requests waiting for access

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

ToSet(s) == { s[i] : i \in DOMAIN s }

IsRead(p)  == p[1] = "read"
IsWrite(p) == p[1] = "write"

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, IsRead)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, IsWrite)) }

----------------------------------------------------------------------------
\* Type invariant

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \X Actors)

----------------------------------------------------------------------------
\* Actions

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

\* An actor requests read access by joining the queue
TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ actor \notin readers
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

\* An actor requests write access by joining the queue
TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ actor \notin writers
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

\* Grant read access to the actor at the head of the queue
Read(actor) ==
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

\* Grant write access to the actor at the head of the queue
Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

\* Process the head of the FIFO queue
ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN CASE pair[1] = "read"  -> Read(actor)
            [] pair[1] = "write" -> Write(actor)

\* Release access
StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in readers \cup writers : StopActivity(actor)

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Fairness ==
    /\ WF_vars(ReadOrWrite)
    /\ \A actor \in Actors : WF_vars(StopActivity(actor) /\ actor \in readers \cup writers)

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
\* Safety

Safety ==
    /\ ~(readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

----------------------------------------------------------------------------
\* Liveness

AllRead  == \A actor \in Actors : []<>(actor \in readers)
AllWrite == \A actor \in Actors : []<>(actor \in writers)

NoStarvation ==
    \A actor \in Actors :
        /\ (actor \in WaitingToRead)  ~> (actor \in readers)
        /\ (actor \in WaitingToWrite) ~> (actor \in writers)

Liveness == NoStarvation

=============================================================================