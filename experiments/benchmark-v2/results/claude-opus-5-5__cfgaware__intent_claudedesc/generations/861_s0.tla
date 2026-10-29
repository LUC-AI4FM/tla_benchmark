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

----------------------------------------------------------------------------

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \X Actors)

Safety ==
    /\ ~(readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

----------------------------------------------------------------------------

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

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

ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN CASE pair[1] = "read"  -> Read(actor)
            [] pair[1] = "write" -> Write(actor)

Stop(actor) ==
    /\ actor \in readers \union writers
    /\ IF actor \in readers
       THEN /\ readers' = readers \ {actor}
            /\ UNCHANGED <<writers, waiting>>
       ELSE /\ writers' = writers \ {actor}
            /\ UNCHANGED <<readers, waiting>>

Next ==
    \/ \E actor \in Actors : TryRead(actor)
    \/ \E actor \in Actors : TryWrite(actor)
    \/ ReadOrWrite
    \/ \E actor \in readers \union writers : Stop(actor)

Fairness ==
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ \A actor \in Actors : WF_vars(Stop(actor))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

THEOREM Spec => [](TypeOK /\ Safety)

=============================================================================