--------------------------- MODULE ReadersWriters ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS NumActors, n

ASSUME NumActors \in Nat \ {0}
ASSUME n \in Nat

VARIABLES readers, writers, waiting

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

ToSet(s) == { s[i] : i \in DOMAIN s }

WaitingActors == { p[2] : p \in ToSet(waiting) }

Active == readers \cup writers

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \X Actors)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = <<>>

TryRead(actor) ==
    /\ actor \notin WaitingActors
    /\ actor \notin Active
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

TryWrite(actor) ==
    /\ actor \notin WaitingActors
    /\ actor \notin Active
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

Read(actor) ==
    /\ readers' = readers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \cup {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

ReadOrWrite ==
    /\ waiting /= <<>>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN CASE pair[1] = "read"  -> Read(actor)
            [] pair[1] = "write" -> Write(actor)

StopActivity(actor) ==
    /\ actor \in Active
    /\ readers' = readers \ {actor}
    /\ writers' = writers \ {actor}
    /\ UNCHANGED waiting

Next ==
    \/ ReadOrWrite
    \/ \E actor \in Actors : TryRead(actor) \/ TryWrite(actor) \/ StopActivity(actor)

Fairness ==
    /\ WF_vars(ReadOrWrite)
    /\ \A actor \in Actors : WF_vars(StopActivity(actor))

Spec == Init /\ [][Next]_vars /\ Fairness

Safety ==
    /\ Cardinality(writers) <= 1
    /\ (writers /= {} => readers = {})
    /\ readers \cap writers = {}

Liveness ==
    \A actor \in Actors :
        (actor \in WaitingActors) ~> (actor \in readers \cup writers)

=============================================================================