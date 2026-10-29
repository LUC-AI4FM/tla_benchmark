--------------------------- MODULE MCReadersWriters ---------------------------
(***************************************************************************)
(* Apalache-compatible, type-annotated readers-writers specification.      *)
(* The behavior matches the ReadersWriters module. It is written inline    *)
(* here so that the module parses on its own, without the separate file.   *)
(***************************************************************************)
EXTENDS FiniteSets, Naturals, Sequences

CONSTANT
    \* @type: Int;
    NumActors

VARIABLES
    \* @type: Set(Int);
    readers,
    \* @type: Set(Int);
    writers,
    \* @type: Seq(<<Str, Int>>);
    waiting

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

\* Helper operators, redefined with explicit Apalache type annotations

\* @type: Seq(<<Str, Int>>) => Set(<<Str, Int>>);
ToSet(s) == { s[i] : i \in DOMAIN s }

\* @type: <<Str, Int>> => Bool;
read(s) == s[1] = "read"

\* @type: <<Str, Int>> => Bool;
write(s) == s[1] = "write"

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \X Actors)

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
    /\ \A actor \in Actors : WF_vars(StopActivity(actor))

Spec == Init /\ [][Next]_vars /\ Fairness

Safety ==
    /\ ~(readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

===============================================================================