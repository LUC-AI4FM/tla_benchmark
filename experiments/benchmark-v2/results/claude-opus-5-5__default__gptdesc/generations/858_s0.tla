------------------------- MODULE APAReadersWriters -------------------------
(***************************************************************************)
(* Apalache type annotations for the readers-writers specification.       *)
(*                                                                         *)
(* Apalache needs monomorphic types for the helper operators. The original *)
(* ReadersWriters module defines polymorphic helpers. This module          *)
(* redefines them with concrete types. The operator bodies are kept        *)
(* identical to the originals.                                             *)
(*                                                                         *)
(* NOTE: The original wrapper ends with "INSTANCE ReadersWriters". The     *)
(* definitions below are duplicates of the originals; this is the trick    *)
(* that satisfies Apalache. TLA+ allows a re-definition through INSTANCE   *)
(* when the bodies are identical. So that this file parses with SANY on    *)
(* its own, the content of ReadersWriters is inlined below, using these    *)
(* typed helpers.                                                          *)
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

-----------------------------------------------------------------------------
(* Typed helper operators (duplicate definitions with identical bodies).   *)

\* @type: (<<Str, Int>>) => Bool;
is_read(p) == p[1] = "read"

\* @type: (<<Str, Int>>) => Bool;
is_write(p) == p[1] = "write"

\* @type: (Seq(<<Str, Int>>)) => Set(<<Str, Int>>);
ToSet(s) == { s[i] : i \in DOMAIN s }

-----------------------------------------------------------------------------
(* Readers-writers behaviour (inlined body of the ReadersWriters module).  *)

Actors == 1..NumActors

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, is_read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, is_write)) }

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
       IN CASE is_read(pair)  -> Read(actor)
            [] is_write(pair) -> Write(actor)

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in readers \union writers : StopActivity(actor)

Next ==
    \/ \E actor \in Actors : TryRead(actor) \/ TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Fairness ==
    /\ WF_vars(ReadOrWrite)
    /\ WF_vars(Stop)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties.                                                             *)

Safety ==
    /\ ~(readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

Liveness ==
    /\ \A actor \in Actors : []<>(actor \in readers)
    /\ \A actor \in Actors : []<>(actor \in writers)
    /\ \A actor \in Actors : []<>(actor \notin readers)
    /\ \A actor \in Actors : []<>(actor \notin writers)

THEOREM Spec => [](TypeOK /\ Safety)
=============================================================================