--------------------------- MODULE APAReadersWriters ---------------------------
(***************************************************************************)
(* Apalache-specific wrapper for the readers-writers specification.        *)
(*                                                                         *)
(* The original wrapper redefines a few polymorphic helper operators with  *)
(* concrete monomorphic type annotations and then instantiates the         *)
(* ReadersWriters module. Apalache needs these operators to have a single  *)
(* concrete type.                                                          *)
(*                                                                         *)
(* NOTE: This is a duplicate-definition trick. The operator bodies below   *)
(* are identical to those in ReadersWriters; only the type annotations     *)
(* are added. The definitions of ReadersWriters are inlined here so the    *)
(* module is self-contained and parses on its own. The behavior is the     *)
(* same as INSTANCE ReadersWriters.                                        *)
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

(***************************************************************************)
(* Helper operators with monomorphic types (duplicate definitions that     *)
(* keep the operator bodies identical to those in ReadersWriters).         *)
(***************************************************************************)

\* @type: Seq(<<Str, Int>>) => Set(<<Str, Int>>);
ToSet(s) == { s[i] : i \in DOMAIN s }

\* @type: <<Str, Int>> => Bool;
read(s) == s[1] = "read"

\* @type: <<Str, Int>> => Bool;
write(s) == s[1] = "write"

(***************************************************************************)
(* Body of ReadersWriters (equivalent to INSTANCE ReadersWriters).         *)
(***************************************************************************)

Actors == 1..NumActors

WaitingToRead == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }

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

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in readers \union writers : StopActivity(actor)

Next ==
    \E actor \in Actors :
        \/ TryRead(actor)
        \/ TryWrite(actor)
        \/ ReadOrWrite
        \/ Stop

Spec == Init /\ [][Next]_vars

Safety ==
    /\ ~(readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

=============================================================================