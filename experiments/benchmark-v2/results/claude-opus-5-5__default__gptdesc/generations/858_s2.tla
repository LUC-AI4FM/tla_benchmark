-------------------------- MODULE APAReadersWriters --------------------------
(***************************************************************************)
(* Apalache-typed wrapper for the Readers-Writers specification.          *)
(*                                                                         *)
(* In the original layout, this module declares the state variables with  *)
(* Apalache type annotations. It then redefines the polymorphic helper    *)
(* operators (ToSet, read, write) with concrete monomorphic types and      *)
(* instantiates ReadersWriters:                                            *)
(*                                                                         *)
(*     INSTANCE ReadersWriters                                             *)
(*                                                                         *)
(* Duplicate-definition trick: Apalache cannot type the generic helper    *)
(* operators of the original module. We therefore define operators with   *)
(* the same names and identical bodies here, annotated with monomorphic   *)
(* types. Because the bodies are identical, the semantics are preserved.  *)
(*                                                                         *)
(* This version must pass SANY without the external ReadersWriters        *)
(* module. For that reason, the instantiated definitions are inlined      *)
(* below rather than imported.                                             *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
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

(***************************************************************************)
(* Typed helper operators. These are the duplicate definitions; their     *)
(* bodies are identical to those in ReadersWriters.                       *)
(***************************************************************************)

\* @type: Seq(<<Str, Int>>) => Set(<<Str, Int>>);
ToSet(s) == { s[i] : i \in DOMAIN s }

\* @type: <<Str, Int>> => Bool;
read(s) == s[1] = "read"

\* @type: <<Str, Int>> => Bool;
write(s) == s[1] = "write"

(***************************************************************************)
(* Body of ReadersWriters (inlined in place of INSTANCE ReadersWriters).  *)
(***************************************************************************)

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \X Actors)

Safety ==
    /\ ~(readers /= {} /\ writers /= {})
    /\ Cardinality(writers) <= 1

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
       IN  CASE pair[1] = "read"  -> Read(actor)
             [] pair[1] = "write" -> Write(actor)

StopActivity(actor) ==
    IF actor \in readers
    THEN /\ readers' = readers \ {actor}
         /\ UNCHANGED <<writers, waiting>>
    ELSE /\ writers' = writers \ {actor}
         /\ UNCHANGED <<readers, waiting>>

Stop == \E actor \in readers \cup writers : StopActivity(actor)

Next ==
    \/ \E actor \in Actors : TryRead(actor) \/ TryWrite(actor)
    \/ ReadOrWrite
    \/ Stop

Spec == Init /\ [][Next]_vars

Fairness ==
    /\ \A actor \in Actors : WF_vars(TryRead(actor))
    /\ \A actor \in Actors : WF_vars(TryWrite(actor))
    /\ WF_vars(ReadOrWrite)
    /\ \A actor \in Actors : WF_vars(StopActivity(actor))

FairSpec == Spec /\ Fairness

AllReadersEventuallyRead  == \A actor \in Actors : []<>(actor \in readers)
AllWritersEventuallyWrite == \A actor \in Actors : []<>(actor \in writers)

Liveness == AllReadersEventuallyRead /\ AllWritersEventuallyWrite

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM FairSpec => Liveness
=============================================================================