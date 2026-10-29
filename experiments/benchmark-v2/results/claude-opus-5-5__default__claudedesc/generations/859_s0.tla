---------------------------- MODULE MC_ReadersWriters ----------------------------
(***************************************************************************)
(* Model-checking configuration for the Readers-Writers specification,     *)
(* made self-contained so that it can be parsed on its own.                *)
(*                                                                         *)
(* The configuration fixes the number of actors to n = 3 and binds it to   *)
(* the constant NumActors of the ReadersWriters specification. In the TLC  *)
(* config file this is written as:                                         *)
(*                                                                         *)
(*     CONSTANT NumActors <- n                                             *)
(*     SPECIFICATION Spec                                                  *)
(*     INVARIANT TypeOK Safety                                             *)
(*     PROPERTY Liveness                                                   *)
(*                                                                         *)
(* The following invariants are intentionally violated. They are checked   *)
(* only to explore behaviours that the system permits, not properties it   *)
(* guarantees:                                                             *)
(*     ReadersBound        == Cardinality(readers) <= 1                    *)
(*     WaitingWritersBound == Cardinality(WaitingToWrite) <= 1             *)
(*     NoMixedWaiting      == ~(WaitingToRead # {} /\ WaitingToWrite # {}) *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT NumActors

\* Concrete model value used by the configuration (NumActors <- n).
n == 3

ASSUME NumActorsAssumption == NumActors \in Nat \ {0}

VARIABLES
    readers,   \* set of actors currently reading
    writers,   \* set of actors currently writing
    waiting    \* queue of <<kind, actor>> requests, kind \in {"read","write"}

vars == <<readers, writers, waiting>>

Actors == 1..NumActors

ToSet(s) == { s[i] : i \in DOMAIN s }

read(s)  == s[1] = "read"
write(s) == s[1] = "write"

WaitingToRead  == { p[2] : p \in ToSet(SelectSeq(waiting, read)) }
WaitingToWrite == { p[2] : p \in ToSet(SelectSeq(waiting, write)) }

---------------------------------------------------------------------------

TypeOK ==
    /\ readers \subseteq Actors
    /\ writers \subseteq Actors
    /\ waiting \in Seq({"read", "write"} \X Actors)

Init ==
    /\ readers = {}
    /\ writers = {}
    /\ waiting = << >>

\* An actor asks to read (at most one pending read request per actor).
TryRead(actor) ==
    /\ actor \notin WaitingToRead
    /\ waiting' = Append(waiting, <<"read", actor>>)
    /\ UNCHANGED <<readers, writers>>

\* An actor asks to write (at most one pending write request per actor).
TryWrite(actor) ==
    /\ actor \notin WaitingToWrite
    /\ waiting' = Append(waiting, <<"write", actor>>)
    /\ UNCHANGED <<readers, writers>>

\* Grant a read access to the actor at the head of the queue.
Read(actor) ==
    /\ readers' = readers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED writers

\* Grant exclusive write access to the actor at the head of the queue.
Write(actor) ==
    /\ readers = {}
    /\ writers' = writers \union {actor}
    /\ waiting' = Tail(waiting)
    /\ UNCHANGED readers

\* Serve the request at the head of the waiting queue.
ReadOrWrite ==
    /\ waiting # << >>
    /\ writers = {}
    /\ LET pair  == Head(waiting)
           actor == pair[2]
       IN  CASE pair[1] = "read"  -> Read(actor)
             [] pair[1] = "write" -> Write(actor)

\* An active actor releases the resource.
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
    /\ SF_vars(ReadOrWrite)
    /\ \A actor \in Actors : WF_vars(StopActivity(actor))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Properties                                                              *)
---------------------------------------------------------------------------

\* Readers and writers never access the resource simultaneously, and
\* there is never more than one writer.
Safety ==
    /\ ~(readers # {} /\ writers # {})
    /\ Cardinality(writers) <= 1

\* Every actor waiting to read eventually reads, and every actor waiting
\* to write eventually writes.
Liveness ==
    /\ \A actor \in Actors : (actor \in WaitingToRead)  ~> (actor \in readers)
    /\ \A actor \in Actors : (actor \in WaitingToWrite) ~> (actor \in writers)

---------------------------------------------------------------------------
(* Exploratory invariants, expected to be VIOLATED by the model checker.   *)
---------------------------------------------------------------------------

ReadersBound        == Cardinality(readers) <= 1
WaitingWritersBound == Cardinality(WaitingToWrite) <= 1
NoMixedWaiting      == ~(WaitingToRead # {} /\ WaitingToWrite # {})

THEOREM Spec => [](TypeOK /\ Safety)
THEOREM Spec => Liveness
=============================================================================