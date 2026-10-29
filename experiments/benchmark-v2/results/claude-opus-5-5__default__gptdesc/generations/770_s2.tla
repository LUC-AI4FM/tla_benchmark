---------------------------- MODULE RingBuffer ----------------------------
(***************************************************************************)
(* A ring buffer abstraction with a fixed number of slots indexed modulo   *)
(* the buffer size. Each slot holds either a value from Values or NULL.    *)
(* The module also tracks which readers and writers are currently          *)
(* accessing each slot, so that reads and writes can take several steps.   *)
(*                                                                         *)
(* NOTE: Client specifications that use this module should include        *)
(* NoDataRaces as an invariant.                                            *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    Size,       \* Number of slots in the ring buffer.
    Readers,    \* Set of reader identities.
    Writers,    \* Set of writer identities.
    Values      \* Set of values that can be stored in the buffer.

ASSUME SizeAssumption == Size \in Nat \ {0}

VARIABLE ringbuffer

vars == << ringbuffer >>

LastIndex == Size - 1

Indices == 0 .. LastIndex

\* The empty value: a value that is not in Values.
NULL == CHOOSE v : v \notin Values

-----------------------------------------------------------------------------
(* Initialization *)

Init ==
    ringbuffer = [
        slots   |-> [i \in Indices |-> NULL],
        readers |-> [i \in Indices |-> {}],
        writers |-> [i \in Indices |-> {}]
    ]

-----------------------------------------------------------------------------
(* Index computation: sequence numbers wrap around the buffer. *)

IndexOf(sequence) == sequence % Size

-----------------------------------------------------------------------------
(* Write operations *)

\* A writer begins writing value into the slot at index.
Write(index, writer, value) ==
    ringbuffer' = [ringbuffer EXCEPT
        !.writers[index] = @ \union {writer},
        !.slots[index]   = value
    ]

\* The writer finishes writing to the slot at index.
EndWrite(index, writer) ==
    ringbuffer' = [ringbuffer EXCEPT !.writers[index] = @ \ {writer}]

-----------------------------------------------------------------------------
(* Read operations *)

\* A reader begins reading the slot at index.
BeginRead(index, reader) ==
    ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \union {reader}]

\* The value currently stored in the slot at index.
Read(index) == ringbuffer.slots[index]

\* The reader finishes reading the slot at index.
EndRead(index, reader) ==
    ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \ {reader}]

-----------------------------------------------------------------------------
(* A generic standalone next-state relation that exercises the operators.  *)
(* Accesses are guarded so that a writer only enters a slot that nobody    *)
(* else is using, and a reader only enters a slot nobody is writing to.    *)

IsWriting(w) == \E i \in Indices : w \in ringbuffer.writers[i]
IsReading(r) == \E i \in Indices : r \in ringbuffer.readers[i]

DoBeginWrite ==
    \E i \in Indices, w \in Writers, v \in Values :
        /\ ~IsWriting(w)
        /\ ringbuffer.writers[i] = {}
        /\ ringbuffer.readers[i] = {}
        /\ Write(i, w, v)

DoEndWrite ==
    \E i \in Indices, w \in Writers :
        /\ w \in ringbuffer.writers[i]
        /\ EndWrite(i, w)

DoBeginRead ==
    \E i \in Indices, r \in Readers :
        /\ ~IsReading(r)
        /\ ringbuffer.writers[i] = {}
        /\ BeginRead(i, r)

DoEndRead ==
    \E i \in Indices, r \in Readers :
        /\ r \in ringbuffer.readers[i]
        /\ EndRead(i, r)

Next ==
    \/ DoBeginWrite
    \/ DoEndWrite
    \/ DoBeginRead
    \/ DoEndRead

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Invariants *)

TypeOk ==
    ringbuffer \in [
        slots   : [Indices -> Values \union {NULL}],
        readers : [Indices -> SUBSET Readers],
        writers : [Indices -> SUBSET Writers]
    ]

\* No slot is read while being written, and at most one writer per slot.
\* Client specifications using this module should include NoDataRaces as an
\* invariant.
NoDataRaces ==
    \A i \in Indices :
        /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
        /\ Cardinality(ringbuffer.writers[i]) <= 1

THEOREM Spec => [](TypeOk /\ NoDataRaces)

=============================================================================