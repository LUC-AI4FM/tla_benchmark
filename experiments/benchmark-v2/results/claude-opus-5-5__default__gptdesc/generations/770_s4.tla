------------------------------ MODULE RingBuffer ------------------------------
(***************************************************************************)
(* A ring buffer abstraction with a fixed number of slots indexed modulo   *)
(* the buffer size. Each slot stores either a value from Values or NULL.   *)
(* The module also tracks the set of readers and writers currently         *)
(* accessing each slot, so that reads and writes can take several steps.   *)
(*                                                                         *)
(* NOTE: Client specifications using this module should include           *)
(*       NoDataRaces as an invariant.                                      *)
(***************************************************************************)

EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
  Size,     \* Number of slots in the ring buffer.
  Readers,  \* Set of reader identifiers.
  Writers,  \* Set of writer identifiers.
  Values,   \* Set of values that can be stored in a slot.
  NULL      \* Distinguished value for an empty slot.

ASSUME SizeAssumption    == Size \in Nat \ {0}
ASSUME WritersAssumption == Writers /= {}
ASSUME ReadersAssumption == Readers /= {}
ASSUME NullAssumption    == NULL \notin Values

VARIABLE ringbuffer

vars == << ringbuffer >>

LastIndex == Size - 1

Indices == 0 .. LastIndex

(***************************************************************************)
(* Initialization: all slots are NULL and nobody is accessing any slot.    *)
(***************************************************************************)
Init ==
  ringbuffer = [
    slots   |-> [i \in Indices |-> NULL],
    readers |-> [i \in Indices |-> {}],
    writers |-> [i \in Indices |-> {}]
  ]

(***************************************************************************)
(* Index computation: map a (monotonically increasing) sequence number to  *)
(* a slot index.                                                           *)
(***************************************************************************)
IndexOf(sequence) == sequence % Size

(***************************************************************************)
(* Write operations.                                                       *)
(***************************************************************************)

\* Begin writing value into the slot at index (registers the writer).
Write(index, writer, value) ==
  ringbuffer' = [ringbuffer EXCEPT
    !.writers[index] = @ \union {writer},
    !.slots[index]   = value
  ]

\* Finish writing into the slot at index (deregisters the writer).
EndWrite(index, writer) ==
  ringbuffer' = [ringbuffer EXCEPT !.writers[index] = @ \ {writer}]

(***************************************************************************)
(* Read operations.                                                        *)
(***************************************************************************)

\* Begin reading the slot at index (registers the reader).
BeginRead(index, reader) ==
  ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \union {reader}]

\* The value currently stored at index.
Read(index) == ringbuffer.slots[index]

\* Finish reading the slot at index (deregisters the reader).
EndRead(index, reader) ==
  ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \ {reader}]

(***************************************************************************)
(* A generic, race-free next-state relation exercising the abstraction.    *)
(* Client specifications normally compose the operators above themselves. *)
(***************************************************************************)
DoBeginWrite(i, w, v) ==
  /\ ringbuffer.writers[i] = {}
  /\ ringbuffer.readers[i] = {}
  /\ Write(i, w, v)

DoEndWrite(i, w) ==
  /\ w \in ringbuffer.writers[i]
  /\ EndWrite(i, w)

DoBeginRead(i, r) ==
  /\ ringbuffer.writers[i] = {}
  /\ r \notin ringbuffer.readers[i]
  /\ BeginRead(i, r)

DoEndRead(i, r) ==
  /\ r \in ringbuffer.readers[i]
  /\ EndRead(i, r)

Next ==
  \E i \in Indices :
    \/ \E w \in Writers, v \in Values : DoBeginWrite(i, w, v)
    \/ \E w \in Writers : DoEndWrite(i, w)
    \/ \E r \in Readers : DoBeginRead(i, r)
    \/ \E r \in Readers : DoEndRead(i, r)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)

TypeOk ==
  /\ ringbuffer \in [
       slots   : [Indices -> Values \union {NULL}],
       readers : [Indices -> SUBSET Readers],
       writers : [Indices -> SUBSET Writers]
     ]

\* No slot is read and written at the same time, and there is at most one
\* writer per slot. Clients of this module should check this invariant.
NoDataRaces ==
  \A i \in Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

THEOREM Spec => [](TypeOk /\ NoDataRaces)

===============================================================================