---------------------------- MODULE Disruptor_MPMC ----------------------------

------------------------------ MODULE RingBuffer ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  Size,
  Readers,
  Writers,
  Values,
  NULL

VARIABLE ringbuffer

LastIndex == Size - 1

Buffer == 0 .. LastIndex

Type ==
  ringbuffer \in [
    slots   : [Buffer -> Values \union {NULL}],
    readers : [Buffer -> SUBSET Readers],
    writers : [Buffer -> SUBSET Writers]
  ]

Init ==
  ringbuffer = [
    slots   |-> [i \in Buffer |-> NULL],
    readers |-> [i \in Buffer |-> {}],
    writers |-> [i \in Buffer |-> {}]
  ]

IndexOf(sequence) == sequence % Size

Write(index, writer, value) ==
  ringbuffer' = [ringbuffer EXCEPT
                   !.writers[index] = @ \union {writer},
                   !.slots[index]   = value]

EndWrite(index, writer) ==
  ringbuffer' = [ringbuffer EXCEPT !.writers[index] = @ \ {writer}]

BeginRead(index, reader) ==
  ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \union {reader}]

Read(index) == ringbuffer.slots[index]

EndRead(index, reader) ==
  ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \ {reader}]

(* No slot is accessed by a reader and a writer at the same time, and at   *)
(* most one writer accesses a slot at any time.                           *)
NoDataRaces ==
  \A i \in Buffer :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1
===============================================================================