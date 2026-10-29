------------------------- MODULE Disruptor_MPMC -------------------------
(***************************************************************************)
(* Bounded multi-producer, multi-consumer Disruptor-style ring buffer.     *)
(* Producers claim sequence numbers, write the claimed sequence into the   *)
(* ring buffer and publish it. Every consumer reads every published value  *)
(* (multicast).                                                            *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
  MaxPublished,   \* Bound on the number of sequences that may be published
  Writers,        \* Producers
  Readers,        \* Consumers
  Size,           \* Ring buffer size
  NULL            \* Empty slot marker

ASSUME /\ MaxPublished \in Nat
       /\ Size \in Nat \ {0}
       /\ Writers # {}
       /\ Readers # {}
       /\ Writers \cap Readers = {}
       /\ NULL \notin Nat

VARIABLES
  ringbuffer,        \* The shared ring buffer (managed by RingBuffer module)
  next_sequence,     \* Next sequence number available to be claimed
  claimed_sequence,  \* Sequence currently claimed by each writer
  published,         \* published[i]: highest sequence published at slot i
  read,              \* read[r]: next sequence reader r will read
  consumed,          \* consumed[r]: history of values read by reader r
  pc                 \* Program counter of each writer / reader

vars == << ringbuffer, next_sequence, claimed_sequence, published,
           read, consumed, pc >>

(***************************************************************************)
(* Ring buffer module: tracks concurrent accesses to detect data races.    *)
(***************************************************************************)
---------------------------- MODULE RingBuffer ----------------------------
LOCAL INSTANCE Naturals
LOCAL INSTANCE Integers
LOCAL INSTANCE FiniteSets

CONSTANTS Size, Readers, Writers, Values, NULL

VARIABLE ringbuffer

LastIndex == Size - 1

Init ==
  ringbuffer = [
    slots   |-> [i \in 0 .. LastIndex |-> NULL],
    readers |-> [i \in 0 .. LastIndex |-> {}],
    writers |-> [i \in 0 .. LastIndex |-> {}]
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

TypeOk ==
  ringbuffer \in [
    slots   : [0 .. LastIndex -> Values \union {NULL}],
    readers : [0 .. LastIndex -> SUBSET Readers],
    writers : [0 .. LastIndex -> SUBSET Writers]
  ]

NoDataRaces ==
  \A i \in 0 .. LastIndex :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1
===========================================================================