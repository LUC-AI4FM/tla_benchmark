------------------------------ MODULE RingBuffer ------------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
  Size,     \* Number of slots in the ring buffer.
  Readers,  \* Set of possible readers.
  Writers,  \* Set of possible writers.
  Values,   \* Set of values that can be stored in the slots.
  NULL      \* Marker for an empty slot.

ASSUME Size \in Nat \ {0}
ASSUME NULL \notin Values

VARIABLE ringbuffer

LastIndex == Size - 1

Indices == 0 .. LastIndex

(* Initially all slots are empty and no readers or writers are active. *)
Init ==
  ringbuffer = [
    slots   |-> [i \in Indices |-> NULL],
    readers |-> [i \in Indices |-> {}],
    writers |-> [i \in Indices |-> {}]
  ]

(* Map a sequence number to a slot index. *)
IndexOf(sequence) == sequence % Size

(* Write access: register the writer and store the value. *)
Write(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
    !.writers[index] = @ \union {writer},
    !.slots[index]   = value
  ]

(* Deregister the writer. *)
EndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ {writer} ]

(* Read access: register the reader. *)
BeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \union {reader} ]

(* Return the value stored in the slot. *)
Read(index) == ringbuffer.slots[index]

(* Deregister the reader. *)
EndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ {reader} ]

TypeOk ==
  ringbuffer \in [
    slots   : [Indices -> Values \union {NULL}],
    readers : [Indices -> SUBSET Readers],
    writers : [Indices -> SUBSET Writers]
  ]

(* No slot is accessed by readers and writers at the same time,
   and at most one writer accesses a slot at any time. *)
NoDataRaces ==
  \A i \in Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

===============================================================================