------------------------------ MODULE RingBuffer ------------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
  Size,      \* Number of slots in the ring buffer
  Readers,   \* Set of reader thread identifiers
  Writers,   \* Set of writer thread identifiers
  Values,    \* Set of values that may be stored in slots
  NULL       \* Marker for an empty slot

ASSUME Size \in Nat \ {0}
ASSUME Writers /= {}
ASSUME Readers /= {}
ASSUME NULL \notin Values

VARIABLE ringbuffer

LastIndex == Size - 1

Indices == 0 .. LastIndex

(* Initial state: all slots empty, no active readers or writers. *)
Init ==
  ringbuffer = [
    slots   |-> [i \in Indices |-> NULL],
    readers |-> [i \in Indices |-> {}],
    writers |-> [i \in Indices |-> {}]
  ]

(* The index into the ring buffer for a sequence number. *)
IndexOf(sequence) ==
  sequence % Size

(* Non-atomic write, part 1: writer marks itself active and stores the value. *)
Write(index, writer, value) ==
  ringbuffer' = [ringbuffer EXCEPT
                   !.writers[index] = @ \union {writer},
                   !.slots[index]   = value]

(* Non-atomic write, part 2: writer is no longer active on the slot. *)
EndWrite(index, writer) ==
  ringbuffer' = [ringbuffer EXCEPT !.writers[index] = @ \ {writer}]

(* Non-atomic read, part 1: reader marks itself active on the slot. *)
BeginRead(index, reader) ==
  ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \union {reader}]

(* Access the current value of a slot. *)
Read(index) ==
  ringbuffer.slots[index]

(* Non-atomic read, part 2: reader is no longer active on the slot. *)
EndRead(index, reader) ==
  ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \ {reader}]

(* Unconstrained usage of the buffer (races allowed; clients must enforce). *)
Next ==
  \E i \in Indices :
    \/ \E w \in Writers, v \in Values : Write(i, w, v)
    \/ \E w \in Writers : w \in ringbuffer.writers[i] /\ EndWrite(i, w)
    \/ \E r \in Readers : BeginRead(i, r)
    \/ \E r \in Readers : r \in ringbuffer.readers[i] /\ EndRead(i, r)

Spec == Init /\ [][Next]_ringbuffer

TypeOk ==
  ringbuffer \in [
    slots:   [Indices -> Values \union {NULL}],
    readers: [Indices -> SUBSET Readers],
    writers: [Indices -> SUBSET Writers]
  ]

NoDataRaces ==
  \A i \in Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

=============================================================================