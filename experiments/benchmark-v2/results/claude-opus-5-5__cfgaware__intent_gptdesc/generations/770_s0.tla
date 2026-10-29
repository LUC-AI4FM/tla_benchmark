------------------------------ MODULE RingBuffer ------------------------------
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
  Size,     \* Number of slots in the ring buffer
  Readers,  \* Set of consumer threads
  Writers,  \* Set of producer threads
  Values,   \* Set of values that can be written
  NULL      \* Marker for an empty slot

ASSUME Size \in Nat \ {0}
ASSUME Readers /= {}
ASSUME Writers /= {}
ASSUME NULL \notin Values

VARIABLE ringbuffer

vars == << ringbuffer >>

LastIndex == Size - 1

Slots == 0 .. LastIndex

\* Map a sequence number to a slot index, with wrap-around.
IndexOf(sequence) == sequence % Size

-------------------------------------------------------------------------------
(* Initial state: every slot is empty and no thread has access. *)

Init ==
  ringbuffer = [
    slots   |-> [i \in Slots |-> NULL],
    readers |-> [i \in Slots |-> {}],
    writers |-> [i \in Slots |-> {}]
  ]

-------------------------------------------------------------------------------
(* Operations. A write is a write step (begin + perform) followed by       *)
(* EndWrite. A read is BeginRead, Read (the value), then EndRead.          *)

\* Producer acquires write access to the slot and stores the value.
Write(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
                    !.writers[index] = @ \union {writer},
                    !.slots[index]   = value ]

\* Producer releases write access to the slot.
EndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ {writer} ]

\* Consumer acquires read access to the slot.
BeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \union {reader} ]

\* The value a consumer observes when reading the slot.
Read(index) ==
  ringbuffer.slots[index]

\* Consumer releases read access to the slot.
EndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ {reader} ]

-------------------------------------------------------------------------------
(* Concurrent behavior of producers and consumers. Access is only granted *)
(* when it cannot cause a data race.                                      *)

\* A thread holds at most one slot at a time.
WriterBusy(w) == \E i \in Slots : w \in ringbuffer.writers[i]
ReaderBusy(r) == \E i \in Slots : r \in ringbuffer.readers[i]

ProducerWrite(w, seq, v) ==
  LET i == IndexOf(seq) IN
  /\ ~WriterBusy(w)
  /\ ringbuffer.writers[i] = {}
  /\ ringbuffer.readers[i] = {}
  /\ Write(i, w, v)

ProducerEndWrite(w, i) ==
  /\ w \in ringbuffer.writers[i]
  /\ EndWrite(i, w)

ConsumerBeginRead(r, seq) ==
  LET i == IndexOf(seq) IN
  /\ ~ReaderBusy(r)
  /\ ringbuffer.writers[i] = {}
  /\ BeginRead(i, r)

ConsumerEndRead(r, i) ==
  /\ r \in ringbuffer.readers[i]
  /\ Read(i) = Read(i)   \* the read is performed while access is held
  /\ EndRead(i, r)

Next ==
  \/ \E w \in Writers, s \in Slots, v \in Values : ProducerWrite(w, s, v)
  \/ \E w \in Writers, i \in Slots : ProducerEndWrite(w, i)
  \/ \E r \in Readers, s \in Slots : ConsumerBeginRead(r, s)
  \/ \E r \in Readers, i \in Slots : ConsumerEndRead(r, i)

Spec == Init /\ [][Next]_vars

-------------------------------------------------------------------------------
(* Correctness requirements. *)

TypeOk ==
  /\ ringbuffer \in [ slots   : [Slots -> Values \union {NULL}],
                      readers : [Slots -> SUBSET Readers],
                      writers : [Slots -> SUBSET Writers] ]

NoDataRaces ==
  \A i \in Slots :
    /\ Cardinality(ringbuffer.writers[i]) <= 1
    /\ (ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {})

\* A slot's content only changes when a writer validly acquires it
\* (no other writers and no readers before the step).
SlotPreservation ==
  [][ \A i \in Slots :
        ringbuffer'.slots[i] /= ringbuffer.slots[i] =>
          /\ ringbuffer.writers[i] = {}
          /\ ringbuffer.readers[i] = {}
          /\ Cardinality(ringbuffer'.writers[i]) = 1
    ]_vars

THEOREM Spec => [](TypeOk /\ NoDataRaces)
===============================================================================