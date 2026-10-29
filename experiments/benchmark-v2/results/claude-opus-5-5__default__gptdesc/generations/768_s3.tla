------------------------------ MODULE Disruptor_MPMC ------------------------------
EXTENDS Integers, FiniteSets, Sequences

-------------------------------- MODULE RingBuffer --------------------------------
(* Ring buffer with bookkeeping of the active readers and writers per slot.          *)
EXTENDS Naturals

CONSTANTS Size, Readers, Writers, Values, NULL

VARIABLE ringbuffer

LastIndex == Size - 1
Indices   == 0 .. LastIndex

Init ==
  ringbuffer = [ slots   |-> [ i \in Indices |-> NULL ],
                 readers |-> [ i \in Indices |-> {}   ],
                 writers |-> [ i \in Indices |-> {}   ] ]

IndexOf(sequence) == sequence % Size

Write(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
                    !.writers[index] = @ \union {writer},
                    !.slots[index]   = value ]

EndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ {writer} ]

BeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \union {reader} ]

Read(index) == ringbuffer.slots[index]

EndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ {reader} ]

TypeOk ==
  /\ ringbuffer.slots   \in [ Indices -> Values \union {NULL} ]
  /\ ringbuffer.readers \in [ Indices -> SUBSET Readers ]
  /\ ringbuffer.writers \in [ Indices -> SUBSET Writers ]

(* No slot is accessed by a reader and a writer at the same time, and no two        *)
(* writers write the same slot concurrently.                                         *)
NoDataRaces ==
  \A i \in Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1
===================================================================================