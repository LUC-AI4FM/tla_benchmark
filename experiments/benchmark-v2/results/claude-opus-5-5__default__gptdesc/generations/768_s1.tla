---------------------------- MODULE Disruptor_MPMC ----------------------------
(***************************************************************************)
(* Bounded multi-producer / multi-consumer Disruptor-style ring buffer.    *)
(* Producers claim sequence numbers, write the claimed sequence into the   *)
(* shared ring buffer and publish it.  Consumers read published entries in *)
(* multicast fashion: every consumer reads every published value.          *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

(***************************************************************************)
(* Ring buffer model used to detect data races between producers and      *)
(* consumers.  It is instantiated below as RingBuffer.                     *)
(***************************************************************************)
---------------------------- MODULE RingBuffer ------------------------------
CONSTANTS Size, Readers, Writers, Values, NULL

VARIABLE ringbuffer

LastIndex == Size - 1

IndexOf(sequence) == sequence % Size

Init ==
  ringbuffer = [ slots   |-> [ i \in 0 .. LastIndex |-> NULL ],
                 readers |-> [ i \in 0 .. LastIndex |-> {} ],
                 writers |-> [ i \in 0 .. LastIndex |-> {} ] ]

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
  ringbuffer \in [ slots   : [ 0 .. LastIndex -> Values \union {NULL} ],
                   readers : [ 0 .. LastIndex -> SUBSET Readers ],
                   writers : [ 0 .. LastIndex -> SUBSET Writers ] ]

NoDataRaces ==
  \A i \in 0 .. LastIndex :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1
=============================================================================