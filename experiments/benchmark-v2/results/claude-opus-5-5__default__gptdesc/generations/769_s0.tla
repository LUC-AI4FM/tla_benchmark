------------------------------ MODULE Disruptor_SPMC ------------------------------
(***************************************************************************)
(* Single Producer, Multi Consumer Disruptor.                              *)
(* The producer publishes sequence numbers 0, 1, 2, ... into a ring        *)
(* buffer. Every consumer reads every published value (multicast). The     *)
(* ring buffer is modelled in a separate module that is instantiated and   *)
(* used to detect data races.                                              *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  MaxPublished,   \* Maximum number of values published by the producer.
  Writers,        \* Set containing the single producer.
  Readers,        \* Set of consumers.
  Size,           \* Size of the ring buffer.
  NULL            \* Value of an empty slot.

ASSUME Writers /= {}
ASSUME Cardinality(Writers) = 1
ASSUME Readers /= {}
ASSUME Writers \cap Readers = {}
ASSUME Size \in Nat \ {0}
ASSUME MaxPublished \in Nat \ {0}

    ---------------------------- MODULE RingBuffer ----------------------------
    EXTENDS Naturals, FiniteSets

    CONSTANTS Size, Readers, Writers, NULL

    VARIABLE ringbuffer

    LastIndex == Size - 1

    Init ==
      ringbuffer = [ slots   |-> [ i \in 0 .. LastIndex |-> NULL ],
                     readers |-> [ i \in 0 .. LastIndex |-> {}   ],
                     writers |-> [ i \in 0 .. LastIndex |-> {}   ] ]

    IndexOf(sequence) == sequence % Size

    Write(index, writer, value) ==
      ringbuffer' = [ ringbuffer EXCEPT
                        !.writers[index] = @ \union { writer },
                        !.slots[index]   = value ]

    EndWrite(index, writer) ==
      ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ { writer } ]

    BeginRead(index, reader) ==
      ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \union { reader } ]

    Read(index) == ringbuffer.slots[index]

    EndRead(index, reader) ==
      ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ { reader } ]

    TypeOk ==
      ringbuffer \in [ slots   : [ 0 .. LastIndex -> Nat \union { NULL } ],
                       readers : [ 0 .. LastIndex -> SUBSET Readers ],
                       writers : [ 0 .. LastIndex -> SUBSET Writers ] ]

    NoDataRaces ==
      \A i \in 0 .. LastIndex :
        /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
        /\ Cardinality(ringbuffer.writers[i]) <= 1
    ===========================================================================