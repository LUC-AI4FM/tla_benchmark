--------------------------- MODULE Disruptor_SPMC ---------------------------

  ------------------------------ MODULE RingBuffer ------------------------------
  EXTENDS Naturals, FiniteSets

  CONSTANTS
    Size,
    Readers,
    Writers,
    NULL

  VARIABLE ringbuffer

  LastIndex == Size - 1

  Value == Nat \union {NULL}

  Init ==
    ringbuffer = [ slots   |-> [ i \in 0..LastIndex |-> NULL ],
                   readers |-> [ i \in 0..LastIndex |-> {}   ],
                   writers |-> [ i \in 0..LastIndex |-> {}   ] ]

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
    ringbuffer \in [ slots   : [ 0..LastIndex -> Value          ],
                     readers : [ 0..LastIndex -> SUBSET Readers ],
                     writers : [ 0..LastIndex -> SUBSET Writers ] ]

  NoDataRaces ==
    \A i \in 0..LastIndex :
      /\ \/ ringbuffer.readers[i] = {}
         \/ ringbuffer.writers[i] = {}
      /\ Cardinality(ringbuffer.writers[i]) <= 1
  ===============================================================================