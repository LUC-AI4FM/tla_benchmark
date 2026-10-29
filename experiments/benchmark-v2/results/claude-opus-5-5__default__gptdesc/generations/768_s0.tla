------------------------------ MODULE Disruptor_MPMC ------------------------------
(***************************************************************************)
(* Bounded multi-producer, multi-consumer Disruptor-style ring buffer.     *)
(* Producers claim sequence numbers, write their claimed sequence into the *)
(* shared ring buffer and publish it. Consumers read published entries in  *)
(* multicast fashion, so every consumer reads every published value.       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

  ---------------------------- MODULE RingBuffer ----------------------------
  (*************************************************************************)
  (* Shared ring buffer that tracks which readers and writers are         *)
  (* currently accessing each slot, so that data races can be detected.   *)
  (*************************************************************************)
  EXTENDS Naturals, FiniteSets

  CONSTANTS
    Size,
    Readers,
    Writers,
    Values,
    NULL

  VARIABLE ringbuffer

  LastIndex == Size - 1
  Indices   == 0 .. LastIndex

  Init ==
    ringbuffer = [
      slots   |-> [i \in Indices |-> NULL],
      readers |-> [i \in Indices |-> {}],
      writers |-> [i \in Indices |-> {}]
    ]

  TypeOk ==
    ringbuffer \in [
      slots   : [Indices -> Values \cup {NULL}],
      readers : [Indices -> SUBSET Readers],
      writers : [Indices -> SUBSET Writers]
    ]

  IndexOf(sequence) == sequence % Size

  Write(index, writer, value) ==
    ringbuffer' = [ringbuffer EXCEPT
                     !.writers[index] = @ \cup {writer},
                     !.slots[index]   = value]

  EndWrite(index, writer) ==
    ringbuffer' = [ringbuffer EXCEPT !.writers[index] = @ \ {writer}]

  BeginRead(index, reader) ==
    ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \cup {reader}]

  Read(index) == ringbuffer.slots[index]

  EndRead(index, reader) ==
    ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \ {reader}]

  NoDataRaces ==
    \A i \in Indices :
      /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
      /\ Cardinality(ringbuffer.writers[i]) <= 1
  ============================================================================