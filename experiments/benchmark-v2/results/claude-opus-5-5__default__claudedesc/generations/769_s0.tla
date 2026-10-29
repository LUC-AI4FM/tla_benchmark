---------------------------- MODULE Disruptor_SPMC ----------------------------
(***************************************************************************)
(* Single Producer, Multi Consumer (SPMC) Disruptor.                       *)
(*                                                                         *)
(* One writer publishes events into a fixed-size ring buffer. Several      *)
(* readers each consume every published event (multicast).                 *)
(*                                                                         *)
(* The ring buffer operations (the "RingBuffer" module) are inlined below  *)
(* under the RingBuffer_ prefix, so that this file parses on its own.      *)
(*                                                                         *)
(* Model configuration: MaxPublished = 10, Writers = {w}, Readers =        *)
(* {r1, r2, r3}, Size = 4, NULL = model value.                             *)
(* CONSTRAINT StateConstraint, INVARIANTS TypeOk NoDataRaces,              *)
(* PROPERTY Liveliness.                                                    *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  MaxPublished,   \* Bound on the number of published events (model checking).
  Writers,        \* Writer threads (exactly one for SPMC).
  Readers,        \* Reader threads (consumers).
  Size,           \* Size of the ring buffer.
  NULL            \* Value of an empty slot.

ASSUME Writers /= {}
ASSUME Readers /= {}
ASSUME Size \in Nat \ {0}
ASSUME MaxPublished \in Nat \ {0}

VARIABLES
  ringbuffer,   \* The ring buffer (slots plus per-slot active readers/writers).
  published,    \* Write cursor: last published sequence number.
  read,         \* Read cursors: last sequence number read by each reader.
  consumed,     \* History: sequence of values read by each reader.
  pc            \* Program counter of each thread.

vars == << ringbuffer, published, read, consumed, pc >>

-------------------------------------------------------------------------------
(***************************************************************************)
(* Ring buffer                                                             *)
(***************************************************************************)

RingBuffer_LastIndex == Size - 1

RingBuffer_Indices == 0 .. RingBuffer_LastIndex

RingBuffer_TypeOk ==
  ringbuffer \in [
    slots:   [ RingBuffer_Indices -> Int \union { NULL } ],
    readers: [ RingBuffer_Indices -> SUBSET Readers ],
    writers: [ RingBuffer_Indices -> SUBSET Writers ]
  ]

RingBuffer_Init ==
  ringbuffer = [
    slots   |-> [ i \in RingBuffer_Indices |-> NULL ],
    readers |-> [ i \in RingBuffer_Indices |-> {} ],
    writers |-> [ i \in RingBuffer_Indices |-> {} ]
  ]

RingBuffer_IndexOf(sequence) == sequence % Size

RingBuffer_Write(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
                    !.writers[index] = @ \union { writer },
                    !.slots[index]   = value ]

RingBuffer_EndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ { writer } ]

RingBuffer_BeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \union { reader } ]

RingBuffer_Read(index) == ringbuffer.slots[index]

RingBuffer_EndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ { reader } ]

RingBuffer_NoDataRaces ==
  \A i \in RingBuffer_Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

-------------------------------------------------------------------------------
(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)

Range(f) == { f[x] : x \in DOMAIN f }

MinReadSequence ==
  CHOOSE min \in Range(read) : \A r \in Readers : min <= read[r]

Access  == "Access"
Advance == "Advance"

Transition(t, from, to) ==
  /\ pc[t] = from
  /\ pc' = [ pc EXCEPT ![t] = to ]

-------------------------------------------------------------------------------
(***************************************************************************)
(* Producer                                                                *)
(***************************************************************************)

BeginWrite(writer) ==
  LET
    next  == published + 1
    index == RingBuffer_IndexOf(next)
    min   == MinReadSequence
  IN
    \* All consumers must have read the slot's previous event (one full
    \* buffer cycle behind) before it can be overwritten.
    /\ min >= next - Size
    /\ Transition(writer, Access, Advance)
    /\ RingBuffer_Write(index, writer, next)
    /\ UNCHANGED << published, read, consumed >>

EndWrite(writer) ==
  LET
    next  == published + 1
    index == RingBuffer_IndexOf(next)
  IN
    /\ Transition(writer, Advance, Access)
    /\ RingBuffer_EndWrite(index, writer)
    /\ published' = next
    /\ UNCHANGED << read, consumed >>

-------------------------------------------------------------------------------
(***************************************************************************)
(* Consumers                                                               *)
(***************************************************************************)

BeginRead(reader) ==
  LET
    next  == read[reader] + 1
    index == RingBuffer_IndexOf(next)
  IN
    /\ published >= next
    /\ Transition(reader, Access, Advance)
    /\ RingBuffer_BeginRead(index, reader)
    \* Track what was read in the history variable.
    /\ consumed' = [ consumed EXCEPT
                       ![reader] = Append(@, RingBuffer_Read(index)) ]
    /\ UNCHANGED << published, read >>

EndRead(reader) ==
  LET
    next  == read[reader] + 1
    index == RingBuffer_IndexOf(next)
  IN
    /\ Transition(reader, Advance, Access)
    /\ RingBuffer_EndRead(index, reader)
    /\ read' = [ read EXCEPT ![reader] = next ]
    /\ UNCHANGED << published, consumed >>

-------------------------------------------------------------------------------
(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Init ==
  /\ RingBuffer_Init
  /\ published = -1
  /\ read      = [ r \in Readers |-> -1 ]
  /\ consumed  = [ r \in Readers |-> << >> ]
  /\ pc        = [ t \in Writers \union Readers |-> Access ]

Next ==
  \/ \E w \in Writers : BeginWrite(w)
  \/ \E w \in Writers : EndWrite(w)
  \/ \E r \in Readers : BeginRead(r)
  \/ \E r \in Readers : EndRead(r)

Fairness ==
  /\ \A r \in Readers : WF_vars(BeginRead(r))
  /\ \A r \in Readers : WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ Fairness

StateConstraint == published < MaxPublished

-------------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeOk ==
  /\ RingBuffer_TypeOk
  /\ published \in Int
  /\ read      \in [ Readers -> Int ]
  /\ consumed  \in [ Readers -> Seq(Nat) ]
  /\ pc        \in [ Writers \union Readers -> { Access, Advance } ]

NoDataRaces == RingBuffer_NoDataRaces

-------------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: every reader eventually and permanently has read all          *)
(* published values, in order.                                             *)
(***************************************************************************)

Liveliness ==
  <>[] (\A r \in Readers :
          /\ read[r] = published
          /\ \A i \in 0 .. published :
                /\ i + 1 <= Len(consumed[r])
                /\ consumed[r][i + 1] = i)

THEOREM Spec => []TypeOk
THEOREM Spec => []NoDataRaces

===============================================================================