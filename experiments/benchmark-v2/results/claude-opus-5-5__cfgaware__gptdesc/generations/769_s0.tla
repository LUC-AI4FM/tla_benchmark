------------------------------ MODULE Disruptor_SPMC ------------------------------
(***************************************************************************)
(* Single Producer, Multi Consumer Disruptor modelled on a ring buffer.    *)
(* The producer publishes sequence numbers 0 .. MaxPublished-1 into the    *)
(* ring buffer. Every consumer reads every published value (multicast).    *)
(* The ring buffer operators are defined inline (equivalent to the         *)
(* RingBuffer module) so that the specification is self contained.         *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
  MaxPublished,   \* Max number of published values (bounds the model).
  Writers,        \* Writer/producer thread ids.
  Readers,        \* Reader/consumer thread ids.
  Size,           \* Ring buffer size.
  NULL

ASSUME MaxPublished \in Nat \ {0}
ASSUME Size \in Nat \ {0}
ASSUME Writers # {}
ASSUME Readers # {}
ASSUME Writers \cap Readers = {}

VARIABLES
  ringbuffer,     \* [slots, readers, writers]
  next_sequence,  \* Next sequence the producer will claim.
  published,      \* Highest published sequence (the producer cursor).
  read,           \* Last sequence fully read by each reader.
  consumed,       \* Values consumed by each reader.
  pc              \* Program counter of each thread.

vars == << ringbuffer, next_sequence, published, read, consumed, pc >>

(***************************************************************************)
(* Ring buffer                                                             *)
(***************************************************************************)
Indices == 0 .. (Size - 1)
Values  == 0 .. MaxPublished

IndexOf(sequence) == sequence % Size

BufferInit ==
  ringbuffer = [ slots   |-> [ i \in Indices |-> NULL ],
                 readers |-> [ i \in Indices |-> {}   ],
                 writers |-> [ i \in Indices |-> {}   ] ]

BufferTypeOk ==
  /\ ringbuffer.slots   \in [ Indices -> Values \cup { NULL } ]
  /\ ringbuffer.readers \in [ Indices -> SUBSET Readers ]
  /\ ringbuffer.writers \in [ Indices -> SUBSET Writers ]

BufferWrite(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
                    !.writers[index] = @ \cup { writer },
                    !.slots[index]   = value ]

BufferEndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ { writer } ]

BufferBeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \cup { reader } ]

BufferEndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ { reader } ]

BufferRead(index) == ringbuffer.slots[index]

BufferNoDataRaces ==
  \A i \in Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)
Access  == "Access"
Advance == "Advance"

Range(f) == { f[x] : x \in DOMAIN f }

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Transition(t, from, to) ==
  /\ pc[t]  = from
  /\ pc'    = [ pc EXCEPT ![t] = to ]

(***************************************************************************)
(* Producer                                                                *)
(***************************************************************************)
BeginWrite(writer) ==
  LET seq      == next_sequence
      index    == IndexOf(seq)
      min_read == Min(Range(read))
  IN
    /\ seq < MaxPublished
    \* Do not overwrite a slot that has not been read by all consumers.
    /\ seq - Size <= min_read
    /\ Transition(writer, Access, Advance)
    /\ next_sequence' = seq + 1
    /\ BufferWrite(index, writer, seq)
    /\ UNCHANGED << published, read, consumed >>

EndWrite(writer) ==
  LET seq   == next_sequence - 1
      index == IndexOf(seq)
  IN
    /\ Transition(writer, Advance, Access)
    /\ BufferEndWrite(index, writer)
    /\ published' = seq
    /\ UNCHANGED << next_sequence, read, consumed >>

(***************************************************************************)
(* Consumers                                                               *)
(***************************************************************************)
BeginRead(reader) ==
  LET next  == read[reader] + 1
      index == IndexOf(next)
  IN
    /\ next <= published
    /\ Transition(reader, Access, Advance)
    /\ BufferBeginRead(index, reader)
    /\ consumed' = [ consumed EXCEPT ![reader] = Append(@, BufferRead(index)) ]
    /\ UNCHANGED << next_sequence, published, read >>

EndRead(reader) ==
  LET next  == read[reader] + 1
      index == IndexOf(next)
  IN
    /\ Transition(reader, Advance, Access)
    /\ BufferEndRead(index, reader)
    /\ read' = [ read EXCEPT ![reader] = next ]
    /\ UNCHANGED << next_sequence, published, consumed >>

(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)
Init ==
  /\ BufferInit
  /\ next_sequence = 0
  /\ published     = -1
  /\ read          = [ r \in Readers |-> -1 ]
  /\ consumed      = [ r \in Readers |-> << >> ]
  /\ pc            = [ t \in Writers \cup Readers |-> Access ]

Done ==
  /\ next_sequence = MaxPublished
  /\ \A t \in Writers \cup Readers : pc[t] = Access
  /\ \A r \in Readers : read[r] = MaxPublished - 1

Terminating ==
  /\ Done
  /\ UNCHANGED vars

Next ==
  \/ \E w \in Writers : BeginWrite(w) \/ EndWrite(w)
  \/ \E r \in Readers : BeginRead(r)  \/ EndRead(r)
  \/ Terminating

Fairness ==
  /\ \A w \in Writers : WF_vars(BeginWrite(w)) /\ WF_vars(EndWrite(w))
  /\ \A r \in Readers : WF_vars(BeginRead(r))  /\ WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ Fairness

StateConstraint == next_sequence <= MaxPublished

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOk ==
  /\ BufferTypeOk
  /\ next_sequence \in 0 .. MaxPublished
  /\ published     \in -1 .. (MaxPublished - 1)
  /\ read          \in [ Readers -> -1 .. (MaxPublished - 1) ]
  /\ consumed      \in [ Readers -> Seq(Values) ]
  /\ pc            \in [ Writers \cup Readers -> { Access, Advance } ]

NoDataRaces == BufferNoDataRaces

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
\* Every consumer eventually always has read every published value.
Liveliness ==
  \A r \in Readers :
    \A i \in 0 .. (MaxPublished - 1) :
      <>[](i \in Range(consumed[r]))

=============================================================================