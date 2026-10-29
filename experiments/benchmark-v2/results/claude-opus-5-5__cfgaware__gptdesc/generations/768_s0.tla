------------------------------- MODULE MPMC -------------------------------
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS
  MaxPublished,   \* Number of sequences that may be published in total.
  Writers,        \* Set of producer identifiers.
  Readers,        \* Set of consumer identifiers.
  Size,           \* Size of the ring buffer.
  NULL            \* Value of an empty slot.

ASSUME Writers /= {}
ASSUME Readers /= {}
ASSUME Size \in Nat \ {0}
ASSUME MaxPublished \in Nat \ {0}

VARIABLES
  ringbuffer,        \* Shared ring buffer: slots plus active readers/writers per slot.
  next_sequence,     \* Next sequence number a producer can claim.
  claimed_sequence,  \* Sequence currently claimed by each producer.
  published,         \* Per slot: the last sequence published into that slot (-1 if none).
  read,              \* Per consumer: last sequence fully consumed (-1 if none).
  consumed,          \* Per consumer: history of consumed values.
  pc                 \* Program counter of each producer/consumer.

vars == << ringbuffer, next_sequence, claimed_sequence, published, read, consumed, pc >>

(***************************************************************************)
(* Ring buffer (shared memory with data race tracking).                    *)
(***************************************************************************)

LastIndex == Size - 1

IndexOf(sequence) == sequence % Size

BufferInit ==
  ringbuffer = [ slots   |-> [ i \in 0 .. LastIndex |-> NULL ],
                 readers |-> [ i \in 0 .. LastIndex |-> {} ],
                 writers |-> [ i \in 0 .. LastIndex |-> {} ] ]

BufferBeginWrite(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
                    !.writers[index] = @ \union { writer },
                    !.slots[index]   = value ]

BufferEndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ { writer } ]

BufferBeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \union { reader } ]

BufferEndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ { reader } ]

BufferRead(index) == ringbuffer.slots[index]

BufferTypeOk ==
  /\ ringbuffer.slots   \in [ 0 .. LastIndex -> (0 .. MaxPublished) \union { NULL } ]
  /\ ringbuffer.readers \in [ 0 .. LastIndex -> SUBSET Readers ]
  /\ ringbuffer.writers \in [ 0 .. LastIndex -> SUBSET Writers ]

\* No slot is accessed concurrently by a writer and a reader, nor by two writers.
NoDataRaces ==
  \A i \in 0 .. LastIndex :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

(***************************************************************************)
(* Helpers.                                                                *)
(***************************************************************************)

Access  == "Access"
Advance == "Advance"

Transition(t, from, to) ==
  /\ pc[t] = from
  /\ pc'   = [ pc EXCEPT ![t] = to ]

IsAvailable(sequence) == published[IndexOf(sequence)] = sequence

\* A sequence may be claimed only when all consumers have finished with the
\* sequence that previously occupied the same slot.
CanClaim(sequence) ==
  \A r \in Readers : read[r] >= sequence - Size

(***************************************************************************)
(* Producers.                                                              *)
(***************************************************************************)

BeginWrite(writer) ==
  LET seq   == next_sequence
      index == IndexOf(seq)
  IN
    /\ seq < MaxPublished
    /\ CanClaim(seq)
    /\ Transition(writer, Access, Advance)
    /\ next_sequence'    = seq + 1
    /\ claimed_sequence' = [ claimed_sequence EXCEPT ![writer] = seq ]
    /\ BufferBeginWrite(index, writer, seq)
    /\ UNCHANGED << published, read, consumed >>

EndWrite(writer) ==
  LET seq   == claimed_sequence[writer]
      index == IndexOf(seq)
  IN
    /\ Transition(writer, Advance, Access)
    /\ BufferEndWrite(index, writer)
    /\ published' = [ published EXCEPT ![index] = seq ]
    /\ UNCHANGED << next_sequence, claimed_sequence, read, consumed >>

(***************************************************************************)
(* Consumers (multicast: each consumer reads every published value).       *)
(***************************************************************************)

BeginRead(reader) ==
  LET next  == read[reader] + 1
      index == IndexOf(next)
  IN
    /\ next < MaxPublished
    /\ IsAvailable(next)
    /\ Transition(reader, Access, Advance)
    /\ BufferBeginRead(index, reader)
    /\ consumed' = [ consumed EXCEPT ![reader] = Append(@, BufferRead(index)) ]
    /\ UNCHANGED << next_sequence, claimed_sequence, published, read >>

EndRead(reader) ==
  LET next  == read[reader] + 1
      index == IndexOf(next)
  IN
    /\ Transition(reader, Advance, Access)
    /\ BufferEndRead(index, reader)
    /\ read' = [ read EXCEPT ![reader] = next ]
    /\ UNCHANGED << next_sequence, claimed_sequence, published, consumed >>

(***************************************************************************)
(* Specification.                                                          *)
(***************************************************************************)

Init ==
  /\ BufferInit
  /\ next_sequence    = 0
  /\ claimed_sequence = [ w \in Writers |-> -1 ]
  /\ published        = [ i \in 0 .. LastIndex |-> -1 ]
  /\ read             = [ r \in Readers |-> -1 ]
  /\ consumed         = [ r \in Readers |-> << >> ]
  /\ pc               = [ a \in Writers \union Readers |-> Access ]

Terminated ==
  /\ next_sequence = MaxPublished
  /\ \A a \in Writers \union Readers : pc[a] = Access
  /\ \A r \in Readers : read[r] = MaxPublished - 1

Done ==
  /\ Terminated
  /\ UNCHANGED vars

Next ==
  \/ \E w \in Writers : BeginWrite(w) \/ EndWrite(w)
  \/ \E r \in Readers : BeginRead(r)  \/ EndRead(r)
  \/ Done

Fairness ==
  /\ \A w \in Writers : WF_vars(BeginWrite(w)) /\ WF_vars(EndWrite(w))
  /\ \A r \in Readers : WF_vars(BeginRead(r))  /\ WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Invariants, constraints and properties.                                 *)
(***************************************************************************)

TypeOk ==
  /\ BufferTypeOk
  /\ next_sequence    \in 0 .. MaxPublished
  /\ claimed_sequence \in [ Writers -> -1 .. MaxPublished ]
  /\ published        \in [ 0 .. LastIndex -> -1 .. MaxPublished ]
  /\ read             \in [ Readers -> -1 .. MaxPublished ]
  /\ consumed         \in [ Readers -> Seq(0 .. MaxPublished) ]
  /\ pc               \in [ Writers \union Readers -> { Access, Advance } ]

StateConstraint ==
  /\ next_sequence <= MaxPublished
  /\ \A r \in Readers : Len(consumed[r]) <= MaxPublished

\* Every consumer eventually consumes every published value, in order.
Liveness ==
  \A r \in Readers :
    \A i \in 0 .. (MaxPublished - 1) :
      <>[] ( IsAvailable(i) =>
               /\ Len(consumed[r]) >= i + 1
               /\ consumed[r][i + 1] = i )

=============================================================================