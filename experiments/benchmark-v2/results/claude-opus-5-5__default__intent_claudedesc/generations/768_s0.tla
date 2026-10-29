------------------------------ MODULE Disruptor_MPMC ------------------------------
(***************************************************************************)
(* Multi-Producer, Multi-Consumer (multicast) Disruptor ring buffer.       *)
(*                                                                         *)
(* Producers claim increasing sequence numbers. Each producer then writes  *)
(* its claimed sequence number into slot (seq % Size) and publishes it.    *)
(* A sequence is available to a consumer only when it and all earlier     *)
(* unread sequences are published. Every consumer reads every event in     *)
(* order. A producer may not reuse a slot until all consumers have read    *)
(* the event it previously held.                                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  MaxPublished,   \* Bound on the total number of events published
  Writers,        \* Set of producer threads
  Readers,        \* Set of consumer threads
  Size,           \* Ring buffer size
  NULL            \* Value of an empty slot

ASSUME Writers /= {}
ASSUME Readers /= {}
ASSUME Writers \cap Readers = {}
ASSUME Size \in Nat \ {0}
ASSUME MaxPublished \in Nat \ {0}
ASSUME NULL \notin Nat

VARIABLES
  ringbuffer,        \* [slots, readers, writers] per slot index
  next_sequence,     \* Next sequence number to be claimed
  claimed_sequence,  \* Sequence currently claimed by each producer
  published,         \* Availability buffer: last sequence published per slot
  read,              \* Last sequence fully read by each consumer
  pc,                \* Program counter of each thread
  consumed           \* History of values read by each consumer

vars == <<ringbuffer, next_sequence, claimed_sequence, published, read, pc, consumed>>

Indices == 0 .. (Size - 1)

-----------------------------------------------------------------------------
(* Helpers *)

Range(f) == { f[x] : x \in DOMAIN f }

MinReadSequence ==
  CHOOSE m \in Range(read) : \A r \in Readers : m <= read[r]

IsPublished(seq) == published[seq % Size] = seq

\* seq is available to r only if every sequence after r's cursor up to seq
\* has been published.
Available(r, seq) == \A s \in (read[r] + 1) .. seq : IsPublished(s)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ ringbuffer = [ slots   |-> [i \in Indices |-> NULL],
                    readers |-> [i \in Indices |-> {}],
                    writers |-> [i \in Indices |-> {}] ]
  /\ next_sequence    = 0
  /\ claimed_sequence = [w \in Writers |-> -1]
  /\ published        = [i \in Indices |-> -1]
  /\ read             = [r \in Readers |-> -1]
  /\ pc               = [t \in Writers \cup Readers |-> "Access"]
  /\ consumed         = [r \in Readers |-> << >>]

-----------------------------------------------------------------------------
(* Producer steps *)

\* Atomically claim the next sequence and start writing its slot. The slot
\* must not be reused until every consumer has read sequence (seq - Size).
BeginWrite(w) ==
  LET seq   == next_sequence
      index == seq % Size
  IN
    /\ pc[w] = "Access"
    /\ seq < MaxPublished
    /\ MinReadSequence >= seq - Size
    /\ next_sequence'    = seq + 1
    /\ claimed_sequence' = [claimed_sequence EXCEPT ![w] = seq]
    /\ ringbuffer'       = [ringbuffer EXCEPT !.writers[index] = @ \cup {w}]
    /\ pc'               = [pc EXCEPT ![w] = "Advance"]
    /\ UNCHANGED <<published, read, consumed>>

\* Write the claimed sequence number into the slot and publish it.
EndWrite(w) ==
  LET seq   == claimed_sequence[w]
      index == seq % Size
  IN
    /\ pc[w] = "Advance"
    /\ ringbuffer' = [ringbuffer EXCEPT !.slots[index]   = seq,
                                        !.writers[index] = @ \ {w}]
    /\ published'  = [published EXCEPT ![index] = seq]
    /\ pc'         = [pc EXCEPT ![w] = "Access"]
    /\ UNCHANGED <<next_sequence, claimed_sequence, read, consumed>>

-----------------------------------------------------------------------------
(* Consumer steps *)

\* Start reading the next sequence once it and all preceding ones are published.
BeginRead(r) ==
  LET next  == read[r] + 1
      index == next % Size
  IN
    /\ pc[r] = "Access"
    /\ next < MaxPublished
    /\ Available(r, next)
    /\ ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \cup {r}]
    /\ pc'         = [pc EXCEPT ![r] = "Advance"]
    /\ UNCHANGED <<next_sequence, claimed_sequence, published, read, consumed>>

\* Finish reading: record the value and advance the consumer's sequence.
EndRead(r) ==
  LET next  == read[r] + 1
      index == next % Size
  IN
    /\ pc[r] = "Advance"
    /\ consumed'   = [consumed EXCEPT ![r] = Append(@, ringbuffer.slots[index])]
    /\ ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \ {r}]
    /\ read'       = [read EXCEPT ![r] = next]
    /\ pc'         = [pc EXCEPT ![r] = "Access"]
    /\ UNCHANGED <<next_sequence, claimed_sequence, published>>

-----------------------------------------------------------------------------
(* Termination, used to avoid a spurious deadlock *)

Terminating ==
  /\ next_sequence = MaxPublished
  /\ \A t \in Writers \cup Readers : pc[t] = "Access"
  /\ \A r \in Readers : read[r] = MaxPublished - 1
  /\ UNCHANGED vars

Next ==
  \/ \E w \in Writers : BeginWrite(w) \/ EndWrite(w)
  \/ \E r \in Readers : BeginRead(r)  \/ EndRead(r)
  \/ Terminating

\* Weak fairness of consumer steps.
ConsumerFairness ==
  \A r \in Readers : WF_vars(BeginRead(r)) /\ WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ ConsumerFairness

\* Optional variant that also makes producers fair, so all MaxPublished
\* events are eventually published.
ProducerFairness ==
  \A w \in Writers : WF_vars(BeginWrite(w)) /\ WF_vars(EndWrite(w))

FairSpec == Spec /\ ProducerFairness

-----------------------------------------------------------------------------
(* Safety *)

TypeOk ==
  /\ ringbuffer \in [ slots   : [Indices -> (0 .. MaxPublished - 1) \cup {NULL}],
                      readers : [Indices -> SUBSET Readers],
                      writers : [Indices -> SUBSET Writers] ]
  /\ next_sequence    \in 0 .. MaxPublished
  /\ claimed_sequence \in [Writers -> -1 .. (MaxPublished - 1)]
  /\ published        \in [Indices -> -1 .. (MaxPublished - 1)]
  /\ read             \in [Readers -> -1 .. (MaxPublished - 1)]
  /\ pc               \in [Writers \cup Readers -> {"Access", "Advance"}]
  /\ consumed         \in [Readers -> Seq(0 .. (MaxPublished - 1))]

\* No slot is read and written at the same time, and no slot has two writers.
NoDataRaces ==
  \A i \in Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

\* The value read at each position equals the sequence claimed by its producer.
ConsumedCorrectly ==
  \A r \in Readers :
    /\ Len(consumed[r]) = read[r] + 1
    /\ \A j \in 1 .. Len(consumed[r]) : consumed[r][j] = j - 1

-----------------------------------------------------------------------------
(* Liveness *)

\* Under consumer fairness, every consumer eventually reads every published
\* (available) value.
ReadsAllPublished ==
  \A r \in Readers, i \in 0 .. (MaxPublished - 1) :
    (read[r] < i /\ Available(r, i)) ~> (read[r] >= i)

\* Every value each consumer reads is the sequence number its producer claimed.
ReadsCorrectValues == []ConsumedCorrectly

Liveness == ReadsAllPublished /\ ReadsCorrectValues

\* Under FairSpec, every consumer eventually reads all MaxPublished events in
\* order: 0, 1, ..., MaxPublished - 1.
Liveliness ==
  <>[] (\A r \in Readers : consumed[r] = [j \in 1 .. MaxPublished |-> j - 1])

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOk /\ NoDataRaces)
THEOREM Spec => Liveness
THEOREM FairSpec => Liveliness
=============================================================================