------------------------------ MODULE Disruptor_SPMC ------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  MaxPublished,   \* Number of events the producer publishes (bound for model checking)
  Writers,        \* Producer identifiers (single producer: one writer at a time)
  Readers,        \* Consumer identifiers
  Size,           \* Capacity of the ring buffer
  NULL            \* Marker for an empty slot

ASSUME Writers /= {}
ASSUME Readers /= {}
ASSUME Size \in Nat /\ Size > 0
ASSUME MaxPublished \in Nat /\ MaxPublished > 0
ASSUME NULL \notin Int

VARIABLES
  ringbuffer,   \* [slots, readers, writers]: slot contents and current accessors
  published,    \* Global published cursor (highest published sequence, -1 if none)
  read,         \* Per-consumer read cursor (last sequence read, -1 if none)
  pc,           \* Program counter of each process: "Access" or "Advance"
  consumed      \* History of values observed by each consumer

vars == << ringbuffer, published, read, pc, consumed >>

Range == 0 .. (Size - 1)

IndexOf(seq) == seq % Size

(***************************************************************************)
(* Ring buffer operations                                                  *)
(***************************************************************************)

EmptyRingBuffer ==
  [ slots   |-> [ i \in Range |-> NULL ],
    readers |-> [ i \in Range |-> {} ],
    writers |-> [ i \in Range |-> {} ] ]

MinReadSequence ==
  CHOOSE m \in { read[r] : r \in Readers } : \A r \in Readers : m <= read[r]

\* Producer is blocked when the next slot to be written still holds an
\* event that some consumer has not yet read.
BufferFull ==
  (published + 1) - Size > MinReadSequence

\* No writer is in the middle of a write (single-producer discipline).
NoActiveWriter ==
  \A w \in Writers : pc[w] = "Access"

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)

Init ==
  /\ ringbuffer = EmptyRingBuffer
  /\ published  = -1
  /\ read       = [ r \in Readers |-> -1 ]
  /\ pc         = [ p \in Writers \cup Readers |-> "Access" ]
  /\ consumed   = [ r \in Readers |-> << >> ]

(***************************************************************************)
(* Producer actions                                                        *)
(***************************************************************************)

\* Claim the next slot: only if within bound, no other write in progress,
\* and the slot is no longer needed by any consumer.
BeginWrite(w) ==
  LET next  == published + 1
      index == IndexOf(next)
  IN
  /\ pc[w] = "Access"
  /\ NoActiveWriter
  /\ next < MaxPublished
  /\ ~BufferFull
  /\ ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \cup {w} ]
  /\ pc' = [ pc EXCEPT ![w] = "Advance" ]
  /\ UNCHANGED << published, read, consumed >>

\* Write the value into the slot and advance the published cursor atomically.
EndWrite(w) ==
  LET next  == published + 1
      index == IndexOf(next)
  IN
  /\ pc[w] = "Advance"
  /\ ringbuffer' = [ ringbuffer EXCEPT !.slots[index]   = next,
                                       !.writers[index] = @ \ {w} ]
  /\ published' = next
  /\ pc' = [ pc EXCEPT ![w] = "Access" ]
  /\ UNCHANGED << read, consumed >>

Write(w) == BeginWrite(w) \/ EndWrite(w)

(***************************************************************************)
(* Consumer actions                                                        *)
(***************************************************************************)

\* Start reading the next sequence, only if it has been published.
BeginRead(r) ==
  LET next  == read[r] + 1
      index == IndexOf(next)
  IN
  /\ pc[r] = "Access"
  /\ published >= next
  /\ ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \cup {r} ]
  /\ pc' = [ pc EXCEPT ![r] = "Advance" ]
  /\ UNCHANGED << published, read, consumed >>

\* Observe the slot value, release the slot, and advance the read cursor.
EndRead(r) ==
  LET next  == read[r] + 1
      index == IndexOf(next)
  IN
  /\ pc[r] = "Advance"
  /\ consumed' = [ consumed EXCEPT ![r] = Append(@, ringbuffer.slots[index]) ]
  /\ ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ {r} ]
  /\ read' = [ read EXCEPT ![r] = next ]
  /\ pc' = [ pc EXCEPT ![r] = "Access" ]
  /\ UNCHANGED << published >>

Read(r) == BeginRead(r) \/ EndRead(r)

(***************************************************************************)
(* Termination (avoid spurious deadlock once everything is consumed)       *)
(***************************************************************************)

Done ==
  /\ published = MaxPublished - 1
  /\ \A r \in Readers : read[r] = MaxPublished - 1
  /\ \A p \in Writers \cup Readers : pc[p] = "Access"

Terminating == Done /\ UNCHANGED vars

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)

Next ==
  \/ \E w \in Writers : Write(w)
  \/ \E r \in Readers : Read(r)
  \/ Terminating

Fairness ==
  /\ \A w \in Writers : WF_vars(Write(w))
  /\ \A r \in Readers : WF_vars(Read(r))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* State constraint for model checking                                     *)
(***************************************************************************)

StateConstraint ==
  /\ published < MaxPublished
  /\ \A r \in Readers : Len(consumed[r]) <= MaxPublished

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)

TypeOk ==
  /\ ringbuffer \in [ slots   : [ Range -> Int \cup {NULL} ],
                      readers : [ Range -> SUBSET Readers ],
                      writers : [ Range -> SUBSET Writers ] ]
  /\ published \in -1 .. (MaxPublished - 1)
  /\ read \in [ Readers -> -1 .. (MaxPublished - 1) ]
  /\ pc \in [ Writers \cup Readers -> { "Access", "Advance" } ]
  /\ consumed \in [ Readers -> Seq(Int) ]

\* A slot is never accessed concurrently by a writer and a reader,
\* and never by more than one writer.
NoDataRaces ==
  \A i \in Range :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

\* Consumers never run ahead of the published cursor, and the producer
\* never runs more than Size ahead of the slowest consumer.
CapacityRespected ==
  /\ \A r \in Readers : read[r] <= published
  /\ published - MinReadSequence <= Size

\* Each consumer has observed exactly the published sequence, in order,
\* with no gaps or duplicates.
Consistency ==
  \A r \in Readers :
    /\ Len(consumed[r]) = read[r] + 1
    /\ \A i \in 1 .. Len(consumed[r]) : consumed[r][i] = i - 1

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)

\* Every published value is eventually read by every consumer.
Liveliness ==
  <>[] (\A r \in Readers : consumed[r] = [ i \in 1 .. MaxPublished |-> i - 1 ])

\* Every published sequence is eventually read by every consumer.
EventuallyRead ==
  \A r \in Readers : \A s \in 0 .. (MaxPublished - 1) :
    (published >= s) ~> (read[r] >= s)

=============================================================================