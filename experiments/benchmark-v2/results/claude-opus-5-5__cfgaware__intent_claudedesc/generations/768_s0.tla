------------------------------ MODULE Disruptor_MPMC ------------------------------
(***************************************************************************)
(* Multi-Producer, Multi-Consumer (MPMC) Disruptor ring buffer.            *)
(*                                                                         *)
(* Producers (Writers) atomically claim increasing sequence numbers. Each  *)
(* producer writes its claimed sequence number into the slot               *)
(* (sequence % Size) and then publishes that slot. Sequence s counts as    *)
(* published when published[s % Size] = s.                                 *)
(*                                                                         *)
(* Consumers (Readers) are multicast. Each consumer reads every sequence   *)
(* in order. It can read sequence s only after s is published, and it     *)
(* reads sequentially, so all preceding sequences have already been read   *)
(* and were therefore published.                                           *)
(*                                                                         *)
(* A producer may claim sequence s only if every consumer has advanced     *)
(* past s - Size. This rule stops a slot from being overwritten before all *)
(* consumers have read its previous contents.                              *)
(***************************************************************************)
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
  MaxPublished,   \* Maximum number of events published.
  Writers,        \* Set of producer threads.
  Readers,        \* Set of consumer threads.
  Size,           \* Ring buffer size.
  NULL            \* Value of an empty slot.

ASSUME Writers /= {}
ASSUME Readers /= {}
ASSUME Size \in Nat \ {0}
ASSUME MaxPublished \in Nat \ {0}

VARIABLES
  ringbuffer,        \* Slots, plus the threads currently accessing each slot.
  next_sequence,     \* Next sequence that a producer can claim.
  claimed_sequence,  \* Sequence currently claimed by each producer.
  published,         \* published[i] = last sequence published into slot i.
  read,              \* read[r] = last sequence fully read by consumer r.
  consumed,          \* consumed[r] = sequence of values read by consumer r.
  pc                 \* Program counter of each thread.

vars == << ringbuffer, next_sequence, claimed_sequence, published,
           read, consumed, pc >>

Indices == 0 .. (Size - 1)
Threads == Writers \cup Readers
Values  == 0 .. (MaxPublished - 1)

IndexOf(seq) == seq % Size

IsPublished(seq) == published[IndexOf(seq)] = seq

(***************************************************************************)
(* Ring buffer operations                                                  *)
(***************************************************************************)
StartWrite(idx, w) ==
  [ringbuffer EXCEPT !.writers[idx] = @ \cup {w}]

EndWriteRB(idx, w, val) ==
  [ringbuffer EXCEPT !.writers[idx] = @ \ {w},
                     !.slots[idx]   = val]

StartReadRB(idx, r) ==
  [ringbuffer EXCEPT !.readers[idx] = @ \cup {r}]

EndReadRB(idx, r) ==
  [ringbuffer EXCEPT !.readers[idx] = @ \ {r}]

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
  /\ ringbuffer = [ slots   |-> [i \in Indices |-> NULL],
                    readers |-> [i \in Indices |-> {}],
                    writers |-> [i \in Indices |-> {}] ]
  /\ next_sequence    = 0
  /\ claimed_sequence = [w \in Writers |-> -1]
  /\ published        = [i \in Indices |-> -1]
  /\ read             = [r \in Readers |-> -1]
  /\ consumed         = [r \in Readers |-> << >>]
  /\ pc               = [t \in Threads |-> "Access"]

(***************************************************************************)
(* Producer actions                                                        *)
(***************************************************************************)
BeginWrite(w) ==
  LET seq   == next_sequence
      index == IndexOf(seq)
  IN
    /\ pc[w] = "Access"
    /\ seq < MaxPublished
    \* Do not overwrite a slot that some consumer has not yet read.
    /\ \A r \in Readers : read[r] >= seq - Size
    /\ next_sequence'    = seq + 1
    /\ claimed_sequence' = [claimed_sequence EXCEPT ![w] = seq]
    /\ ringbuffer'       = StartWrite(index, w)
    /\ pc'               = [pc EXCEPT ![w] = "Advance"]
    /\ UNCHANGED << published, read, consumed >>

EndWrite(w) ==
  LET seq   == claimed_sequence[w]
      index == IndexOf(seq)
  IN
    /\ pc[w] = "Advance"
    /\ ringbuffer' = EndWriteRB(index, w, seq)
    /\ published'  = [published EXCEPT ![index] = seq]
    /\ pc'         = [pc EXCEPT ![w] = "Access"]
    /\ UNCHANGED << next_sequence, claimed_sequence, read, consumed >>

(***************************************************************************)
(* Consumer actions                                                        *)
(***************************************************************************)
BeginRead(r) ==
  LET next  == read[r] + 1
      index == IndexOf(next)
  IN
    /\ pc[r] = "Access"
    \* The consumer reads in order, so all preceding sequences have already
    \* been published and read.
    /\ IsPublished(next)
    /\ ringbuffer' = StartReadRB(index, r)
    /\ pc'         = [pc EXCEPT ![r] = "Advance"]
    /\ UNCHANGED << next_sequence, claimed_sequence, published, read, consumed >>

EndRead(r) ==
  LET next  == read[r] + 1
      index == IndexOf(next)
  IN
    /\ pc[r] = "Advance"
    /\ consumed'   = [consumed EXCEPT ![r] = Append(@, ringbuffer.slots[index])]
    /\ ringbuffer' = EndReadRB(index, r)
    /\ read'       = [read EXCEPT ![r] = next]
    /\ pc'         = [pc EXCEPT ![r] = "Access"]
    /\ UNCHANGED << next_sequence, claimed_sequence, published >>

(***************************************************************************)
(* Termination: all events have been published and consumed.              *)
(***************************************************************************)
Terminated ==
  /\ next_sequence = MaxPublished
  /\ \A t \in Threads : pc[t] = "Access"
  /\ \A r \in Readers : read[r] = MaxPublished - 1
  /\ UNCHANGED vars

(***************************************************************************)
(* Specification                                                           *)
(***************************************************************************)
Next ==
  \/ \E w \in Writers : BeginWrite(w) \/ EndWrite(w)
  \/ \E r \in Readers : BeginRead(r) \/ EndRead(r)
  \/ Terminated

Fairness ==
  /\ \A w \in Writers : WF_vars(EndWrite(w))
  /\ \A r \in Readers : WF_vars(BeginRead(r)) /\ WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Model bound                                                             *)
(***************************************************************************)
StateConstraint == next_sequence <= MaxPublished

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOk ==
  /\ ringbuffer \in [ slots   : [Indices -> Values \cup {NULL}],
                      readers : [Indices -> SUBSET Readers],
                      writers : [Indices -> SUBSET Writers] ]
  /\ next_sequence    \in 0 .. MaxPublished
  /\ claimed_sequence \in [Writers -> -1 .. (MaxPublished - 1)]
  /\ published        \in [Indices -> -1 .. (MaxPublished - 1)]
  /\ read             \in [Readers -> -1 .. (MaxPublished - 1)]
  /\ consumed         \in [Readers -> Seq(Values)]
  /\ pc               \in [Threads -> {"Access", "Advance"}]

NoDataRaces ==
  \A i \in Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

\* Each value read equals the sequence number written at that position.
ConsumedCorrect ==
  \A r \in Readers :
    \A i \in 1 .. Len(consumed[r]) : consumed[r][i] = i - 1

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* Every published value is eventually read by every consumer, and the
\* value read is the sequence number that was claimed for that position.
Liveliness ==
  \A r \in Readers :
    \A i \in Values :
      IsPublished(i) ~> (Len(consumed[r]) > i /\ consumed[r][i + 1] = i)

\* Eventually every consumer has read every event, in sequence order.
AllConsumed ==
  <>[] (\A r \in Readers :
          consumed[r] = [i \in 1 .. MaxPublished |-> i - 1])

=============================================================================