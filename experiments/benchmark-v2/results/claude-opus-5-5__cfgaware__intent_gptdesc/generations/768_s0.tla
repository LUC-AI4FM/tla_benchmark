---------------------------- MODULE Disruptor_MPMC ----------------------------
EXTENDS Integers, Naturals, FiniteSets, Sequences

CONSTANTS
  MaxPublished,   \* Bound on the number of sequences published (finite model)
  Writers,        \* Set of producers
  Readers,        \* Set of consumers
  Size,           \* Ring buffer size
  NULL            \* Empty-slot marker

ASSUME Size \in Nat \ {0}
ASSUME MaxPublished \in Nat
ASSUME Writers # {}
ASSUME Readers # {}

VARIABLES
  ringbuffer,        \* [slots, readers, writers] per buffer index
  next_sequence,     \* Next sequence number available to claim
  claimed_sequence,  \* Sequence claimed by each writer
  published,         \* Per index: highest sequence fully published there (-1 = none)
  read,              \* Per reader: next sequence it will read
  consumed,          \* Per reader: history of values read
  pc                 \* Program counter of each process

vars == << ringbuffer, next_sequence, claimed_sequence, published,
           read, consumed, pc >>

Range == 0 .. (Size - 1)

IndexOf(seq) == seq % Size

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinReadSequence == Min({ read[r] : r \in Readers })

-------------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ ringbuffer = [ slots   |-> [ i \in Range |-> NULL ],
                    readers |-> [ i \in Range |-> {} ],
                    writers |-> [ i \in Range |-> {} ] ]
  /\ next_sequence    = 0
  /\ claimed_sequence = [ w \in Writers |-> -1 ]
  /\ published        = [ i \in Range |-> -1 ]
  /\ read             = [ r \in Readers |-> 0 ]
  /\ consumed         = [ r \in Readers |-> << >> ]
  /\ pc               = [ p \in Writers \cup Readers |-> "Access" ]

-------------------------------------------------------------------------------
(* Producers *)

\* Claim the next sequence (atomic claim) and start writing into the slot.
\* A producer may not wrap past the slowest consumer.
BeginWrite(w) ==
  LET seq   == next_sequence
      index == IndexOf(seq)
  IN
  /\ pc[w] = "Access"
  /\ seq < MaxPublished
  /\ seq < MinReadSequence + Size
  /\ next_sequence'    = seq + 1
  /\ claimed_sequence' = [ claimed_sequence EXCEPT ![w] = seq ]
  /\ ringbuffer' = [ ringbuffer EXCEPT
                       !.writers[index] = @ \cup {w},
                       !.slots[index]   = seq ]   \* value written = sequence
  /\ pc' = [ pc EXCEPT ![w] = "Advance" ]
  /\ UNCHANGED << published, read, consumed >>

\* Finish writing and publish the sequence.
EndWrite(w) ==
  LET seq   == claimed_sequence[w]
      index == IndexOf(seq)
  IN
  /\ pc[w] = "Advance"
  /\ ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ {w} ]
  /\ published'  = [ published EXCEPT ![index] = seq ]
  /\ pc' = [ pc EXCEPT ![w] = "Access" ]
  /\ UNCHANGED << next_sequence, claimed_sequence, read, consumed >>

-------------------------------------------------------------------------------
(* Consumers *)

\* Begin reading the next sequence once it has been fully published.
BeginRead(r) ==
  LET seq   == read[r]
      index == IndexOf(seq)
  IN
  /\ pc[r] = "Access"
  /\ published[index] = seq
  /\ ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \cup {r} ]
  /\ consumed'   = [ consumed EXCEPT ![r] = Append(@, ringbuffer.slots[index]) ]
  /\ pc' = [ pc EXCEPT ![r] = "Advance" ]
  /\ UNCHANGED << next_sequence, claimed_sequence, published, read >>

\* Finish reading and advance the read cursor.
EndRead(r) ==
  LET seq   == read[r]
      index == IndexOf(seq)
  IN
  /\ pc[r] = "Advance"
  /\ ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ {r} ]
  /\ read' = [ read EXCEPT ![r] = seq + 1 ]
  /\ pc' = [ pc EXCEPT ![r] = "Access" ]
  /\ UNCHANGED << next_sequence, claimed_sequence, published, consumed >>

-------------------------------------------------------------------------------
(* Termination: all sequences published and read by everyone. *)

Terminated ==
  /\ next_sequence = MaxPublished
  /\ \A w \in Writers : pc[w] = "Access"
  /\ \A r \in Readers : read[r] = MaxPublished /\ pc[r] = "Access"

Terminating == Terminated /\ UNCHANGED vars

-------------------------------------------------------------------------------
(* Specification *)

Writer(w) == BeginWrite(w) \/ EndWrite(w)
Reader(r) == BeginRead(r) \/ EndRead(r)

Next ==
  \/ \E w \in Writers : Writer(w)
  \/ \E r \in Readers : Reader(r)
  \/ Terminating

Fairness ==
  /\ \A w \in Writers : WF_vars(Writer(w))
  /\ \A r \in Readers : WF_vars(Reader(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------------
(* State constraint for bounded model checking *)

StateConstraint == next_sequence <= MaxPublished

-------------------------------------------------------------------------------
(* Safety properties *)

TypeOk ==
  /\ ringbuffer \in [ slots   : [ Range -> (0 .. MaxPublished) \cup {NULL} ],
                      readers : [ Range -> SUBSET Readers ],
                      writers : [ Range -> SUBSET Writers ] ]
  /\ next_sequence \in 0 .. MaxPublished
  /\ claimed_sequence \in [ Writers -> -1 .. MaxPublished ]
  /\ published \in [ Range -> -1 .. MaxPublished ]
  /\ read \in [ Readers -> 0 .. MaxPublished ]
  /\ \A r \in Readers :
       /\ Len(consumed[r]) <= MaxPublished
       /\ \A i \in DOMAIN consumed[r] :
            consumed[r][i] \in (0 .. MaxPublished) \cup {NULL}
  /\ pc \in [ Writers \cup Readers -> { "Access", "Advance" } ]

\* No slot is ever written while being read, nor written by two writers at once.
NoDataRaces ==
  \A i \in Range :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

\* Producers never get more than Size ahead of the slowest consumer.
NoOverwrite ==
  next_sequence <= MinReadSequence + Size

\* Consumers never read past what has been claimed/published.
ReadOnlyPublished ==
  \A r \in Readers : read[r] <= next_sequence

\* Every consumer has seen exactly 0,1,2,... in order with no gaps,
\* i.e. no torn or stale data even under wrap-around.
BufferIntegrity ==
  \A r \in Readers :
    \A i \in DOMAIN consumed[r] : consumed[r][i] = i - 1

-------------------------------------------------------------------------------
(* Liveness properties *)

\* Every published sequence is eventually read by every consumer.
MulticastDelivery ==
  \A r \in Readers :
    \A s \in 0 .. (MaxPublished - 1) :
      (\E i \in Range : published[i] = s) ~> (read[r] > s)

\* Eventually all consumers have consumed everything, in order.
AllEventuallyConsumed ==
  <>[] (\A r \in Readers :
          consumed[r] = [ i \in 1 .. MaxPublished |-> i - 1 ])

Liveness == MulticastDelivery /\ AllEventuallyConsumed

=============================================================================