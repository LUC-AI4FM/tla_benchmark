--------------------------- MODULE RingBufferSPMC ---------------------------
EXTENDS Integers, Naturals, Sequences, FiniteSets

CONSTANTS
  MaxPublished,   \* Max number of published events (bound for model checking).
  Writers,        \* Set of writer/producer threads (exactly one).
  Readers,        \* Set of reader/consumer threads.
  Size,           \* Ring buffer size.
  NULL            \* Value of an unwritten slot.

ASSUME Size \in Nat \ {0}
ASSUME MaxPublished \in Nat \ {0}
ASSUME Cardinality(Writers) = 1
ASSUME Readers # {}
ASSUME Writers \cap Readers = {}

VARIABLES
  ringbuffer,     \* Slots plus the threads currently accessing each slot.
  published,      \* Producer cursor: last published sequence number.
  read,           \* Consumer cursors: last sequence read by each consumer.
  consumed,       \* Sequence of values read by each consumer.
  pc              \* Program counter of each thread.

vars == << ringbuffer, published, read, consumed, pc >>

Threads == Writers \cup Readers

Indices == 0 .. (Size - 1)

IndexOf(sequence) == sequence % Size

Range(f) == { f[x] : x \in DOMAIN f }

MinOf(S) == CHOOSE s \in S : \A t \in S : s <= t

(***************************************************************************)
(* Ring buffer operations.                                                 *)
(***************************************************************************)

InitRingBuffer ==
  [ slots   |-> [ i \in Indices |-> NULL ],
    readers |-> [ i \in Indices |-> {}   ],
    writers |-> [ i \in Indices |-> {}   ] ]

StartWrite(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
                    !.slots[index]   = value,
                    !.writers[index] = @ \cup { writer } ]

FinishWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ { writer } ]

StartRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \cup { reader } ]

FinishRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ { reader } ]

Transition(t, from, to) ==
  /\ pc[t]  = from
  /\ pc'    = [ pc EXCEPT ![t] = to ]

(***************************************************************************)
(* Producer.                                                               *)
(***************************************************************************)

BeginWrite(writer) ==
  LET next  == published + 1
      index == IndexOf(next)
      min   == MinOf(Range(read))
  IN
    /\ next < MaxPublished
    \* The slot was last used by sequence next - Size; all readers must be past it.
    /\ min >= next - Size
    /\ Transition(writer, "Access", "Advance")
    /\ StartWrite(index, writer, next)
    /\ UNCHANGED << published, read, consumed >>

EndWrite(writer) ==
  LET next  == published + 1
      index == IndexOf(next)
  IN
    /\ Transition(writer, "Advance", "Access")
    /\ FinishWrite(index, writer)
    /\ published' = next
    /\ UNCHANGED << read, consumed >>

(***************************************************************************)
(* Consumers.                                                              *)
(***************************************************************************)

BeginRead(reader) ==
  LET next  == read[reader] + 1
      index == IndexOf(next)
  IN
    /\ published >= next
    /\ Transition(reader, "Access", "Advance")
    /\ StartRead(index, reader)
    /\ consumed' = [ consumed EXCEPT ![reader] = Append(@, ringbuffer.slots[index]) ]
    /\ UNCHANGED << published, read >>

EndRead(reader) ==
  LET next  == read[reader] + 1
      index == IndexOf(next)
  IN
    /\ Transition(reader, "Advance", "Access")
    /\ FinishRead(index, reader)
    /\ read' = [ read EXCEPT ![reader] = next ]
    /\ UNCHANGED << published, consumed >>

(***************************************************************************)
(* Termination: everything published and consumed.                         *)
(***************************************************************************)

Terminated ==
  /\ published = MaxPublished - 1
  /\ \A t \in Threads : pc[t] = "Access"
  /\ \A r \in Readers : read[r] = published
  /\ UNCHANGED vars

(***************************************************************************)
(* Spec.                                                                   *)
(***************************************************************************)

Init ==
  /\ ringbuffer = InitRingBuffer
  /\ published  = -1
  /\ read       = [ r \in Readers |-> -1 ]
  /\ consumed   = [ r \in Readers |-> << >> ]
  /\ pc         = [ t \in Threads |-> "Access" ]

Next ==
  \/ \E w \in Writers : BeginWrite(w) \/ EndWrite(w)
  \/ \E r \in Readers : BeginRead(r)  \/ EndRead(r)
  \/ Terminated

Fairness ==
  \A r \in Readers : WF_vars(BeginRead(r)) /\ WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Model checking bound.                                                   *)
(***************************************************************************)

StateConstraint == published < MaxPublished

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)

TypeOk ==
  /\ ringbuffer \in [ slots   : [ Indices -> (0 .. MaxPublished) \cup { NULL } ],
                      readers : [ Indices -> SUBSET Readers ],
                      writers : [ Indices -> SUBSET Writers ] ]
  /\ published \in -1 .. MaxPublished
  /\ read      \in [ Readers -> -1 .. MaxPublished ]
  /\ consumed  \in [ Readers -> Seq((0 .. MaxPublished) \cup { NULL }) ]
  /\ pc        \in [ Threads -> { "Access", "Advance" } ]

NoDataRaces ==
  \A i \in Indices :
    \/ ringbuffer.writers[i] = {}
    \/ /\ Cardinality(ringbuffer.writers[i]) = 1
       /\ ringbuffer.readers[i] = {}

(***************************************************************************)
(* Liveness: every published value is eventually read by every consumer,   *)
(* and the value read at each position equals its sequence number.         *)
(***************************************************************************)

Liveliness ==
  \A r \in Readers :
    \A i \in 0 .. (MaxPublished - 1) :
      (published >= i) ~> ( /\ Len(consumed[r]) >= i + 1
                            /\ consumed[r][i + 1] = i )

=============================================================================