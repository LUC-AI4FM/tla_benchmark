------------------------------ MODULE Disruptor_MPMC ------------------------------
EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS
  MaxPublished,   \* Max number of published events. Bounds the model.
  Writers,        \* Writer/publisher thread ids.
  Readers,        \* Reader/consumer thread ids.
  Size,           \* Ringbuffer size.
  NULL

ASSUME Writers /= {}
ASSUME Readers /= {}
ASSUME Writers \cap Readers = {}
ASSUME Size \in Nat \ {0}
ASSUME MaxPublished \in Nat \ {0}

VARIABLES
  ringbuffer,        \* Ring buffer slots plus active readers/writers per slot.
  next_sequence,     \* Shared atomic counter used to claim sequences.
  claimed_sequence,  \* Sequence claimed by each writer.
  published,         \* Per slot published bit (flips every round).
  read,              \* Next sequence each reader will read.
  pc,                \* Program counter for each thread.
  consumed           \* Sequence of values consumed by each reader.

vars == << ringbuffer, next_sequence, claimed_sequence, published, read, consumed, pc >>

(***************************************************************************)
(* Helpers.                                                                *)
(***************************************************************************)

LastIndex == Size - 1

Range(f) == { f[x] : x \in DOMAIN f }

Max(S) == CHOOSE m \in S : \A s \in S : s <= m

Min(S) == CHOOSE m \in S : \A s \in S : m <= s

IndexOf(sequence) == sequence % Size

Transition(t, from, to) ==
  /\ pc[t] = from
  /\ pc' = [ pc EXCEPT ![t] = to ]

(***************************************************************************)
(* Ring buffer operations (with tracking of concurrent accesses).          *)
(***************************************************************************)

RBInit ==
  [ slots   |-> [ i \in 0 .. LastIndex |-> NULL ],
    readers |-> [ i \in 0 .. LastIndex |-> {}   ],
    writers |-> [ i \in 0 .. LastIndex |-> {}   ] ]

RBWrite(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
                    !.writers[index] = @ \union { writer },
                    !.slots[index]   = value ]

RBEndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ { writer } ]

RBBeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \union { reader } ]

RBRead(index) == ringbuffer.slots[index]

RBEndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ { reader } ]

(***************************************************************************)
(* Publishing state encoded as a round bit per slot.                       *)
(* In even rounds a slot is published when its bit is TRUE, in odd rounds  *)
(* when its bit is FALSE. Each publish flips the bit.                      *)
(***************************************************************************)

IsPublished(sequence) ==
  LET index        == IndexOf(sequence)
      round        == sequence \div Size
      even_round   == (round % 2) = 0
  IN  published[index] = even_round

MinReadSequence == Min(Range(read))

\* Highest sequence s such that all sequences from..s are published.
\* Returns from - 1 if sequence 'from' is not yet published.
AvailablePublishedSequence(from) ==
  LET candidates == { s \in from .. (next_sequence - 1) :
                        \A x \in from .. s : IsPublished(x) }
  IN  IF candidates = {} THEN from - 1 ELSE Max(candidates)

(***************************************************************************)
(* Initial state.                                                          *)
(***************************************************************************)

Init ==
  /\ ringbuffer       = RBInit
  /\ next_sequence    = 0
  /\ claimed_sequence = [ w \in Writers |-> -1 ]
  /\ published        = [ i \in 0 .. LastIndex |-> FALSE ]
  /\ read             = [ r \in Readers |-> 0 ]
  /\ consumed         = [ r \in Readers |-> << >> ]
  /\ pc               = [ t \in Writers \union Readers |-> "Access" ]

(***************************************************************************)
(* Producer actions.                                                       *)
(***************************************************************************)

BeginWrite(writer) ==
  LET seq   == next_sequence
      index == IndexOf(seq)
  IN  \* Do not lap the slowest reader.
      /\ seq < MinReadSequence + Size
      /\ Transition(writer, "Access", "Advance")
      /\ next_sequence'    = seq + 1
      /\ claimed_sequence' = [ claimed_sequence EXCEPT ![writer] = seq ]
      /\ RBWrite(index, writer, seq)
      /\ UNCHANGED << published, read, consumed >>

EndWrite(writer) ==
  LET seq   == claimed_sequence[writer]
      index == IndexOf(seq)
  IN  /\ Transition(writer, "Advance", "Access")
      /\ published' = [ published EXCEPT ![index] = ~ @ ]
      /\ RBEndWrite(index, writer)
      /\ UNCHANGED << next_sequence, claimed_sequence, read, consumed >>

(***************************************************************************)
(* Consumer actions.                                                       *)
(***************************************************************************)

BeginRead(reader) ==
  LET next  == read[reader]
      index == IndexOf(next)
  IN  /\ AvailablePublishedSequence(next) >= next
      /\ Transition(reader, "Access", "Advance")
      /\ RBBeginRead(index, reader)
      /\ consumed' = [ consumed EXCEPT ![reader] = Append(@, RBRead(index)) ]
      /\ UNCHANGED << next_sequence, claimed_sequence, published, read >>

EndRead(reader) ==
  LET next  == read[reader]
      index == IndexOf(next)
  IN  /\ Transition(reader, "Advance", "Access")
      /\ RBEndRead(index, reader)
      /\ read' = [ read EXCEPT ![reader] = next + 1 ]
      /\ UNCHANGED << next_sequence, claimed_sequence, published, consumed >>

(***************************************************************************)
(* Spec.                                                                   *)
(***************************************************************************)

Next ==
  \/ \E w \in Writers : BeginWrite(w)
  \/ \E w \in Writers : EndWrite(w)
  \/ \E r \in Readers : BeginRead(r)
  \/ \E r \in Readers : EndRead(r)

Fairness ==
  /\ \A r \in Readers : WF_vars(BeginRead(r))
  /\ \A r \in Readers : WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ Fairness

StateConstraint == next_sequence <= MaxPublished

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)

NoDataRaces ==
  \A i \in 0 .. LastIndex :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

TypeOk ==
  /\ ringbuffer \in [ slots   : [ 0 .. LastIndex -> Int \union { NULL } ],
                      readers : [ 0 .. LastIndex -> SUBSET Readers ],
                      writers : [ 0 .. LastIndex -> SUBSET Writers ] ]
  /\ next_sequence \in Nat
  /\ claimed_sequence \in [ Writers -> Int ]
  /\ published \in [ 0 .. LastIndex -> BOOLEAN ]
  /\ read \in [ Readers -> Nat ]
  /\ consumed \in [ Readers -> Seq(Nat) ]
  /\ pc \in [ Writers \union Readers -> { "Access", "Advance" } ]

(***************************************************************************)
(* Properties.                                                             *)
(***************************************************************************)

Liveliness ==
  \A r \in Readers :
    <>[] (consumed[r] = [ i \in 1 .. MaxPublished |-> i - 1 ])

=============================================================================