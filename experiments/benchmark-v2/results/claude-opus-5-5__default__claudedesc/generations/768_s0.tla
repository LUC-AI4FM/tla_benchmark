------------------------------ MODULE Disruptor_MPMC ------------------------------
(***************************************************************************)
(* Multi-Producer, Multi-Consumer (MPMC) Disruptor ring buffer.            *)
(* Several writers claim sequence numbers from a shared atomic counter,    *)
(* write their value into the slot, and then publish the slot by flipping  *)
(* its published bit. The meaning of the bit alternates between even and  *)
(* odd rounds of the ring. Every reader consumes every published event in  *)
(* sequence order (multicast semantics).                                   *)
(***************************************************************************)

EXTENDS Naturals, Integers, FiniteSets, Sequences

CONSTANTS
  Writers,       \* Producer thread identifiers.
  Readers,       \* Consumer thread identifiers.
  Size,          \* Ring buffer capacity.
  MaxPublished,  \* Upper bound on published events (finite model checking).
  NULL

ASSUME /\ Writers # {}
       /\ Readers # {}
       /\ Writers \cap Readers = {}
       /\ Size \in Nat \ {0}
       /\ MaxPublished \in Nat \ {0}
       /\ NULL \notin Int

VARIABLES
  ringbuffer,        \* Slots plus the readers/writers currently accessing each slot.
  next_sequence,     \* Shared atomic counter used to claim sequences.
  claimed_sequence,  \* Sequence claimed by each writer.
  published,         \* Per-slot published bit (even/odd round encoding).
  read,              \* Per-reader cursor: next sequence to read.
  consumed,          \* Per-reader history of consumed values.
  pc                 \* Program counter for each thread.

vars == << ringbuffer, next_sequence, claimed_sequence, published, read, consumed, pc >>

Access  == "Access"
Advance == "Advance"

Threads == Writers \cup Readers

-----------------------------------------------------------------------------
(* Helpers *)

Indices == 0 .. (Size - 1)

IndexOf(sequence) == sequence % Size

Range(f) == { f[x] : x \in DOMAIN f }

Min(S) == CHOOSE x \in S : \A y \in S : x <= y
Max(S) == CHOOSE x \in S : \A y \in S : x >= y

Transition(t, from, to) ==
  /\ pc[t] = from
  /\ pc' = [pc EXCEPT ![t] = to]

(* Ring buffer operations with access tracking for data race detection. *)

BufWrite(index, writer, value) ==
  ringbuffer' = [ringbuffer EXCEPT
                   !.slots[index]   = value,
                   !.writers[index] = @ \cup {writer}]

BufEndWrite(index, writer) ==
  ringbuffer' = [ringbuffer EXCEPT !.writers[index] = @ \ {writer}]

BufBeginRead(index, reader) ==
  ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \cup {reader}]

BufEndRead(index, reader) ==
  ringbuffer' = [ringbuffer EXCEPT !.readers[index] = @ \ {reader}]

(* Published bit: TRUE means published in an even round,              *)
(* FALSE means published in an odd round (bit is flipped per publish). *)
IsPublished(sequence) ==
  LET index   == IndexOf(sequence)
      round   == sequence \div Size
      is_even == round % 2 = 0
  IN  published[index] = is_even

Publish(sequence) ==
  LET index == IndexOf(sequence)
  IN  [published EXCEPT ![index] = ~ @]

(* Highest contiguous published sequence starting at 'from'. Gaps left  *)
(* by slower producers that have not yet published stop the scan.      *)
AvailablePublishedSequence(from) ==
  LET candidates ==
        { s \in (from - 1) .. (next_sequence - 1) :
            \A k \in from .. s : IsPublished(k) }
  IN  Max(candidates)

-----------------------------------------------------------------------------
(* Producers *)

BeginWrite(writer) ==
  LET seq      == next_sequence
      index    == IndexOf(seq)
      min_read == Min(Range(read))
  IN  /\ seq < MaxPublished
      \* Do not lap the slowest consumer by a full ring cycle.
      /\ seq - min_read < Size
      /\ Transition(writer, Access, Advance)
      \* Atomically claim the sequence.
      /\ next_sequence' = seq + 1
      /\ claimed_sequence' = [claimed_sequence EXCEPT ![writer] = seq]
      \* Write the value into the slot.
      /\ BufWrite(index, writer, seq)
      /\ UNCHANGED << published, read, consumed >>

EndWrite(writer) ==
  LET seq   == claimed_sequence[writer]
      index == IndexOf(seq)
  IN  /\ Transition(writer, Advance, Access)
      /\ BufEndWrite(index, writer)
      /\ published' = Publish(seq)
      /\ claimed_sequence' = [claimed_sequence EXCEPT ![writer] = NULL]
      /\ UNCHANGED << next_sequence, read, consumed >>

-----------------------------------------------------------------------------
(* Consumers *)

BeginRead(reader) ==
  LET next  == read[reader]
      index == IndexOf(next)
  IN  /\ next <= AvailablePublishedSequence(next)
      /\ Transition(reader, Access, Advance)
      /\ BufBeginRead(index, reader)
      /\ consumed' = [consumed EXCEPT
                        ![reader] = Append(@, ringbuffer.slots[index])]
      /\ UNCHANGED << next_sequence, claimed_sequence, published, read >>

EndRead(reader) ==
  LET index == IndexOf(read[reader])
  IN  /\ Transition(reader, Advance, Access)
      /\ BufEndRead(index, reader)
      /\ read' = [read EXCEPT ![reader] = @ + 1]
      /\ UNCHANGED << next_sequence, claimed_sequence, published, consumed >>

-----------------------------------------------------------------------------
(* Termination: all events written and consumed. *)

Terminating ==
  /\ \A t \in Threads : pc[t] = Access
  /\ next_sequence = MaxPublished
  /\ \A r \in Readers : read[r] = MaxPublished
  /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Specification *)

Init ==
  /\ ringbuffer = [ slots   |-> [i \in Indices |-> NULL],
                    readers |-> [i \in Indices |-> {}],
                    writers |-> [i \in Indices |-> {}] ]
  /\ next_sequence    = 0
  /\ claimed_sequence = [w \in Writers |-> NULL]
  /\ published        = [i \in Indices |-> FALSE]
  /\ read             = [r \in Readers |-> 0]
  /\ consumed         = [r \in Readers |-> << >>]
  /\ pc               = [t \in Threads |-> Access]

Next ==
  \/ \E w \in Writers : BeginWrite(w) \/ EndWrite(w)
  \/ \E r \in Readers : BeginRead(r) \/ EndRead(r)
  \/ Terminating

Fairness ==
  /\ \A r \in Readers : WF_vars(BeginRead(r))
  /\ \A r \in Readers : WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

TypeOk ==
  /\ ringbuffer \in [ slots   : [Indices -> Nat \cup {NULL}],
                      readers : [Indices -> SUBSET Readers],
                      writers : [Indices -> SUBSET Writers] ]
  /\ next_sequence \in 0 .. MaxPublished
  /\ claimed_sequence \in [Writers -> Nat \cup {NULL}]
  /\ published \in [Indices -> BOOLEAN]
  /\ read \in [Readers -> 0 .. MaxPublished]
  /\ consumed \in [Readers -> Seq(Nat)]
  /\ pc \in [Threads -> {Access, Advance}]

(* No slot is ever accessed concurrently by a reader and a writer, *)
(* and no two writers access the same slot at the same time.        *)
NoDataRaces ==
  \A i \in Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

(* Every reader eventually and permanently has consumed all published *)
(* values, in order, up to MaxPublished.                              *)
Liveliness ==
  <>[] (\A r \in Readers : consumed[r] = [i \in 1 .. MaxPublished |-> i - 1])

THEOREM Spec => [](TypeOk /\ NoDataRaces)

==============================================================================