------------------------------ MODULE Disruptor_SPMC ------------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

CONSTANTS
  MaxPublished,  \* Max number of published events (bounds the model).
  Writers,       \* Writer/producer thread ids.
  Readers,       \* Reader/consumer thread ids.
  Size,          \* Ring buffer size.
  NULL

VARIABLES
  ringbuffer,    \* Ring buffer state: slots and per-slot active readers/writers.
  published,     \* Write cursor (single producer).
  read,          \* Read cursor per reader/consumer.
  pc,            \* Program counter per thread.
  consumed       \* History variable: sequence of values read per reader.

vars == << ringbuffer, published, read, pc, consumed >>

Access  == "Access"
Advance == "Advance"

Threads == Writers \cup Readers

Range(f) == { f[x] : x \in DOMAIN f }
Min(S) == CHOOSE s \in S : \A t \in S : s <= t

(***************************************************************************)
(* Ring buffer (inlined).                                                   *)
(***************************************************************************)

Indices == 0 .. (Size - 1)

IndexOf(sequence) == sequence % Size

RBInit ==
  [ slots   |-> [ i \in Indices |-> NULL ],
    readers |-> [ i \in Indices |-> {}   ],
    writers |-> [ i \in Indices |-> {}   ] ]

RBWrite(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
                    !.writers[index] = @ \cup { writer },
                    !.slots[index]   = value ]

RBEndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ { writer } ]

RBBeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \cup { reader } ]

RBRead(index) == ringbuffer.slots[index]

RBEndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ { reader } ]

(***************************************************************************)
(* Helpers.                                                                 *)
(***************************************************************************)

Transition(t, from, to) ==
  /\ pc[t] = from
  /\ pc'   = [ pc EXCEPT ![t] = to ]

(***************************************************************************)
(* Producer.                                                                *)
(***************************************************************************)

BeginWrite(writer) ==
  LET
    next     == published + 1
    index    == IndexOf(next)
    min_read == Min(Range(read))
  IN
    \* Are we clear of all consumers? (Potentially a full cycle behind).
    /\ min_read >= next - Size
    /\ Transition(writer, Access, Advance)
    /\ RBWrite(index, writer, next)
    /\ UNCHANGED << published, read, consumed >>

EndWrite(writer) ==
  LET
    next  == published + 1
    index == IndexOf(next)
  IN
    /\ Transition(writer, Advance, Access)
    /\ published' = next
    /\ RBEndWrite(index, writer)
    /\ UNCHANGED << read, consumed >>

(***************************************************************************)
(* Consumers.                                                               *)
(***************************************************************************)

BeginRead(reader) ==
  LET
    next  == read[reader] + 1
    index == IndexOf(next)
  IN
    /\ published >= next
    /\ Transition(reader, Access, Advance)
    /\ RBBeginRead(index, reader)
    \* Track what we read from the ring buffer.
    /\ consumed' = [ consumed EXCEPT ![reader] = Append(@, RBRead(index)) ]
    /\ UNCHANGED << published, read >>

EndRead(reader) ==
  LET
    next  == read[reader] + 1
    index == IndexOf(next)
  IN
    /\ Transition(reader, Advance, Access)
    /\ RBEndRead(index, reader)
    /\ read' = [ read EXCEPT ![reader] = next ]
    /\ UNCHANGED << published, consumed >>

(***************************************************************************)
(* Spec.                                                                    *)
(***************************************************************************)

Init ==
  /\ ringbuffer = RBInit
  /\ published  = -1
  /\ read       = [ r \in Readers |-> -1 ]
  /\ consumed   = [ r \in Readers |-> << >> ]
  /\ pc         = [ t \in Threads |-> Access ]

Next ==
  \/ \E w \in Writers : BeginWrite(w)
  \/ \E w \in Writers : EndWrite(w)
  \/ \E r \in Readers : BeginRead(r)
  \/ \E r \in Readers : EndRead(r)

Fairness ==
  \A r \in Readers :
    /\ WF_vars(BeginRead(r))
    /\ WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ Fairness

StateConstraint == published < MaxPublished

(***************************************************************************)
(* Invariants.                                                              *)
(***************************************************************************)

TypeOk ==
  /\ ringbuffer \in [ slots   : [ Indices -> Int \cup { NULL } ],
                      readers : [ Indices -> SUBSET Readers ],
                      writers : [ Indices -> SUBSET Writers ] ]
  /\ published \in Int
  /\ read      \in [ Readers -> Int ]
  /\ consumed  \in [ Readers -> Seq(Int) ]
  /\ pc        \in [ Threads -> { Access, Advance } ]

NoDataRaces ==
  \A i \in Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

(***************************************************************************)
(* Properties.                                                              *)
(***************************************************************************)

\* Every consumer eventually and permanently has read every published value
\* in order, where each value equals its sequence number.
Liveliness ==
  <>[] (\A r \in Readers :
          \A i \in 0 .. published :
            /\ Len(consumed[r]) > i
            /\ consumed[r][i + 1] = i)

=============================================================================