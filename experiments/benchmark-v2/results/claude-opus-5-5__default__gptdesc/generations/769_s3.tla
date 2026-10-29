------------------------- MODULE Disruptor_SPMC -----------------------------
(***************************************************************************)
(* Single Producer, Multi Consumer Disruptor backed by a ring buffer.      *)
(* The producer publishes sequence numbers 0, 1, 2, ... into the buffer.   *)
(* Every consumer reads every published value (multicast).                 *)
(* The ring buffer is modelled inline with operators prefixed "RB_".       *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  MaxPublished,   \* Max number of published events (bounds the model).
  Writers,        \* Writer/producer thread ids (single producer).
  Readers,        \* Reader/consumer thread ids.
  Size,           \* Ringbuffer size.
  NULL

ASSUME Writers /= {}
ASSUME Cardinality(Writers) = 1
ASSUME Readers /= {}
ASSUME Writers \cap Readers = {}
ASSUME Size \in Nat \ {0}
ASSUME MaxPublished \in Nat \ {0}

VARIABLES
  ringbuffer,   \* Ring buffer: slots plus active readers/writers per slot.
  published,    \* Producer cursor: last published sequence number.
  read,         \* Per-consumer cursor: last read sequence number.
  consumed,     \* Per-consumer history of consumed values.
  pc            \* Program counter of each thread.

vars == << ringbuffer, published, read, consumed, pc >>

Access  == "Access"
Advance == "Advance"

-----------------------------------------------------------------------------
(* Ring buffer                                                             *)
-----------------------------------------------------------------------------

Indices == 0 .. (Size - 1)

RB_Init ==
  ringbuffer = [
    slots   |-> [ i \in Indices |-> NULL ],
    readers |-> [ i \in Indices |-> {} ],
    writers |-> [ i \in Indices |-> {} ]
  ]

RB_IndexOf(sequence) == sequence % Size

RB_Write(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
                    !.writers[index] = @ \union { writer },
                    !.slots[index]   = value ]

RB_EndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ { writer } ]

RB_BeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \union { reader } ]

RB_Read(index) == ringbuffer.slots[index]

RB_EndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ { reader } ]

RB_TypeOk ==
  ringbuffer \in [
    slots   : [ Indices -> Nat \union { NULL } ],
    readers : [ Indices -> SUBSET Readers ],
    writers : [ Indices -> SUBSET Writers ]
  ]

RB_NoDataRaces ==
  \A i \in Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

-----------------------------------------------------------------------------
(* Helpers                                                                 *)
-----------------------------------------------------------------------------

Range(f) == { f[x] : x \in DOMAIN f }

MinReadSequence ==
  CHOOSE min \in Range(read) : \A r \in Readers : min <= read[r]

Transition(t, from, to) ==
  /\ pc[t] = from
  /\ pc'   = [ pc EXCEPT ![t] = to ]

-----------------------------------------------------------------------------
(* Producer actions                                                        *)
-----------------------------------------------------------------------------

BeginWrite(writer) ==
  LET next  == published + 1
      index == RB_IndexOf(next)
      min   == MinReadSequence
  IN
    \* Do not overwrite entries not yet read by all consumers.
    /\ min + Size > next
    /\ Transition(writer, Access, Advance)
    /\ RB_Write(index, writer, next)
    /\ UNCHANGED << consumed, published, read >>

EndWrite(writer) ==
  LET next  == published + 1
      index == RB_IndexOf(next)
  IN
    /\ Transition(writer, Advance, Access)
    /\ published' = next
    /\ RB_EndWrite(index, writer)
    /\ UNCHANGED << consumed, read >>

-----------------------------------------------------------------------------
(* Consumer actions                                                        *)
-----------------------------------------------------------------------------

BeginRead(reader) ==
  LET next  == read[reader] + 1
      index == RB_IndexOf(next)
  IN
    /\ published >= next
    /\ Transition(reader, Access, Advance)
    /\ RB_BeginRead(index, reader)
    /\ consumed' = [ consumed EXCEPT ![reader] = Append(@, RB_Read(index)) ]
    /\ UNCHANGED << published, read >>

EndRead(reader) ==
  LET next  == read[reader] + 1
      index == RB_IndexOf(next)
  IN
    /\ Transition(reader, Advance, Access)
    /\ RB_EndRead(index, reader)
    /\ read' = [ read EXCEPT ![reader] = next ]
    /\ UNCHANGED << consumed, published >>

-----------------------------------------------------------------------------
(* Spec                                                                    *)
-----------------------------------------------------------------------------

Init ==
  /\ RB_Init
  /\ published = -1
  /\ read      = [ r \in Readers |-> -1 ]
  /\ consumed  = [ r \in Readers |-> << >> ]
  /\ pc        = [ a \in Writers \union Readers |-> Access ]

Next ==
  \/ \E w \in Writers : BeginWrite(w)
  \/ \E w \in Writers : EndWrite(w)
  \/ \E r \in Readers : BeginRead(r)
  \/ \E r \in Readers : EndRead(r)

Fairness ==
  /\ \A w \in Writers : WF_vars(BeginWrite(w))
  /\ \A w \in Writers : WF_vars(EndWrite(w))
  /\ \A r \in Readers : WF_vars(BeginRead(r))
  /\ \A r \in Readers : WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* State constraint                                                        *)
-----------------------------------------------------------------------------

StateConstraint == published < MaxPublished

-----------------------------------------------------------------------------
(* Invariants                                                              *)
-----------------------------------------------------------------------------

TypeOk ==
  /\ RB_TypeOk
  /\ published \in Int
  /\ read      \in [ Readers -> Int ]
  /\ consumed  \in [ Readers -> Seq(Nat) ]
  /\ pc        \in [ Writers \union Readers -> { Access, Advance } ]

NoDataRaces == RB_NoDataRaces

-----------------------------------------------------------------------------
(* Liveness                                                                *)
-----------------------------------------------------------------------------

\* Every consumer eventually always has read every published value.
Liveliness ==
  \A r \in Readers :
    \A i \in 0 .. (MaxPublished - 1) :
      <>[](i \in Range(consumed[r]))

THEOREM Spec => [](TypeOk /\ NoDataRaces)

=============================================================================