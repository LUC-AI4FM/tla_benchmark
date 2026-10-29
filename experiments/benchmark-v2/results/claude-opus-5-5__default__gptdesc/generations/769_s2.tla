------------------------------ MODULE Disruptor_SPMC ------------------------------
(***************************************************************************)
(* Single Producer, Multi Consumer Disruptor.                              *)
(* A single producer publishes sequence numbers 0, 1, 2, ... into a ring   *)
(* buffer. Several consumers each read every published value (multicast).  *)
(* The ring buffer operations are defined below with the RB_ prefix. They  *)
(* correspond to an instantiation of a RingBuffer module with              *)
(* Values <- Nat and Writers <- {Writer}.                                  *)
(***************************************************************************)
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS
  MaxPublished,  \* Max number of published events (bounds the model).
  Writer,        \* The single producer/writer.
  Readers,       \* Set of consumers/readers.
  Size,          \* Ring buffer size.
  NULL           \* Value of an empty slot.

ASSUME /\ MaxPublished \in Nat \ {0}
       /\ Size \in Nat \ {0}
       /\ Writer \notin Readers
       /\ Readers # {}
       /\ NULL \notin Nat

VARIABLES
  ringbuffer,   \* The ring buffer: slots plus active readers/writers per slot.
  published,    \* Sequence number of the last published event.
  read,         \* read[r]: sequence number of the last event read by r.
  consumed,     \* consumed[r]: sequence of values read by r (for checking).
  pc            \* Program counter of each actor.

vars == << ringbuffer, published, read, consumed, pc >>

Access  == "Access"
Advance == "Advance"

Actors == {Writer} \cup Readers

(***************************************************************************)
(* Ring buffer (inlined RingBuffer module with Values <- Nat).            *)
(***************************************************************************)
RB_Values  == Nat
RB_Writers == {Writer}
RB_Readers == Readers

RB_LastIndex == Size - 1
RB_Indices   == 0 .. RB_LastIndex

RB_Init ==
  ringbuffer = [ slots   |-> [ i \in RB_Indices |-> NULL ],
                 readers |-> [ i \in RB_Indices |-> {} ],
                 writers |-> [ i \in RB_Indices |-> {} ] ]

RB_IndexOf(sequence) == sequence % Size

RB_Write(index, writer, value) ==
  ringbuffer' = [ ringbuffer EXCEPT
                    !.writers[index] = @ \cup {writer},
                    !.slots[index]   = value ]

RB_EndWrite(index, writer) ==
  ringbuffer' = [ ringbuffer EXCEPT !.writers[index] = @ \ {writer} ]

RB_BeginRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \cup {reader} ]

RB_Read(index) == ringbuffer.slots[index]

RB_EndRead(index, reader) ==
  ringbuffer' = [ ringbuffer EXCEPT !.readers[index] = @ \ {reader} ]

RB_TypeOk ==
  ringbuffer \in [ slots   : [ RB_Indices -> RB_Values \cup {NULL} ],
                   readers : [ RB_Indices -> SUBSET RB_Readers ],
                   writers : [ RB_Indices -> SUBSET RB_Writers ] ]

RB_NoDataRaces ==
  \A i \in RB_Indices :
    /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
    /\ Cardinality(ringbuffer.writers[i]) <= 1

(***************************************************************************)
(* Helpers                                                                 *)
(***************************************************************************)
Transition(t, from, to) ==
  /\ pc[t]  = from
  /\ pc'    = [ pc EXCEPT ![t] = to ]

Range(f) == { f[x] : x \in DOMAIN f }

MinReadSequence ==
  CHOOSE min \in Range(read) : \A r \in Readers : min <= read[r]

(***************************************************************************)
(* Producer actions                                                        *)
(***************************************************************************)
BeginWrite ==
  LET next     == published + 1
      index    == RB_IndexOf(next)
      min_read == MinReadSequence
  IN
    \* Are we clear of all consumers? (Potentially a full cycle behind.)
    /\ min_read >= next - Size
    /\ Transition(Writer, Access, Advance)
    /\ RB_Write(index, Writer, next)
    /\ UNCHANGED << published, read, consumed >>

EndWrite ==
  LET next  == published + 1
      index == RB_IndexOf(next)
  IN
    /\ Transition(Writer, Advance, Access)
    /\ RB_EndWrite(index, Writer)
    /\ published' = next
    /\ UNCHANGED << read, consumed >>

(***************************************************************************)
(* Consumer actions                                                        *)
(***************************************************************************)
BeginRead(reader) ==
  LET next  == read[reader] + 1
      index == RB_IndexOf(next)
  IN
    /\ published >= next
    /\ Transition(reader, Access, Advance)
    /\ RB_BeginRead(index, reader)
    \* Track what has been read (for checking purposes).
    /\ consumed' = [ consumed EXCEPT ![reader] = Append(@, RB_Read(index)) ]
    /\ UNCHANGED << published, read >>

EndRead(reader) ==
  LET next  == read[reader] + 1
      index == RB_IndexOf(next)
  IN
    /\ Transition(reader, Advance, Access)
    /\ RB_EndRead(index, reader)
    /\ read' = [ read EXCEPT ![reader] = next ]
    /\ UNCHANGED << published, consumed >>

(***************************************************************************)
(* Spec                                                                    *)
(***************************************************************************)
Init ==
  /\ RB_Init
  /\ published = -1
  /\ read      = [ r \in Readers |-> -1 ]
  /\ consumed  = [ r \in Readers |-> << >> ]
  /\ pc        = [ a \in Actors  |-> Access ]

Next ==
  \/ BeginWrite
  \/ EndWrite
  \/ \E r \in Readers : BeginRead(r) \/ EndRead(r)

Fairness ==
  /\ WF_vars(BeginWrite)
  /\ WF_vars(EndWrite)
  /\ \A r \in Readers : WF_vars(BeginRead(r))
  /\ \A r \in Readers : WF_vars(EndRead(r))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* State constraint to bound exploration                                   *)
(***************************************************************************)
StateConstraint == published < MaxPublished

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOk ==
  /\ RB_TypeOk
  /\ published \in Int
  /\ read      \in [ Readers -> Int ]
  /\ consumed  \in [ Readers -> Seq(Nat) ]
  /\ pc        \in [ Actors  -> { Access, Advance } ]

NoDataRaces == RB_NoDataRaces

(***************************************************************************)
(* Liveness: every consumer eventually always has read each published     *)
(* value, in order.                                                        *)
(***************************************************************************)
Liveliness ==
  \A r \in Readers :
    \A i \in 0 .. (MaxPublished - 1) :
      <>[] ( /\ Len(consumed[r]) > i
             /\ consumed[r][i + 1] = i )

THEOREM Spec => [](TypeOk /\ NoDataRaces)
===================================================================================