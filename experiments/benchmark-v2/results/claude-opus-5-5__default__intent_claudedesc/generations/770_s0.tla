---------------------------- MODULE RingBuffer ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Size,       \* Number of slots in the ring buffer
    Readers,    \* Set of reader thread identifiers
    Writers,    \* Set of writer thread identifiers
    Values,     \* Set of valid values that may be stored in a slot
    NULL        \* Marker for an empty slot

ASSUME SizeAssumption   == Size \in Nat /\ Size > 0
ASSUME NullAssumption   == NULL \notin Values
ASSUME ReadersFinite    == IsFiniteSet(Readers)
ASSUME WritersFinite    == IsFiniteSet(Writers)

VARIABLE ringbuffer

vars == << ringbuffer >>

-----------------------------------------------------------------------------
(* Helpers                                                                 *)
-----------------------------------------------------------------------------

LastIndex == Size - 1

Indices == 0 .. LastIndex

\* Convert a (monotonically increasing) sequence number to a buffer index.
IndexOf(sequence) == sequence % Size

-----------------------------------------------------------------------------
(* Initial state: all slots empty, no active readers or writers            *)
-----------------------------------------------------------------------------

Init ==
    ringbuffer = [ slots   |-> [ i \in Indices |-> NULL ],
                   readers |-> [ i \in Indices |-> {} ],
                   writers |-> [ i \in Indices |-> {} ] ]

-----------------------------------------------------------------------------
(* Non-atomic operations, intended for use by client specifications.       *)
(* These operators do not enforce synchronization; the client protocol    *)
(* is responsible for preserving NoDataRaces.                              *)
-----------------------------------------------------------------------------

\* Begin a write: the writer becomes active on the slot and stores the value.
Write(index, writer, value) ==
    ringbuffer' = [ ringbuffer EXCEPT
                      !.writers[index] = @ \union {writer},
                      !.slots[index]   = value ]

\* Complete a write: the writer is no longer active on the slot.
EndWrite(index, writer) ==
    ringbuffer' = [ ringbuffer EXCEPT
                      !.writers[index] = @ \ {writer} ]

\* Begin a read: the reader becomes active on the slot.
BeginRead(index, reader) ==
    ringbuffer' = [ ringbuffer EXCEPT
                      !.readers[index] = @ \union {reader} ]

\* Access the current value of a slot (state function, no state change).
Read(index) == ringbuffer.slots[index]

\* Complete a read: the reader is no longer active on the slot.
EndRead(index, reader) ==
    ringbuffer' = [ ringbuffer EXCEPT
                      !.readers[index] = @ \ {reader} ]

-----------------------------------------------------------------------------
(* Standalone (unconstrained) environment for exercising the module.      *)
(* Arbitrary threads may begin/end reads and writes on arbitrary slots;   *)
(* this is precisely what allows data races to be detected by the checker. *)
-----------------------------------------------------------------------------

BeginWriteStep(i, w, v) ==
    /\ w \notin ringbuffer.writers[i]
    /\ Write(i, w, v)

EndWriteStep(i, w) ==
    /\ w \in ringbuffer.writers[i]
    /\ EndWrite(i, w)

BeginReadStep(i, r) ==
    /\ r \notin ringbuffer.readers[i]
    /\ BeginRead(i, r)

EndReadStep(i, r) ==
    /\ r \in ringbuffer.readers[i]
    /\ EndRead(i, r)

Next ==
    \/ \E i \in Indices, w \in Writers, v \in Values : BeginWriteStep(i, w, v)
    \/ \E i \in Indices, w \in Writers               : EndWriteStep(i, w)
    \/ \E i \in Indices, r \in Readers               : BeginReadStep(i, r)
    \/ \E i \in Indices, r \in Readers               : EndReadStep(i, r)

Fairness ==
    /\ \A i \in Indices, w \in Writers : WF_vars(EndWriteStep(i, w))
    /\ \A i \in Indices, r \in Readers : WF_vars(EndReadStep(i, r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties                                                       *)
-----------------------------------------------------------------------------

TypeOK ==
    /\ ringbuffer \in [ slots   : [ Indices -> Values \union {NULL} ],
                        readers : [ Indices -> SUBSET Readers ],
                        writers : [ Indices -> SUBSET Writers ] ]

\* Data race freedom: must be preserved by the client protocol.
NoDataRaces ==
    \A i \in Indices :
        /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
        /\ Cardinality(ringbuffer.writers[i]) <= 1

-----------------------------------------------------------------------------
(* Liveness properties                                                     *)
-----------------------------------------------------------------------------

\* Every in-progress write eventually completes.
WritesComplete ==
    \A i \in Indices, w \in Writers :
        (w \in ringbuffer.writers[i]) ~> (w \notin ringbuffer.writers[i])

\* Every in-progress read eventually completes.
ReadsComplete ==
    \A i \in Indices, r \in Readers :
        (r \in ringbuffer.readers[i]) ~> (r \notin ringbuffer.readers[i])

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
=============================================================================