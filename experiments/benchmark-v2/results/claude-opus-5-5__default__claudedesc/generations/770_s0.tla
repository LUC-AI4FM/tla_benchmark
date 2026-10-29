------------------------------ MODULE RingBuffer ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Size,       \* number of slots in the ring buffer
    Values,     \* set of values that may be stored
    Readers,    \* set of readers that may access the buffer
    Writers,    \* set of writers that may access the buffer
    NULL        \* marker for an empty slot

ASSUME SizeAssumption  == Size \in Nat /\ Size > 0
ASSUME NullAssumption  == NULL \notin Values

VARIABLES ringbuffer

vars == << ringbuffer >>

Indices == 0 .. (Size - 1)

-----------------------------------------------------------------------------
(* Map a sequence number onto a slot index *)
IndexOf(seq) == seq % Size

-----------------------------------------------------------------------------
TypeOk ==
    /\ ringbuffer \in [ slots   : [Indices -> Values \cup {NULL}],
                        readers : [Indices -> SUBSET Readers],
                        writers : [Indices -> SUBSET Writers] ]

Init ==
    ringbuffer = [ slots   |-> [i \in Indices |-> NULL],
                   readers |-> [i \in Indices |-> {}],
                   writers |-> [i \in Indices |-> {}] ]

-----------------------------------------------------------------------------
(* Write access: Write registers the writer and stores a value; *)
(* EndWrite deregisters the writer.                             *)

Write(i, writer, value) ==
    ringbuffer' = [ ringbuffer EXCEPT
                        !.slots[i]   = value,
                        !.writers[i] = @ \cup {writer} ]

EndWrite(i, writer) ==
    ringbuffer' = [ ringbuffer EXCEPT
                        !.writers[i] = @ \ {writer} ]

(* Read access: BeginRead registers the reader, Read returns the slot *)
(* value, EndRead deregisters the reader.                             *)

BeginRead(i, reader) ==
    ringbuffer' = [ ringbuffer EXCEPT
                        !.readers[i] = @ \cup {reader} ]

Read(i) == ringbuffer.slots[i]

EndRead(i, reader) ==
    ringbuffer' = [ ringbuffer EXCEPT
                        !.readers[i] = @ \ {reader} ]

-----------------------------------------------------------------------------
(* Generic next-state relation (specifications using this module are   *)
(* expected to define their own, built from the operations above).    *)

Next ==
    \E i \in Indices :
        \/ \E w \in Writers, v \in Values : Write(i, w, v)
        \/ \E w \in Writers : /\ w \in ringbuffer.writers[i]
                              /\ EndWrite(i, w)
        \/ \E r \in Readers : BeginRead(i, r)
        \/ \E r \in Readers : /\ r \in ringbuffer.readers[i]
                              /\ EndRead(i, r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety: no slot is accessed concurrently by readers and writers, *)
(* and at most one writer accesses any slot at a time.              *)

NoDataRaces ==
    \A i \in Indices :
        /\ ringbuffer.readers[i] = {} \/ ringbuffer.writers[i] = {}
        /\ Cardinality(ringbuffer.writers[i]) <= 1

THEOREM Spec => []TypeOk
=============================================================================