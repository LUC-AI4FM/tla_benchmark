------------------------------- MODULE RingBuffer -------------------------------
(***************************************************************************)
(* A ring buffer abstraction with a fixed number of slots, indexed modulo  *)
(* the buffer size.  Each slot stores either a value from Values or the    *)
(* distinguished value NULL.  The module also tracks the set of readers    *)
(* and the set of writers currently accessing each slot.  This lets reads  *)
(* and writes be modeled as multi-step operations, so that data races can  *)
(* be detected.                                                            *)
(*                                                                         *)
(* The begin/end actions deliberately do NOT prevent races.  Any client    *)
(* specification that uses this module SHOULD include NoDataRaces as an    *)
(* invariant, so that racy client behaviour is reported by the checker.    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Size,       \* number of slots in the ring buffer
    Values,     \* set of values that may be stored in a slot
    Processes   \* set of processes that may read or write slots

ASSUME SizeAssumption == Size \in Nat \ {0}

NULL == CHOOSE v : v \notin Values

VARIABLES
    buffer,     \* buffer[s] : contents of slot s
    readers,    \* readers[s] : processes currently reading slot s
    writers     \* writers[s] : processes currently writing slot s

vars == << buffer, readers, writers >>

Slots == 0 .. (Size - 1)

(***************************************************************************)
(* Index computation: map an arbitrary natural number onto a slot.         *)
(***************************************************************************)
Index(i) == i % Size

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ buffer  \in [Slots -> Values \cup {NULL}]
    /\ readers \in [Slots -> SUBSET Processes]
    /\ writers \in [Slots -> SUBSET Processes]

(***************************************************************************)
(* No data races: a slot being written has exactly one writer and no       *)
(* readers.  Client specifications should check this invariant.            *)
(***************************************************************************)
NoDataRaces ==
    \A s \in Slots :
        writers[s] # {} => /\ Cardinality(writers[s]) = 1
                           /\ readers[s] = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init ==
    /\ buffer  = [s \in Slots |-> NULL]
    /\ readers = [s \in Slots |-> {}]
    /\ writers = [s \in Slots |-> {}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Multi-step read                                                         *)
(***************************************************************************)
BeginRead(i, p) ==
    LET s == Index(i) IN
    /\ p \notin readers[s]
    /\ readers' = [readers EXCEPT ![s] = @ \cup {p}]
    /\ UNCHANGED << buffer, writers >>

\* The value obtained by a completed read of slot Index(i).
ReadValue(i) == buffer[Index(i)]

EndRead(i, p) ==
    LET s == Index(i) IN
    /\ p \in readers[s]
    /\ readers' = [readers EXCEPT ![s] = @ \ {p}]
    /\ UNCHANGED << buffer, writers >>

(***************************************************************************)
(* Multi-step write                                                        *)
(***************************************************************************)
BeginWrite(i, p) ==
    LET s == Index(i) IN
    /\ p \notin writers[s]
    /\ writers' = [writers EXCEPT ![s] = @ \cup {p}]
    /\ UNCHANGED << buffer, readers >>

\* The write takes effect when it completes.
\* v may be NULL, for example to clear a slot.
EndWrite(i, p, v) ==
    LET s == Index(i) IN
    /\ p \in writers[s]
    /\ v \in Values \cup {NULL}
    /\ buffer'  = [buffer  EXCEPT ![s] = v]
    /\ writers' = [writers EXCEPT ![s] = @ \ {p}]
    /\ UNCHANGED readers

-----------------------------------------------------------------------------
(***************************************************************************)
(* Standalone next-state relation and specification                        *)
(***************************************************************************)
Next ==
    \E i \in Slots, p \in Processes :
        \/ BeginRead(i, p)
        \/ EndRead(i, p)
        \/ BeginWrite(i, p)
        \/ \E v \in Values \cup {NULL} : EndWrite(i, p, v)

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeOK
=============================================================================