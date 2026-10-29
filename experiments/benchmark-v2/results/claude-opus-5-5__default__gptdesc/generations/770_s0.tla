------------------------------- MODULE RingBuffer -------------------------------
(***************************************************************************)
(* A ring buffer abstraction with a fixed number of slots indexed modulo   *)
(* the buffer size. Each slot holds either a value from Values or NULL.    *)
(* The module also tracks, per slot, the set of readers and the set of     *)
(* writers currently accessing that slot, so that reads and writes can be  *)
(* modeled as multi-step (begin/end) operations.                           *)
(*                                                                         *)
(* NOTE: The begin/end actions do NOT prevent concurrent conflicting       *)
(* access. Client specifications using this module SHOULD include          *)
(* NoDataRaces as an invariant to check that they never cause a data race. *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Size,       \* number of slots in the ring buffer
    Values,     \* set of storable values
    NULL,       \* distinguished "empty" value
    Processes   \* set of process identifiers that may read or write

ASSUME SizeAssumption == Size \in Nat /\ Size > 0
ASSUME NullAssumption == NULL \notin Values

VARIABLES
    buffer,     \* buffer[i] : contents of slot i
    readers,    \* readers[i] : set of processes currently reading slot i
    writers     \* writers[i] : set of processes currently writing slot i

vars == <<buffer, readers, writers>>

Slots == 0..(Size - 1)

(***************************************************************************)
(* Index computation: any natural number maps to a slot modulo Size.       *)
(***************************************************************************)
Index(i) == i % Size

(***************************************************************************)
(* Initialization                                                          *)
(***************************************************************************)
Init ==
    /\ buffer  = [s \in Slots |-> NULL]
    /\ readers = [s \in Slots |-> {}]
    /\ writers = [s \in Slots |-> {}]

(***************************************************************************)
(* Value currently stored at logical position i.                           *)
(***************************************************************************)
Read(i) == buffer[Index(i)]

(***************************************************************************)
(* Read actions                                                            *)
(***************************************************************************)
BeginRead(p, i) ==
    LET s == Index(i) IN
    /\ p \notin readers[s]
    /\ readers' = [readers EXCEPT ![s] = @ \cup {p}]
    /\ UNCHANGED <<buffer, writers>>

EndRead(p, i) ==
    LET s == Index(i) IN
    /\ p \in readers[s]
    /\ readers' = [readers EXCEPT ![s] = @ \ {p}]
    /\ UNCHANGED <<buffer, writers>>

(***************************************************************************)
(* Write actions: the value becomes visible when the write ends.           *)
(***************************************************************************)
BeginWrite(p, i) ==
    LET s == Index(i) IN
    /\ p \notin writers[s]
    /\ writers' = [writers EXCEPT ![s] = @ \cup {p}]
    /\ UNCHANGED <<buffer, readers>>

EndWrite(p, i, v) ==
    LET s == Index(i) IN
    /\ p \in writers[s]
    /\ v \in Values \cup {NULL}
    /\ buffer'  = [buffer EXCEPT ![s] = v]
    /\ writers' = [writers EXCEPT ![s] = @ \ {p}]
    /\ UNCHANGED readers

(***************************************************************************)
(* Clearing a slot is a write of NULL.                                     *)
(***************************************************************************)
EndClear(p, i) == EndWrite(p, i, NULL)

(***************************************************************************)
(* Next-state relation (for standalone use of the module)                  *)
(***************************************************************************)
Next ==
    \E p \in Processes, i \in Slots :
        \/ BeginRead(p, i)
        \/ EndRead(p, i)
        \/ BeginWrite(p, i)
        \/ \E v \in Values \cup {NULL} : EndWrite(p, i, v)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ buffer  \in [Slots -> Values \cup {NULL}]
    /\ readers \in [Slots -> SUBSET Processes]
    /\ writers \in [Slots -> SUBSET Processes]

(***************************************************************************)
(* No data races: a slot being written has exactly one writer and no       *)
(* concurrent readers. Concurrent readers without writers are allowed.     *)
(* Client specifications using this module should include NoDataRaces     *)
(* as an invariant.                                                        *)
(***************************************************************************)
NoDataRaces ==
    \A s \in Slots :
        writers[s] # {} =>
            /\ Cardinality(writers[s]) = 1
            /\ readers[s] = {}

=============================================================================