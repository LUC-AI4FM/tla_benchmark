---------------------------- MODULE RingBuffer ----------------------------
(***************************************************************************)
(* A ring buffer abstraction with a fixed number of slots, indexed modulo  *)
(* the buffer size. Each slot holds either a value from Values or the      *)
(* distinguished value NULL.                                               *)
(*                                                                         *)
(* Reads and writes take more than one step: a begin action and an end    *)
(* action. To model this, the module tracks the set of readers and the set *)
(* of writers currently accessing each slot.                               *)
(*                                                                         *)
(* NOTE: The actions in this module do NOT prevent data races. Client      *)
(* specifications that use this module should include NoDataRaces as an   *)
(* invariant, so that the model checker confirms the clients never access *)
(* a slot in a racy way.                                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Size,       \* number of slots in the ring buffer
    Values,     \* set of values that can be stored
    Readers,    \* set of reader identifiers
    Writers,    \* set of writer identifiers
    NULL        \* distinguished "empty" value

ASSUME SizeAssumption == Size \in Nat /\ Size > 0
ASSUME NullAssumption == NULL \notin Values

VARIABLES
    slots,      \* slots[i] is the value stored in slot i
    readers,    \* readers[i] is the set of readers currently reading slot i
    writers     \* writers[i] is the set of writers currently writing slot i

vars == <<slots, readers, writers>>

Slots == 0 .. (Size - 1)

(***************************************************************************)
(* Index computation: map an arbitrary natural number onto a slot.         *)
(***************************************************************************)
IndexOf(i) == i % Size

(***************************************************************************)
(* Initialization: every slot is empty and nobody is accessing any slot.  *)
(***************************************************************************)
Init ==
    /\ slots   = [i \in Slots |-> NULL]
    /\ readers = [i \in Slots |-> {}]
    /\ writers = [i \in Slots |-> {}]

(***************************************************************************)
(* Reading a slot: BeginRead registers the reader on the slot. EndRead     *)
(* deregisters it; the value read is slots[IndexOf(i)].                   *)
(***************************************************************************)
BeginRead(i, r) ==
    LET idx == IndexOf(i) IN
    /\ r \notin readers[idx]
    /\ readers' = [readers EXCEPT ![idx] = @ \cup {r}]
    /\ UNCHANGED <<slots, writers>>

EndRead(i, r) ==
    LET idx == IndexOf(i) IN
    /\ r \in readers[idx]
    /\ readers' = [readers EXCEPT ![idx] = @ \ {r}]
    /\ UNCHANGED <<slots, writers>>

(* The value currently held by the slot that index i maps to. *)
Read(i) == slots[IndexOf(i)]

(***************************************************************************)
(* Writing a slot: BeginWrite registers the writer on the slot. EndWrite  *)
(* stores the value (which may be NULL, to clear the slot) and            *)
(* deregisters the writer.                                                 *)
(***************************************************************************)
BeginWrite(i, w) ==
    LET idx == IndexOf(i) IN
    /\ w \notin writers[idx]
    /\ writers' = [writers EXCEPT ![idx] = @ \cup {w}]
    /\ UNCHANGED <<slots, readers>>

EndWrite(i, w, v) ==
    LET idx == IndexOf(i) IN
    /\ w \in writers[idx]
    /\ slots'   = [slots EXCEPT ![idx] = v]
    /\ writers' = [writers EXCEPT ![idx] = @ \ {w}]
    /\ UNCHANGED readers

(***************************************************************************)
(* Next-state relation: the most general client of the buffer.            *)
(***************************************************************************)
Next ==
    \/ \E i \in Slots, r \in Readers : BeginRead(i, r)
    \/ \E i \in Slots, r \in Readers : EndRead(i, r)
    \/ \E i \in Slots, w \in Writers : BeginWrite(i, w)
    \/ \E i \in Slots, w \in Writers, v \in Values \cup {NULL} :
           EndWrite(i, w, v)

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ slots   \in [Slots -> Values \cup {NULL}]
    /\ readers \in [Slots -> SUBSET Readers]
    /\ writers \in [Slots -> SUBSET Writers]

(***************************************************************************)
(* No data races: while a slot is being written, exactly one writer and   *)
(* no reader may access it. Any number of concurrent readers is allowed   *)
(* when no writer is active.                                              *)
(*                                                                         *)
(* Client specifications using this module should include NoDataRaces as  *)
(* an invariant.                                                           *)
(***************************************************************************)
NoDataRaces ==
    \A i \in Slots :
        writers[i] # {} =>
            /\ Cardinality(writers[i]) = 1
            /\ readers[i] = {}

=============================================================================