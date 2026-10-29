---------------------------- MODULE ConcurrentRingBuffer ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    BufferSize,   \* number of slots in the ring buffer
    Readers,      \* set of consumer thread identifiers
    Writers,      \* set of producer thread identifiers
    Values,       \* set of values that may be stored
    Empty,        \* special marker denoting an empty slot
    MaxSeq        \* bound on sequence numbers, for model checking

ASSUME BufferSizeAssm == BufferSize \in Nat /\ BufferSize > 0
ASSUME ReadersAssm    == Readers # {}
ASSUME WritersAssm    == Writers # {}
ASSUME ValuesAssm     == Values # {} /\ Empty \notin Values
ASSUME MaxSeqAssm     == MaxSeq \in Nat

Slots    == 0 .. (BufferSize - 1)
SeqNums  == 0 .. MaxSeq
NoSlot   == -1

\* Wrap-around: a sequence number maps to a slot index modulo the buffer size.
IndexOf(seq) == seq % BufferSize

\* Thread sub-step phases
\*   "idle"   : no access held
\*   "begun"  : access acquired on a slot, operation not yet performed
\*   "done"   : operation performed, access still held (awaiting end)
Phases == {"idle", "begun", "done"}

VARIABLES
    buffer,    \* buffer[i] : contents of slot i (a value or Empty)
    readers,   \* readers[i]: set of consumer threads holding read access on slot i
    writers,   \* writers[i]: set of producer threads holding write access on slot i
    rstate,    \* rstate[r] : phase of consumer r
    rslot,     \* rslot[r]  : slot accessed by consumer r (or NoSlot)
    rval,      \* rval[r]   : value most recently read by consumer r
    wstate,    \* wstate[w] : phase of producer w
    wslot,     \* wslot[w]  : slot accessed by producer w (or NoSlot)
    wval       \* wval[w]   : value producer w intends to write

vars == <<buffer, readers, writers, rstate, rslot, rval, wstate, wslot, wval>>

-----------------------------------------------------------------------------
(* Type safety *)

TypeOK ==
    /\ buffer  \in [Slots -> Values \cup {Empty}]
    /\ readers \in [Slots -> SUBSET Readers]
    /\ writers \in [Slots -> SUBSET Writers]
    /\ rstate  \in [Readers -> Phases]
    /\ rslot   \in [Readers -> Slots \cup {NoSlot}]
    /\ rval    \in [Readers -> Values \cup {Empty}]
    /\ wstate  \in [Writers -> Phases]
    /\ wslot   \in [Writers -> Slots \cup {NoSlot}]
    /\ wval    \in [Writers -> Values \cup {Empty}]

-----------------------------------------------------------------------------
(* Initial state: all slots empty, no thread holds any access *)

Init ==
    /\ buffer  = [i \in Slots |-> Empty]
    /\ readers = [i \in Slots |-> {}]
    /\ writers = [i \in Slots |-> {}]
    /\ rstate  = [r \in Readers |-> "idle"]
    /\ rslot   = [r \in Readers |-> NoSlot]
    /\ rval    = [r \in Readers |-> Empty]
    /\ wstate  = [w \in Writers |-> "idle"]
    /\ wslot   = [w \in Writers |-> NoSlot]
    /\ wval    = [w \in Writers |-> Empty]

-----------------------------------------------------------------------------
(* Producer operations: BeginWrite -> DoWrite -> EndWrite *)

BeginWrite(w, seq, v) ==
    LET i == IndexOf(seq) IN
    /\ wstate[w] = "idle"
    /\ writers[i] = {}          \* no other writer on this slot
    /\ readers[i] = {}          \* no reader on this slot
    /\ writers' = [writers EXCEPT ![i] = @ \cup {w}]
    /\ wstate'  = [wstate EXCEPT ![w] = "begun"]
    /\ wslot'   = [wslot EXCEPT ![w] = i]
    /\ wval'    = [wval EXCEPT ![w] = v]
    /\ UNCHANGED <<buffer, readers, rstate, rslot, rval>>

DoWrite(w) ==
    /\ wstate[w] = "begun"
    /\ buffer' = [buffer EXCEPT ![wslot[w]] = wval[w]]
    /\ wstate' = [wstate EXCEPT ![w] = "done"]
    /\ UNCHANGED <<readers, writers, rstate, rslot, rval, wslot, wval>>

EndWrite(w) ==
    /\ wstate[w] = "done"
    /\ writers' = [writers EXCEPT ![wslot[w]] = @ \ {w}]
    /\ wstate'  = [wstate EXCEPT ![w] = "idle"]
    /\ wslot'   = [wslot EXCEPT ![w] = NoSlot]
    /\ wval'    = [wval EXCEPT ![w] = Empty]
    /\ UNCHANGED <<buffer, readers, rstate, rslot, rval>>

-----------------------------------------------------------------------------
(* Consumer operations: BeginRead -> DoRead -> EndRead *)

BeginRead(r, seq) ==
    LET i == IndexOf(seq) IN
    /\ rstate[r] = "idle"
    /\ writers[i] = {}          \* no writer on this slot
    /\ readers' = [readers EXCEPT ![i] = @ \cup {r}]
    /\ rstate'  = [rstate EXCEPT ![r] = "begun"]
    /\ rslot'   = [rslot EXCEPT ![r] = i]
    /\ UNCHANGED <<buffer, writers, rval, wstate, wslot, wval>>

DoRead(r) ==
    /\ rstate[r] = "begun"
    /\ rval'   = [rval EXCEPT ![r] = buffer[rslot[r]]]
    /\ rstate' = [rstate EXCEPT ![r] = "done"]
    /\ UNCHANGED <<buffer, readers, writers, rslot, wstate, wslot, wval>>

EndRead(r) ==
    /\ rstate[r] = "done"
    /\ readers' = [readers EXCEPT ![rslot[r]] = @ \ {r}]
    /\ rstate'  = [rstate EXCEPT ![r] = "idle"]
    /\ rslot'   = [rslot EXCEPT ![r] = NoSlot]
    /\ UNCHANGED <<buffer, writers, rval, wstate, wslot, wval>>

-----------------------------------------------------------------------------

Next ==
    \/ \E w \in Writers, seq \in SeqNums, v \in Values : BeginWrite(w, seq, v)
    \/ \E w \in Writers : DoWrite(w)
    \/ \E w \in Writers : EndWrite(w)
    \/ \E r \in Readers, seq \in SeqNums : BeginRead(r, seq)
    \/ \E r \in Readers : DoRead(r)
    \/ \E r \in Readers : EndRead(r)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

\* At most one active writer per slot.
AtMostOneWriter ==
    \A i \in Slots : Cardinality(writers[i]) <= 1

\* No slot has active readers and active writers simultaneously.
NoReadWriteOverlap ==
    \A i \in Slots : readers[i] = {} \/ writers[i] = {}

NoDataRace == AtMostOneWriter /\ NoReadWriteOverlap

\* Access bookkeeping is consistent with per-thread state.
AccessConsistent ==
    /\ \A r \in Readers :
         /\ (rstate[r] = "idle") <=> (rslot[r] = NoSlot)
         /\ \A i \in Slots : (r \in readers[i]) <=> (rstate[r] # "idle" /\ rslot[r] = i)
    /\ \A w \in Writers :
         /\ (wstate[w] = "idle") <=> (wslot[w] = NoSlot)
         /\ (wstate[w] = "idle") <=> (wval[w] = Empty)
         /\ \A i \in Slots : (w \in writers[i]) <=> (wstate[w] # "idle" /\ wslot[w] = i)

\* A consumer that has read a slot and still holds access sees stable contents.
ReadStable ==
    \A r \in Readers : rstate[r] = "done" => rval[r] = buffer[rslot[r]]

\* Stored values are never the empty marker unless the slot was never written.
BufferWellFormed ==
    /\ DOMAIN buffer = Slots
    /\ \A i \in Slots : buffer[i] \in Values \cup {Empty}

Invariants ==
    /\ TypeOK
    /\ NoDataRace
    /\ AccessConsistent
    /\ ReadStable
    /\ BufferWellFormed

-----------------------------------------------------------------------------
(* Action-level safety: slot contents are preserved except by a valid write *)

ValidWriteOn(i) ==
    \E w \in writers[i] :
        /\ wstate[w] = "begun"
        /\ wslot[w] = i
        /\ writers[i] = {w}
        /\ readers[i] = {}
        /\ buffer'[i] = wval[w]

ContentPreservation ==
    \A i \in Slots : buffer'[i] # buffer[i] => ValidWriteOn(i)

ContentPreservationProp == [][ContentPreservation]_vars

THEOREM Spec => []Invariants
THEOREM Spec => ContentPreservationProp
=============================================================================