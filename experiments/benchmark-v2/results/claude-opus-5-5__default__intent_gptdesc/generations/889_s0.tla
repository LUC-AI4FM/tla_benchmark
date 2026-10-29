------------------------------ MODULE AsyncChannel ------------------------------
(***************************************************************************)
(* Asynchronous point-to-point channel with one sender and one receiver,   *)
(* using a two-phase ready/ack handshake.                                  *)
(*                                                                         *)
(* Each flag has a single owner. The sender toggles only `ready`. The      *)
(* receiver toggles only `ack`. No action updates both sides' flags at     *)
(* once.                                                                   *)
(*   ready # ack : the channel holds a datum that is not yet acknowledged. *)
(*   ready = ack : the previous datum (if any) has been acknowledged, so   *)
(*                 the channel is free and may be (over)written.           *)
(* The receiver works in two separate steps. It first Reads the datum into *)
(* a local buffer, then Acks it.                                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Data,        \* finite set of data items
    NoVal,       \* model value standing for "no datum"
    InitReady,   \* initial value of the sender's ready flag
    InitAck      \* initial value of the receiver's ack flag

ASSUME
    /\ IsFiniteSet(Data)
    /\ Data # {}
    /\ NoVal \notin Data
    /\ InitReady \in BOOLEAN
    /\ InitAck \in BOOLEAN

VARIABLES
    val,        \* value currently stored in the channel
    ready,      \* sender's "new data ready" flag (owned by sender)
    ack,        \* receiver's acknowledgement flag (owned by receiver)
    rbuf,       \* receiver's local copy of a datum read but not yet acked
    \* ---- ghost / history variables used only for specification ----
    lastSent,   \* most recently written datum
    everSent,   \* set of all data ever written
    lastAcked,  \* most recently acknowledged datum
    pending     \* TRUE iff a written datum is not yet acknowledged

vars == << val, ready, ack, rbuf, lastSent, everSent, lastAcked, pending >>

DataOrNone == Data \cup {NoVal}

-----------------------------------------------------------------------------
TypeOK ==
    /\ val \in DataOrNone
    /\ ready \in BOOLEAN
    /\ ack \in BOOLEAN
    /\ rbuf \in DataOrNone
    /\ lastSent \in DataOrNone
    /\ everSent \subseteq Data
    /\ lastAcked \in DataOrNone
    /\ pending \in BOOLEAN

(***************************************************************************)
(* Initial state. It is parameterised by InitReady and InitAck.            *)
(* If the two flags differ, the channel starts out holding an              *)
(* unacknowledged datum. That datum is treated as already written.         *)
(***************************************************************************)
Init ==
    /\ ready = InitReady
    /\ ack = InitAck
    /\ rbuf = NoVal
    /\ lastAcked = NoVal
    /\ IF InitReady = InitAck
          THEN /\ val = NoVal
               /\ lastSent = NoVal
               /\ everSent = {}
               /\ pending = FALSE
          ELSE /\ val \in Data
               /\ lastSent = val
               /\ everSent = {val}
               /\ pending = TRUE

-----------------------------------------------------------------------------
(***************************************************************************)
(* Sender writes datum d. This is allowed only when the channel is empty   *)
(* or the previous datum has been acknowledged (ready = ack). Unacked data *)
(* is therefore never overwritten. The sender changes only its own flag.   *)
(***************************************************************************)
Write(d) ==
    /\ ready = ack
    /\ val' = d
    /\ ready' = ~ready
    /\ lastSent' = d
    /\ everSent' = everSent \cup {d}
    /\ pending' = TRUE
    /\ UNCHANGED << ack, rbuf, lastAcked >>

(***************************************************************************)
(* Receiver reads the datum. This is allowed only when data is ready and   *)
(* the datum has not already been read.                                    *)
(***************************************************************************)
Read ==
    /\ ready # ack
    /\ rbuf = NoVal
    /\ rbuf' = val
    /\ UNCHANGED << val, ready, ack, lastSent, everSent, lastAcked, pending >>

(***************************************************************************)
(* Receiver acknowledges the datum it has read. This consumes the datum.   *)
(* The receiver changes only its own flag.                                 *)
(***************************************************************************)
Ack ==
    /\ rbuf # NoVal
    /\ ack' = ~ack
    /\ lastAcked' = rbuf
    /\ rbuf' = NoVal
    /\ pending' = FALSE
    /\ UNCHANGED << val, ready, lastSent, everSent >>

SenderStep   == \E d \in Data : Write(d)
ReceiverStep == Read \/ Ack

Next == SenderStep \/ ReceiverStep

Fairness ==
    /\ WF_vars(SenderStep)
    /\ WF_vars(Read)
    /\ WF_vars(Ack)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*************************** SAFETY PROPERTIES *****************************)

\* No phantom data: the receiver never holds or acknowledges a datum
\* that was never written.
NoPhantomData ==
    /\ (rbuf # NoVal) => rbuf \in everSent
    /\ (lastAcked # NoVal) => lastAcked \in everSent

\* No corruption: the value read equals the value most recently written,
\* and that value is still the one stored in the channel.
NoCorruption ==
    /\ (rbuf # NoVal) => (rbuf = lastSent /\ rbuf = val)
    /\ (lastAcked # NoVal /\ ~pending) => lastAcked = lastSent

\* No data loss and no race: a datum is outstanding exactly when the
\* handshake flags differ. The receiver holds data only while it is outstanding.
NoRace ==
    /\ pending <=> (ready # ack)
    /\ (rbuf # NoVal) => (ready # ack)
    /\ pending => val = lastSent

\* Action-level safety: the sender never overwrites unacknowledged data.
\* Every write occurs only after the previous datum was acknowledged.
NoOverwriteUnacked ==
    [][ pending => (val' = val /\ lastSent' = lastSent) ]_vars

WriteOnlyWhenAcked ==
    [][ \A d \in Data : Write(d) => ~pending ]_vars

Safety ==
    /\ TypeOK
    /\ NoPhantomData
    /\ NoCorruption
    /\ NoRace

-----------------------------------------------------------------------------
(*************************** LIVENESS PROPERTIES ***************************)

\* Every written datum is eventually read and acknowledged.
WrittenEventuallyAcked ==
    \A d \in Data : (pending /\ lastSent = d) ~> (~pending /\ lastAcked = d)

\* Data that is ready is eventually read.
ReadyEventuallyRead ==
    (ready # ack /\ rbuf = NoVal) ~> (rbuf # NoVal \/ ready = ack)

\* The channel never gets stuck in an intermediate state.
NoPermanentPending == (ready # ack) ~> (ready = ack)
NoPermanentRead    == (rbuf # NoVal) ~> (rbuf = NoVal)

\* The protocol keeps making progress.
InfinitelyOftenAcked == []<>(~pending)
InfinitelyOftenSent  == []<>(pending)

Liveness ==
    /\ WrittenEventuallyAcked
    /\ ReadyEventuallyRead
    /\ NoPermanentPending
    /\ NoPermanentRead
    /\ InfinitelyOftenAcked
    /\ InfinitelyOftenSent

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => NoOverwriteUnacked /\ WriteOnlyWhenAcked
THEOREM Spec => Liveness
=============================================================================