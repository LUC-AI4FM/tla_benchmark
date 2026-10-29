--------------------------- MODULE AsynchInterface ---------------------------
(***************************************************************************)
(* An asynchronous communication channel between a sender and a receiver.  *)
(* The channel uses a two-phase (alternating bit) Ready/Acknowledge        *)
(* handshake:                                                              *)
(*   - val : the data value currently on the channel                       *)
(*   - rdy : toggled by the sender when new data has been placed           *)
(*   - ack : toggled by the receiver when the data has been consumed       *)
(* The channel is "empty" (ready for new data) when rdy = ack, and it      *)
(* holds unacknowledged data when rdy # ack.                               *)
(*                                                                         *)
(* The set of transmittable values is the parameter Data, so the module    *)
(* can be instantiated with any data domain and composed into larger       *)
(* specifications, for example via                                         *)
(*   C == INSTANCE AsynchInterface WITH Data <- Msg, val <- v, ...         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack

vars == << val, rdy, ack >>

---------------------------------------------------------------------------
(* Type correctness *)

TypeInvariant ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack \in {0, 1}

---------------------------------------------------------------------------
(* Initial state: some arbitrary value is on the channel, nothing pending. *)

Init ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack = rdy

(* The sender places a new value d on the channel. It may do so only when *)
(* the previous value has been acknowledged (rdy = ack), so it never      *)
(* overwrites unacknowledged data.                                        *)
Send(d) ==
    /\ rdy = ack
    /\ val' = d
    /\ rdy' = 1 - rdy
    /\ UNCHANGED ack

(* The receiver reads and acknowledges the value on the channel. It may   *)
(* do so only when there is unacknowledged data (rdy # ack). After this   *)
(* step rdy = ack, so the same value cannot be received again.            *)
Rcv ==
    /\ rdy # ack
    /\ ack' = 1 - ack
    /\ UNCHANGED << val, rdy >>

Next == (\E d \in Data : Send(d)) \/ Rcv

(* Safety-only specification, suitable for composition. *)
SafetySpec == Init /\ [][Next]_vars

(* Full specification: the receiver eventually consumes pending data. *)
Spec == SafetySpec /\ WF_vars(Rcv)

---------------------------------------------------------------------------
(* Correctness properties *)

(* Data is pending exactly when the handshake bits differ. *)
Pending == rdy # ack

(* Proper sequencing: the sender writes only when the channel is empty,   *)
(* and the receiver acknowledges only when data is pending.               *)
SendOnlyWhenAcked ==
    [][ \A d \in Data : Send(d) => rdy = ack ]_vars

RcvOnlyWhenReady ==
    [][ Rcv => rdy # ack ]_vars

(* Handshake signals alternate: in every step at most one of rdy/ack      *)
(* changes; rdy changes only when rdy = ack, ack changes only when        *)
(* rdy # ack.                                                             *)
ProperSequencing ==
    [][ /\ ~(rdy' # rdy /\ ack' # ack)
        /\ (rdy' # rdy) => (rdy = ack)
        /\ (ack' # ack) => (rdy # ack) ]_vars

(* No data loss: while data is unacknowledged, the value on the channel   *)
(* cannot change.                                                         *)
NoDataLoss ==
    [][ Pending => val' = val ]_vars

(* No duplication: every acknowledgement consumes the pending value and   *)
(* leaves the channel empty, so a value cannot be received twice without  *)
(* an intervening Send.                                                   *)
NoDuplication ==
    [][ (ack' # ack) => (Pending /\ ~Pending') ]_vars

(* Liveness: every value placed on the channel is eventually received. *)
EventuallyReceived ==
    Pending ~> ~Pending

---------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
THEOREM Spec => SendOnlyWhenAcked /\ RcvOnlyWhenReady /\ ProperSequencing
THEOREM Spec => NoDataLoss /\ NoDuplication
THEOREM Spec => EventuallyReceived
=============================================================================