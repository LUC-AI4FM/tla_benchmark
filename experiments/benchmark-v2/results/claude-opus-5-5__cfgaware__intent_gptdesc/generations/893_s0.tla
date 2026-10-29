------------------------- MODULE AsynchInterface -------------------------
(***************************************************************************)
(* A single-message asynchronous channel with a handshake between a       *)
(* sender and a receiver.  The channel holds one data value (val) and two  *)
(* bits: rdy (ready) and ack (acknowledge).                                *)
(*   - rdy = ack : the previous value has been acknowledged, so the       *)
(*                 sender may write a new value.                           *)
(*   - rdy # ack : an unacknowledged value is present, so the receiver    *)
(*                 may acknowledge it.                                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

VARIABLES val, rdy, ack

vars == << val, rdy, ack >>

-----------------------------------------------------------------------------
(* Type correctness *)

TypeInvariant == /\ val \in Data
                 /\ rdy \in {0, 1}
                 /\ ack \in {0, 1}

-----------------------------------------------------------------------------
(* Initial state: a valid data element, and the bits are equal. *)

Init == /\ val \in Data
        /\ rdy \in {0, 1}
        /\ ack = rdy

(* Sender: allowed only when the previous value was acknowledged.        *)
(* It stores a nondeterministically chosen value and flips rdy.          *)
Send == /\ rdy = ack
        /\ \E d \in Data : val' = d
        /\ rdy' = 1 - rdy
        /\ UNCHANGED ack

(* Receiver: allowed only when an unacknowledged value is present.       *)
(* It flips ack so that it matches rdy.                                  *)
Rcv == /\ rdy # ack
       /\ ack' = 1 - ack
       /\ UNCHANGED << val, rdy >>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties of the handshake *)

(* The bits are always well formed; any combination of two bits in      *)
(* {0,1} is either "equal" (slot empty) or "different" (slot full).      *)
ValidBits == (rdy = ack) \/ (rdy # ack /\ rdy = 1 - ack)

(* A value is never overwritten before it has been acknowledged:         *)
(* whenever val or rdy changes, the slot was empty beforehand.           *)
NoOverwrite == [][(rdy' # rdy) => (rdy = ack)]_vars

(* A value is never acknowledged when absent:                           *)
(* whenever ack changes, an unacknowledged value was present.            *)
NoSpuriousAck == [][(ack' # ack) => (rdy # ack)]_vars

(* rdy becomes equal to ack only by a receiver step (or initially).      *)
EqualOnlyAfterRcv ==
    [][(rdy' = ack' /\ rdy # ack) => (ack' # ack /\ UNCHANGED << val, rdy >>)]_vars

(* Received value is stable: while unacknowledged, the value is kept.    *)
ValueStableUntilAck == [][(rdy # ack) => (val' = val)]_vars

(* Each step flips exactly one bit, so the bits never jump.             *)
OneBitAtATime == [][(rdy' # rdy) # (ack' # ack)]_vars

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM TypeCorrect == Spec => []TypeInvariant

THEOREM SendPreservesType ==
    TypeInvariant /\ Send => TypeInvariant'

THEOREM RcvPreservesType ==
    TypeInvariant /\ Rcv => TypeInvariant'

THEOREM BitsValid == Spec => []ValidBits

THEOREM HandshakeNoOverwrite == Spec => NoOverwrite

THEOREM HandshakeNoSpuriousAck == Spec => NoSpuriousAck

THEOREM HandshakeEqualOnlyAfterRcv == Spec => EqualOnlyAfterRcv

THEOREM HandshakeValueStable == Spec => ValueStableUntilAck

THEOREM HandshakeOneBit == Spec => OneBitAtATime

=============================================================================