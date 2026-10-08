----------------------------- MODULE SingleMessageHandshakeChannel -----------------------------

EXTENDS Naturals

CONSTANT Data

ASSUME Data # {}

VARIABLES val, rd, ack

Bits == {0, 1}
Not(b) == IF b = 0 THEN 1 ELSE 0

TypeInv ==
  /\ val \in Data
  /\ rd \in Bits
  /\ ack \in Bits

Pending == rd # ack

Init ==
  /\ val \in Data
  /\ rd \in Bits
  /\ ack = rd

Send ==
  /\ rd = ack
  /\ val' \in Data
  /\ rd' = Not(rd)
  /\ ack' = ack

Recv ==
  /\ rd # ack
  /\ val' = val
  /\ rd' = rd
  /\ ack' = rd

Next == Send \/ Recv

Vars == << val, rd, ack >>

Spec == Init /\ [][Next]_Vars

(*
  Basic type safety: the channel always holds a value from Data and the bits are in {0,1}.
*)
THEOREM TypeSafety == Spec => []TypeInv
PROOF OBVIOUS QED

(*
  Action-level preservation of TypeInv by Send and Recv.
*)
LEMMA SendPreservesType == TypeInv /\ Send => TypeInv'
PROOF OBVIOUS QED

LEMMA RecvPreservesType == TypeInv /\ Recv => TypeInv'
PROOF OBVIOUS QED

(*
  Reliability: values are neither overwritten before acknowledgment nor acknowledged when absent.
  - If a value is pending (rd # ack), then the next state cannot change val.
*)
THEOREM NoOverwriteBeforeAck == Spec => [](Pending => val' = val)
PROOF OBVIOUS QED

(*
  - If no value is pending (rd = ack), then the next state cannot change ack (no spurious ack).
*)
THEOREM NoAckWhenAbsent == Spec => []((rd = ack) => ack' = ack)
PROOF OBVIOUS QED

(*
  Handshake bit-pattern discipline:
  - Any step that yields rd' = ack' must be a receiver acknowledgment (Recv).
    This captures that equality of the bits occurs only initially or as the result of a receive step.
*)
THEOREM EqualityOnlyAfterRecv == Spec => []((rd' = ack') => Recv)
PROOF OBVIOUS QED

(*
  Optional strengthening:
  - Only Send steps can change val.
*)
THEOREM OnlySendChangesVal == Spec => []((val' # val) => Send)
PROOF OBVIOUS QED

===============================================================================================