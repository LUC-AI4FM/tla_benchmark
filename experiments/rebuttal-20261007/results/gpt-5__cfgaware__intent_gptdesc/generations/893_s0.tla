------------------------------ MODULE HandshakeChannel ------------------------------

EXTENDS Integers

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

Bits == {0, 1}

VARIABLES val, rdy, ack

vars == << val, rdy, ack >>

Init ==
  /\ val \in Data
  /\ rdy \in Bits
  /\ ack = rdy

Send ==
  /\ rdy = ack
  /\ val' \in Data
  /\ rdy' = 1 - rdy
  /\ ack' = ack

Recv ==
  /\ rdy # ack
  /\ val' = val
  /\ ack' = rdy
  /\ rdy' = rdy

Next == Send \/ Recv

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ val \in Data
  /\ rdy \in Bits
  /\ ack \in Bits

TypeInvariant == TypeOK

(*
  Basic preservation theorems: send/receive preserve typing.
*)
THEOREM SendPreservesType == TypeOK /\ Send => TypeOK'
PROOF OMITTED

THEOREM RecvPreservesType == TypeOK /\ Recv => TypeOK'
PROOF OMITTED

THEOREM TypeInvPreserved == TypeOK /\ Next => TypeOK'
PROOF OMITTED

THEOREM TypeInvAlways == Spec => []TypeOK
PROOF OMITTED

(*
  Initialization ensures the handshake bits start equal (empty/acknowledged).
*)
THEOREM EqAtInit == Init => rdy = ack
PROOF OMITTED

(*
  Equality of the handshake bits (ready = ack) occurs only initially
  or as the result of a receiver acknowledgment step. Any non-stuttering
  step that yields ready' = ack' must be a Recv.
*)
THEOREM EqOnlyByRecv ==
  Spec => [](((rdy' = ack') /\ ~UNCHANGED << rdy, ack >>) => Recv)
PROOF OMITTED

(*
  Reliable single-slot handshake safety:
  - Values are never overwritten before acknowledgment.
  - No acknowledgment occurs when absent (when ready = ack).
*)
THEOREM NoOverwriteBeforeAck ==
  Spec => []( (rdy # ack) => UNCHANGED val )
PROOF OMITTED

THEOREM NoAckWhenEmpty ==
  Spec => []((rdy = ack) => ack' = ack)
PROOF OMITTED

=============================================================================