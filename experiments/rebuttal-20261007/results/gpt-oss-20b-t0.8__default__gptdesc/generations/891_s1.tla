------------------------------- MODULE SenderReceiver -------------------------------
EXTENDS Naturals

CONSTANTS Data

BOOLEAN == {TRUE, FALSE}

VARIABLES rdy, ack, val

Init ==
  /\ rdy = FALSE
  /\ ack = FALSE
  /\ val ∈ Data

Send ==
  /\ rdy = ack
  /\ val' ∈ Data
  /\ val' # val
  /\ rdy' = ~rdy
  /\ ack' = ack

Rcv ==
  /\ rdy # ack
  /\ ack' = ~ack
  /\ rdy' = rdy
  /\ val' = val

Stutter ==
  /\ rdy' = rdy
  /\ ack' = ack
  /\ val' = val

Next == Send \/ Rcv \/ Stutter

TypeInvariant ==
  rdy ∈ BOOLEAN /\ ack ∈ BOOLEAN /\ val ∈ Data

Spec ==
  Init /\ [][Next]_<<rdy, ack, val>>

THEOREM SpecImplyTypeInv == Spec => [] TypeInvariant
=============================================================================