MODULE Handshake
EXTENDS Naturals

CONSTANTS Data

VARIABLES rdy, ack, val

Init ==
  /\ rdy = FALSE
  /\ ack = FALSE
  /\ val ∈ Data

Send ==
  /\ rdy' = ~rdy
  /\ ack' = ack
  /\ val' ∈ Data
  /\ rdy = ack

Rcv ==
  /\ rdy' = rdy
  /\ ack' = ~ack
  /\ val' = val
  /\ rdy # ack

Skip ==
  /\ rdy' = rdy
  /\ ack' = ack
  /\ val' = val

Next == Send \/ Rcv \/ Skip

TypeInvariant ==
  rdy ∈ {FALSE, TRUE} /\ ack ∈ {FALSE, TRUE} /\ val ∈ Data

Spec == Init /\ [][Next]_<<rdy,ack,val>>

THEOREM SpecImpliesType : Spec => []TypeInvariant

END MODULE