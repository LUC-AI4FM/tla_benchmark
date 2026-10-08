MODULE AsyncHandshake
EXTENDS Naturals, TLC

CONSTANTS Data

VARIABLES rdy, ack, val

Init ==
    /\ rdy = FALSE
    /\ ack = FALSE
    /\ val ∈ Data

Send ==
    /\ rdy = ack
    /\ val' ∈ Data
    /\ rdy' = ~rdy
    /\ ack' = ack

Rcv ==
    /\ rdy # ack
    /\ ack' = ~ack
    /\ rdy' = rdy
    /\ val' = val

Stutter ==
    <<rdy', ack', val'>> = <<rdy, ack, val>>

Next == Send \/ Rcv

Spec == Init /\ [] (Next \/ Stutter)

TypeInvariant ==
    /\ rdy ∈ BOOLEAN
    /\ ack ∈ BOOLEAN
    /\ val ∈ Data

THEOREM Spec => TypeInvariant