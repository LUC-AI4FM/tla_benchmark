------------------------------ MODULE AlternatingBitProtocol ------------------------------

EXTENDS TLC

CONSTANTS Data

ASSUME Data /= {}

VARIABLES sb, ab, rb, sd, rd

vars == << sb, ab, rb, sd, rd >>

Init ==
  /\ sb = FALSE
  /\ ab = FALSE
  /\ rb = FALSE
  /\ sd \in Data
  /\ rd \in Data

Send ==
  /\ ab = sb
  /\ sb' = ~sb
  /\ sd' \in Data
  /\ UNCHANGED << rb, rd, ab >>

Rcv ==
  /\ rb /= sb
  /\ rb' = sb
  /\ rd' = sd
  /\ UNCHANGED << sb, sd, ab >>

Ack ==
  /\ rb /= ab
  /\ ab' = rb
  /\ UNCHANGED << sb, sd, rb, rd >>

Next == Send \/ Rcv \/ Ack

TypeInv ==
  /\ sb \in BOOLEAN
  /\ ab \in BOOLEAN
  /\ rb \in BOOLEAN
  /\ sd \in Data
  /\ rd \in Data

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Rcv)
  /\ WF_vars(Ack)

InfOftenOutOfSync == []<>(sb /= ab)

=============================================================================