------------------------------- MODULE InnerModule -------------------------------
VARIABLES result

CONSTANTS inputSeq

Next ==
  /\ result = 0
  /\ result' = 1

FilterSeq ==
  [seq \in Seq(NAT) |-> SelectSeq(seq, (lambda x: x # result'))]

Vars == <<result>>

=============================================================================