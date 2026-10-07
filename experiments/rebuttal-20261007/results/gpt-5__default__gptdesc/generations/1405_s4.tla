----------------------------- MODULE Inner -----------------------------
EXTENDS Sequences, Naturals

VARIABLES res, seq

Step ==
  /\ res = 0
  /\ res' = 1
  /\ seq' = SelectSeq(seq, LAMBDA x: x # res')

=============================================================================