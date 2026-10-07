---- MODULE Inner ----
EXTENDS Sequences, Integers, Naturals

VARIABLES r, s

Step ==
  /\ r = 0
  /\ r' = 1
  /\ s' = SelectSeq(s, LAMBDA x: x # r')

====