--------------------------- MODULE Inner ---------------------------
EXTENDS Naturals, Sequences

VARIABLES r, s

RECURSIVE SelectSeq(_,_)
SelectSeq(seq, v) ==
  IF seq = << >> THEN << >>
  ELSE IF Head(seq) = v THEN
          SelectSeq(Tail(seq), v)
       ELSE
          << Head(seq) >> \o SelectSeq(Tail(seq), v)

Step ==
  /\ r = 0
  /\ r' = 1
  /\ s' = SelectSeq(s, r')
====================================================================