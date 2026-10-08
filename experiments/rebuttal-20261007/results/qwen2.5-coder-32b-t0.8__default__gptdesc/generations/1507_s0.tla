------------------------------- MODULE ClockSystem -------------------------------
EXTENDS Naturals

CONSTANTS TRUE, FALSE

VARIABLES clock

Check(v) == \/ v = TRUE
            \/ v = FALSE

Flip(v) == ~v

Init == Check(clock)

Next ==
  /\ \/ clock' = Flip(clock)
     /\ Check(clock')

Spec ==
  /\ Init
  /\ [][Next]_<<clock>>

Inv ==
  /\ Check(clock)

TypeOK ==
  \A c \in BOOLEAN : Check(c)

Fairness ==
  WF_next(<<clock>>)

=============================================================================