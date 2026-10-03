------------------------------ MODULE Outer ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS Elem

VARIABLES r, s

InnerM == INSTANCE Inner WITH res <- r, seq <- s

Init ==
  /\ r = 0
  /\ s \in Seq(Elem)

Next ==
  InnerM!Step
  \/ (/\ ~ENABLED InnerM!Step
      /\ UNCHANGED << r, s >>)

Spec ==
  Init /\ [][Next]_<< r, s >> /\ WF_<< r, s >>(InnerM!Step)

Liveness ==
  <>[] (~ENABLED InnerM!Step)

THEOREM Spec => Liveness

=============================================================================