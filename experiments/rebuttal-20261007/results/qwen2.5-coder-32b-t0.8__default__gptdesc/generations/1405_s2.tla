---- MODULE OuterModule ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS N

VARIABLES result, sequence

InnerStep == 
  /\ result' = 1
  /\ sequence' = SelectSeq(sequence, LAMBDA x: x # result')

Init ==
  /\ result = 0
  /\ sequence \in Seq(N)

Next ==
  \/ InnerStep
  \/ /\ result' = result
     /\ sequence' = sequence

Spec ==
  Init /\ [][Next]_<<result, sequence>> /\ WF_<<InnerStep>>_

Liveness ==
  <>[](result # 1) \/ []<>(result = 1) /\ [](result = 1)

====