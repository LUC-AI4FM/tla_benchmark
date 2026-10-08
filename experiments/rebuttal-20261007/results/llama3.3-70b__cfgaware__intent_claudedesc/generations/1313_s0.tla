---------------------------- MODULE DieHard --------------------------------
EXTENDS Integers, TLC

CONSTANT Jug3Capacity, Jug5Capacity
VARIABLES bigJug, smallJug, totalDrawn
bigJug == 0
smallJug == 0
totalDrawn == 0

TypeInvariant == (bigJug \in 0..Jug5Capacity) /\ (smallJug \in 0..Jug3Capacity)

FillBig == totalDrawn' = totalDrawn + (Jug5Capacity - bigJug)
           /\ bigJug' = Jug5Capacity
           /\ smallJug' = smallJug

FillSmall == totalDrawn' = totalDrawn + (Jug3Capacity - smallJug)
            /\ bigJug' = bigJug
            /\ smallJug' = Jug3Capacity

EmptyBig == totalDrawn' = totalDrawn
          /\ bigJug' = 0
          /\ smallJug' = smallJug

EmptySmall == totalDrawn' = totalDrawn
           /\ bigJug' = bigJug
           /\ smallJug' = 0

PourBigToSmall == 
  IF smallJug + bigJug > Jug3Capacity 
  THEN totalDrawn' = totalDrawn
       /\ bigJug' = bigJug - (Jug3Capacity - smallJug)
       /\ smallJug' = Jug3Capacity
  ELSE totalDrawn' = totalDrawn
       /\ bigJug' = 0
       /\ smallJug' = smallJug + bigJug

PourSmallToBig == 
  IF bigJug + smallJug > Jug5Capacity 
  THEN totalDrawn' = totalDrawn
       /\ bigJug' = Jug5Capacity
       /\ smallJug' = smallJug - (Jug5Capacity - bigJug)
  ELSE totalDrawn' = totalDrawn
       /\ bigJug' = bigJug + smallJug
       /\ smallJug' = 0

Next == FillBig \/ FillSmall \/ EmptyBig \/ EmptySmall \/ PourBigToSmall \/ PourSmallToBig

Spec == Init /\ [][Next]_<<bigJug, smallJug, totalDrawn>>
THEOREM Spec => []TypeInvariant
=============================================================================