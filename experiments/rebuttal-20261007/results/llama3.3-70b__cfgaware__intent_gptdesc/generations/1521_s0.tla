---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT MaxBeans

VARIABLE blackCount, whiteCount

Init ==
  /\ blackCount \in Nat
  /\ whiteCount \in Nat
  /\ blackCount + whiteCount > 0

Next ==
  /\ (blackCount # 0) /\ (whiteCount # 0)
  /\ (blackCount' = IF (blackCount > 1) 
                  THEN IF (whiteCount = 0) 
                       THEN blackCount - 1 
                       ELSE blackCount
                  ELSE UNCHANGED)
  /\ (whiteCount' = IF (whiteCount > 0) 
                 THEN IF (blackCount = 0) 
                      THEN whiteCount - 1 
                      ELSE IF (whiteCount > 1) 
                           THEN whiteCount - 1 
                           ELSE whiteCount + 1
                 ELSE UNCHANGED)

Spec == Init /\ [][Next]_<<blackCount, whiteCount>>

THEOREM Spec => []<>(blackCount = 1 /\ whiteCount = 0)
THEOREM Spec => []<>(whiteCount = 1 /\ blackCount = 0) 

Inv == (blackCount + whiteCount) mod 2 = (InitBlack + InitWhite) mod 2

THEOREM Spec => []Inv

Fairness == <>[]<>(blackCount = 1 /\ whiteCount = 0) \/ (whiteCount = 1 /\ blackCount = 0)

THEOREM Spec /\ Fairness => [](blackCount # 0) \* (whiteCount # 0)
=============================================================================