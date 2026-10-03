```
MODULE SimpleClock
VARIABLE hr

HCini == (hr \in 1..12)

HCnxt == hr' = IF hr = 12 THEN 1 ELSE hr + 1

HC == HCini /\ [][HCnxt]_hr

THEOREM HCini => []HCini
PROOF BY induction
  BASE CASE: OBVIOUS
  INDUCTIVE STEP: 
    ASSUME HCini
    PROVE  HCnxt => HCini'
      <1>1. HCini
         BY ASSUME
      <1>2. hr \in 1..12
         BY DEF HCini
      <1>3. hr' = IF hr = 12 THEN 1 ELSE hr + 1
         BY DEF HCnxt
      <1>4. hr' \in 1..12
         PROOF 
           CASES hr = 12
             S1: hr = 12
               THEN hr' = 1
                 BY <1>3, S1
               ELSE hr' = hr + 1
                 BY <1>3, ~S1
           END CASE
           CONTRADICT <1>2, ~S1 IF hr' > 12
         END PROOF
      <1>5. HCini'
         BY DEF HCini, <1>4
END PROOF
```
Note: The proof provided uses a simple inductive argument to show that `HCini` is an invariant of the system. It first establishes the base case (that `HCini` holds initially), and then shows that if `HCini` holds at some step, it also holds at the next step (`HCnxt => HCini'`). The inductive step uses a cases analysis to handle the wrap-around from 12 to 1.