--------------------------- MODULE HourClockLive ---------------------------
EXTENDS Integers, HourClock

VARIABLE hour

Fairness == WF_vars ticked (hour)

LSpec == Init /\ [][Next]_hour /\ Fairness

AlwaysTick == <>[]<>(ticked' = TRUE)

AllTimes == \A i \in 1..12 : <>[]<>(hour = i)

TypeInvariance == hour \in 1..12

THEOREM LSpec => []AlwaysTick
PROOF
  <1>1. LSpec
     BY DEF LSpec
   <1>2. Init /\ [][Next]_hour /\ Fairness
     BY <1>1
   <1>3. WF_vars ticked (hour)
     BY <1>2, Fairness
   <1>4. <>[]<>(ticked' = TRUE)
     BY <1>3, DEF WF_vars
  QED

THEOREM LSpec => []AllTimes
PROOF
  <2>1. LSpec
     BY DEF LSpec
   <2>2. Init /\ [][Next]_hour /\ Fairness
     BY <2>1
   <2>3. \A i \in 1..12 : <>[]<>(hour = i)
     BY <2>2, DEF Next, DEF hour
  QED

THEOREM LSpec => []TypeInvariance
PROOF
  <3>1. LSpec
     BY DEF LSpec
   <3>2. Init /\ [][Next]_hour /\ Fairness
     BY <3>1
   <3>3. hour \in 1..12
     BY <3>2, DEF Next, DEF hour
  QED

=============================================================================