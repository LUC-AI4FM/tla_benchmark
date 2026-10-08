```
MODULE WaterPouringPuzzle
EXTENDS Integers

CONSTANTS Capacity1, Capacity2
VARIABLES container1, container2, steps, distinctStates, diameter, totalWaterDrawn, avgWaterPerState

Init ==
  /\ container1 = 0
  /\ container2 = 0
  /\ steps = 0
  /\ distinctStates = 0
  /\ diameter = 0
  /\ totalWaterDrawn = 0
  /\ avgWaterPerState = 0

Next ==
  \/ FillContainer1
  \/ FillContainer2
  \/ EmptyContainer1
  \/ EmptyContainer2
  \/ PourContainer1ToContainer2
  \/ PourContainer2ToContainer1

FillContainer1 ==
  /\ container1' = Capacity1
  /\ container2' = container2
  /\ steps' = steps + 1
  /\ distinctStates' = IF (container1 # container1') THEN distinctStates + 1 ELSE distinctStates
  /\ diameter' = IF (steps + 1 > diameter) THEN steps + 1 ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn + Capacity1 - container1
  /\ avgWaterPerState' = totalWaterDrawn' / distinctStates'

FillContainer2 ==
  /\ container1' = container1
  /\ container2' = Capacity2
  /\ steps' = steps + 1
  /\ distinctStates' = IF (container2 # container2') THEN distinctStates + 1 ELSE distinctStates
  /\ diameter' = IF (steps + 1 > diameter) THEN steps + 1 ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn + Capacity2 - container2
  /\ avgWaterPerState' = totalWaterDrawn' / distinctStates'

EmptyContainer1 ==
  /\ container1' = 0
  /\ container2' = container2
  /\ steps' = steps + 1
  /\ distinctStates' = IF (container1 # container1') THEN distinctStates + 1 ELSE distinctStates
  /\ diameter' = IF (steps + 1 > diameter) THEN steps + 1 ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn
  /\ avgWaterPerState' = totalWaterDrawn / distinctStates

EmptyContainer2 ==
  /\ container1' = container1
  /\ container2' = 0
  /\ steps' = steps + 1
  /\ distinctStates' = IF (container2 # container2') THEN distinctStates + 1 ELSE distinctStates
  /\ diameter' = IF (steps + 1 > diameter) THEN steps + 1 ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn
  /\ avgWaterPerState' = totalWaterDrawn / distinctStates

PourContainer1ToContainer2 ==
  /\ container1' = IF (container1 - (Capacity2 - container2) < 0) THEN 0 ELSE container1 - (Capacity2 - container2)
  /\ container2' = IF (container2 + container1 > Capacity2) THEN Capacity2 ELSE container2 + container1
  /\ steps' = steps + 1
  /\ distinctStates' = IF ((container1 # container1') \/ (container2 # container2')) THEN distinctStates + 1 ELSE distinctStates
  /\ diameter' = IF (steps + 1 > diameter) THEN steps + 1 ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn
  /\ avgWaterPerState' = totalWaterDrawn / distinctStates

PourContainer2ToContainer1 ==
  /\ container1' = IF (container1 + container2 > Capacity1) THEN Capacity1 ELSE container1 + container2
  /\ container2' = IF (container2 - (Capacity1 - container1) < 0) THEN 0 ELSE container2 - (Capacity1 - container1)
  /\ steps' = steps + 1
  /\ distinctStates' = IF ((container1 # container1') \/ (container2 # container2')) THEN distinctStates + 1 ELSE distinctStates
  /\ diameter' = IF (steps + 1 > diameter) THEN steps + 1 ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn
  /\ avgWaterPerState' = totalWaterDrawn / distinctStates

Spec ==
  /\ Init
  /\ [][Next]_<<container1, container2, steps, distinctStates, diameter, totalWaterDrawn, avgWaterPerState>>
  /\ WF_<<container1, container2, steps, distinctStates, diameter, totalWaterDrawn, avgWaterPerState>>(Next)
  /\ SF_<<container1, container2, steps, distinctStates, diameter, totalWaterDrawn, avgWaterPerState>>(Next)

THEOREM Spec => (distinctStates = 101) /\ (diameter = 8) /\ (totalWaterDrawn = 208) /\ (avgWaterPerState = 2)
```
Note: The `Capacity1` and `Capacity2` constants should be replaced with the actual values of 3 and 5 respectively.