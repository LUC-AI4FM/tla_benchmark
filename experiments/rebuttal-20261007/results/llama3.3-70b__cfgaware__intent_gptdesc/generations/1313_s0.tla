---------------------------- MODULE WaterPuzzle ----------------------------
EXTENDS Integers

CONSTANTS Capacity1, Capacity2
VARIABLES container1, container2, statesGenerated, distinctStates, diameter, totalWaterDrawn, avgWaterPerState, stepCount

Init ==
  /\ container1 = 0
  /\ container2 = 0
  /\ statesGenerated = 1
  /\ distinctStates = 1
  /\ diameter = 0
  /\ totalWaterDrawn = 0
  /\ avgWaterPerState = 0
  /\ stepCount = 0

TypeInvariant ==
  /\ container1 \in 0..Capacity1
  /\ container2 \in 0..Capacity2
  /\ statesGenerated \in Nat
  /\ distinctStates \in Nat
  /\ diameter \in Nat
  /\ totalWaterDrawn \in Nat
  /\ avgWaterPerState \in Nat

FillContainer1 ==
  /\ container1' = Capacity1
  /\ container2' = container2
  /\ statesGenerated' = statesGenerated + 1
  /\ IF (container1 # container1') THEN distinctStates' = distinctStates + 1 ELSE distinctStates' = distinctStates
  /\ diameter' = IF (diameter < statesGenerated) THEN statesGenerated ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn + Capacity1 - container1
  /\ avgWaterPerState' = (totalWaterDrawn' / distinctStates')
  /\ stepCount' = stepCount + 1

FillContainer2 ==
  /\ container1' = container1
  /\ container2' = Capacity2
  /\ statesGenerated' = statesGenerated + 1
  /\ IF (container2 # container2') THEN distinctStates' = distinctStates + 1 ELSE distinctStates' = distinctStates
  /\ diameter' = IF (diameter < statesGenerated) THEN statesGenerated ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn + Capacity2 - container2
  /\ avgWaterPerState' = (totalWaterDrawn' / distinctStates')
  /\ stepCount' = stepCount + 1

EmptyContainer1 ==
  /\ container1' = 0
  /\ container2' = container2
  /\ statesGenerated' = statesGenerated + 1
  /\ IF (container1 # container1') THEN distinctStates' = distinctStates + 1 ELSE distinctStates' = distinctStates
  /\ diameter' = IF (diameter < statesGenerated) THEN statesGenerated ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn
  /\ avgWaterPerState' = (totalWaterDrawn' / distinctStates')
  /\ stepCount' = stepCount + 1

EmptyContainer2 ==
  /\ container1' = container1
  /\ container2' = 0
  /\ statesGenerated' = statesGenerated + 1
  /\ IF (container2 # container2') THEN distinctStates' = distinctStates + 1 ELSE distinctStates' = distinctStates
  /\ diameter' = IF (diameter < statesGenerated) THEN statesGenerated ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn
  /\ avgWaterPerState' = (totalWaterDrawn' / distinctStates')
  /\ stepCount' = stepCount + 1

PourContainer1ToContainer2 ==
  /\ container1' = IF (container1 > Capacity2 - container2) THEN container1 - (Capacity2 - container2) ELSE 0
  /\ container2' = IF (container1 > Capacity2 - container2) THEN Capacity2 ELSE container2 + container1
  /\ statesGenerated' = statesGenerated + 1
  /\ IF ((container1 # container1') \lor (container2 # container2')) THEN distinctStates' = distinctStates + 1 ELSE distinctStates' = distinctStates
  /\ diameter' = IF (diameter < statesGenerated) THEN statesGenerated ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn
  /\ avgWaterPerState' = (totalWaterDrawn' / distinctStates')
  /\ stepCount' = stepCount + 1

PourContainer2ToContainer1 ==
  /\ container1' = IF (container2 > Capacity1 - container1) THEN Capacity1 ELSE container1 + container2
  /\ container2' = IF (container2 > Capacity1 - container1) THEN container2 - (Capacity1 - container1) ELSE 0
  /\ statesGenerated' = statesGenerated + 1
  /\ IF ((container1 # container1') \lor (container2 # container2')) THEN distinctStates' = distinctStates + 1 ELSE distinctStates' = distinctStates
  /\ diameter' = IF (diameter < statesGenerated) THEN statesGenerated ELSE diameter
  /\ totalWaterDrawn' = totalWaterDrawn
  /\ avgWaterPerState' = (totalWaterDrawn' / distinctStates')
  /\ stepCount' = stepCount + 1

Next ==
  \/ FillContainer1
  \/ FillContainer2
  \/ EmptyContainer1
  \/ EmptyContainer2
  \/ PourContainer1ToContainer2
  \/ PourContainer2ToContainer1

Spec ==
  Init /\ [][Next]_<<container1, container2, statesGenerated, distinctStates, diameter, totalWaterDrawn, avgWaterPerState, stepCount>>

THEOREM Spec => (statesGenerated = 64) /\ (distinctStates = 13) /\ (diameter = 6) /\ (totalWaterDrawn = 104) /\ (avgWaterPerState = 8)
=============================================================================