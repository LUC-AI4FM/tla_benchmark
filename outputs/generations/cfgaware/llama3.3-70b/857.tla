---------------------------- MODULE PrisonerPuzzle ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS NumPrisoners, InitialLightState
VARIABLES prisonersVisited, lightSwitch, victoryAnnounced, counter

TypeOK == 
  /\ prisonersVisited \in [1..NumPrisoners -> {<< >>}]
  /\ lightSwitch \in {<<True>>, <<False>>}
  /\ victoryAnnounced \in {<<True>>, <<False>>}
  /\ counter \in Nat

InitUnknown ==
  /\ prisonersVisited = [i \in 1..NumPrisoners |-> {<< >>}]
  /\ lightSwitch = <<InitialLightState>>
  /\ victoryAnnounced = <<False>>
  /\ counter = 0

InitKnown ==
  /\ prisonersVisited = [i \in 1..NumPrisoners |-> {<< >>}]
  /\ lightSwitch = <<False>>
  /\ victoryAnnounced = <<False>>
  /\ counter = 0

Init == 
  IF InitialLightState = "Unknown" THEN InitUnknown
  ELSE InitKnown

Next(i \in 1..NumPrisoners) ==
  /\ (victoryAnnounced = <<False>>) 
  /\ (lightSwitch = <<True>>)
  /\ prisonersVisited' = [prisonersVisited EXCEPT ![i] = {<< >>} \cup {[i]}]
  /\ lightSwitch' = <<False>>
  /\ victoryAnnounced' = victoryAnnounced
  /\ counter' = IF i = NumPrisoners THEN (counter + 1) ELSE counter

NextCounter ==
  /\ (victoryAnnounced = <<False>>) 
  /\ (lightSwitch = <<True>>)
  /\ prisonersVisited' = prisonersVisited
  /\ lightSwitch' = <<False>>
  /\ victoryAnnounced' = IF InitialLightState = "Unknown" THEN 
                            IF counter = 2 * NumPrisoners - 1 THEN <<True>> ELSE victoryAnnounced
                          ELSE 
                            IF counter = NumPrisoners THEN <<True>> ELSE victoryAnnounced
  /\ counter' = IF InitialLightState = "Unknown" THEN 
                  IF i \in 1..NumPrisoners - 1 THEN (counter + 1) ELSE counter
                ELSE counter

NextNonCounter(i \in 1..(NumPrisoners-1)) ==
  /\ (victoryAnnounced = <<False>>) 
  /\ prisonersVisited' = [prisonersVisited EXCEPT ![i] = {<< >>} \cup {[i]}]
  /\ lightSwitch' = IF InitialLightState = "Unknown" THEN 
                      IF lightSwitch = <<True>> THEN <<False>> ELSE <<True>>
                    ELSE 
                      IF lightSwitch = <<True>> THEN <<False>> ELSE <<True>>
  /\ victoryAnnounced' = victoryAnnounced
  /\ counter' = counter

Spec == Init /\ [][Next(NumPrisoners) \/ NextCounter \/ (\E i \in 1..(NumPrisoners-1): NextNonCounter(i))]

Terminating == FALSE

VictoryOK == 
  []<(victoryAnnounced = <<True>>) => (\A i \in 1..NumPrisoners: {[i]} \subseteq prisonersVisited![i])>
=============================================================================