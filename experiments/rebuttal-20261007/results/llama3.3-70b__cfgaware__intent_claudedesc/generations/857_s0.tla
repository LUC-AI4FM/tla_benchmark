---------------------------- MODULE PrisonerLampPuzzle ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N, ConfigFlag
VARIABLES lamp, count, visited, wardenQueue

Init ==
  /\ lamp = IF ConfigFlag = "known" THEN FALSE ELSE TRUE
  /\ count = 0
  /\ visited = {}
  /\ wardenQueue = Seq(N)

Next ==
  /\ ~Terminating
  /\ ( \E p \in 1..N :
        /\ wardenQueue # <<p>> 
        /\ lamp' = IF ConfigFlag = "known"
                  THEN IF p = 1 /\ lamp THEN FALSE ELSE lamp
                  ELSE IF p = 1 /\ count < IF ConfigFlag = "known" THEN N ELSE 2*N-1
                       THEN IF lamp THEN TRUE ELSE FALSE
                       ELSE IF p # 1 /\ ~lamp /\ (ConfigFlag = "unknown" \/ count' < 1)
                            THEN TRUE
                            ELSE lamp
        /\ count' = IF ConfigFlag = "known"
                    THEN IF p = 1 /\ lamp THEN count + 1 ELSE count
                    ELSE IF p = 1 /\ lamp THEN count + 1 ELSE count
        /\ visited' = visited \cup {p}
        /\ wardenQueue' = Append(Tail(wardenQueue), <<p>>)
      )
  /\ TypeOK

Spec == Init /\ [][Next]_<<lamp, count, visited, wardenQueue>>

Terminating == (ConfigFlag = "known" /\ count = N) \/ (ConfigFlag = "unknown" /\ count = 2*N-1)

TypeOK ==
  /\ lamp \in BOOLEAN
  /\ count \in 0..N
  /\ visited \subseteq 1..N
  /\ wardenQueue \in Seq(1..N)
  
VictoryOK == 
  (ConfigFlag = "known" /\ count = N) \/ (ConfigFlag = "unknown" /\ count = 2*N-1) => visited = 1..N

THEOREM Spec => []Terminating
THEOREM Spec => VictoryOK
====================================================================================