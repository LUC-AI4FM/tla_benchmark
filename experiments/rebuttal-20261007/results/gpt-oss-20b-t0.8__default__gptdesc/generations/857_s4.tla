MODULE PrisonLight
EXTENDS Naturals, Sequences

CONSTANTS N, INITIAL_STATE
ASSUME INITIAL_STATE \in {TRUE, FALSE}

DEF PRISONS        == 1..N
DEF COUNTER        == 1
DEF NON_COUNTERS   == PRISONS \ {COUNTER}
DEF ON             == TRUE
DEF OFF            == FALSE

(* Derived constants *)
THRESHOLD          == IF INITIAL_STATE = OFF THEN N ELSE 2*N - 1
SIGNAL_LIMIT       == IF INITIAL_STATE = OFF THEN 1 ELSE 2

VARIABLES lamp, visited, counterCnt, signalsUsed, announceVictory

vars == <<lamp, visited, counterCnt, signalsUsed, announceVictory>>

(* Initial state *)
Init ==
  /\ lamp = INITIAL_STATE
  /\ visited = {}
  /\ counterCnt = 0
  /\ signalsUsed = [p \in NON_COUNTERS |-> 0]
  /\ announceVictory = FALSE

(* Action for the counter prisoner *)
CounterAction ==
  LET
    newCount      == IF lamp = ON THEN counterCnt + 1 ELSE counterCnt
    newLamp       == IF lamp = ON THEN OFF ELSE lamp
    newAnnounce   == IF newCount >= THRESHOLD THEN TRUE ELSE announceVictory
  IN
    /\ lamp'        = newLamp
    /\ visited'     = visited \cup {COUNTER}
    /\ counterCnt'  = newCount
    /\ signalsUsed' = signalsUsed
    /\ announceVictory' = newAnnounce

(* Action for a non-counter prisoner p *)
NonCounterAction(p) ==
  LET
    used          == signalsUsed[p]
    turnOn        == (lamp = OFF /\ used < SIGNAL_LIMIT)
    newSignals    == IF turnOn THEN used + 1 ELSE used
    newLamp       == IF turnOn THEN ON ELSE lamp
  IN
    /\ lamp'        = newLamp
    /\ visited'     = visited \cup {p}
    /\ signalsUsed' = [signalsUsed EXCEPT ![p] = newSignals]
    /\ counterCnt'  = counterCnt
    /\ announceVictory' = announceVictory

(* Next action: a prisoner is chosen nondeterministically *)
Next ==
  ∃ p \in PRISONS :
     IF p = COUNTER THEN CounterAction ELSE NonCounterAction(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

SafetyInvariant ==
  announceVictory => visited = PRISONS

LivenessProperty ==
  <> announceVictory

THEOREM Safety : Spec => SafetyInvariant
THEOREM Liveness : Spec => LivenessProperty

END MODULE