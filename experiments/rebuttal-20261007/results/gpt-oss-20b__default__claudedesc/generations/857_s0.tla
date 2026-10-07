MODULE PrisonerPuzzle
EXTENDS Naturals, Temporal, TLC

CONSTANTS Prisoner, Counter, Light_Unknown

ASSUME Counter ∈ Prisoner

VARIABLES cnt, victoryAnnounced, signals, lamp, visited

N          == #Prisoner
maxSignals == IF Light_Unknown THEN 2 ELSE 1
Threshold  == IF Light_Unknown THEN 2 * N - 1 ELSE N

Init ==
    /\ cnt = 1
    /\ victoryAnnounced = FALSE
    /\ signals = [p \in Prisoner |-> 0]
    /\ lamp = IF Light_Unknown THEN CHOOSE b \in BOOLEAN : b ELSE FALSE
    /\ visited = {Counter}

Visit(p) ==
   LET isCounter == (p = Counter)
       maxS      == IF Light_Unknown THEN 2 ELSE 1
   IN
   /\ p ∈ Prisoner
   /\ visited' = visited \cup {p}
   /\ IF isCounter THEN
        (* counter action *)
        IF lamp THEN
           /\ lamp' = FALSE
           /\ cnt' = cnt + 1
           /\ victoryAnnounced' =
                IF NOT victoryAnnounced /\ (cnt + 1) >= Threshold /\ visited' = Prisoner THEN TRUE ELSE victoryAnnounced
        ELSE
           /\ lamp' = lamp
           /\ cnt' = cnt
           /\ victoryAnnounced' = victoryAnnounced
        /\ signals' = signals
      ELSE
        (* non-counter action *)
        IF lamp = FALSE /\ signals[p] < maxS THEN
           /\ lamp' = TRUE
           /\ signals' = [signals EXCEPT ![p] = signals[p] + 1]
           /\ cnt' = cnt
           /\ victoryAnnounced' = victoryAnnounced
        ELSE
           /\ lamp' = lamp
           /\ signals' = signals
           /\ cnt' = cnt
           /\ victoryAnnounced' = victoryAnnounced

Next == ∃p \in Prisoner : Visit(p)

TypeOK ==
    /\ cnt ∈ Nat
    /\ victoryAnnounced ∈ BOOLEAN
    /\ lamp ∈ BOOLEAN
    /\ visited ⊆ Prisoner
    /\ signals ∈ [Prisoner -> Nat]
    /\ ∀p ∈ Prisoner \ {Counter} : signals[p] <= maxSignals

VictoryOK ==
    victoryAnnounced => visited = Prisoner

Spec == Init /\ [][Next]_vars
        /\ WF_action(Visit)
        /\ ∀p ∈ Prisoner : WF_action(Visit(p))

Terminating == <> victoryAnnounced

THEOREM Spec => Terminating
THEOREM Spec => TypeOK
THEOREM Spec => VictoryOK