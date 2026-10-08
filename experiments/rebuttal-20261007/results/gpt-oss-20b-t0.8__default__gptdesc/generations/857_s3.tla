MODULE PrisonerLightSwitch
EXTENDS Naturals, Sequences

CONSTANTS N, Counter, InitialLampKnownOff

ASSUME 1 <= Counter /\ Counter <= N
ASSUME N >= 2

VARIABLES lamp, CountSignals, Signaled, Visited, Announced

THRESHOLD == IF InitialLampKnownOff THEN N-1 ELSE 2*N - 1
maxSignal  == IF InitialLampKnownOff THEN 1 ELSE 2

Init ==
    /\ (IF InitialLampKnownOff THEN lamp = 0 ELSE lamp ∈ {0,1})
    /\ CountSignals = 0
    /\ Signaled   = [i \in 1..N |-> 0]
    /\ Visited    = {}
    /\ Announced  = FALSE

Action(i) ==
    /\ Visited' = Visited ∪ {i}
    /\ IF i = Counter THEN
        /\ IF lamp = 1 THEN
            /\ lamp'          = 0
            /\ CountSignals'  = CountSignals + 1
          ELSE
            /\ lamp'          = lamp
            /\ CountSignals'  = CountSignals
        /\ Announced' =
              IF CountSignals' >= THRESHOLD /\ NOT Announced THEN TRUE ELSE Announced
       ELSE
        /\ IF lamp = 0 /\ Signaled[i] < maxSignal THEN
                /\ lamp'         = 1
                /\ Signaled'     = [Signaled EXCEPT ![i] = Signaled[i] + 1]
           ELSE
                /\ lamp'         = lamp
                /\ Signaled'     = Signaled
        /\ CountSignals' = CountSignals

Next == ∃ i \in 1..N : Action(i)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Inv == (Announced => (∀ i \in 1..N : i ∈ Visited))

THEOREM SafeInv == Spec => [](Inv)