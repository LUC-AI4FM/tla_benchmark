---- MODULE PrisonerLightSwitch ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS N, UNKNOWN_INITIAL_LIGHT_STATE

ASSUME N \in Nat /\ N > 1
ASSUME UNKNOWN_INITIAL_LIGHT_STATE \in BOOLEAN

Prisoner == 1..N
Counter == 1
NonCounter == Prisoner \ {Counter}

(*--algorithm
variables
    light_on = IF UNKNOWN_INITIAL_LIGHT_STATE THEN CHOOSE b \in BOOLEAN : TRUE ELSE FALSE,
    count = 1,
    visited = {},
    announced_victory = FALSE,
    prisoner_signals = [p \in NonCounter |-> 0];

process warden = "Warden"
begin
WardenLoop:
    while ~announced_victory do
        with p \in Prisoner do
            visited := visited \cup {p};
            if p = Counter then
                if light_on then
                    count := count + 1;
                    light_on := FALSE;
                end if;
                if (UNKNOWN_INITIAL_LIGHT_STATE /\ count = 2*N - 1) \/
                   (~UNKNOWN_INITIAL_LIGHT_STATE /\ count = N)
                then
                    announced_victory := TRUE;
                end if;
            else \* p \in NonCounter
                assert p \in NonCounter;
                if ~light_on then
                    variable max_signals;
                    max_signals := IF UNKNOWN_INITIAL_LIGHT_STATE THEN 2 ELSE 1;
                    if prisoner_signals[p] < max_signals then
                        light_on := TRUE;
                        prisoner_signals[p] := prisoner_signals[p] + 1;
                    end if;
                end if;
            end if;
        end with;
    end while;
end process;
end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES
    light_on,
    count,
    visited,
    announced_victory,
    prisoner_signals,
    pc

vars == << light_on, count, visited, announced_victory, prisoner_signals, pc >>

Init == (* Global variables *)
        /\ light_on = (IF UNKNOWN_INITIAL_LIGHT_STATE THEN CHOOSE b \in BOOLEAN : TRUE ELSE FALSE)
        /\ count = 1
        /\ visited = {}
        /\ announced_victory = FALSE
        /\ prisoner_signals = [p \in NonCounter |-> 0]
        (* Process warden *)
        /\ pc = "WardenLoop"

WardenLoop == /\ pc = "WardenLoop"
              /\ IF ~announced_victory
                    THEN /\ \E p \in Prisoner:
                                /\ pc' = "WardenLoop"
                                /\ visited' = visited \cup {p}
                                /\ IF p = Counter
                                      THEN /\ IF light_on
                                                 THEN /\ count' = count + 1
                                                      /\ light_on' = FALSE
                                                 ELSE /\ UNCHANGED << count, light_on >>
                                           /\ IF (UNKNOWN_INITIAL_LIGHT_STATE /\ (IF light_on THEN count + 1 ELSE count) = 2*N - 1) \/ (~UNKNOWN_INITIAL_LIGHT_STATE /\ (IF light_on THEN count + 1 ELSE count) = N)
                                                 THEN /\ announced_victory' = TRUE
                                                 ELSE /\ UNCHANGED announced_victory
                                           /\ UNCHANGED prisoner_signals
                                      ELSE /\ Assert(p \in NonCounter, "Failure of assertion at line 46, column 17 of translation")
                                           /\ IF ~light_on
                                                 THEN /\ LET max_signals == IF UNKNOWN_INITIAL_LIGHT_STATE THEN 2 ELSE 1
                                                      IN  IF prisoner_signals[p] < max_signals
                                                              THEN /\ light_on' = TRUE
                                                                   /\ prisoner_signals' = [prisoner_signals EXCEPT ![p] = prisoner_signals[p] + 1]
                                                              ELSE /\ UNCHANGED << light_on, prisoner_signals >>
                                                 ELSE /\ UNCHANGED << light_on, prisoner_signals >>
                                           /\ UNCHANGED << count, announced_victory >>
                    ELSE /\ pc' = "Done"
                         /\ UNCHANGED << light_on, count, visited,
                                         announced_victory, prisoner_signals >>

warden == WardenLoop

Next == warden
           \/ (* Disjunct to prevent deadlock on termination *)
              (pc = "Done" /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

VictoryImpliesAllVisited ==
    announced_victory => (visited = Prisoner)

EventuallyVictory ==
    <>(announced_victory)

Fairness == WF_vars(Next)

====