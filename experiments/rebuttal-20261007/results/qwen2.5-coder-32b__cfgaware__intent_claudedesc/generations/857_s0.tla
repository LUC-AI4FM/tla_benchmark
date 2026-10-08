------------------------------- MODULE PrisonerLampPuzzle -------------------------------

CONSTANTS N \* Number of prisoners
VARIABLES lampState, prisonerCount, visitedPrisoners, currentPrisoner

ASSUME N > 1

(*--algorithm PrisonerLampPuzzle
variables 
    lampState = IF InitialLampStateKnown THEN FALSE ELSE BOOLEAN,
    prisonerCount = 0,
    visitedPrisoners = {},
    currentPrisoner \in 1..N;

fair process (prisoner \in 1..N) \in 1..N
begin
    loop:
        await currentPrisoner = prisoner;
        if prisoner = 1 then \* Counter prisoner
            if lampState then
                lampState := FALSE;
                prisonerCount := prisonerCount + 1;
                visitedPrisoners := visitedPrisoners \cup {currentPrisoner};
                if prisonerCount >= (IF InitialLampStateKnown THEN N ELSE 2*N - 1) then
                    call AnnounceVictory();
                end if;
            else
                visitedPrisoners := visitedPrisoners \cup {currentPrisoner};
            end if;
        else \* Non-counter prisoners
            if lampState = FALSE then
                lampState := TRUE;
                visitedPrisoners := visitedPrisoners \cup {currentPrisoner};
                if NOT InitialLampStateKnown then
                    await currentPrisoner \notin visitedPrisoners;
                    lampState := TRUE;
                    visitedPrisoners := visitedPrisoners \cup {currentPrisoner};
                end if;
            else
                visitedPrisoners := visitedPrisoners \cup {currentPrisoner};
            end if;
        end if;
        currentPrisoner := <<currentPrisoner>>_mod_N + 1;
end loop;

procedure AnnounceVictory()
begin
    assert(\A p \in 1..N: p \in visitedPrisoners);
    skip; \* Victory is announced here
end procedure;
end algorithm *)

Spec == /\ Init
        /\ [][Next]_<<lampState, prisonerCount, visitedPrisoners, currentPrisoner>>
        /\ WF_next(<<lampState, prisonerCount, visitedPrisoners, currentPrisoner>>)

Init == /\ lampState = IF InitialLampStateKnown THEN FALSE ELSE BOOLEAN
      /\ prisonerCount = 0
      /\ visitedPrisoners = {}
      /\ currentPrisoner \in 1..N

Next == \/ CounterStep
        \/ NonCounterStep

CounterStep ==
    /\ currentPrisoner = 1
    /\ (lampState -> 
            (\E newLampState \in BOOLEAN: lampState' = newLampState)
            /\ prisonerCount' = prisonerCount + 1
            /\ visitedPrisoners' = visitedPrisoners \cup {currentPrisoner}
        \/ ~lampState ->
            lampState' = lampState
            /\ prisonerCount' = prisonerCount
            /\ visitedPrisoners' = visitedPrisoners \cup {currentPrisoner})
    /\ currentPrisoner' = (currentPrisoner + 1) % N

NonCounterStep ==
    /\ currentPrisoner /= 1
    /\ (lampState = FALSE -> 
            (\E newLampState \in BOOLEAN: lampState' = newLampState)
            /\ visitedPrisoners' = visitedPrisoners \cup {currentPrisoner}
        \/ ~lampState ->
            lampState' = lampState
            /\ visitedPrisoners' = visitedPrisoners \cup {currentPrisoner})
    /\ currentPrisoner' = (currentPrisoner + 1) % N

Terminating ==
    /\ Spec
    /\ <>(\A p \in 1..N: p \in visitedPrisoners)

TypeOK ==
    /\ lampState \in BOOLEAN
    /\ prisonerCount \in 0..(IF InitialLampStateKnown THEN N ELSE 2*N - 1)
    /\ visitedPrisoners \subseteq (1..N)
    /\ currentPrisoner \in 1..N

VictoryOK ==
    /\ Spec
    /\ <>(\A p \in 1..N: p \in visitedPrisoners)

WF_next(vars) == WF_vars(Next, vars)

=============================================================================