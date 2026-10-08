------------------------------- MODULE PrisonersAndLightBulb -------------------------------

CONSTANTS N \* Number of prisoners
ASSUME N > 1

VARIABLES lampState, prisonerCount, prisonerSignals, currentPrisoner

(*--algorithm PrisonersAndLightBulb
variables 
    lampState = FALSE, \* Initial state of the lamp (unknown)
    prisonerCount = 0, \* Count of unique prisoners who have visited the room
    prisonerSignals = [1..N -> 0], \* Number of times each prisoner has toggled the lamp as a signal
    currentPrisoner; \* The prisoner currently in the room

fair process (prisoners = 1..N) \* Each prisoner is chosen nondeterministically
begin
    while TRUE do
        await currentPrisoner = prisoners;
        if prisonerCount < N - 1 then
            if prisonerSignals[prisoners] < 2 then \* Allow each non-counter prisoner to signal at most twice
                lampState := NOT lampState; \* Toggle the lamp state as a signal
                prisonerSignals[prisoners] := prisonerSignals[prisoners] + 1;
            end if;
        else
            if prisoners = 1 then \* Distinguished prisoner increments count when seeing the lamp on
                if lampState then
                    prisonerCount := prisonerCount + 1;
                    lampState := FALSE; \* Reset the lamp state after counting
                end if;
            else
                if prisonerSignals[prisoners] < 2 then \* Allow each non-counter prisoner to signal at most twice
                    lampState := NOT lampState; \* Toggle the lamp state as a signal
                    prisonerSignals[prisoners] := prisonerSignals[prisoners] + 1;
                end if;
            end if;
        end if;
        currentPrisoner := << >>; \* Reset current prisoner after visit
    end while;
end process;

fair process (announcer = 1) \* Any prisoner can make an announcement
begin
    await prisonerCount = N - 1 AND lampState = FALSE; \* Wait until all prisoners have visited and the lamp is off
    print "All prisoners have visited the room.";
    break;
end process;

end algorithm *)

Spec == /\ TypeOK
        /\ VictoryOK
        /\ Terminating

TypeOK == /\ lampState \in {TRUE, FALSE}
          /\ prisonerCount \in 0..N-1
          /\ \A p \in 1..N : prisonerSignals[p] \in 0..2
          /\ currentPrisoner \in (1..N) \cup {<< >>}

VictoryOK == [](prisonerCount < N - 1 \/ lampState = FALSE)

Terminating == <>(prisonerCount = N - 1 /\ lampState = FALSE)

=============================================================================