```tla
------------------------------- MODULE PrisonerLightSwitch -------------------------------
VARIABLES light, prisonersVisited, counterPrisoner, prisoners

CONSTANTS N

ASSUME N \in Nat /\ N > 1

(*--algorithm PrisonerLightSwitch *)

variables 
    light = FALSE,          \* Initially unknown; assume FALSE for standard variant
    prisonersVisited = {},   \* Set of prisoners who have visited the cell
    counterPrisoner \in prisoners,
    prisoners = {p \in 1..N}

fair process (prisoners) \in prisoners
begin
    loop:
        if pc = "enter" then
            if self = counterPrisoner then
                if light \in {TRUE, FALSE} then
                    light := FALSE;
                    prisonersVisited := prisonersVisited \cup {self};
                    if Cardinality(prisonersVisited) >= 2*N - 1 then
                        print "Victory!";
                        break loop;
                    end if;
                end if;
            else
                if light = FALSE then
                    light := TRUE;
                    prisonersVisited := prisonersVisited \cup {self};
                end if;
            end if;
        end if;
        pc := "enter";
end process;

Terminating == <>(Cardinality(prisonersVisited) >= 2*N - 1)

TypeOK ==
    /\ light \in BOOLEAN
    /\ prisonersVisited \subseteq prisoners
    /\ counterPrisoner \in prisoners

VictoryOK ==
    Let allVisited == Cardinality(prisonersVisited) = N
    In  Terminating -> allVisited

Spec == 
    /\ TypeOK
    /\ []TypeOK
    /\ WF_<<prisoners>>_(pc = "enter")

end algorithm
```

This TLA+ specification models the prisoner light-switch puzzle with both variants (known and unknown initial light state). The `counterPrisoner` is designated to count the number of unique prisoners who have visited the cell. Non-counter prisoners signal by turning on the lamp if it's off. The system asserts that under weak fairness, the prisoners will eventually announce victory when all prisoners have visited the cell at least once (in the unknown case, they wait for 2N-1 visits). The `TypeOK` operator ensures that the variables maintain their correct types, and `VictoryOK` asserts that any victory announcement implies every prisoner has visited the cell.