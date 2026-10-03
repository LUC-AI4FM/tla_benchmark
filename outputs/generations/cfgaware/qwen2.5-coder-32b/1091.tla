------------------------------- MODULE PcrCycle -------------------------------

CONSTANTS 
    MaxPrimers \* Maximum number of primers
    MaxTemplates \* Maximum number of templates

VARIABLES 
    temperature, \* Current temperature
    primers,     \* Count of available primers
    dsDNA,       \* Count of double-stranded DNA molecules
    ssTemplates, \* Count of single-stranded template molecules
    hybrids      \* Count of template-primer hybrid molecules

\* Define the possible states for the PCR cycle
PCRCycleStates == {"heating", "cooling", "annealing", "extension"}

\* Initial state predicate
Init == 
    /\ temperature = "heating"
    /\ primers \in 0..MaxPrimers
    /\ dsDNA = 0
    /\ ssTemplates \in 0..MaxTemplates
    /\ hybrids = 0

\* TypeOK: All counts are nonnegative integers and within bounds
TypeOK == 
    /\ primers \in 0..MaxPrimers
    /\ dsDNA \in 0..
    /\ ssTemplates \in 0..MaxTemplates
    /\ hybrids \in 0..

\* primerPositive: There is at least one primer available
primerPositive == primers > 0

\* Preservation invariant: Total count of molecules does not increase
preservationInvariant ==
    LET totalMolecules == primers + dsDNA + ssTemplates + hybrids
    IN  \/ totalMolecules = 0
        \/ \A s1, s2 \in PCRCycleStates : 
            /\ [][temperature' = s1]_<<s2>> => totalMolecules' = totalMolecules

\* Preservation property: The preservation invariant holds throughout the execution
preservationProperty == \A s \in PCRCycleStates : preservationInvariant

\* Next state relation for heating
Heating ==
    /\ temperature = "heating"
    /\ temperature' = "cooling"

\* Next state relation for cooling
Cooling ==
    /\ temperature = "cooling"
    /\ temperature' = "annealing"

\* Next state relation for annealing
Annealing ==
    /\ temperature = "annealing"
    /\ \E consumedPrimers, consumedTemplates \in 0..Min(primers, ssTemplates) :
        /\ primers' = primers - consumedPrimers
        /\ ssTemplates' = ssTemplates - consumedTemplates
        /\ hybrids' = hybrids + consumedPrimers * consumedTemplates
        /\ dsDNA' = dsDNA
        /\ temperature' = "extension"

\* Next state relation for extension
Extension ==
    /\ temperature = "extension"
    /\ dsDNA' = dsDNA + hybrids
    /\ hybrids' = 0
    /\ primers' = primers
    /\ ssTemplates' = ssTemplates
    /\ temperature' = "heating"

\* Complete next-state action relation
Next == Heating \/ Cooling \/ Annealing \/ Extension

\* Specification: Initial state and temporal properties
Spec ==
    Init /\ [][Next]_<<temperature>>

=============================================================================