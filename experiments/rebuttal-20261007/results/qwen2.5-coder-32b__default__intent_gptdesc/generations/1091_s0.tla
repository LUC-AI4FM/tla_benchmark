------------------------------- MODULE PCRModel -------------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS 
    InitDoubleStranded,
    InitTemplates,
    InitPrimers,
    MaxCycles

VARIABLES 
    DoubleStranded,
    Templates,
    Primers,
    Hybrids,
    Temperature,
    CycleCount

Init == 
    /\ DoubleStranded = InitDoubleStranded
    /\ Templates = InitTemplates
    /\ Primers = InitPrimers
    /\ Hybrids = 0
    /\ Temperature \in {"HighDenaturation", "LowerAnnealing", "IntermediateExtension"}
    /\ CycleCount = 0

Next == 
    \/ /\ Temperature = "HighDenaturation"
       /\ DoubleStranded' = 0
       /\ Templates' = DoubleStranded + Templates
       /\ Primers' = Primers + [Hybrids -> 1]
       /\ Hybrids' = 0
       /\ Temperature' \in {"LowerAnnealing", "IntermediateExtension"}
    \/ /\ Temperature = "LowerAnnealing"
       /\ LET MaxHybrids == MIN(Templates, Primers)
          NewHybrids == CHOOSE h \in 0..MaxHybrids : TRUE
       IN
           /\ DoubleStranded' = DoubleStranded
           /\ Templates' = Templates - NewHybrids
           /\ Primers' = Primers - NewHybrids
           /\ Hybrids' = Hybrids + NewHybrids
           /\ Temperature' \in {"IntermediateExtension", "HighDenaturation"}
    \/ /\ Temperature = "IntermediateExtension"
       /\ DoubleStranded' = DoubleStranded + Hybrids
       /\ Templates' = Templates
       /\ Primers' = Primers
       /\ Hybrids' = 0
       /\ Temperature' = "HighDenaturation"
       /\ CycleCount' = CycleCount + 1

Spec == 
    Init /\ [][Next]_<<DoubleStranded, Templates, Primers, Hybrids, Temperature, CycleCount>>

ConservationInvariant ==
    DoubleStranded + Templates + Primers + Hybrids = InitDoubleStranded + InitTemplates + InitPrimers

NonNegativityInvariant ==
    /\ DoubleStranded >= 0
    /\ Templates >= 0
    /\ Primers >= 0
    /\ Hybrids >= 0

SafetyProperties ==
    /\ ConservationInvariant
    /\ NonNegativityInvariant

LivenessProperties ==
    \/ CycleCount < MaxCycles
    \/ \E n \in Nat : <<DoubleStranded, Templates, Primers, Hybrids, Temperature, CycleCount>>_n = <<DoubleStranded, Templates, Primers, Hybrids, Temperature, MaxCycles>>
       /\ DoubleStranded_n > InitDoubleStranded

Fairness ==
    WF_next(<<DoubleStranded, Templates, Primers, Hybrids, Temperature, CycleCount>>)

=============================================================================