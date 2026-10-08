------------------------------- MODULE PCRModel -------------------------------

CONSTANTS 
    InitDoubleStranded,  \* Initial count of intact double-stranded target molecules
    InitTemplates,       \* Initial count of single-stranded templates
    InitPrimers          \* Initial count of primer molecules (pooled)

VARIABLES 
    DoubleStranded,      \* Count of intact double-stranded target molecules
    Templates,           \* Count of single-stranded templates
    Primers,             \* Count of primer molecules (pooled)
    Hybrids,             \* Count of primer-template hybrids
    Temperature          \* Current temperature phase: "Denaturation", "Annealing", or "Extension"

\* Type invariants for the system variables
TypeOK == 
    /\ DoubleStranded \in Nat
    /\ Templates \in Nat
    /\ Primers \in Nat
    /\ Hybrids \in Nat
    /\ Temperature \in {"Denaturation", "Annealing", "Extension"}

\* Invariant to ensure primers are non-negative
primerPositive == 
    Primers >= 0

\* Linear invariant for conservation of molecular material
preservationInvariant ==
    DoubleStranded + Templates + Primers + Hybrids = InitDoubleStranded + InitTemplates + InitPrimers

\* Property stating that the preservation invariant always holds
preservationProperty ==
    [] preservationInvariant

\* Initial predicate defining the start state of the system
Init == 
    /\ DoubleStranded = InitDoubleStranded
    /\ Templates = InitTemplates
    /\ Primers = InitPrimers
    /\ Hybrids = 0
    /\ Temperature \in {"Denaturation", "Annealing", "Extension"}

\* Action for denaturation phase: breaks double strands and hybrids into single strands
Denaturation ==
    /\ Temperature = "Denaturation"
    /\ DoubleStranded' = 0
    /\ Templates' = Templates + DoubleStranded + Hybrids
    /\ Primers' = Primers + Hybrids
    /\ Hybrids' = 0
    /\ Temperature' \in {"Annealing", "Extension"}

\* Action for annealing phase: consumes primers and templates to form hybrids
Annealing ==
    /\ Temperature = "Annealing"
    /\ \/ Templates > 0 /\ Primers > 0
       \/ Hybrids' = Min(Templates, Primers)
    /\ DoubleStranded' = DoubleStranded
    /\ Templates' = Templates - Hybrids'
    /\ Primers' = Primers - Hybrids'
    /\ Hybrids' = Hybrids + Min(Templates, Primers)
    /\ Temperature' \in {"Denaturation", "Extension"}

\* Action for extension phase: converts hybrids into new double strands
Extension ==
    /\ Temperature = "Extension"
    /\ Hybrids > 0
    /\ DoubleStranded' = DoubleStranded + Hybrids
    /\ Templates' = Templates
    /\ Primers' = Primers
    /\ Hybrids' = 0
    /\ Temperature' \in {"Denaturation", "Annealing"}

\* Next-state relation capturing all possible actions
Next == 
    \/ Denaturation
    \/ Annealing
    \/ Extension

\* Specification of the system behavior
Spec ==
    Init /\ [][Next]_<<DoubleStranded, Templates, Primers, Hybrids, Temperature>>

=============================================================================