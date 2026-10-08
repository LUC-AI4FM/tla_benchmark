------------------------------- MODULE PCR -------------------------------

CONSTANTS 
    InitialPrimerStock \* The initial number of primers
    InitialDNAStock    \* The initial number of double-stranded DNA molecules

VARIABLES 
    Temperature,        \* Current temperature state: "HighHeat", "Cooling", "Warm", "MediumHeat"
    DoubleStrandedDNA,  \* Quantity of double-stranded DNA
    Templates,          \* Quantity of single-stranded templates
    Primers,            \* Quantity of free primers
    Hybrids             \* Quantity of template-primer hybrids

\* Type invariants for the system variables
TypeOK == 
    /\ DoubleStrandedDNA \in Nat
    /\ Templates         \in Nat
    /\ Primers           \in Nat
    /\ Hybrids          \in Nat
    /\ Temperature      \in {"HighHeat", "Cooling", "Warm", "MediumHeat"}

\* Invariant: primers must be non-negative
primerPositive == 
    Primers >= 0

\* Conservation invariant: total count of nucleic acid strands is preserved
preservationInvariant ==
    (Primers + Templates + 2 * DoubleStrandedDNA + 2 * Hybrids) = (InitialPrimerStock + 2 * InitialDNAStock)

\* Stuttering-tolerant temporal property for conservation
preservationProperty ==
    [] preservationInvariant

\* Next-state relation for the PCR process
Next == 
    \/ /\ Temperature = "HighHeat"
       /\ DoubleStrandedDNA' = 0
       /\ Templates'         = DoubleStrandedDNA + Hybrids
       /\ Primers'           = Primers + 2 * Hybrids
       /\ Hybrids'           = 0
       /\ Temperature'       \in {"Cooling", "Warm", "MediumHeat"}
    \/ /\ Temperature = "Cooling"
       /\ UNCHANGED <<DoubleStrandedDNA, Templates, Primers, Hybrids>>
       /\ Temperature'       \in {"Warm", "HighHeat", "MediumHeat"}
    \/ /\ Temperature = "Warm"
       /\ DoubleStrandedDNA' = DoubleStrandedDNA
       /\ Templates'         = Templates - HybridFormation
       /\ Primers'           = Primers - HybridFormation
       /\ Hybrids'           = Hybrids + HybridFormation
       /\ Temperature'       \in {"MediumHeat", "HighHeat", "Cooling"}
    \/ /\ Temperature = "MediumHeat"
       /\ DoubleStrandedDNA' = DoubleStrandedDNA + 2 * Hybrids
       /\ Templates'         = Templates
       /\ Primers'           = Primers
       /\ Hybrids'           = 0
       /\ Temperature'       \in {"HighHeat", "Cooling", "Warm"}

\* Nondeterministic number of hybrids formed during annealing
HybridFormation == CHOOSE n \in 0..Templates : TRUE

\* Initial predicate for the system
Init ==
    /\ DoubleStrandedDNA = InitialDNAStock
    /\ Templates         = 0
    /\ Primers           = InitialPrimerStock
    /\ Hybrids          = 0
    /\ Temperature      = "HighHeat"

\* Specification of the PCR process
Spec == 
    Init /\ [][Next]_<<DoubleStrandedDNA, Templates, Primers, Hybrids, Temperature>> /\ preservationProperty

=============================================================================