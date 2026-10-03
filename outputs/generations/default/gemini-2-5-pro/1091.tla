-------------------------------- MODULE PCR --------------------------------
EXTENDS Integers, TLC

CONSTANTS
    \* The initial number of primers available.
    InitialPrimers,

    \* The initial number of double-stranded DNA molecules.
    InitialDNA

ASSUME InitialPrimers \in Nat /\ InitialDNA \in Nat

VARIABLES
    \* The current stage of the PCR cycle.
    stage,

    \* The number of free primers.
    primers,

    \* The number of double-stranded DNA molecules.
    dna,

    \* The number of single-stranded DNA templates.
    templates,

    \* The number of template-primer hybrids ready for extension.
    hybrids

vars == <<stage, primers, dna, templates, hybrids>>

\* The set of possible stages in the PCR cycle.
Stages == {"heating", "cooling", "annealing", "extending"}

-----------------------------------------------------------------------------
\* Define the initial state of the system.
Init ==
    /\ stage = "heating"
    /\ primers = InitialPrimers
    /\ dna = InitialDNA
    /\ templates = 0
    /\ hybrids = 0

-----------------------------------------------------------------------------
\* The actions define the steps of the PCR cycle.

\* Denaturation: High heat separates double-stranded DNA into single strands.
Denature ==
    /\ stage = "heating"
    /\ templates' = templates + 2 * dna
    /\ dna' = 0
    /\ stage' = "cooling"
    /\ UNCHANGED <<primers, hybrids>>

\* Cooling: The temperature is lowered to allow for primer annealing.
TransitionToAnneal ==
    /\ stage = "cooling"
    /\ stage' = "annealing"
    /\ UNCHANGED <<primers, dna, templates, hybrids>>

\* Annealing: Primers bind to single-stranded templates.
\* This step is non-deterministic: some number of possible bindings occur.
Anneal ==
    /\ stage = "annealing"
    /\ IF primers > 0 /\ templates > 0
       THEN LET num_annealed == CHOOSE n \in 1..Min(primers, templates) : TRUE
            IN  /\ primers' = primers - n
                /\ templates' = templates - n
                /\ hybrids' = hybrids + n
                /\ UNCHANGED <<dna>>
       ELSE /\ UNCHANGED <<primers, dna, templates, hybrids>>
    /\ stage' = "extending"

\* Extension: DNA polymerase synthesizes a new strand, converting a hybrid
\* into a full double-stranded DNA molecule. In this abstract model, we assume
\* this step also consumes a free template to pair with the newly synthesized
\* strand, which preserves the total strand count.
Extend ==
    /\ stage = "extending"
    /\ LET num_extended == Min(hybrids, templates)
       IN  /\ dna' = dna + num_extended
           /\ hybrids' = hybrids - num_extended
           /\ templates' = templates - num_extended
           /\ UNCHANGED <<primers>>
    /\ stage' = "heating"


\* The next-state relation is the disjunction of all possible actions.
Next ==
    \/ Denature
    \/ TransitionToAnneal
    \/ Anneal
    \/ Extend

-----------------------------------------------------------------------------
\* The full specification including fairness. Weak fairness on Next ensures
\* the cycle does not get stuck if an action is continuously enabled.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
\* INVARIANTS

\* Type safety: all variables must maintain their expected types.
TypeOK ==
    /\ stage \in Stages
    /\ primers \in Nat
    /\ dna \in Nat
    /\ templates \in Nat
    /\ hybrids \in Nat

\* This expression defines the total count of template strands in the system.
TotalStrands == 2 * dna + templates + hybrids

\* A key safety property is that the total number of template strands is
\* conserved throughout the process. This requires the abstract model of the
\* Extend action as defined above.
CountInvariant == TotalStrands = 2 * InitialDNA

-----------------------------------------------------------------------------
\* LIVENESS PROPERTIES

\* This property states that eventually all primers will be used up.
\* TLC will find a counterexample for this property, because if templates
\* are depleted first, annealing stops and the number of primers becomes
\* constant.
EventuallyPrimersDepleted == <>(primers = 0)

=============================================================================