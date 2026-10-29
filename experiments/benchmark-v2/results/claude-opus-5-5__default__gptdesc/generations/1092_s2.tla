------------------------------- MODULE PCR -------------------------------
EXTENDS Naturals

CONSTANTS MaxCycles, InitDNA, InitPrimers

ASSUME MaxCycles \in Nat /\ InitDNA \in Nat /\ InitPrimers \in Nat

VARIABLES
    temp,          \* current temperature
    stage,         \* current stage of the thermal cycle
    cycle,         \* number of cycles started
    primer,        \* free primer supply
    template,      \* single-stranded original templates
    longT,         \* single strands with one defined end (longer than product)
    shortT,        \* single strands of exact product length
    hybTemplate,   \* original template annealed with primer
    hybLong,       \* long strand annealed with primer
    hybShort,      \* short strand annealed with primer
    dna,           \* original double-stranded DNA
    dnaLong,       \* double strand: original template + long strand
    dnaLongShort,  \* double strand: long strand + short strand
    product        \* final product: short strand + short strand

vars == << temp, stage, cycle, primer, template, longT, shortT,
           hybTemplate, hybLong, hybShort, dna, dnaLong, dnaLongShort,
           product >>

Temps  == {25, 55, 72, 95}
Stages == {"ready", "denatured", "cooled", "annealed", "extended"}

Min(a, b) == IF a <= b THEN a ELSE b

TypeOK ==
    /\ temp \in Temps
    /\ stage \in Stages
    /\ cycle \in 0..MaxCycles
    /\ primer \in Nat
    /\ template \in Nat
    /\ longT \in Nat
    /\ shortT \in Nat
    /\ hybTemplate \in Nat
    /\ hybLong \in Nat
    /\ hybShort \in Nat
    /\ dna \in Nat
    /\ dnaLong \in Nat
    /\ dnaLongShort \in Nat
    /\ product \in Nat

Init ==
    /\ temp = 25
    /\ stage = "ready"
    /\ cycle = 0
    /\ primer = InitPrimers
    /\ template = 0
    /\ longT = 0
    /\ shortT = 0
    /\ hybTemplate = 0
    /\ hybLong = 0
    /\ hybShort = 0
    /\ dna = InitDNA
    /\ dnaLong = 0
    /\ dnaLongShort = 0
    /\ product = 0

\* Heating: denature all double-stranded forms into single strands; new cycle
Heat ==
    /\ stage \in {"ready", "extended"}
    /\ cycle < MaxCycles
    /\ temp' = 95
    /\ stage' = "denatured"
    /\ cycle' = cycle + 1
    /\ template' = template + 2 * dna + dnaLong
    /\ longT' = longT + dnaLong + dnaLongShort
    /\ shortT' = shortT + dnaLongShort + 2 * product
    /\ dna' = 0
    /\ dnaLong' = 0
    /\ dnaLongShort' = 0
    /\ product' = 0
    /\ UNCHANGED << primer, hybTemplate, hybLong, hybShort >>

\* Cooling: lower temperature to the annealing temperature
Cool ==
    /\ stage = "denatured"
    /\ temp' = 55
    /\ stage' = "cooled"
    /\ UNCHANGED << cycle, primer, template, longT, shortT, hybTemplate,
                    hybLong, hybShort, dna, dnaLong, dnaLongShort, product >>

\* Annealing: primers bind to single strands, limited by primer supply
Anneal ==
    /\ stage = "cooled"
    /\ LET a1 == Min(template, primer)
           a2 == Min(longT, primer - a1)
           a3 == Min(shortT, primer - a1 - a2)
       IN /\ template' = template - a1
          /\ longT' = longT - a2
          /\ shortT' = shortT - a3
          /\ hybTemplate' = hybTemplate + a1
          /\ hybLong' = hybLong + a2
          /\ hybShort' = hybShort + a3
          /\ primer' = primer - a1 - a2 - a3
    /\ stage' = "annealed"
    /\ UNCHANGED << temp, cycle, dna, dnaLong, dnaLongShort, product >>

\* Extension: polymerase extends primed strands into double-stranded forms
Extend ==
    /\ stage = "annealed"
    /\ temp' = 72
    /\ stage' = "extended"
    /\ dnaLong' = dnaLong + hybTemplate
    /\ dnaLongShort' = dnaLongShort + hybLong
    /\ product' = product + hybShort
    /\ hybTemplate' = 0
    /\ hybLong' = 0
    /\ hybShort' = 0
    /\ UNCHANGED << cycle, primer, template, longT, shortT, dna >>

\* Terminal stuttering once all cycles are complete
Done ==
    /\ stage \in {"ready", "extended"}
    /\ cycle = MaxCycles
    /\ UNCHANGED vars

Next == Heat \/ Cool \/ Anneal \/ Extend \/ Done

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Heat)
    /\ WF_vars(Cool)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)

\* Safety: no final product exists before the third cycle
NoEarlyProduct == (cycle < 3) => (product = 0)

\* Liveness: the process eventually completes all cycles
Termination == <>(cycle = MaxCycles /\ stage = "extended")

THEOREM Spec => [](TypeOK /\ NoEarlyProduct)
==========================================================================