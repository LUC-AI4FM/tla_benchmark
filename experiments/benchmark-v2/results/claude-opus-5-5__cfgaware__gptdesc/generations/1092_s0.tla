---------------------------- MODULE PCRProduct ----------------------------
EXTENDS Naturals

CONSTANTS DNA,      \* initial number of double-stranded original DNA molecules
          PRIMER    \* initial number of primers

ASSUME DNA \in Nat /\ DNA >= 1
ASSUME PRIMER \in Nat

VARIABLES
    temp,           \* current temperature
    stage,          \* current stage of the cycle
    cycle,          \* number of heating cycles performed
    primer,         \* remaining primer supply
    dna,            \* original double-stranded DNA
    template,       \* single-stranded original templates
    longTemplate,   \* single-stranded long (first-generation) templates
    shortTemplate,  \* single-stranded short (target-length) templates
    hybridTemplate, \* primer annealed to original template
    hybridLong,     \* primer annealed to long template
    hybridShort,    \* primer annealed to short template
    dsTemplate,     \* double strand: original template + long strand
    dsLong,         \* double strand: long strand + short strand
    product         \* final product: short + short double strand

vars == << temp, stage, cycle, primer, dna, template, longTemplate,
           shortTemplate, hybridTemplate, hybridLong, hybridShort,
           dsTemplate, dsLong, product >>

Temps  == {"low", "mid", "high"}
Stages == {"init", "denatured", "cooled", "extended"}

TypeOK ==
    /\ temp \in Temps
    /\ stage \in Stages
    /\ cycle \in Nat
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ longTemplate \in Nat
    /\ shortTemplate \in Nat
    /\ hybridTemplate \in Nat
    /\ hybridLong \in Nat
    /\ hybridShort \in Nat
    /\ dsTemplate \in Nat
    /\ dsLong \in Nat
    /\ product \in Nat

Init ==
    /\ temp = "low"
    /\ stage = "init"
    /\ cycle = 0
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ longTemplate = 0
    /\ shortTemplate = 0
    /\ hybridTemplate = 0
    /\ hybridLong = 0
    /\ hybridShort = 0
    /\ dsTemplate = 0
    /\ dsLong = 0
    /\ product = 0

\* Heating: denature all double-stranded forms into single strands.
Heat ==
    /\ stage \in {"init", "extended"}
    /\ primer > 0
    /\ temp' = "high"
    /\ stage' = "denatured"
    /\ cycle' = cycle + 1
    /\ dna' = 0
    /\ template' = template + 2 * dna + dsTemplate
    /\ longTemplate' = longTemplate + dsTemplate + dsLong
    /\ shortTemplate' = shortTemplate + dsLong + 2 * product
    /\ dsTemplate' = 0
    /\ dsLong' = 0
    /\ product' = 0
    /\ UNCHANGED << primer, hybridTemplate, hybridLong, hybridShort >>

\* Cooling to annealing temperature.
Cool ==
    /\ stage = "denatured"
    /\ temp' = "low"
    /\ stage' = "cooled"
    /\ UNCHANGED << cycle, primer, dna, template, longTemplate, shortTemplate,
                    hybridTemplate, hybridLong, hybridShort,
                    dsTemplate, dsLong, product >>

AnnealTemplate ==
    /\ template > 0
    /\ template' = template - 1
    /\ hybridTemplate' = hybridTemplate + 1
    /\ UNCHANGED << longTemplate, shortTemplate, hybridLong, hybridShort >>

AnnealLong ==
    /\ longTemplate > 0
    /\ longTemplate' = longTemplate - 1
    /\ hybridLong' = hybridLong + 1
    /\ UNCHANGED << template, shortTemplate, hybridTemplate, hybridShort >>

AnnealShort ==
    /\ shortTemplate > 0
    /\ shortTemplate' = shortTemplate - 1
    /\ hybridShort' = hybridShort + 1
    /\ UNCHANGED << template, longTemplate, hybridTemplate, hybridLong >>

\* Annealing: a primer binds to a single-stranded template.
Anneal ==
    /\ stage = "cooled"
    /\ primer > 0
    /\ primer' = primer - 1
    /\ (AnnealTemplate \/ AnnealLong \/ AnnealShort)
    /\ UNCHANGED << temp, stage, cycle, dna, dsTemplate, dsLong, product >>

\* Extension: polymerase extends annealed primers into double strands.
Extend ==
    /\ stage = "cooled"
    /\ (primer = 0 \/ template + longTemplate + shortTemplate = 0)
    /\ temp' = "mid"
    /\ stage' = "extended"
    /\ dsTemplate' = dsTemplate + hybridTemplate
    /\ dsLong' = dsLong + hybridLong
    /\ product' = product + hybridShort
    /\ hybridTemplate' = 0
    /\ hybridLong' = 0
    /\ hybridShort' = 0
    /\ UNCHANGED << cycle, primer, dna, template, longTemplate, shortTemplate >>

\* Terminal stuttering once primers are exhausted.
Done ==
    /\ stage \in {"init", "extended"}
    /\ primer = 0
    /\ UNCHANGED vars

Next == Heat \/ Cool \/ Anneal \/ Extend \/ Done

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Heat)
    /\ WF_vars(Cool)
    /\ WF_vars(Anneal)
    /\ WF_vars(Extend)

\* Safety: no final product exists before the third cycle.
thirdCycleProduct == [](cycle < 3 => product = 0)

\* Stages progress in the prescribed order.
stagesSpec ==
    [][ /\ (stage = "init"      => stage' \in {"init", "denatured"})
        /\ (stage = "denatured" => stage' \in {"denatured", "cooled"})
        /\ (stage = "cooled"    => stage' \in {"cooled", "extended"})
        /\ (stage = "extended"  => stage' \in {"extended", "denatured"}) ]_stage

\* Liveness: the primer supply is eventually exhausted.
primerDepleted == <>(primer = 0)

=============================================================================