------------------------------ MODULE product ------------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

ASSUME DNA \in Nat /\ PRIMER \in Nat

VARIABLES
    tee,           \* temperature: "Hot", "Cold", "Warm"
    stage,         \* "init", "denatured", "ready", "annealed", "extended"
    cycle,         \* number of completed extension steps
    primer,        \* free primers
    dna,           \* original double strands (template/template)
    template,      \* original single-stranded templates
    longTemplate,  \* single strands with one primer-defined end
    shortTemplate, \* single strands with both ends primer-defined
    hybrid,        \* primer annealed to template
    longHybrid,    \* primer annealed to longTemplate
    shortHybrid,   \* primer annealed to shortTemplate
    mixed,         \* double strand: template / longTemplate
    longShort,     \* double strand: longTemplate / shortTemplate
    product        \* small final product: shortTemplate / shortTemplate

vars == << tee, stage, cycle, primer, dna, template, longTemplate,
           shortTemplate, hybrid, longHybrid, shortHybrid, mixed,
           longShort, product >>

counts == << primer, dna, template, longTemplate, shortTemplate, hybrid,
             longHybrid, shortHybrid, mixed, longShort, product >>

\* Every strand or primer counts as one unit of mass.
Mass == primer + template + longTemplate + shortTemplate
        + 2 * (dna + hybrid + longHybrid + shortHybrid
               + mixed + longShort + product)

TypeOK ==
    /\ tee \in {"Hot", "Cold", "Warm"}
    /\ stage \in {"init", "denatured", "ready", "annealed", "extended"}
    /\ cycle \in Nat
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ longTemplate \in Nat
    /\ shortTemplate \in Nat
    /\ hybrid \in Nat
    /\ longHybrid \in Nat
    /\ shortHybrid \in Nat
    /\ mixed \in Nat
    /\ longShort \in Nat
    /\ product \in Nat

MassConserved == Mass = PRIMER + 2 * DNA

PrimerBound == primer <= PRIMER

Init ==
    /\ tee = "Hot"
    /\ stage = "init"
    /\ cycle = 0
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ longTemplate = 0
    /\ shortTemplate = 0
    /\ hybrid = 0
    /\ longHybrid = 0
    /\ shortHybrid = 0
    /\ mixed = 0
    /\ longShort = 0
    /\ product = 0

\* High temperature: separate all doubles, release primers from hybrids.
denature ==
    /\ stage \in {"init", "extended"}
    /\ tee' = "Hot"
    /\ stage' = "denatured"
    /\ primer' = primer + hybrid + longHybrid + shortHybrid
    /\ template' = template + 2 * dna + mixed + hybrid
    /\ longTemplate' = longTemplate + mixed + longShort + longHybrid
    /\ shortTemplate' = shortTemplate + longShort + 2 * product + shortHybrid
    /\ dna' = 0
    /\ hybrid' = 0
    /\ longHybrid' = 0
    /\ shortHybrid' = 0
    /\ mixed' = 0
    /\ longShort' = 0
    /\ product' = 0
    /\ UNCHANGED cycle

\* Cooling: system becomes ready for annealing.
cool ==
    /\ stage = "denatured"
    /\ tee = "Hot"
    /\ tee' = "Cold"
    /\ stage' = "ready"
    /\ UNCHANGED << cycle, primer, dna, template, longTemplate, shortTemplate,
                    hybrid, longHybrid, shortHybrid, mixed, longShort, product >>

\* Annealing: primers bind to a nondeterministic number of available templates.
anneal ==
    /\ stage = "ready"
    /\ tee = "Cold"
    /\ primer > 0
    /\ template + longTemplate + shortTemplate > 0
    /\ \E k1 \in 0..template, k2 \in 0..longTemplate, k3 \in 0..shortTemplate :
          /\ k1 + k2 + k3 >= 1
          /\ k1 + k2 + k3 <= primer
          /\ primer' = primer - (k1 + k2 + k3)
          /\ template' = template - k1
          /\ longTemplate' = longTemplate - k2
          /\ shortTemplate' = shortTemplate - k3
          /\ hybrid' = hybrid + k1
          /\ longHybrid' = longHybrid + k2
          /\ shortHybrid' = shortHybrid + k3
    /\ stage' = "annealed"
    /\ UNCHANGED << tee, cycle, dna, mixed, longShort, product >>

\* Extension: hybrids become double strands; completes a cycle.
extend ==
    /\ stage = "annealed"
    /\ tee' = "Warm"
    /\ stage' = "extended"
    /\ cycle' = cycle + 1
    /\ mixed' = mixed + hybrid
    /\ longShort' = longShort + longHybrid
    /\ product' = product + shortHybrid
    /\ hybrid' = 0
    /\ longHybrid' = 0
    /\ shortHybrid' = 0
    /\ UNCHANGED << primer, dna, template, longTemplate, shortTemplate >>

\* Process terminates when no further annealing is possible.
Done ==
    /\ stage = "ready"
    /\ (primer = 0 \/ template + longTemplate + shortTemplate = 0)
    /\ UNCHANGED vars

Next == denature \/ cool \/ anneal \/ extend \/ Done

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(anneal)
        /\ WF_vars(denature)
        /\ WF_vars(cool)
        /\ WF_vars(extend)

-----------------------------------------------------------------------------
\* Safety: no final product before the third cycle.
thirdCycleProduct == (cycle < 3) => (product = 0)

\* Stage ordering: denature -> cool -> anneal -> extend -> denature ...
StageNext ==
    \/ /\ stage \in {"init", "extended"} /\ stage' = "denatured"
       /\ cycle' = cycle
    \/ /\ stage = "denatured" /\ stage' = "ready"
       /\ cycle' = cycle
    \/ /\ stage = "ready" /\ stage' = "annealed"
       /\ cycle' = cycle
    \/ /\ stage = "annealed" /\ stage' = "extended"
       /\ cycle' = cycle + 1

stagesSpec == /\ stage = "init"
              /\ cycle = 0
              /\ [][StageNext]_<<stage, cycle>>

\* Liveness: primers are eventually used up.
primerDepleted == <>(primer = 0)

=============================================================================