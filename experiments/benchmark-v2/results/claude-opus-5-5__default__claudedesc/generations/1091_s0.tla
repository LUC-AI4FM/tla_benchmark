---------------------------- MODULE PCR ----------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

ASSUME /\ DNA \in Nat
       /\ PRIMER \in Nat

VARIABLES tee,       \* current temperature
          primer,    \* number of free primers
          dna,       \* number of double-stranded DNA molecules
          template,  \* number of single-stranded templates
          hybrid     \* number of template-primer hybrids

vars == <<tee, primer, dna, template, hybrid>>

natMin(a, b) == IF a < b THEN a ELSE b

Total == template + primer + 2 * (dna + hybrid)

-----------------------------------------------------------------------------

TypeOK ==
    /\ tee \in {"Hot", "TooHot", "Warm"}
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

Init ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0

\* Denaturation: all double strands and hybrids come apart
heat ==
    /\ tee = "Hot"
    /\ tee' = "TooHot"
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ template' = template + hybrid + 2 * dna
    /\ hybrid' = 0

cool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ UNCHANGED <<primer, dna, template, hybrid>>

\* Annealing: some primers bind to some templates
anneal ==
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ UNCHANGED dna
    /\ \E k \in 1..natMin(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k

\* Extension: all hybrids become double-stranded DNA
extend ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ UNCHANGED <<primer, template>>
    /\ dna' = dna + hybrid
    /\ hybrid' = 0

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------------

\* Redundant non-negativity invariant
PrimerNonNeg == primer >= 0

\* Conservation invariant
ConstantCount == Total = PRIMER + 2 * DNA

\* Conservation expressed as a stuttering-tolerant safety property
Conservation == [][Total' = Total]_vars

\* Eventual primer depletion (does NOT hold)
PrimerDepleted == <>(primer = 0)

THEOREM Spec => [](TypeOK /\ PrimerNonNeg /\ ConstantCount)
THEOREM Spec => Conservation

=============================================================================