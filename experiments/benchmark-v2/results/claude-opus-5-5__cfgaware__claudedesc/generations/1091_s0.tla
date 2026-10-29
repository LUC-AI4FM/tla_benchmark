------------------------------- MODULE PCR -------------------------------
EXTENDS Naturals

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

vars == <<tee, primer, dna, template, hybrid>>

natMin(a, b) == IF a < b THEN a ELSE b

Init ==
    /\ tee = "Hot"
    /\ primer = PRIMER
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0

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

anneal ==
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ UNCHANGED dna
    /\ \E k \in 1..natMin(primer, template) :
          /\ primer' = primer - k
          /\ template' = template - k
          /\ hybrid' = hybrid + k

extend ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ UNCHANGED <<primer, template>>
    /\ dna' = dna + hybrid
    /\ hybrid' = 0

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
    /\ tee \in {"Hot", "TooHot", "Warm"}
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

primerPositive == primer >= 0

preservationInvariant ==
    template + primer + 2 * (dna + hybrid) = PRIMER + 2 * DNA

preservationProperty ==
    [][ template + primer + 2 * (dna + hybrid)
        = template' + primer' + 2 * (dna' + hybrid') ]_vars

\* Does NOT hold: the system may cycle heat/cool forever.
primersDepleted == <>(primer = 0)

=============================================================================