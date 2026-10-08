------------------------------ MODULE PCR ------------------------------

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

vars == <<tee, primer, dna, template, hybrid>>

TypeOK ==
    /\ tee \in {"Hot", "TooHot", "Warm"}
    /\ primer \in Nat
    /\ dna \in Nat
    /\ template \in Nat
    /\ hybrid \in Nat

primerPositive == primer >= 0

preservationInvariant == template + primer + 2*(dna + hybrid) = PRIMER + 2*DNA

preservationProperty == [][template + primer + 2*(dna + hybrid) = PRIMER + 2*DNA]_vars

Init ==
    /\ tee = "Hot"
    /\ dna = DNA
    /\ primer = PRIMER
    /\ template = 0
    /\ hybrid = 0

heat ==
    /\ tee = "Hot"
    /\ tee' = "TooHot"
    /\ template' = template + 2*dna + hybrid
    /\ primer' = primer + hybrid
    /\ dna' = 0
    /\ hybrid' = 0

cool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"
    /\ UNCHANGED <<primer, dna, template, hybrid>>

anneal ==
    /\ tee = "Hot"
    /\ tee' = "Warm"
    /\ \E n \in 0..primer :
        /\ n <= template
        /\ primer' = primer - n
        /\ template' = template - n
        /\ hybrid' = hybrid + n
        /\ UNCHANGED dna

extend ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED <<primer, template>>

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_vars

primerDepletion == <>(primer = 0)

=============================================================================