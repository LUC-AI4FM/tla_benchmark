---------------------------- MODULE PCR ----------------------------

EXTENDS Integers

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

vars == <<tee, primer, dna, template, hybrid>>

Temperature == {"Hot", "TooHot", "Warm"}

TypeOK ==
    /\ tee \in Temperature
    /\ primer \in Int
    /\ dna \in Int
    /\ template \in Int
    /\ hybrid \in Int

Init ==
    /\ tee = "Hot"
    /\ dna = DNA
    /\ template = 0
    /\ hybrid = 0
    /\ primer = PRIMER

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
    /\ \E n \in 0..primer :
        /\ n <= template
        /\ primer' = primer - n
        /\ template' = template - n
        /\ hybrid' = hybrid + n
        /\ dna' = dna
    /\ tee' = "Warm"

extend ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ dna' = dna + hybrid
    /\ hybrid' = 0
    /\ UNCHANGED <<primer, template>>

Next ==
    \/ heat
    \/ cool
    \/ anneal
    \/ extend

Spec == Init /\ [][Next]_vars

NonNegPrimer == primer >= 0

Conservation == template + primer + 2*(dna + hybrid) = PRIMER + 2*DNA

ConservationSafety == [][Conservation]_vars

EventualPrimerDepletion == <>(primer = 0)

=============================================================================