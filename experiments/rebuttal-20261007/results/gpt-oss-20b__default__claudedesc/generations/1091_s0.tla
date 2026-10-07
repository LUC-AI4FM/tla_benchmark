MODULE PCR
CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

Nat == {n \in Int : n >= 0}

TypeOK ==
    /\ tee \in {"Hot","TooHot","Warm"}
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

heat ==
    /\ tee = "Hot"
    /\ tee' = "TooHot"
    /\ dna' = 0
    /\ template' = template + dna + hybrid
    /\ primer' = primer + hybrid
    /\ hybrid' = 0

cool ==
    /\ tee = "TooHot"
    /\ tee' = "Hot"

anneal ==
    /\ tee = "Hot"
    /\ k \in Nat
    /\ k <= Min(primer, template)
    /\ tee' = "Warm"
    /\ primer' = primer - k
    /\ template' = template - k
    /\ hybrid' = hybrid + k
    /\ dna' = dna

extend ==
    /\ tee = "Warm"
    /\ tee' = "Hot"
    /\ dna' = dna + hybrid
    /\ primer' = 0
    /\ template' = 0
    /\ hybrid' = 0

Next == heat \/ cool \/ anneal \/ extend

vars == {tee, primer, dna, template, hybrid}

ConservationInvariant ==
    [] (template + primer + 2 * (dna + hybrid) = PRIMER + 2 * DNA)

TypeInvariant ==
    [] TypeOK

Liveness ==
    <> (primer = 0)

Spec == Init /\ [][Next]_vars
===============================================================================