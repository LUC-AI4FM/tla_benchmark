```
MODULE PCR
EXTENDS Integers, Strings

CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

Init ==
  /\ tee = "Hot"
  /\ primer = PRIMER
  /\ dna = DNA
  /\ template = 0
  /\ hybrid = 0

Next ==
  \/ heat
  \/ cool
  \/ anneal
  \/ extend

heat ==
  /\ tee = "Hot"
  /\ tee' = "TooHot"
  /\ dna' = 0
  /\ template' = DNA + hybrid
  /\ primer' = PRIMER
  /\ hybrid' = 0

cool ==
  /\ tee = "TooHot"
  /\ tee' = "Hot"
  /\ primer' = primer
  /\ dna' = dna
  /\ template' = template
  /\ hybrid' = hybrid

anneal ==
  /\ tee = "Hot"
  /\ tee' = "Warm"
  /\ primer' \in 0..primer
  /\ dna' = dna
  /\ template' = template - (primer - primer')
  /\ hybrid' = hybrid + (primer - primer')

extend ==
  /\ tee = "Warm"
  /\ tee' = "Hot"
  /\ primer' = primer + hybrid
  /\ dna' = dna + hybrid
  /\ template' = template
  /\ hybrid' = 0

TypeOK == 
  /\ tee \in {"Hot", "TooHot", "Warm"}
  /\ primer \in Int
  /\ dna \in Int
  /\ template \in Int
  /\ hybrid \in Int

NonNegPrimer == primer >= 0

Conservation == template + primer + 2*(dna + hybrid) = PRIMER + 2*DNA

Spec == Init /\ [][Next]_<<tee, primer, dna, template, hybrid>>
          /\ WF_<<heat, cool, anneal, extend>>(Next)
          /\ []TypeOK
          /\ []NonNegPrimer
          /\ []Conservation

THEOREM Spec => []<>primer = 0
```