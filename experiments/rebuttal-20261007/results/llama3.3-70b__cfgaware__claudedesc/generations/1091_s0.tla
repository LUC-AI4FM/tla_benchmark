---------------------------- MODULE PCR --------------------------------
EXTENDS Integers, Strings

CONSTANT DNA, PRIMER

VARIABLE tee, primer, dna, template, hybrid

TypeOK == 
  (tee \in {"Hot", "TooHot", "Warm"}) 
  /\ (primer \in 0..PRIMER) 
  /\ (dna \in 0..DNA) 
  /\ (template \in 0..2*DNA) 
  /\ (hybrid \in 0..(PRIMER + DNA))

Init == 
  (tee = "Hot") 
  /\ (primer = PRIMER) 
  /\ (dna = DNA) 
  /\ (template = 0) 
  /\ (hybrid = 0)

heat == 
  (tee' = "TooHot") 
  /\ (primer' = primer + hybrid) 
  /\ (dna' = 0) 
  /\ (template' = template + 2*dna + 2*hybrid) 
  /\ (hybrid' = 0) 
  /\ (tee = "Hot")

cool == 
  (tee' = "Hot") 
  /\ (primer' = primer) 
  /\ (dna' = dna) 
  /\ (template' = template) 
  /\ (hybrid' = hybrid) 
  /\ (tee = "TooHot")

anneal == 
  (tee' = "Warm") 
  /\ (primer' \in 0..primer) 
  /\ (dna' = dna) 
  /\ (template' = template - (primer - primer')) 
  /\ (hybrid' = hybrid + (primer - primer')) 
  /\ (tee = "Hot")

extend == 
  (tee' = "Hot") 
  /\ (primer' = primer) 
  /\ (dna' = dna + hybrid) 
  /\ (template' = template) 
  /\ (hybrid' = 0) 
  /\ (tee = "Warm")

Next == heat \/ cool \/ anneal \/ extend

Spec == Init /\ [][Next]_<<tee, primer, dna, template, hybrid>>

primerPositive == primer >= 0

preservationInvariant == template + primer + 2*(dna + hybrid) = PRIMER + 2*DNA

preservationProperty == []preservationInvariant

THEOREM Spec => []TypeOK
THEOREM Spec => []primerPositive
THEOREM Spec => preservationProperty
THEOREM Spec => <>[](primer = 0)  \* This theorem does not hold.
================================================================================