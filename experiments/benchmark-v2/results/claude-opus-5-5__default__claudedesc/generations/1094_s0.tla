------------------------------- MODULE stages -------------------------------
EXTENDS Naturals

------------------------------- MODULE clean --------------------------------
(***************************************************************************)
(* The simpler prior PCR specification, without stages or cycle counting.  *)
(***************************************************************************)
CONSTANTS DNA, PRIMER

VARIABLES tee, primer, dna, template, hybrid

cvars == <<tee, primer, dna, template, hybrid>>

cnatMin(i, j) == IF i < j THEN i ELSE j

cheat == /\ tee = "Hot"
         /\ tee' = "TooHot"
         /\ primer' = primer + hybrid
         /\ dna' = 0
         /\ template' = template + hybrid + 2 * dna
         /\ hybrid' = 0

ccool == /\ tee = "TooHot"
         /\ tee' = "Hot"
         /\ UNCHANGED <<primer, dna, template, hybrid>>

canneal == /\ tee = "Hot"
           /\ tee' = "Warm"
           /\ UNCHANGED dna
           /\ \E k \in 1..cnatMin(primer, template) :
                 /\ primer' = primer - k
                 /\ template' = template - k
                 /\ hybrid' = hybrid + k

cextend == /\ tee = "Warm"
           /\ tee' = "Hot"
           /\ UNCHANGED <<primer, template>>
           /\ dna' = dna + hybrid
           /\ hybrid' = 0

cInit == /\ tee = "Hot"
         /\ primer = PRIMER
         /\ dna = DNA
         /\ template = 0
         /\ hybrid = 0

cNext == cheat \/ ccool \/ canneal \/ cextend

Spec == /\ cInit
        /\ [][cNext]_cvars
        /\ WF_cvars(canneal)
        /\ WF_cvars(cheat)
        /\ WF_cvars(ccool)
        /\ WF_cvars(cextend)

primerDepleted == <>(primer = 0)
=============================================================================