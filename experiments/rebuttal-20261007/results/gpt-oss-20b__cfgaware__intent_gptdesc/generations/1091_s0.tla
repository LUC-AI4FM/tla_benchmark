------------------------------ MODULE PCR ------------------------------
EXTENDS Naturals

CONSTANTS initDoubleStrand, initSingleStrand, initPrimer

VARIABLES doubleStrand, singleStrand, primer, hybrid, phase

\* Helper function
min(a,b) == IF a <= b THEN a ELSE b

TypeOK ==
  /\ doubleStrand \in Nat
  /\ singleStrand \in Nat
  /\ primer \in Nat
  /\ hybrid \in Nat
  /\ phase \in {"Denature", "Anneal", "Extend"}

primerPositive == (primer > 0)

preservationInvariant ==
  LET totalMass == 2*doubleStrand + singleStrand + primer + 2*hybrid
      initTotalMass == 2*initDoubleStrand + initSingleStrand + initPrimer
  IN totalMass = initTotalMass

Init ==
  /\ doubleStrand = initDoubleStrand
  /\ singleStrand = initSingleStrand
  /\ primer = initPrimer
  /\ hybrid = 0
  /\ phase = "Denature"
  /\ TypeOK

DenatureAction ==
  /\ phase = "Denature"
  /\ LET newSS == 2*doubleStrand + hybrid
         newPrimers == hybrid
     IN /\ singleStrand' = newSS
        /\ primer' = primer + newPrimers
        /\ doubleStrand' = 0
        /\ hybrid' = 0
        /\ phase' = "Anneal"
        /\ TypeOK

AnnealingAction ==
  /\ phase = "Anneal"
  /\ LET maxPairs == min(primer, singleStrand)
     IN /\ \E k \in 0..maxPairs :
          /\ doubleStrand' = doubleStrand
          /\ singleStrand' = singleStrand - k
          /\ primer' = primer - k
          /\ hybrid' = hybrid + k
          /\ phase' = "Extend"
          /\ TypeOK

ExtensionAction ==
  /\ phase = "Extend"
  /\ LET maxExt == hybrid
     IN /\ \E l \in 0..maxExt :
          /\ doubleStrand' = doubleStrand + l
          /\ singleStrand' = singleStrand
          /\ primer' = primer
          /\ hybrid' = hybrid - l
          /\ phase' = "Denature"
          /\ TypeOK

Next ==
  DenatureAction \/ AnnealingAction \/ ExtensionAction

Spec == Init /\ [][Next]_<<doubleStrand, singleStrand, primer, hybrid, phase>>

preservationProperty ==
  /\ (initPrimer > 0 /\ initSingleStrand > 0)
  => <> (doubleStrand > initDoubleStrand)

=============================================================================