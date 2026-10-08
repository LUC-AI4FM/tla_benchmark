---------------------------- MODULE CigaretteSmokers ----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Smokers
ASSUME Smokers = {"paper", "matches", "tobacco"}
VARIABLES offer, smoking

Init == 
  /\ offer \in SUBSET Smokers
  /\ #offer = 2
  /\ smoking \in SUBSET Smokers
  /\ #smoking = 0

Next ==
  \/ \E smoker \in Smokers \ offer : 
     (smoking' = {smoker} /\ offer' \in SUBSET Smokers /\ #offer' = 2)
  \/ \E s \in smoking :
     (smoking' = {} /\ offer' = offer)

AtMostOne ==
  #smoking <= 1

Spec ==
  Init /\ [][Next]_<<offer, smoking>>

FairSpec ==
  Spec /\ WF_next(<<offer, smoking>>)

===============================================================================