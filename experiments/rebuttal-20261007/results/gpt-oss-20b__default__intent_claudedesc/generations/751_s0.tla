MODULE CigaretteSmokers

EXTENDS Naturals, TLC

CONSTANTS INGREDIENTS, OFFERS, SMOKER_INGREDIENTS

VARIABLES table, smoking

Smokers == DOMAIN SMOKER_INGREDIENTS

Init ==
  /\ table = {}
  /\ smoking = 0

DealerSelect(o) ==
  o \in OFFERS
  /\ table = {}
  /\ smoking = 0
  => table' = o

SmokerStart(i,o) ==
  i \in Smokers
  /\ SMOKER_INGREDIENTS[i] \notin o
  /\ table = o
  /\ smoking = 0
  => /\ smoking' = i
     /\ table' = {}

SmokerFinish(i) ==
  i \in Smokers
  /\ smoking = i
  => smoking' = 0

DealerAction == ∃o \in OFFERS : DealerSelect(o)
SmokerAction == ∃i \in Smokers, o \in OFFERS : SmokerStart(i,o)
FinishAction == ∃i \in Smokers : SmokerFinish(i)

Next == DealerAction \/ SmokerAction \/ FinishAction

MutualExclusion ==
  \A i,j \in Smokers :
    (i # j) => ~(smoking = i /\ smoking = j)

Spec == Init
        /\ [][Next]_<<table, smoking>>
        /\ WF(DealerAction)
        /\ WF(SmokerAction)