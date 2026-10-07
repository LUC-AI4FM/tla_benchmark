----------------------------- MODULE CigaretteSmokers -----------------------------

EXTENDS Naturals, FiniteSets

CONSTANTS
  INGREDIENTS, \* e.g., {"Tobacco", "Paper", "Matches"}
  NoOffer

(*
  Structural assumptions:
  - Classic problem has exactly three ingredients.
  - NoOffer is not a set of ingredients (so it cannot be confused with any offer).
*)
ASSUME Cardinality(INGREDIENTS) = 3
ASSUME NoOffer \notin SUBSET INGREDIENTS

VARIABLES
  dealerOffer, \* either NoOffer or a subset of INGREDIENTS missing exactly one ingredient
  Smoking      \* a map from INGREDIENTS to booleans indicating who is smoking

vars == << dealerOffer, Smoking >>

OFFERS ==
  { S \in SUBSET INGREDIENTS : Cardinality(S) = Cardinality(INGREDIENTS) - 1 }

Missing(S) == INGREDIENTS \ S

TypeInv ==
  /\ Smoking \in [INGREDIENTS -> BOOLEAN]
  /\ dealerOffer \in OFFERS \cup {NoOffer}

AtMostOne ==
  Cardinality({ i \in INGREDIENTS : Smoking[i] }) <= 1

Init ==
  /\ dealerOffer = NoOffer
  /\ Smoking \in [INGREDIENTS -> BOOLEAN]
  /\ \A i \in INGREDIENTS : ~Smoking[i]

DealerOfferAct ==
  /\ dealerOffer = NoOffer
  /\ \E S \in OFFERS :
        /\ dealerOffer' = S
        /\ UNCHANGED Smoking

StartSmokingAct ==
  /\ dealerOffer \in OFFERS
  /\ \A i \in INGREDIENTS : ~Smoking[i]
  /\ LET m == CHOOSE x \in INGREDIENTS : x \in Missing(dealerOffer)
     IN
        /\ Smoking' = [ i \in INGREDIENTS |-> IF i = m THEN TRUE ELSE FALSE ]
        /\ UNCHANGED dealerOffer

FinishSmokingAct ==
  /\ \E m \in INGREDIENTS : Smoking[m]
  /\ Smoking' = [ i \in INGREDIENTS |-> FALSE ]
  /\ dealerOffer' = NoOffer

Next ==
  DealerOfferAct \/ StartSmokingAct \/ FinishSmokingAct

Spec ==
  Init /\ [][Next]_vars

FairSpec ==
  Spec /\ WF_vars(Next)

================================================================================