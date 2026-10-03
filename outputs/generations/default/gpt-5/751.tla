----------------------------- MODULE CigaretteSmokers -----------------------------

EXTENDS TLC

CONSTANTS
  SMOKERS, \* nonempty set of smokers
  INGS,    \* nonempty set of ingredients
  Own,     \* function mapping each smoker to the single ingredient they own
  Null     \* special value meaning "no current offer"

(*
  Structural assumptions:
  - Each smoker owns exactly one ingredient.
  - Ownership is a bijection between SMOKERS and INGS.
*)
ASSUME
  /\ SMOKERS # {}
  /\ INGS # {}
  /\ Own \in [SMOKERS -> INGS]
  /\ \A s \in SMOKERS: \A t \in SMOKERS: s # t => Own[s] # Own[t]
  /\ \A i \in INGS: \E s \in SMOKERS: Own[s] = i

(*
  The set of structurally valid offers: an offer is "all ingredients except one".
*)
Offers == { INGS \ {i} : i \in INGS }

ASSUME Null \notin Offers

VARIABLES
  Offer,    \* current offer on the table; either Null or one of Offers
  Smoking   \* function [SMOKERS -> BOOLEAN]: whether each smoker is currently smoking

vars == << Offer, Smoking >>

Init ==
  /\ Offer = Null
  /\ Smoking = [ s \in SMOKERS |-> FALSE ]

NoOneSmoking ==
  ~(\E s \in SMOKERS: Smoking[s])

Deal ==
  /\ Offer = Null
  /\ NoOneSmoking
  /\ \E i \in INGS: Offer' = INGS \ {i}
  /\ UNCHANGED Smoking

StartSmoke(s) ==
  /\ s \in SMOKERS
  /\ Offer \in Offers
  /\ NoOneSmoking
  /\ ~Smoking[s]
  /\ Own[s] \notin Offer
  /\ Smoking' = [Smoking EXCEPT ![s] = TRUE]
  /\ Offer' = Null

StopSmoke(s) ==
  /\ s \in SMOKERS
  /\ Smoking[s]
  /\ Smoking' = [Smoking EXCEPT ![s] = FALSE]
  /\ UNCHANGED Offer

Next ==
  Deal
  \/ (\E s \in SMOKERS: StartSmoke(s))
  \/ (\E s \in SMOKERS: StopSmoke(s))

Spec ==
  Init /\ [][Next]_vars

FairSpec ==
  Spec /\ WF_vars(Next)

(*
  Safety invariant: at most one smoker is smoking at any time.
*)
AtMostOne ==
  \A s \in SMOKERS:
    \A t \in SMOKERS:
      s = t \/ ~(Smoking[s] /\ Smoking[t])

================================================================================