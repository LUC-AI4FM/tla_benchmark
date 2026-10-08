------------------------------ MODULE CigSmokers ------------------------------

CONSTANTS Ingredients, Offers

(* Each smoker holds exactly one ingredient; the set of smokers equals the
   set of ingredients. *)
Smokers == Ingredients

VAR dealerOffer, smokingSet

vars == <<dealerOffer, smokingSet>>

Init ==
  /\ dealerOffer = {}
  /\ smokingSet = {}

DealerChoose(o) ==
  /\ o \in Offers
  /\ dealerOffer = {}
  /\ dealerOffer' = o
  /\ smokingSet' = {}

SmokerStart ==
  /\ dealerOffer # {}          (* an offer is on the table *)
  /\ smokingSet = {}           (* no smoker currently smoking *)
  /\ LET s == CHOOSE x \in Smokers : x \in (Ingredients \ dealerOffer) IN
       smokingSet' = {s}

SmokerFinish ==
  /\ smokingSet # {}
  /\ smokingSet' = {}

Next ==
  \/ ∃ o \in Offers : DealerChoose(o)
  \/ SmokerStart
  \/ SmokerFinish

TypeOK ==
  /\ dealerOffer \subseteq Ingredients
  /\ smokingSet \subseteq Smokers

AtMostOne ==
  /\ smokingSet = {}
  \/ ∃ s \in Smokers : smokingSet = {s}

FairnessCond ==
  [] (dealerOffer # {} => <> (smokingSet # {}))
  /\ [] (smokingSet # {} => <> (smokingSet = {}))

Spec == Init
        /\ [][Next]_vars
        /\ TypeOK
        /\ AtMostOne
        /\ FairnessCond

=============================================================================