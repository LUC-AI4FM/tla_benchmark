---- MODULE CigaretteSmokers ----

VARIABLES smoking, offer

Ing == {"tobacco", "paper", "matches"}

Missing(i) == Ing \ {i}
NoOffer == offer = {}
NoOneSmoking == \A i \in Ing: ~smoking[i]
ValidOffer == NoOffer \/ (\E i \in Ing: offer = Missing(i))

Init ==
  /\ smoking = [i \in Ing |-> FALSE]
  /\ offer = {}

DealerOffers(i) ==
  /\ i \in Ing
  /\ NoOneSmoking
  /\ NoOffer
  /\ offer' = Missing(i)
  /\ UNCHANGED smoking

SmokerStarts(i) ==
  /\ i \in Ing
  /\ NoOneSmoking
  /\ offer = Missing(i)
  /\ smoking' = [smoking EXCEPT ![i] = TRUE]
  /\ offer' = {}

SmokerStops(i) ==
  /\ i \in Ing
  /\ smoking[i] = TRUE
  /\ smoking' = [smoking EXCEPT ![i] = FALSE]
  /\ UNCHANGED offer

Next ==
  \E i \in Ing:
      DealerOffers(i)
    \/ SmokerStarts(i)
    \/ SmokerStops(i)

vars == << smoking, offer >>

TypeOK ==
  /\ smoking \in [Ing -> {TRUE, FALSE}]
  /\ offer \subseteq Ing
  /\ ValidOffer

AtMostOne ==
  \A i, j \in Ing: i # j => ~(smoking[i] /\ smoking[j])

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

====