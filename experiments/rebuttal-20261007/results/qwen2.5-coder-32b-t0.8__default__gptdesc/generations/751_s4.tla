------------------------------ MODULE CigaretteSmokers ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Smokers
ASSUME Smokers = {"paper", "tobacco", "matches"}

VARIABLES dealerOffer, smokingFlags

Init == /\ dealerOffer \in {{"paper", "tobacco"}, {"paper", "matches"}, {"tobacco", "matches"}}
        /\ smokingFlags = <<FALSE, FALSE, FALSE>>

Next ==
    \/ \/ /\ dealerOffer = {"paper", "tobacco"}
           /\ smokingFlags[3] = TRUE
           /\ \E nextOffer \in {{"paper", "tobacco"}, {"paper", "matches"}, {"tobacco", "matches"}} :
                /\ dealerOffer' = nextOffer
                /\ smokingFlags' = <<FALSE, FALSE, FALSE>>
       \/ /\ dealerOffer = {"paper", "matches"}
           /\ smokingFlags[2] = TRUE
           /\ \E nextOffer \in {{"paper", "tobacco"}, {"paper", "matches"}, {"tobacco", "matches"}} :
                /\ dealerOffer' = nextOffer
                /\ smokingFlags' = <<FALSE, FALSE, FALSE>>
       \/ /\ dealerOffer = {"tobacco", "matches"}
           /\ smokingFlags[1] = TRUE
           /\ \E nextOffer \in {{"paper", "tobacco"}, {"paper", "matches"}, {"tobacco", "matches"}} :
                /\ dealerOffer' = nextOffer
                /\ smokingFlags' = <<FALSE, FALSE, FALSE>>
    \/ /\ dealerOffer \in {{"paper", "tobacco"}, {"paper", "matches"}, {"tobacco", "matches"}}
       /\ \A i \in 1..3 : smokingFlags[i] = FALSE

Spec == Init /\ [][Next]_<<dealerOffer, smokingFlags>>

AtMostOne ==
    \/ \A i \in 1..3 : ~smokingFlags[i]
    \/ \E i \in 1..3 : /\ smokingFlags[i]
                           /\ \A j \in 1..3 \ {i} : ~smokingFlags[j]

FairSpec == Spec /\ WF_vars(Next)

=============================================================================