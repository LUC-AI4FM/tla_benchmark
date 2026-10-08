---------------------------- MODULE CigaretteSmokers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Ingredients, Offers

ASSUME /\ Ingredients # {}
       /\ Offers \subseteq SUBSET Ingredients
       /\ \A o \in Offers : Cardinality(o) = Cardinality(Ingredients) - 1

VARIABLES table, smoking

vars == <<table, smoking>>

Smokers == {i \in Ingredients : {i} = Ingredients \ (UNION {o \in Offers : i \notin o})} 
           \cup {i \in Ingredients : \E o \in Offers : Ingredients \ o = {i}}

SmokerForOffer(o) == CHOOSE i \in Ingredients : Ingredients \ o = {i}

TypeOK == /\ table \in Offers \cup {{}}
          /\ smoking \in Ingredients \cup {"none"}

AtMostOne == smoking = "none" \/ smoking \in Ingredients

Init == /\ table = {}
        /\ smoking = "none"

DealerPlacesOffer(o) ==
    /\ table = {}
    /\ smoking = "none"
    /\ o \in Offers
    /\ table' = o
    /\ UNCHANGED smoking

SmokerPicksUp(i) ==
    /\ table # {}
    /\ smoking = "none"
    /\ Ingredients \ table = {i}
    /\ smoking' = i
    /\ table' = {}

SmokerFinishes ==
    /\ smoking # "none"
    /\ smoking' = "none"
    /\ UNCHANGED table

Next == \/ \E o \in Offers : DealerPlacesOffer(o)
        \/ \E i \in Ingredients : SmokerPicksUp(i)
        \/ SmokerFinishes

Fairness == /\ \A o \in Offers : WF_vars(DealerPlacesOffer(o))
            /\ \A i \in Ingredients : WF_vars(SmokerPicksUp(i))
            /\ WF_vars(SmokerFinishes)

Spec == Init /\ [][Next]_vars /\ Fairness

MutualExclusion == AtMostOne

NoDeadlock == (table = {} /\ smoking = "none") => ENABLED (\E o \in Offers : DealerPlacesOffer(o))

EventuallySmokes == \A o \in Offers : (table = o) ~> (smoking # "none")

=============================================================================