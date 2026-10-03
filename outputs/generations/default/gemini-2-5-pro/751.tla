---- MODULE CigaretteSmokers ----
EXTENDS TLC, FiniteSets

CONSTANT INGREDIENTS

VARIABLES
    \* offer: The set of ingredients currently on the table.
    \*        An empty set means the table is clear.
    offer,

    \* smoking: The set of smokers currently smoking.
    \*          A smoker is identified by the ingredient they possess.
    smoking

vars == <<offer, smoking>>

\* The set of all possible offers the dealer can make. An offer is the set
\* of all ingredients minus one.
POSSIBLE_OFFERS == {INGREDIENTS \ {i} : i \in INGREDIENTS}

\* Type invariant for the state variables.
TypeOK ==
    /\ offer \in POSSIBLE_OFFERS \union {{}}
    /\ smoking \in SUBSET INGREDIENTS

\* The initial state: the table is empty and no one is smoking.
Init ==
    /\ offer = {}
    /\ smoking = {}

\* The dealer places ingredients on the table.
\* This can only happen when the table is empty and no one is smoking.
DealerOffer ==
    /\ smoking = {}
    /\ offer = {}
    /\ \E o \in POSSIBLE_OFFERS:
         offer' = o
    /\ UNCHANGED smoking

\* A smoker with ingredient s takes the other ingredients and starts to smoke.
\* This can happen if the offer on the table is exactly what they need
\* (i.e., all ingredients except the one they already have).
SmokerSmoke(s) ==
    /\ offer = INGREDIENTS \ {s}
    /\ offer' = {}
    /\ smoking' = {s}

\* A smoker s finishes smoking.
SmokerFinish(s) ==
    /\ smoking = {s}
    /\ smoking' = {}
    /\ UNCHANGED offer

\* The next-state relation is the disjunction of all possible actions.
Next ==
    \/ DealerOffer
    \/ \E s \in INGREDIENTS: SmokerSmoke(s)
    \/ \E s \in INGREDIENTS: SmokerFinish(s)

\* The main temporal specification, asserting safety.
Spec == Init /\ [][Next]_vars

\* A specification including weak fairness on the entire system step.
\* This ensures that if some action is continuously possible, an action
\* (not necessarily the same one) will eventually be taken.
FairSpec == Spec /\ WF_vars(Next)

\* Safety Invariant: At most one smoker can be smoking at any given time.
AtMostOne == Cardinality(smoking) <= 1

=============================================================================