-------------------------- MODULE CigaretteSmokers --------------------------
EXTENDS TLC, FiniteSets

CONSTANTS Ingredients, Smokers, Has

ASSUME /\ Ingredients = {"tobacco", "paper", "matches"}
       /\ Smokers = {"SmokerT", "SmokerP", "SmokerM"}
       /\ Has = [s \in Smokers |->
                    CASE s = "SmokerT" -> "tobacco"
                    [] s = "SmokerP" -> "paper"
                    [] s = "SmokerM" -> "matches"]

VARIABLES offer, smoking

vars == <<offer, smoking>>

\* The set of possible offers the dealer can make (any two ingredients).
Offers == {o \subseteq Ingredients : Cardinality(o) = 2}

TypeOK == /\ offer \in SUBSET Ingredients
          /\ smoking \in [Smokers -> BOOLEAN]

Init == /\ offer = {}
        /\ smoking = [s \in Smokers |-> FALSE]

\* The dealer puts two ingredients on the table.
\* This can only happen when the table is empty and no one is smoking.
DealerOffer == /\ \A s \in Smokers : ~smoking[s]
               /\ offer = {}
               /\ \E o \in Offers : offer' = o
               /\ UNCHANGED smoking

\* Smoker s, who has the missing ingredient, takes the offered ingredients
\* and starts smoking. The table becomes empty.
SmokerSmoke(s) == /\ offer = Ingredients \ {Has[s]}
                  /\ smoking' = [smoking EXCEPT ![s] = TRUE]
                  /\ offer' = {}

\* Smoker s finishes smoking.
SmokerFinish(s) == /\ smoking[s]
                   /\ smoking' = [smoking EXCEPT ![s] = FALSE]
                   /\ UNCHANGED offer

Next == \/ DealerOffer
        \/ \E s \in Smokers : SmokerSmoke(s)
        \/ \E s \in Smokers : SmokerFinish(s)

\* The main specification, including weak fairness on the Next action.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Invariant: At most one smoker is smoking at any time.
AtMostOne == Cardinality({s \in Smokers : smoking[s]}) <= 1

=============================================================================