------------------------------- MODULE CigaretteSmokers -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

(* --algorithm cigarette_smokers
variables 
    smokers = [i \in Ingredients |-> [smoking: FALSE]],
    dealer \in Offers;

fair process (ALL) \in Ingredients
vars
    missing;
begin
    while TRUE do
        await \E i \in Ingredients : smokers[i].smoking = FALSE /\ dealer = {j \in Ingredients \ {i}};
        missing := CHOOSE i \in Ingredients : smokers[i].smoking = FALSE /\ dealer = {j \in Ingredients \ {i}};
        smokers[missing] := [smoking |-> TRUE];
        dealer := {};
    od;
end process;

fair process (ALL) \in Offers
begin
    while TRUE do
        await dealer = {};
        \* Choose a new offer to place on the table
        dealer := CHOOSE o \in Offers : TRUE;
        \* Find the smoker who can now smoke and mark them as done
        missing := CHOOSE i \in Ingredients : smokers[i].smoking = TRUE /\ dealer = {j \in Ingredients \ {i}};
        smokers[missing] := [smoking |-> FALSE];
    od;
end process;

end algorithm *)

Init == 
    /\ dealer \in Offers
    /\ \A i \in Ingredients : smokers[i].smoking = FALSE

Next ==
    \/ \E i \in Ingredients :
        /\ dealer = {j \in Ingredients \ {i}}
        /\ smokers[i].smoking = FALSE
        /\ /\* startSmoking action *\/
            /\ dealer' = {}
            /\ smokers' = [smokers EXCEPT ![i].smoking = TRUE]
    \/ dealer = {}
       /\ \E i \in Ingredients :
           /\ smokers[i].smoking = TRUE
           /\ /\* stopSmoking action *\/
               /\ dealer' \in Offers
               /\ smokers' = [smokers EXCEPT ![i].smoking = FALSE]

Spec == Init /\ [][Next]_<<smokers, dealer>>

FairSpec == Spec /\ WF_next(<<smokers, dealer>>)

TypeOK ==
    /\ dealer \in Offers \/ dealer = {}
    /\ \A i \in Ingredients : smokers[i] \in [smoking: BOOLEAN]

AtMostOne ==
    \A i, j \in Ingredients :
        i # j => ~ (smokers[i].smoking /\ smokers[j].smoking)

=============================================================================