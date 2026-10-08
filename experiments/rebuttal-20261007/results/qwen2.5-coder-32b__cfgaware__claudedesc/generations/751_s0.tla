------------------------------- MODULE CigaretteSmokersProblem -------------------------------

CONSTANTS Ingredients, Offers

VARIABLES smokers, dealer

(* --algorithm cigarette_smokers_problem

variables 
    smokers = [i \in Ingredients | -> [smoking: FALSE]],
    dealer  = CHOOSE offer \in Offers;

fair process (ALL) \in Ingredients
begin
    while TRUE do
        await \E offer \in Offers : offer = dealer /\ i \notin dealer;
        smokers[i].smoking := TRUE;
        dealer := {};
    end while;
end process ************************************************

fair process (ONE) \in 1..3
begin
    while TRUE do
        await dealer = {};
        with s \in Ingredients do
            if smokers[s].smoking then
                smokers[s].smoking := FALSE;
                dealer := CHOOSE offer \in Offers : i \notin offer;
            end if;
        end with;
    end while;
end process ************************************************

end algorithm *)

TypeOK == /\ smokers \in [Ingredients -> [smoking: BOOLEAN]]
          /\ dealer \in Offers \/ dealer = {}

AtMostOne == \A s1, s2 \in Ingredients : s1 # s2 => ~smokers[s1].smoking \/ ~smokers[s2].smoking

Init == /\ TypeOK
        /\ \E offer \in Offers : dealer = offer
        /\ \A i \in Ingredients : smokers[i].smoking = FALSE

startSmoking ==
    \E offer \in Offers, i \in Ingredients :
        offer = dealer /\ i \notin dealer /\
        \/ /\ smokers[i].smoking' = TRUE
           /\ dealer' = {}

stopSmoking ==
    dealer = {} /\
    \E s \in Ingredients :
        smokers[s].smoking /\
        \/ /\ smokers[s].smoking' = FALSE
           /\ dealer' \in Offers

Next == startSmoking \/ stopSmoking

Spec == Init /\ [][Next]_<<smokers, dealer>>

FairSpec == Spec /\ WF_next(<<smokers, dealer>>)

=============================================================================