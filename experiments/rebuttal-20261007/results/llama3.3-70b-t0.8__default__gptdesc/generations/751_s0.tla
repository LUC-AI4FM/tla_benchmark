```
MODULE CigaretteSmokers
EXTENDS Integers, FiniteSets

CONSTANTS SmokerSet, OfferSet
VARIABLES smoking, offer

Init == (* Initial condition: no smokers are smoking and no offer is made *)
        /\ smoking = [s \in SmokerSet |-> FALSE]
        /\ offer \in OfferSet

Next == (* Next state relation: a smoker with the missing ingredient can smoke *)
        \/ (\E s \in SmokerSet :
              (* The dealer offers ingredients without one type, and *)
              /\ offer = [t \in {1, 2, 3} |-> (t # s)]
              (* the corresponding smoker smokes and then stops smoking *)
              /\ smoking' = [smoking EXCEPT ![s] = ~smoking[s]]
              (* The dealer's next offer is arbitrary. *)
              /\ offer' \in OfferSet)
        \/ (\E o \in OfferSet :
              (* Alternatively, the dealer makes a new offer without changing *)
              (* the smokers' smoking status: *)
              /\ smoking' = smoking
              /\ offer' = o)

AtMostOne == (* Invariant: no more than one smoker is smoking at any time *)
             \A s1, s2 \in SmokerSet :
               (smoking[s1] /\ smoking[s2]) => s1 = s2

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(Next)

THEOREM Spec => []AtMostOne
```
Note that `#` is used to denote "except" in the specification, and `[s \in SmokerSet |-> FALSE]` denotes a function mapping each smoker to `FALSE`, indicating no one is smoking initially. Also note that the `OfferSet` should satisfy structural constraints such that it only contains sets of ingredients missing exactly one type, but these constraints are not explicitly defined in this TLA+ specification as they were not provided in the problem description.