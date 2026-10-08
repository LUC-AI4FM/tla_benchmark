```
MODULE Smokers
EXTENDS Integers

CONSTANTS Ingredients, Smokers
VARIABLES smoking, offer

Init == (* Initial condition *)
        /\ smoking = <<>>  (* No smokers are smoking initially *)
        /\ offer = {}      (* The dealer makes no offer initially *)

Next == (* Next state relation *)
        \/ \E s \in Smokers :
            /\ smoking' = [smoking EXCEPT ![s] = TRUE]
            /\ offer' = (offer \cup {IngredientsOf(s)})
        \/ \E i \in Ingredients :
            /\ offer' = {i}
            /\ smoking' = smoking
        \/ (* The system returns to a state where the dealer may offer again *)
            /\ smoking' = <<>>
            /\ offer' = {}

Spec == Init /\ [][Next]_<<smoking, offer>>

AtMostOne == (* No more than one smoker is smoking at any time *)
             \A s1, s2 \in Smokers : 
                 ~(smoking[s1] /\ smoking[s2])

FairSpec == Spec /\ WF_vars(Next)

THEOREM Spec => []AtMostOne
THEOREM FairSpec => <><>~([](~AtMostOne))

IngredientsOf(s) == (* Returns the ingredient of a smoker *)
                    CASE s = 1 -> "match"
                      [] s = 2 -> "tobacco"
                      [] s = 3 -> "paper"

==================
```