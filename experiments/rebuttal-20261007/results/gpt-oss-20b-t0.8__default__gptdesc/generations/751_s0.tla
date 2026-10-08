```
----------------------------- MODULE CigaretteSmokers -----------------------------
EXTENDS Naturals, TLC

CONSTANTS Ingredients, Smokers, Owned

VARIABLES offer, smoking

(* -------------------------------------------------------------------------- *)
(* Types and invariants *)

TypeInvariant ==
    /\ offer \subseteq Ingredients
    /\ smoking \in [Smokers -> BOOLEAN]

Init ==
    /\ offer = {}
    /\ smoking = [s \in Smokers |-> FALSE]
    /\ TypeInvariant

AtMostOne == Len({ s \in Smokers : smoking[s] }) <= 1

(* -------------------------------------------------------------------------- *)
(* Actions *)

DealerAction ==
    /\ Len(offer) = 0
    /\ UNCHANGED <<smoking>>
    /\ ∃ i \in Ingredients :
           offer' = Ingredients \ {i}
        /\ UNCHANGED <<smoking>>

SmokerStart(s) ==
    /\ Len(offer) = 2
    /\ offer = Ingredients \ {Owned[s]}
    /\ smoking[s] = FALSE
    /\ smoking' = [smoking EXCEPT ![s] = TRUE]
    /\ offer' = {}
    /\ UNCHANGED <<>>

SmokerFinish(s) ==
    /\ Len(offer) = 0
    /\ smoking[s] = TRUE
    /\ smoking' = [smoking EXCEPT ![s] = FALSE]
    /\ UNCHANGED <<offer>>

Next ==
    \/ ∃ s \in Smokers : SmokerStart(s)
    \/ ∃ s \in Smokers : SmokerFinish(s)
    \/ DealerAction

(* -------------------------------------------------------------------------- *)
(* Specification *)

Spec == Init /\ [] (Next)

Safety == AtMostOne

FairSpec == Init /\ [] (Next) /\ WF_Next
```