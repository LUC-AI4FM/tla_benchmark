-------------------------------- MODULE Consensus --------------------------------
(******************************************************************************)
(* A formal TLA+ model of the core consensus decision problem for a           *)
(* distributed system of processes that must agree on a single value.         *)
(******************************************************************************)

EXTENDS Naturals

CONSTANTS
    Values      \* The set of possible values that can be proposed and chosen

VARIABLES
    proposed,   \* The set of values that have been proposed
    chosen      \* The chosen value (or a special "none" value if nothing chosen yet)

vars == <<proposed, chosen>>

(******************************************************************************)
(* Type definitions and constants                                             *)
(******************************************************************************)

None == CHOOSE v : v \notin Values  \* A distinguished value representing "no choice yet"

TypeOK ==
    /\ proposed \subseteq Values
    /\ chosen \in Values \cup {None}

(******************************************************************************)
(* Initial State                                                              *)
(******************************************************************************)

Init ==
    /\ proposed = {}       \* No values have been proposed initially
    /\ chosen = None       \* No value has been chosen initially

(******************************************************************************)
(* Actions                                                                    *)
(******************************************************************************)

(* A process proposes a value v from the allowed set of Values *)
Propose(v) ==
    /\ v \in Values
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED chosen

(* A value v is chosen (learned) - can only happen if v was proposed *)
(* and no value has been chosen yet *)
Choose(v) ==
    /\ v \in proposed      \* Can only choose a proposed value
    /\ chosen = None       \* Can only choose if nothing chosen yet
    /\ chosen' = v
    /\ UNCHANGED proposed

(* Combined propose action for any value *)
ProposeAny == \E v \in Values : Propose(v)

(* Combined choose action for any proposed value *)
ChooseAny == \E v \in Values : Choose(v)

(******************************************************************************)
(* Next-State Relation                                                        *)
(******************************************************************************)

Next ==
    \/ ProposeAny          \* Either propose some value
    \/ ChooseAny           \* Or choose some proposed value

(******************************************************************************)
(* Safety Invariants                                                          *)
(******************************************************************************)

(* Validity: Any chosen value must come from the allowed set of Values *)
Validity ==
    chosen /= None => chosen \in Values

(* Agreement: At most one distinct value can be chosen *)
(* This is implicit in our model since 'chosen' is a single value, *)
(* but we state it explicitly for clarity *)
Agreement ==
    \A v1, v2 \in Values \cup {None} :
        (chosen = v1 /\ chosen = v2) => v1 = v2

(* Integrity: A chosen value must have been proposed *)
(* Once chosen, it cannot change to a different value *)
Integrity ==
    chosen /= None => chosen \in proposed

(* Combined safety invariant *)
SafetyInvariant ==
    /\ TypeOK
    /\ Validity
    /\ Agreement
    /\ Integrity

(******************************************************************************)
(* Temporal Safety Property: Once chosen, the value never changes            *)
(******************************************************************************)

ChosenStable ==
    \A v \in Values : (chosen = v) => [](chosen = v)

(******************************************************************************)
(* Liveness Properties (under fairness assumptions)                          *)
(******************************************************************************)

(* Eventual Choice: If a value is proposed, eventually some value is chosen *)
(* This requires weak fairness on the Choose action *)
EventualChoice ==
    (\E v \in Values : v \in proposed) ~> (chosen /= None)

(* Alternative: Eventually a value is chosen (assuming proposals occur) *)
EventuallyChosen ==
    <>(chosen /= None)

(* Nontriviality: If nothing is proposed, choosing nothing is permitted *)
(* This is captured by allowing runs where proposed = {} and chosen = None forever *)
Nontriviality ==
    (proposed = {}) => (chosen = None)

(******************************************************************************)
(* Fairness Conditions                                                       *)
(******************************************************************************)

(* Weak fairness on Choose: if choosing remains enabled, it eventually happens *)
FairChoice == WF_vars(ChooseAny)

(* Weak fairness on Propose: proposals that remain enabled eventually happen *)
FairPropose == WF_vars(ProposeAny)

(* Combined fairness *)
Fairness == FairChoice /\ FairPropose

(******************************************************************************)
(* Specification                                                              *)
(******************************************************************************)

(* Basic specification without fairness *)
Spec == Init /\ [][Next]_vars

(* Specification with fairness for liveness checking *)
FairSpec == Spec /\ Fairness

(* Specification with only fair choice (for checking EventualChoice) *)
SpecWithFairChoice == Spec /\ FairChoice

(******************************************************************************)
(* Theorems / Properties to Check                                            *)
(******************************************************************************)

(* Safety properties to verify with Spec *)
THEOREM Spec => []SafetyInvariant

(* Stability property *)
THEOREM Spec => ChosenStable

(* Liveness under fairness *)
THEOREM FairSpec => EventualChoice

================================================================================