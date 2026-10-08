----------------------------- MODULE DieHard -----------------------------
EXTENDS Naturals, TLC

(*
  Classic Die Hard water jug puzzle:
  - Two jugs with capacities 3 and 5 gallons.
  - Allowed operations:
      Fill either jug from the fountain to capacity,
      Empty either jug to the ground,
      Pour from one jug to the other until source empty or destination full.
  - Both jugs start empty.
  - We instrument Drawn to track total gallons drawn from the fountain.
  - Type invariant ensures jug contents remain within capacities and Drawn ∈ Nat.

  TLC usage hints (typical model setup):
    - VARIABLES: Small, Big, Drawn
    - Init:      Init
    - Next:      Next
    - Spec:      Spec
    - Invariants: TypeInv
    - Property (liveness): Reach4
    - View:      View   (so TLC’s state space shape matches the classic 16 states)
    - You may evaluate BigIsFour, BothChange as state/action predicates.
*)

(***************************************************************)
(* Parameters (fixed to 3 and 5 for the classic puzzle)        *)
(***************************************************************)
CapSmall == 3
CapBig   == 5
C3 == CapSmall
C5 == CapBig

(***************************************************************)
(* State variables                                             *)
(***************************************************************)
VARIABLES Small, Big, Drawn

(* Aliases (provide commonly expected names) *)
small == Small
big == Big
drawn == Drawn

Vars == <<Small, Big, Drawn>>

(***************************************************************)
(* Initial state                                               *)
(***************************************************************)
Init ==
  /\ Small = 0
  /\ Big   = 0
  /\ Drawn = 0

(***************************************************************)
(* Primitive operations                                        *)
(***************************************************************)
FillSmall ==
  /\ Small < CapSmall
  /\ Small' = CapSmall
  /\ Big'   = Big
  /\ Drawn' = Drawn + (CapSmall - Small)

FillBig ==
  /\ Big < CapBig
  /\ Big'   = CapBig
  /\ Small' = Small
  /\ Drawn' = Drawn + (CapBig - Big)

EmptySmall ==
  /\ Small > 0
  /\ Small' = 0
  /\ Big'   = Big
  /\ Drawn' = Drawn

EmptyBig ==
  /\ Big > 0
  /\ Big'   = 0
  /\ Small' = Small
  /\ Drawn' = Drawn

PourSmallToBig ==
  /\ Small > 0
  /\ Big   < CapBig
  /\ LET space == CapBig - Big
         delta == IF Small <= space THEN Small ELSE space
     IN /\ Small' = Small - delta
        /\ Big'   = Big + delta
        /\ Drawn' = Drawn

PourBigToSmall ==
  /\ Big   > 0
  /\ Small < CapSmall
  /\ LET space == CapSmall - Small
         delta == IF Big <= space THEN Big ELSE space
     IN /\ Big'   = Big - delta
        /\ Small' = Small + delta
        /\ Drawn' = Drawn

(***************************************************************)
(* Next-state relation and temporal specification              *)
(***************************************************************)
Next ==
    FillSmall
  \/ FillBig
  \/ EmptySmall
  \/ EmptyBig
  \/ PourSmallToBig
  \/ PourBigToSmall

Spec == Init /\ [][Next]_Vars

(***************************************************************)
(* Invariants and properties                                   *)
(***************************************************************)
TypeInv ==
  /\ Small \in 0..CapSmall
  /\ Big   \in 0..CapBig
  /\ Drawn \in Nat

BigIsFour == (Big = 4)
Big4 == BigIsFour

Reach4 == <>BigIsFour

(* Action predicate: transitions where both jugs change simultaneously *)
BothChange ==
  /\ Small' /= Small
  /\ Big'   /= Big

(***************************************************************)
(* TLC view (ignore Drawn so classic state space is preserved) *)
(***************************************************************)
View == <<Small, Big>>

(***************************************************************)
(* Optional theorem (not required by TLC)                      *)
(***************************************************************)
THEOREM Spec => []TypeInv

=============================================================================