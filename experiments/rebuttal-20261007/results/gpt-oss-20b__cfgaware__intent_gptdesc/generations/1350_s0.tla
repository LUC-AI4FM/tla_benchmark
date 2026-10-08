------------------------------ MODULE CounterSM ------------------------------
EXTENDS Naturals

VARIABLES counter

(* --- Initialization ----------------------------------------------------- *)
Init == counter = 1

(* --- Actions ------------------------------------------------------------ *)
Increment ==
  /\ counter < 5
  /\ counter' = counter + 1

StayAtFive ==
  /\ counter = 5
  /\ counter' = 5

Next == Increment \/ StayAtFive

(* --- Specification ----------------------------------------------------- *)
Spec == Init
        /\ [][Next]_counter          (* always Next holds *)
        /\ WF_vars(Increment)        (* weak fairness of Increment *)

(* --- Liveness Property ------------------------------------------------- *)
Liveness ==
  [](counter = 1 => <> (counter = 5))

(* --- Auxiliary Invariants ---------------------------------------------- *)
Bounds == counter >= 1 /\ counter <= 5

END CounterSM