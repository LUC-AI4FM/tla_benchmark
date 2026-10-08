MODULE SmallPlusCal
EXTENDS Naturals

VARIABLES x, pc

(* ------------------------------------------------------------------------ *)
(* Initial condition:  x is chosen from the range 1..10 and execution starts. *)
Init ==
  /\ x \in 1..10
  /\ pc = "Start"

(* ------------------------------------------------------------------------ *)
(* The single labeled step checks that x^2 <= 100 (which holds for all 
   allowed values of x) and then moves to the terminal state. *)
Step ==
  /\ pc = "Start"
  /\ LET y == x ^ 2 IN y <= 100
  /\ UNCHANGED <<x>>
  /\ pc' = "Done"

(* ------------------------------------------------------------------------ *)
(* After termination, allow infinite stuttering steps that leave all 
   variables unchanged. *)
Stutter ==
  /\ pc = "Done"
  /\ UNCHANGED <<x,pc>>

Next == Step \/ Stutter

(* ------------------------------------------------------------------------ *)
(* The complete specification: initial condition, boxed next-state relation,
   and a liveness property asserting eventual termination. *)
Spec == Init /\ [][Next]_<<x,pc>> /\ <> (pc = "Done")
=============================================================================