------------------------------ MODULE SmallPlusCal ------------------------------
EXTENDS Naturals

VARIABLES x, pc

(* Initial condition: x is chosen from 1..10 and pc starts at "Start". *)
Init == /\ x \in 1..10
          /\ pc = "Start"

(* Next-state relation:
   • From the start state we check that x^2 <= 100 and then move to Done,
     leaving x unchanged.
   • After reaching Done, the system stutters forever. *)
Next ==
    \/ ((pc = "Start") /\ (x^2 <= 100) /\ (pc' = "Done") /\ (x'=x))
    \/ ((pc = "Done")   /\ (pc' = pc)          /\ (x'=x))

(* Termination property: eventually we reach the Done state. *)
Termination == <> (pc = "Done")

Spec == Init /\ [][Next]_(<<x, pc>>) /\ Termination

===============================================================================