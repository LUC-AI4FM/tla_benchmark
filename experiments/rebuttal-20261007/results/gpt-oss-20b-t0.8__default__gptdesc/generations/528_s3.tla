MODULE SmallPlusCal
EXTENDS Naturals, Sequences, TLC

VARIABLES x, y, pc

(* Initial state *)
Init ==
  /\ x = {"a", "b"}
  /\ y = <<1, 2, 3>>
  /\ pc = "Init"

(* One atomic step that updates the data and moves to Done. *)
AddStep ==
  /\ pc = "Init"
  /\ x' = x \cup {"c"}                (* add "c" to the set *)
  /\ y' = <<y[1], 4, y[3]>>            (* update second element of the tuple *)
  /\ pc' = "Done"

(* After completion we allow a stuttering action so that the system
   does not deadlock. *)
Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED <<x, y, pc>>

Next == AddStep \/ Terminating

Spec == Init /\ [][Next]_<<x, y, pc>>

(* Liveness property: eventually we reach Done *)
TerminationProp == <> (pc = "Done")