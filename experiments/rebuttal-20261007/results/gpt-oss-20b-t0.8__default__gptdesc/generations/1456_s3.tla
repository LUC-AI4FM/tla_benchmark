MODULE TinyStateMachine
EXTENDS Naturals, TLC

VARIABLES x, y

(* --- Initial State Constraints --- *)
Init ==
  /\ x \in SUBSET {1, 2, 3}
  /\ y \in SUBSET {1, 2, 3}

(* --- Next-State Relation --- *)
Next ==
  /\ y' = y
  /\ x' \subseteq y

(* --- Predicates --- *)
FullSet == (x = {1, 2, 3})

GainThree ==
  /\ 3 \in x'
  /\ 3 \notin x

(* --- TLC Metadata Inspection --- *)
FullSetCount  == TLC.Get("FullSet")
GainThreeCount == TLC.Get("GainThree")

(* --- Specification --- *)
Spec == Init /\ [][Next]_ <<x, y>>

END MODULE