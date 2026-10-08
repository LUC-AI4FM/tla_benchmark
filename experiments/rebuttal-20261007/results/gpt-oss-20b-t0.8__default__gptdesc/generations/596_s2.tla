MODULE OneVar
EXTENDS Integers

VARIABLE x

(* ---------------------------------------------------------------------- *)
(*  Initial condition                                                     *)
Init == x = 0

(* ---------------------------------------------------------------------- *)
(*  Next-state relation                                                  *)
Next ==
    IF x = 0 THEN
        x' ∈ {1, 2}
    ELSE
        x' = 0

(* ---------------------------------------------------------------------- *)
(*  Specification                                                        *)
Spec == Init /\ [][Next]_x /\ WF_x(Next)

(* ---------------------------------------------------------------------- *)
(*  Safety invariant: state stays within allowed values                  *)
Inv == [] (x ∈ {0, 1, 2})

(* ---------------------------------------------------------------------- *)
(*  Liveness properties                                                  *)
P_awayFrom12    == <> ([] (x = 0))          (* eventually always zero     *)
P_infReturnZero == []<> (x = 0)             (* infinitely often zero      *)
P_negInfReturnZero == ¬ P_infReturnZero   (* negation of the above       *)

(* ---------------------------------------------------------------------- *)
(*  Types for postcondition example                                      *)
RecordType   == [a : Int, b : Bool]
TupleExample == <<1, 2>>
SetExample   == {1, 2}

PostCEX == [] (x ∈ SetExample)

END