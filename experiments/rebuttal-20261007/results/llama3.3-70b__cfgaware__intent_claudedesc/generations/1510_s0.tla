---------------------------- MODULE CaseRecordUpdate ----------------------------
EXTENDS Integers

CONSTANT Values, UpdateValue
VARIABLE chosen, mapping

Init ==
  /\ chosen \in {1, 2, 3}
  /\ mapping = [i \in {1, 2, 3} |-> 0]

Next ==
  /\ chosen' = chosen
  /\ mapping' =
      CASE chosen = 2 -> [mapping EXCEPT ![2] = UpdateValue]
                    OTHER -> mapping

Spec == Init /\ [][Next]_<<chosen, mapping>>

THEOREM Spec => []Init
=============================================================================