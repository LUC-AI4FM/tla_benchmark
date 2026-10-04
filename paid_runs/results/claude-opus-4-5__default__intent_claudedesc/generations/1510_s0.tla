---------------------------- MODULE CaseOtherRecordUpdate ----------------------------

EXTENDS Integers

CONSTANTS Values, SpecialValue, UpdateKey, UpdateValue

ASSUME ValuesAssumption == Values \subseteq Int /\ Values # {}
ASSUME SpecialValueAssumption == SpecialValue \in Values
ASSUME UpdateKeyAssumption == UpdateKey \in Values
ASSUME UpdateValueAssumption == UpdateValue \in Int

VARIABLES chosen, mapping

vars == <<chosen, mapping>>

TypeOK ==
    /\ chosen \in Values
    /\ mapping \in [Values -> Int]

Init ==
    /\ chosen = 0
    /\ mapping = [v \in Values |-> 0]

Next ==
    /\ chosen' = chosen
    /\ mapping' = CASE chosen = SpecialValue -> [mapping EXCEPT ![UpdateKey] = UpdateValue]
                  [] OTHER -> mapping

Spec == Init /\ [][Next]_vars

===================================================================================