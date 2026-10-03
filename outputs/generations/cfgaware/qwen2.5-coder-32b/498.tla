------------------------------- MODULE MultiSlotConsensus -------------------------------

CONSTANTS NumSlots

VARIABLES proposedValues, chosenValues

(*--algorithm MultiSlotConsensus
variables proposedValues = {}, chosenValues = [i \in 1..NumSlots |-> {}];

begin
    while TRUE do
        with v \in Nat \ {proposedValues} do
            Propose:
                proposedValues := proposedValues \cup {v}
        endwith;

        with i \in 1..NumSlots, v \in proposedValues \choose chosenValues[i] do
            Choose:
                if chosenValues[i] = {} then
                    chosenValues[i] := {v}
                end if;
        endwith;
    end while;
end algorithm *)

\* Generated TLA+ translation of the PlusCal algorithm MultiSlotConsensus

Spec == /\ proposedValues \in SUBSET Nat
        /\ chosenValues \in [1..NumSlots -> SUBSET Nat]
        /\ Init
        /\ SF_

Init == /\ proposedValues = {}
        /\ \A i \in 1..NumSlots : chosenValues[i] = {}

Next ==
    \/ \E v \in Nat \ {proposedValues} :
        /\ proposedValues' = proposedValues \cup {v}
        /\ chosenValues' = chosenValues
    \/ \E i \in 1..NumSlots, v \in proposedValues :
        /\ i \notin ChosenIndices(chosenValues)
        /\ chosenValues[i]' = {v}
        /\ /\A j \in 1..NumSlots \ {i} : chosenValues[j]' = chosenValues[j]
        /\ proposedValues' = proposedValues

ChosenIndices(cvs) == {i \in 1..NumSlots | cvs[i] /= {}}

SF_ == SF_Next \/ WF_Next

SF_Next == <>(\A i \in 1..NumSlots : ~(\E v \in Nat : chosenValues[i] = {v})))

WF_Next == [](Next => <>Next)

SpecFair == Spec /\ SF_

LiveSpec == SpecFair

THEOREM LiveSpec => []<>(\A i \in 1..NumSlots : chosenValues[i] /= {})

=============================================================================