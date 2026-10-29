---- MODULE StateTransformer ----
EXTENDS Integers

\* Fixed index set of five elements
Idx == 1..5

\* Finite set of five integers from which the control value is drawn
CtrlValues == 1..5

\* Distinguished control value (also used as the index to overwrite)
D == 3

\* Fixed constant written into the vector entry
K == 42

VARIABLES ctrl, vec

vars == <<ctrl, vec>>

TypeOK ==
    /\ ctrl \in CtrlValues
    /\ vec \in [Idx -> Int]

Init ==
    /\ ctrl \in CtrlValues
    /\ vec = [i \in Idx |-> 0]

Update ==
    /\ ctrl' = ctrl
    /\ vec' = IF ctrl = D
                 THEN [vec EXCEPT ![D] = K]
                 ELSE vec

Next == Update

\* Fairness-free specification: only safety, no liveness requirements
Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Temporal properties

\* (1) The control value never changes
CtrlConstant == [][ctrl' = ctrl]_vars

\* (2) Vector entries are always integers and only change as specified
VecAlwaysInt == [](\A i \in Idx : vec[i] \in Int)

VecChangesOnlyAsSpecified ==
    [][\A i \in Idx : vec'[i] # vec[i] => (ctrl = D /\ i = D /\ vec'[i] = K)]_vars

\* (3) If control equals D, then in the next state vec[D] = K
UpdateWhenDistinguished ==
    [][ctrl = D => vec'[D] = K]_vars

\* (4) If control does not equal D, then all entries remain unchanged
UnchangedOtherwise ==
    [][ctrl # D => \A i \in Idx : vec'[i] = vec[i]]_vars

Properties ==
    /\ CtrlConstant
    /\ VecAlwaysInt
    /\ VecChangesOnlyAsSpecified
    /\ UpdateWhenDistinguished
    /\ UnchangedOtherwise

THEOREM Spec => []TypeOK
THEOREM Spec => Properties

====