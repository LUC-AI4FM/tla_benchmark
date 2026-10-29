--------------------------- MODULE VectorTransformer ---------------------------
EXTENDS Integers

CONSTANTS D,  \* the distinguished control value (also the vector index updated)
          K   \* the fixed constant written into vec[D]

Index   == 1..5           \* fixed index set of five elements
CtrlSet == 1..5           \* finite set of five allowed initial control values

ASSUME DAssump == D \in Index
ASSUME KAssump == K \in Int

VARIABLES ctrl, vec

vars == <<ctrl, vec>>

ZeroVec == [i \in Index |-> 0]

-----------------------------------------------------------------------------
(* State space *)

TypeOK == /\ ctrl \in CtrlSet
          /\ vec \in [Index -> Int]

-----------------------------------------------------------------------------
(* Behaviors *)

Init == /\ ctrl \in CtrlSet
        /\ vec = ZeroVec

Update == /\ ctrl' = ctrl
          /\ vec' = IF ctrl = D
                       THEN [vec EXCEPT ![D] = K]
                       ELSE vec

Next == Update

\* Fairness-free specification: no liveness beyond the deterministic update.
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariants *)

\* Strengthened state invariant describing all reachable states
ReachableInv ==
    /\ TypeOK
    /\ \A i \in Index \ {D} : vec[i] = 0
    /\ vec[D] \in {0, K}
    /\ (ctrl # D) => (vec = ZeroVec)

-----------------------------------------------------------------------------
(* Temporal properties *)

\* (1) The control value never changes
ControlInvariant == [][ctrl' = ctrl]_vars

ControlConstant == \A c \in CtrlSet : [](ctrl = c => [](ctrl = c))

\* (2) Vector entries are always integers and never change except as specified
VecAlwaysInt == [](\A i \in Index : vec[i] \in Int)

VecOnlyChangesAsSpecified ==
    [][\A i \in Index :
          vec'[i] # vec[i] => (ctrl = D /\ i = D /\ vec'[i] = K)]_vars

\* (3) If ctrl = D, then in the next state vec[D] = K
UpdateApplied == [][(ctrl = D) => (vec'[D] = K)]_vars

\* (4) If ctrl # D, then all vector entries keep their previous values
NoChangeOtherwise ==
    [][(ctrl # D) => (\A i \in Index : vec'[i] = vec[i])]_vars

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []TypeOK
THEOREM Spec => []ReachableInv
THEOREM Spec => ControlInvariant
THEOREM Spec => ControlConstant
THEOREM Spec => VecAlwaysInt
THEOREM Spec => VecOnlyChangesAsSpecified
THEOREM Spec => UpdateApplied
THEOREM Spec => NoChangeOtherwise

=============================================================================