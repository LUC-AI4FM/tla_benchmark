------------------------------ MODULE CounterSystem ------------------------------
EXTENDS Naturals, TLC

CONSTANTS Op, InitState, InvSet, ReachPred

VARIABLE s

(* --------------------------------------------------------------------------- *)
(* Type assumptions for the constants (optional but useful for model checking) *)
OpType        ==  Op \in [Int -> SUBSET Int]
InitStateType ==  InitState \in Int
InvSetType    ==  InvSet \subseteq Int
ReachPredType ==  ReachPred \in [Int -> BOOLEAN]

(* --------------------------------------------------------------------------- *)
(* Initial state: the counter starts at InitState and must belong to the invariant set *)
Init == /\ s = InitState
        /\ s \in InvSet

(* --------------------------------------------------------------------------- *)
(* Transition relation: choose any next value from Op[s] that stays within the invariant set *)
Next ==
  \/ /\ s' \in Op[s]
     /\ s' \in InvSet

(* --------------------------------------------------------------------------- *)
(* The full specification *)
Spec == Init
        /\ [][Next]_s
        /\ OpType
        /\ InitStateType
        /\ InvSetType
        /\ ReachPredType

(* --------------------------------------------------------------------------- *)
(* Safety invariant: the state always stays within the invariant set *)
SafetyInvariant == [] (s \in InvSet)

(* --------------------------------------------------------------------------- *)
(* Liveness property: some state satisfying ReachPred is eventually reachable *)
Reachability == <> (ReachPred[s])

(* --------------------------------------------------------------------------- *)
(* Absence of deadlock when Op maps reachable states to nonempty sets *)
NoDeadlock == [] (Op[s] = {} => FALSE)

=============================================================================