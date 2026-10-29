------------------------------- MODULE PrimeParamTest -------------------------------
(***************************************************************************)
(* Conformance test for how primed expressions are handled when they are   *)
(* passed as arguments to parameterized action operators.                  *)
(*                                                                         *)
(* From the initial state, exactly one of two transitions fires:          *)
(*   TypeA : x is incremented and arr[Idx] is set to x' (the new value).   *)
(*   TypeB : x is incremented and arr[Idx] is set to x  (the old value).   *)
(* Both use the same parameterized operator SetElem(i, v). The argument is *)
(* primed or unprimed at the point of use, not at the point of definition. *)
(* The invariants and action properties check that the two results differ. *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Indices,   \* domain of the mapping, e.g. {1, 2}
          Idx,       \* the element that the transitions update
          InitVal    \* initial value of the auxiliary variable x

ASSUME /\ Idx \in Indices
       /\ InitVal \in Nat

VARIABLES arr,       \* the mapping being updated
          x,         \* the auxiliary variable that changes on each step
          phase      \* which transition has fired: "init", "A" or "B"

vars == <<arr, x, phase>>

(***************************************************************************)
(* Parameterized action. The parameter v is an arbitrary expression. If    *)
(* the caller passes x', then v denotes the next-state value of x. If the  *)
(* caller passes x, then v denotes the current-state value of x.           *)
(***************************************************************************)
SetElem(i, v) == arr' = [arr EXCEPT ![i] = v]

(* A second parameterized action that changes x and updates arr with v.   *)
StepWith(v) == /\ x' = x + 1
               /\ SetElem(Idx, v)

TypeOK == /\ arr \in [Indices -> Nat]
          /\ x \in Nat
          /\ phase \in {"init", "A", "B"}

Init == /\ arr = [i \in Indices |-> 0]
        /\ x = InitVal
        /\ phase = "init"

(* Transition Type A: use the next-state (primed) value of x. *)
TypeA == /\ phase = "init"
         /\ StepWith(x')
         /\ phase' = "A"

(* Transition Type B: use the current-state (unprimed) value of x. *)
TypeB == /\ phase = "init"
         /\ StepWith(x)
         /\ phase' = "B"

(* After one transition has fired, the system stutters. *)
Done == /\ phase \in {"A", "B"}
        /\ UNCHANGED vars

Next == TypeA \/ TypeB \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(TypeA \/ TypeB)

-----------------------------------------------------------------------------
(* Safety: state invariants *)

\* 1. Primed parameter: the element equals the new value of x.
PrimedUsesNewValue == phase = "A" => arr[Idx] = x

\* 2. Unprimed parameter: the element keeps the old value of x.
UnprimedUsesOldValue == phase = "B" => arr[Idx] = x - 1

\* 3. The two behaviors are distinguishable.
Distinguishable == /\ phase = "A" => arr[Idx] # x - 1
                   /\ phase = "B" => arr[Idx] # x

\* Other elements of the mapping are never touched.
OthersUnchanged == \A i \in Indices \ {Idx} : arr[i] = 0

Invariants == /\ TypeOK
              /\ PrimedUsesNewValue
              /\ UnprimedUsesOldValue
              /\ Distinguishable
              /\ OthersUnchanged

(* Safety: action properties, checked directly on the transitions *)

ActionPropA == [][TypeA => /\ arr'[Idx] = x'
                           /\ arr'[Idx] = x + 1
                           /\ arr'[Idx] # x]_vars

ActionPropB == [][TypeB => /\ arr'[Idx] = x
                           /\ arr'[Idx] # x']_vars

\* Both transitions start from the same state but produce different arrays.
ActionDistinct == [][(phase = "init") =>
                       ( (TypeA => arr'[Idx] = InitVal + 1) /\
                         (TypeB => arr'[Idx] = InitVal) )]_vars

(* Liveness: one of the two test transitions eventually fires. *)
EventuallyTested == <>(phase \in {"A", "B"})

THEOREM Spec => []Invariants
THEOREM Spec => ActionPropA /\ ActionPropB /\ ActionDistinct
THEOREM Spec => EventuallyTested
=============================================================================