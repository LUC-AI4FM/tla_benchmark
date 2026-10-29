---------------------------- MODULE ClockBit ----------------------------
(***************************************************************************)
(* A single boolean "clock bit" that toggles between TRUE and FALSE on     *)
(* every step.                                                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

VARIABLE x

vars == << x >>

(***************************************************************************)
(* Assumption: applying Boolean negation twice returns the original value. *)
(***************************************************************************)
ASSUME DoubleNegation == \A b \in BOOLEAN : ~(~b) = b

ASSUME NegationClosed == \A b \in BOOLEAN : (~b) \in BOOLEAN /\ (~b) # b

(***************************************************************************)
(* Transition relation on values, separate from the variable.              *)
(***************************************************************************)
NextRel(v, w) == w = ~v

(* Set of successor values of a given boolean value. *)
Successors(v) == { w \in BOOLEAN : NextRel(v, w) }

(***************************************************************************)
(* Initial state and next-state relation.                                  *)
(***************************************************************************)
Init == x \in BOOLEAN

Next == /\ x' \in BOOLEAN
        /\ NextRel(x, x')

(* Weak fairness ensures the bit keeps toggling forever. *)
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

(* Type safety: x is always a boolean. *)
TypeOK == x \in BOOLEAN

(* Determinism: exactly one successor state for every reachable state. *)
Determinism == Cardinality(Successors(x)) = 1

DeterminismUnique ==
    \E w \in BOOLEAN : \A u \in BOOLEAN : NextRel(x, u) <=> (u = w)

(* Deadlock freedom: a next state always exists. *)
NoDeadlock == ENABLED Next

(* Double negation holds in every reachable state. *)
DoubleNegationInv == ~(~x) = x

(***************************************************************************)
(* Action / temporal properties                                            *)
(***************************************************************************)

(* Toggling safety: every non-stuttering step negates the bit. *)
ToggleSafety == [][x' = ~x]_vars

(* Every actual transition changes the bit. *)
AlwaysChanges == [][Next => x' # x]_vars

(* Type is preserved in every step. *)
TypeInvariance == []TypeOK

(* The system never deadlocks. *)
AlwaysEnabled == []NoDeadlock

(* Progress: the bit is TRUE infinitely often and FALSE infinitely often. *)
Progress == /\ []<>(x = TRUE)
            /\ []<>(x = FALSE)

(* From any state, the bit eventually takes the opposite value. *)
EventuallyFlips == \A b \in BOOLEAN : (x = b) ~> (x = ~b)

=============================================================================