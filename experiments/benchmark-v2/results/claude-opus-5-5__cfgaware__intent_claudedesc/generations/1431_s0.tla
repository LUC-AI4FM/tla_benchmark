---------------------------- MODULE ConstraintLiveness ----------------------------
(***************************************************************************)
(* Demonstrates a pitfall of combining state constraints with liveness    *)
(* checking.  The system cycles forever between "A" and "B" and never     *)
(* reaches "Done".  A state constraint bounds the length of the history   *)
(* log.  With the constraint active, every behavior is cut off, so no     *)
(* infinite counterexample (lasso) exists and Prop is spuriously reported *)
(* as satisfied.  Without the constraint, Prop is genuinely violated.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

VARIABLES state, history

vars == <<state, history>>

States == {"A", "B", "Done"}

TypeOK ==
    /\ state \in States
    /\ history \in Seq(States)

Init ==
    /\ state = "A"
    /\ history = <<>>

GoToB ==
    /\ state = "A"
    /\ state' = "B"
    /\ history' = Append(history, state)

GoToA ==
    /\ state = "B"
    /\ state' = "A"
    /\ history' = Append(history, state)

Next == GoToB \/ GoToA

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* State constraint bounding the history log so the state space is finite.
\* This cuts off all infinite behaviors, hiding the liveness violation.
Constraint == Len(history) < 5

\* Liveness property: the system eventually reaches "Done".
\* Truly false (the system cycles A <-> B forever), but reported as
\* satisfied when Constraint is in effect.
Prop == <>(state = "Done")

=============================================================================