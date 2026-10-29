---------------------------- MODULE InstanceInLet ----------------------------
(***************************************************************************)
(* Minimal module used to test an INSTANCE inside a LET context.           *)
(* The state is a single variable x, and the only operator of interest,    *)
(* xplus1, computes x + 1 from the current state.                          *)
(* The Init/Next/Spec definitions below are trivial scaffolding. They add  *)
(* no behavior beyond leaving x unconstrained by actions.                  *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS InitX

VARIABLES x

vars == << x >>

\* The only operator of interest: x + 1 evaluated in the current state
xplus1 == x + 1

Init == x = InitX

\* No actions are described for this system, so the only step is a stutter.
Next == UNCHANGED x

Spec == Init /\ [][Next]_vars

=============================================================================