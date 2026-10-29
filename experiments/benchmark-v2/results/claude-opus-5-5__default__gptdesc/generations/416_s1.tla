---------------------------- MODULE PrimingOperatorArgs ----------------------------
(***************************************************************************)
(* A small test module that exercises priming behavior and operator       *)
(* arguments.  Two variables x and y are declared; x is a function over    *)
(* the domain {1,2}.  The Next action has two non-stuttering branches and  *)
(* a stuttering branch.  The two non-stuttering branches call operators    *)
(* that receive the variable x as an argument.  One operator uses d'       *)
(* inside an EXCEPT update and the other uses d unprimed.  Print and       *)
(* Assert check that priming the formal parameter d means priming the      *)
(* actual argument x.                                                      *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x, y

vars == <<x, y>>

Dom == {1, 2}

(***************************************************************************)
(* Initial state: x is a function over {1,2}; y is a copy of x.            *)
(***************************************************************************)
Init ==
    /\ x = [i \in Dom |-> 0]
    /\ y = x

(***************************************************************************)
(* The operator UsesPrimed uses d' inside the EXCEPT.  When it is called   *)
(* with argument x, d' means x', which is the next-state value of x.       *)
(***************************************************************************)
UsesPrimed(d, e) == e' = [d' EXCEPT ![1] = 5]

(***************************************************************************)
(* The operator UsesUnprimed uses d unprimed inside the EXCEPT.  When it   *)
(* is called with argument x, d means the current-state value of x.        *)
(***************************************************************************)
UsesUnprimed(d, e) == e' = [d EXCEPT ![1] = 5]

(***************************************************************************)
(* Branch 1 uses the primed operator.  y' must be built from x', so        *)
(* y' = (1 :> 5 @@ 2 :> 7).                                               *)
(***************************************************************************)
PrimedBranch ==
    /\ x' = [x EXCEPT ![2] = 7]
    /\ UsesPrimed(x, y)
    /\ PrintT(<<"PrimedBranch", x, x', y'>>)
    /\ Assert(y' = [i \in Dom |-> IF i = 1 THEN 5 ELSE 7],
              "Failure: d' inside EXCEPT did not refer to x'")

(***************************************************************************)
(* Branch 2 uses the unprimed operator.  y' must be built from x, so       *)
(* y'[1] = 5 and y'[2] = x[2] (the current, unprimed value).               *)
(***************************************************************************)
UnprimedBranch ==
    /\ x' = [x EXCEPT ![2] = 7]
    /\ UsesUnprimed(x, y)
    /\ PrintT(<<"UnprimedBranch", x, x', y'>>)
    /\ Assert(y' = [i \in Dom |-> IF i = 1 THEN 5 ELSE x[i]],
              "Failure: unprimed d inside EXCEPT did not refer to x")

(***************************************************************************)
(* Stuttering branch.                                                      *)
(***************************************************************************)
Stutter == UNCHANGED vars

Next ==
    \/ PrimedBranch
    \/ UnprimedBranch
    \/ Stutter

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Safety invariant: both variables remain functions over {1,2} with       *)
(* natural-number values.                                                  *)
(***************************************************************************)
TypeOK ==
    /\ x \in [Dom -> Nat]
    /\ y \in [Dom -> Nat]

THEOREM Spec => []TypeOK
=============================================================================