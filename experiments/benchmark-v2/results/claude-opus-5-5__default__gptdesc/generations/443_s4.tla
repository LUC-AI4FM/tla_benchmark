------------------------------ MODULE InstanceSemanticsTest ------------------------------
(***************************************************************************)
(* A small test module that exercises subtle action-level semantics       *)
(* (priming, ENABLED, and disjunction of actions) of the kind that become *)
(* delicate under INSTANCE substitution, although no INSTANCE declaration  *)
(* appears in this file.                                                   *)
(*                                                                         *)
(* The module has a single variable u. As the description states, it      *)
(* intentionally defines no Init, Next, or Spec, because it only tests     *)
(* action-level semantics.                                                 *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE u

vars == << u >>

(***************************************************************************)
(* G(c, A): a helper action parameterized by a value c and an action A.   *)
(* It assigns c to u in the next state, conjoined with action A.          *)
(***************************************************************************)
G(c, A) == /\ u' = c
           /\ A

(***************************************************************************)
(* H combines a stuttering assignment on u (u' = u) with an ENABLED test  *)
(* over a disjunction of actions built from G. Inside ENABLED, u' is      *)
(* bound by the ENABLED operator, so it is independent of the outer u'.   *)
(***************************************************************************)
H == /\ u' = u
     /\ ENABLED ( \/ G(u, u' = 0)
                  \/ G(u + 1, TRUE) )

(***************************************************************************)
(* Auxiliary state predicates and actions that exercise the same features *)
(***************************************************************************)
EnabledG(c, A) == ENABLED G(c, A)

DisjunctiveAction == G(0, TRUE) \/ G(1, u' # u)

HStutters == H => UNCHANGED vars

==========================================================================================