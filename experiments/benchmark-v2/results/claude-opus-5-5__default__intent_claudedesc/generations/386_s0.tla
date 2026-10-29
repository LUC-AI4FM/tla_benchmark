------------------------------- MODULE ConstantInstantiation -------------------------------
EXTENDS Naturals

(***************************************************************************)
(* An "external" parameterized module, declared as an inner module so the  *)
(* specification is self-contained. It has two constant parameters, P and  *)
(* Q, and defines a few operators over them.                               *)
(***************************************************************************)
---------------------------------- MODULE Dep ----------------------------------
EXTENDS Naturals
CONSTANTS P, Q

DepSum      == P + Q
DepProperty == P + Q = 42
DepIdentity == (Q = 0) => (P + Q = P)
=================================================================================