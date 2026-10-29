---------------------------- MODULE MCTwoPhase ----------------------------
(***************************************************************************)
(* A small wrapper around the TwoPhase specification.  It declares the     *)
(* variables p, c and x, defines the parameter operators XInit and XAct,   *)
(* and instantiates TwoPhase with them.                                    *)
(*                                                                         *)
(*   XInit(v)  : initial-state condition requiring v = 0.                  *)
(*   XAct(i, xInit, xNext) : trivial next-state relation xNext = xInit.    *)
(*                                                                         *)
(* The original file has no temporal specification, theorem or fault      *)
(* model.  So that this module is self-contained, Init, Next and Spec      *)
(* below give the standard two-phase handshake that uses these helpers,    *)
(* together with a simple type invariant.                                  *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES p, c, x

vars == <<p, c, x>>

---------------------------------------------------------------------------
(* Helper operators that parameterize TwoPhase.                           *)
---------------------------------------------------------------------------
XInit(v) == v = 0

XAct(i, xInit, xNext) == xNext = xInit

---------------------------------------------------------------------------
(* Instantiation of the wrapped module.  Its CONSTANT parameters XInit    *)
(* and XAct and its variables p, c, x are substituted implicitly by the   *)
(* identically named definitions and variables above.                     *)
---------------------------------------------------------------------------
TP == INSTANCE TwoPhase

---------------------------------------------------------------------------
(* Self-contained two-phase handshake built from the helpers.             *)
---------------------------------------------------------------------------
Init == /\ p = 0
        /\ c = 0
        /\ XInit(x)

ProducerStep == /\ p = c
                /\ XAct(0, x, x')
                /\ p' = (p + 1) % 2
                /\ c' = c

ConsumerStep == /\ p # c
                /\ XAct(1, x, x')
                /\ c' = (c + 1) % 2
                /\ p' = p

Next == ProducerStep \/ ConsumerStep

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(* Safety invariants                                                      *)
---------------------------------------------------------------------------
TypeOK == /\ p \in {0, 1}
          /\ c \in {0, 1}
          /\ x = 0

=============================================================================