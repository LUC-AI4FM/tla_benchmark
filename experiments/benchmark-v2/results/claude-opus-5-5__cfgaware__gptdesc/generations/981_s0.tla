---------------------------- MODULE Handshake ----------------------------
EXTENDS Naturals

VARIABLES p, c, x

vars == <<p, c, x>>

(* Abstract data operators. They are given concrete definitions so the  *)
(* module is model-checkable; a configuration may override them.        *)
XInit(xx) == xx \in {0, 1}

XAct(i, xx, xxp) == xxp = (xx + 1) % 2

-----------------------------------------------------------------------------
(* The two-phase handshake protocol.                                     *)

Init == /\ p \in {0, 1}
        /\ c = p
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

Inv == /\ p \in {0, 1}
       /\ c \in {0, 1}

-----------------------------------------------------------------------------
(* The Alternate specification, with v replaced by the refinement        *)
(* mapping vBar.                                                         *)

vBar == (p + c) % 2

AInit == /\ vBar = 0
         /\ XInit(x)

ANext == /\ vBar' = 1 - vBar
         /\ XAct(vBar, x, x')

ASpec == AInit /\ [][ANext]_<<vBar, x>>

-----------------------------------------------------------------------------
THEOREM TypeCorrect == Spec => []Inv

THEOREM Implementation == Spec => ASpec
=============================================================================