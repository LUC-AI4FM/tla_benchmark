------------------------------ MODULE TwoPhase ------------------------------
EXTENDS Naturals

CONSTANT XInit(_), XAct(_, _, _)

VARIABLE p, c, x

vars == <<p, c, x>>

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

Inv == (p \in {0, 1}) /\ (c \in {0, 1})

-----------------------------------------------------------------------------
(* Refinement mapping: the Alternate specification instantiated with        *)
(* v <- (p + c) % 2, written out inline.                                    *)

vBar == (p + c) % 2

AInit == /\ vBar = 0
         /\ XInit(x)

ANext == /\ vBar' = (vBar + 1) % 2
         /\ XAct(vBar, x, x')

ASpec == AInit /\ [][ANext]_<<vBar, x>>

THEOREM Implementation == Spec => ASpec
=============================================================================