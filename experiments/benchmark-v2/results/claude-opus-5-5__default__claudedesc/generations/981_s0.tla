---------------------------- MODULE TwoPhase ----------------------------
EXTENDS Naturals

CONSTANTS XInit(_), XAct(_, _, _)

VARIABLES p, c, x

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

Inv == /\ p \in {0, 1}
       /\ c \in {0, 1}

THEOREM TypeCorrect == Spec => []Inv

(***************************************************************************)
(* Refinement mapping to the Alternate specification.                      *)
(* The Alternate spec (variables v, x) is inlined here with v <- vBar:     *)
(*   Init == v = 0 /\ XInit(x)                                             *)
(*   Next == v' = (v + 1) % 2 /\ XAct(v, x, x')                            *)
(*   Spec == Init /\ [][Next]_<<v, x>>                                     *)
(***************************************************************************)
vBar == (p + c) % 2

AltInit == /\ vBar = 0
           /\ XInit(x)

AltNext == /\ vBar' = (vBar + 1) % 2
           /\ XAct(vBar, x, x')

AltSpec == AltInit /\ [][AltNext]_<<vBar, x>>

THEOREM Implementation == Spec => AltSpec
=============================================================================