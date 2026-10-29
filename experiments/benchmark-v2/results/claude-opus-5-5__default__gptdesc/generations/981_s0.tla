------------------------------ MODULE TwoPhase ------------------------------
(***************************************************************************)
(* The two-phase handshake protocol.  A Producer and a Consumer process    *)
(* alternate actions, with the Producer acting first.  p and c are the     *)
(* states of the Producer and Consumer.  x is an abstract data variable    *)
(* that each step modifies.  XInit(x) is the initial condition on x, and   *)
(* XAct(i, x, x') describes how process i (0 = Producer, 1 = Consumer)     *)
(* changes x.                                                              *)
(*                                                                         *)
(* The protocol implements the Alternate specification under the          *)
(* refinement mapping v <- vBar.  To keep this module self-contained, the  *)
(* Alternate specification is written out below with v replaced by vBar.  *)
(***************************************************************************)
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

-----------------------------------------------------------------------------
(* Safety invariant                                                        *)

Inv == /\ p \in {0, 1}
       /\ c \in {0, 1}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping and the Alternate specification under that mapping. *)
(* Alternate:                                                              *)
(*   Init == (v = 0) /\ XInit(x)                                           *)
(*   Next == v' = (v + 1) % 2 /\ XAct(v, x, x')                            *)
(*   Spec == Init /\ [][Next]_<<v, x>>                                     *)
(***************************************************************************)

vBar == (p + c) % 2

AInit == /\ vBar = 0
         /\ XInit(x)

ANext == /\ vBar' = (vBar + 1) % 2
         /\ XAct(vBar, x, x')

ASpec == AInit /\ [][ANext]_<<vBar, x>>

-----------------------------------------------------------------------------
(* Proofs                                                                  *)

THEOREM TypeCorrect == Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv
<1>2. Inv /\ [Next]_vars => Inv'
  BY DEF Inv, Next, ProducerStep, ConsumerStep, vars
<1>3. QED
  BY <1>1, <1>2 DEF Spec

THEOREM Implementation == Spec => ASpec
<1>1. Init => AInit
  BY DEF Init, AInit, vBar
<1>2. Inv /\ [Next]_vars => [ANext]_<<vBar, x>>
  <2> SUFFICES ASSUME Inv,
                      [Next]_vars
               PROVE  [ANext]_<<vBar, x>>
    OBVIOUS
  <2>1. CASE ProducerStep
    \* p = c, so vBar = 0, vBar' = 1, and XAct(0, x, x') = XAct(vBar, x, x')
    BY <2>1 DEF Inv, ProducerStep, ANext, vBar
  <2>2. CASE ConsumerStep
    \* p # c, so vBar = 1, vBar' = 0, and XAct(1, x, x') = XAct(vBar, x, x')
    BY <2>2 DEF Inv, ConsumerStep, ANext, vBar
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, vBar
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY <1>1, <1>2, TypeCorrect DEF Spec, ASpec

=============================================================================