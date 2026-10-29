------------------------------ MODULE TwoPhase ------------------------------
(***************************************************************************)
(* Two-phase handshake protocol.  A Producer and a Consumer alternate      *)
(* actions, the Producer going first.  The Producer owns the bit p and     *)
(* the Consumer owns the bit c.  The Producer may act only when p = c,     *)
(* and the Consumer may act only when p # c.  Each process toggles its     *)
(* own bit after acting, which lets the other process proceed.             *)
(*                                                                         *)
(* The operators XInit and XAct are parameters that let the user plug in   *)
(* application-specific state x and actions:                               *)
(*   XInit(x)          - the initial predicate on x                        *)
(*   XAct(i, x, xp)    - action performed by process i (0 = Producer,      *)
(*                       1 = Consumer) changing x to xp                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT XInit(_), XAct(_, _, _)

VARIABLES p, c, x

vars == <<p, c, x>>

(***************************************************************************)
(* The protocol                                                            *)
(***************************************************************************)
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

(***************************************************************************)
(* Invariant: both signals are always valid bits.                          *)
(***************************************************************************)
Inv == /\ p \in {0, 1}
       /\ c \in {0, 1}

(***************************************************************************)
(* Abstract alternation specification.  A single variable v (here given   *)
(* by a refinement mapping) alternates between 0 and 1; when v = i,        *)
(* process i takes its turn and performs XAct(i, x, x').                   *)
(***************************************************************************)
\* Refinement mapping: the abstract turn variable is the XOR of the bits.
vBar == (p + c) % 2

AltInit == /\ vBar = 0
           /\ XInit(x)

AltNext == /\ vBar' = (vBar + 1) % 2
           /\ XAct(vBar, x, x')

AltSpec == AltInit /\ [][AltNext]_<<vBar, x>>

(***************************************************************************)
(* Correctness theorems.                                                   *)
(***************************************************************************)
LEMMA InvInductive == Inv /\ [Next]_vars => Inv'
  BY DEF Inv, Next, ProducerStep, ConsumerStep, vars

THEOREM SafetyThm == Spec => []Inv

\* Refinement: the two-phase protocol implements the alternation spec.
THEOREM RefinementThm == Spec => AltSpec
=============================================================================