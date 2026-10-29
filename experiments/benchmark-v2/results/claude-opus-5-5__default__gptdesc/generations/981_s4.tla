------------------------------ MODULE Handshake ------------------------------
(***************************************************************************)
(* The two-phase handshake protocol.  A Producer and a Consumer alternate *)
(* actions, with the Producer acting first.  The state of the Producer is *)
(* p, the state of the Consumer is c, and x is abstract data.  The        *)
(* Producer may act when p = c, and the Consumer may act when p # c.      *)
(*                                                                         *)
(* The module shows that this protocol implements the Alternate           *)
(* specification under the refinement mapping v <- vBar, where            *)
(* vBar == (p + c) % 2.                                                   *)
(***************************************************************************)
EXTENDS Integers, TLAPS

CONSTANTS XInit(_), XAct(_, _, _)

VARIABLES p, c, x

vars == <<p, c, x>>

TypeOK == /\ p \in {0, 1}
          /\ c \in {0, 1}

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
(***************************************************************************)
(* Refinement mapping and the Alternate specification under it.  This is  *)
(* the module Alternate (with variables v and x) with v replaced by vBar. *)
(***************************************************************************)
vBar == (p + c) % 2

AInit == /\ vBar = 0
         /\ XInit(x)

ANext == \/ /\ vBar = 0
            /\ vBar' = 1
            /\ XAct(0, x, x')
         \/ /\ vBar = 1
            /\ vBar' = 0
            /\ XAct(1, x, x')

ASpec == AInit /\ [][ANext]_<<vBar, x>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proofs                                                                  *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars PROVE TypeOK'
    OBVIOUS
  <2>1. CASE ProducerStep
    BY <2>1 DEF ProducerStep, TypeOK
  <2>2. CASE ConsumerStep
    BY <2>2 DEF ConsumerStep, TypeOK
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, TypeOK
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM Implementation == Spec => ASpec
<1>1. Init => AInit
  BY DEF Init, AInit, vBar
<1>2. TypeOK /\ [Next]_vars => [ANext]_<<vBar, x>>
  <2> SUFFICES ASSUME TypeOK, [Next]_vars
               PROVE  [ANext]_<<vBar, x>>
    OBVIOUS
  <2>1. CASE ProducerStep
    <3>1. CASE p = 0 /\ c = 0
      BY <2>1, <3>1 DEF ProducerStep, ANext, vBar
    <3>2. CASE p = 1 /\ c = 1
      BY <2>1, <3>2 DEF ProducerStep, ANext, vBar
    <3>3. QED
      BY <2>1, <3>1, <3>2 DEF ProducerStep, TypeOK
  <2>2. CASE ConsumerStep
    <3>1. CASE p = 1 /\ c = 0
      BY <2>2, <3>1 DEF ConsumerStep, ANext, vBar
    <3>2. CASE p = 0 /\ c = 1
      BY <2>2, <3>2 DEF ConsumerStep, ANext, vBar
    <3>3. QED
      BY <2>2, <3>1, <3>2 DEF ConsumerStep, TypeOK
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, vBar
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec, ASpec

=============================================================================