------------------------------ MODULE Handshake ------------------------------
(***************************************************************************)
(* The two-phase handshake protocol.  A Producer and a Consumer alternate  *)
(* actions, with the Producer acting first.  The state of the Producer is  *)
(* p, the state of the Consumer is c, and x is an abstract data variable.  *)
(* The Producer may act when p = c, and the Consumer may act when p # c.   *)
(*                                                                         *)
(* We show that this protocol implements the Alternate specification under *)
(* the refinement mapping v <- vBar, where vBar = (p + c) % 2.             *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANT XInit(_), XAct(_, _, _)

VARIABLES p, c, x

vars == <<p, c, x>>

---------------------------------------------------------------------------
(***************************************************************************)
(* The handshake protocol.                                                 *)
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

---------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants.                                                      *)
(***************************************************************************)
TypeOK == /\ p \in {0, 1}
          /\ c \in {0, 1}

(* The Producer is never more than one step ahead of the Consumer. *)
Alternation == (p = c) \/ (p = (c + 1) % 2)

---------------------------------------------------------------------------
(***************************************************************************)
(* The refinement mapping and the Alternate specification, with v          *)
(* replaced by vBar.                                                       *)
(***************************************************************************)
vBar == (p + c) % 2

AInit == /\ vBar = 0
         /\ XInit(x)

ANext == /\ vBar' = (vBar + 1) % 2
         /\ XAct(vBar, x, x')

ASpec == AInit /\ [][ANext]_<<vBar, x>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Proofs.                                                                 *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK, [Next]_vars
               PROVE  TypeOK'
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

THEOREM AlternationInvariant == Spec => []Alternation
<1>1. TypeOK => Alternation
  BY DEF TypeOK, Alternation
<1>2. QED
  BY <1>1, TypeCorrect, PTL

THEOREM Implementation == Spec => ASpec
<1>1. Init => AInit
  BY DEF Init, AInit, vBar
<1>2. TypeOK /\ [Next]_vars => [ANext]_<<vBar, x>>
  <2> SUFFICES ASSUME TypeOK, [Next]_vars
               PROVE  [ANext]_<<vBar, x>>
    OBVIOUS
  <2>1. CASE ProducerStep
    <3>1. p = c
      BY <2>1 DEF ProducerStep
    <3>2. vBar = 0
      BY <3>1 DEF TypeOK, vBar
    <3>3. vBar' = 1
      BY <2>1, <3>1 DEF ProducerStep, TypeOK, vBar
    <3>4. XAct(vBar, x, x')
      BY <2>1, <3>2 DEF ProducerStep
    <3>5. QED
      BY <3>2, <3>3, <3>4 DEF ANext
  <2>2. CASE ConsumerStep
    <3>1. p # c
      BY <2>2 DEF ConsumerStep
    <3>2. vBar = 1
      BY <3>1 DEF TypeOK, vBar
    <3>3. vBar' = 0
      BY <2>2, <3>1 DEF ConsumerStep, TypeOK, vBar
    <3>4. XAct(vBar, x, x')
      BY <2>2, <3>2 DEF ConsumerStep
    <3>5. QED
      BY <3>2, <3>3, <3>4 DEF ANext
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, vBar
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec, ASpec

=============================================================================