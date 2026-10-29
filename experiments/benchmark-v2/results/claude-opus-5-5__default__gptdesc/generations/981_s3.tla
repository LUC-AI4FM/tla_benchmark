------------------------------ MODULE Handshake ------------------------------
(***************************************************************************)
(* The two-phase handshake protocol.  A Producer and a Consumer alternate  *)
(* actions, with the Producer acting first.  The Producer's state is p,    *)
(* the Consumer's state is c, and x is an abstract data variable.  The     *)
(* Producer may act when p = c and the Consumer may act when p # c.        *)
(*                                                                         *)
(* We show that this protocol implements the Alternate specification under *)
(* the refinement mapping v <- vBar, where vBar == (p + c) % 2.  The       *)
(* Alternate specification is written inline below, with vBar substituted  *)
(* for its variable v.                                                     *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANTS XInit(_), XAct(_, _, _)
  (*************************************************************************)
  (* XInit(x) describes the initial value of x.  XAct(i, x, x') describes  *)
  (* how x changes when process i acts: i = 0 is the Producer and i = 1 is *)
  (* the Consumer.                                                         *)
  (*************************************************************************)

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
(* The refinement mapping.                                                 *)
(***************************************************************************)
vBar == (p + c) % 2

(***************************************************************************)
(* The Alternate specification, with v replaced by vBar.                   *)
(***************************************************************************)
AInit == /\ vBar = 0
         /\ XInit(x)

A0 == /\ vBar = 0
      /\ vBar' = 1
      /\ XAct(0, x, x')

A1 == /\ vBar = 1
      /\ vBar' = 0
      /\ XAct(1, x, x')

ANext == A0 \/ A1

avars == <<vBar, x>>

ASpec == AInit /\ [][ANext]_avars

(***************************************************************************)
(* The invariant of the Alternate specification under the mapping.         *)
(***************************************************************************)
AlternateInv == vBar \in {0, 1}

-----------------------------------------------------------------------------
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

THEOREM AltInvariant == Spec => []AlternateInv
<1>1. TypeOK => AlternateInv
  BY DEF TypeOK, AlternateInv, vBar
<1>2. QED
  BY <1>1, TypeCorrect, PTL

THEOREM Implementation == Spec => ASpec
<1>1. Init => AInit
  BY DEF Init, AInit, vBar
<1>2. TypeOK /\ [Next]_vars => [ANext]_avars
  <2> SUFFICES ASSUME TypeOK, [Next]_vars
               PROVE  [ANext]_avars
    OBVIOUS
  <2>1. CASE ProducerStep
    <3>1. vBar = 0
      BY <2>1 DEF ProducerStep, TypeOK, vBar
    <3>2. vBar' = 1
      BY <2>1 DEF ProducerStep, TypeOK, vBar
    <3>3. XAct(0, x, x')
      BY <2>1 DEF ProducerStep
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF ANext, A0
  <2>2. CASE ConsumerStep
    <3>1. vBar = 1
      BY <2>2 DEF ConsumerStep, TypeOK, vBar
    <3>2. vBar' = 0
      BY <2>2 DEF ConsumerStep, TypeOK, vBar
    <3>3. XAct(1, x, x')
      BY <2>2 DEF ConsumerStep
    <3>4. QED
      BY <3>1, <3>2, <3>3 DEF ANext, A1
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, avars, vBar
  <2>4. QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
  BY <1>1, <1>2, TypeCorrect, PTL DEF Spec, ASpec
=============================================================================