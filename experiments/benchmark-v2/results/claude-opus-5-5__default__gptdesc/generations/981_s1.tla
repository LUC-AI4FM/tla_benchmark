---------------------------- MODULE Handshake ----------------------------
(***************************************************************************)
(* The two-phase handshake protocol.  A Producer and a Consumer alternate  *)
(* actions, with the Producer acting first.  The Producer's state is p,    *)
(* the Consumer's state is c, and x is an abstract data variable.  The     *)
(* Producer may act when p = c, and the Consumer may act when p # c.       *)
(*                                                                         *)
(* The module shows that this protocol implements the Alternate            *)
(* specification under a refinement mapping, using vBar to relate the      *)
(* two.  The Alternate specification is stated inline, with vBar           *)
(* substituted for its variable v.  A TLAPS proof of the implementation    *)
(* is included.                                                            *)
(***************************************************************************)
EXTENDS Integers, TLAPS

CONSTANT Data

VARIABLES p, c, x

vars == <<p, c, x>>

---------------------------------------------------------------------------
(***************************************************************************)
(* The Handshake protocol.                                                 *)
(***************************************************************************)
TypeOK == /\ p \in {0, 1}
          /\ c \in {0, 1}
          /\ x \in Data

Init == /\ p \in {0, 1}
        /\ c = p
        /\ x \in Data

ProducerStep == /\ p = c
                /\ x' \in Data
                /\ p' = (p + 1) % 2
                /\ c' = c

ConsumerStep == /\ p # c
                /\ c' = (c + 1) % 2
                /\ UNCHANGED <<p, x>>

Next == ProducerStep \/ ConsumerStep

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------
(***************************************************************************)
(* The Alternate specification.  XInit and XAct describe the initial       *)
(* value of x and how the two alternating processes change x.  Process 0   *)
(* is the Producer, which sets x to some value in Data.  Process 1 is the  *)
(* Consumer, which leaves x unchanged.                                     *)
(***************************************************************************)
XInit(xx) == xx \in Data

XAct(i, xInit, xNext) == IF i = 0 THEN xNext \in Data
                                  ELSE xNext = xInit

(***************************************************************************)
(* The refinement mapping.  vBar is 0 when it is the Producer's turn       *)
(* (p = c) and 1 when it is the Consumer's turn (p # c).                   *)
(***************************************************************************)
vBar == IF p = c THEN 0 ELSE 1

AltInit == /\ vBar = 0
           /\ XInit(x)

AltA0 == /\ vBar = 0
         /\ vBar' = 1
         /\ XAct(0, x, x')

AltA1 == /\ vBar = 1
         /\ vBar' = 0
         /\ XAct(1, x, x')

AltNext == AltA0 \/ AltA1

AltSpec == AltInit /\ [][AltNext]_<<vBar, x>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants.                                                      *)
(***************************************************************************)
Inv == /\ p \in {0, 1}
       /\ c \in {0, 1}

(* The Alternate variable always has a value in {0, 1}. *)
AltTypeOK == vBar \in {0, 1}

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
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Next
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

THEOREM InvCorrect == Spec => []Inv
<1>1. Init => Inv
  BY DEF Init, Inv
<1>2. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. CASE ProducerStep
    BY <2>1 DEF ProducerStep, Inv
  <2>2. CASE ConsumerStep
    BY <2>2 DEF ConsumerStep, Inv
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, Inv
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Next
<1> QED
  BY <1>1, <1>2, PTL DEF Spec

---------------------------------------------------------------------------
(***************************************************************************)
(* The Handshake protocol implements Alternate under the refinement        *)
(* mapping v <- vBar.                                                      *)
(***************************************************************************)
THEOREM Implementation == Spec => AltSpec
<1>1. Init => AltInit
  BY DEF Init, AltInit, vBar, XInit
<1>2. Inv /\ [Next]_vars => [AltNext]_<<vBar, x>>
  <2> SUFFICES ASSUME Inv, [Next]_vars
               PROVE  [AltNext]_<<vBar, x>>
    OBVIOUS
  <2>1. CASE ProducerStep
    <3>1. vBar = 0
      BY <2>1 DEF ProducerStep, vBar
    <3>2. p' # c'
      BY <2>1, Z3 DEF ProducerStep, Inv
    <3>3. vBar' = 1
      BY <3>2 DEF vBar
    <3>4. XAct(0, x, x')
      BY <2>1 DEF ProducerStep, XAct
    <3> QED
      BY <3>1, <3>3, <3>4 DEF AltNext, AltA0
  <2>2. CASE ConsumerStep
    <3>1. vBar = 1
      BY <2>2 DEF ConsumerStep, vBar
    <3>2. p' = c'
      BY <2>2, Z3 DEF ConsumerStep, Inv
    <3>3. vBar' = 0
      BY <3>2 DEF vBar
    <3>4. XAct(1, x, x')
      BY <2>2 DEF ConsumerStep, XAct
    <3> QED
      BY <3>1, <3>3, <3>4 DEF AltNext, AltA1
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, vBar
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Next
<1>3. Init => Inv
  BY DEF Init, Inv
<1>4. Inv /\ [Next]_vars => Inv'
  <2> SUFFICES ASSUME Inv, [Next]_vars PROVE Inv'
    OBVIOUS
  <2>1. CASE ProducerStep
    BY <2>1 DEF ProducerStep, Inv
  <2>2. CASE ConsumerStep
    BY <2>2 DEF ConsumerStep, Inv
  <2>3. CASE UNCHANGED vars
    BY <2>3 DEF vars, Inv
  <2> QED
    BY <2>1, <2>2, <2>3 DEF Next
<1> QED
  BY <1>1, <1>2, <1>3, <1>4, PTL DEF Spec, AltSpec

THEOREM AltTypeCorrect == Spec => []AltTypeOK
BY PTL DEF AltTypeOK, vBar
=============================================================================