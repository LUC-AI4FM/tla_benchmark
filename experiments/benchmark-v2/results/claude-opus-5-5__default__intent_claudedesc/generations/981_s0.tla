---------------------------- MODULE TwoPhaseHandshake ----------------------------
EXTENDS Naturals

CONSTANTS XInit(_),       \* XInit(x): predicate giving the initial application state
          XAct(_, _, _)   \* XAct(i, x, x'): application action of process i
                          \*   i = 0 : Producer,  i = 1 : Consumer

VARIABLES p,   \* Producer's single-bit signal
          c,   \* Consumer's single-bit signal
          x    \* application-specific state

vars == <<p, c, x>>

---------------------------------------------------------------------------------
(* The two-phase handshake protocol                                             *)

Init == /\ p = 0
        /\ c = 0
        /\ XInit(x)

\* The Producer may act only when both signals are equal.
ProducerStep == /\ p = c
                /\ XAct(0, x, x')
                /\ p' = (p + 1) % 2
                /\ c' = c

\* The Consumer may act only when the signals differ.
ConsumerStep == /\ p # c
                /\ XAct(1, x, x')
                /\ c' = (c + 1) % 2
                /\ p' = p

Next == ProducerStep \/ ConsumerStep

Spec == Init /\ [][Next]_vars

---------------------------------------------------------------------------------
(* Safety: the signals are always valid single bits                             *)

Inv == /\ p \in {0, 1}
       /\ c \in {0, 1}

---------------------------------------------------------------------------------
(* Abstract alternation specification, expressed through a refinement mapping. *)
(* The abstract variable v indicates whose turn it is:                          *)
(*    v = 0 : Producer's turn,   v = 1 : Consumer's turn                        *)

vBar == (p + c) % 2

AltInit == /\ vBar = 0
           /\ XInit(x)

AltNext == /\ vBar' = (vBar + 1) % 2
           /\ XAct(vBar, x, x')

AltSpec == AltInit /\ [][AltNext]_<<vBar, x>>

---------------------------------------------------------------------------------
(* Theorems                                                                     *)

THEOREM InvariantHolds == Spec => []Inv
<1>1. Init => Inv
      BY DEF Init, Inv
<1>2. Inv /\ [Next]_vars => Inv'
      BY DEF Inv, Next, ProducerStep, ConsumerStep, vars
<1>3. QED
      BY <1>1, <1>2 DEF Spec

THEOREM Implementation == Spec => AltSpec
<1>1. Init => AltInit
      BY DEF Init, AltInit, vBar
<1>2. Inv /\ [Next]_vars => [AltNext]_<<vBar, x>>
  <2>1. Inv /\ ProducerStep => AltNext
        BY DEF Inv, ProducerStep, AltNext, vBar
  <2>2. Inv /\ ConsumerStep => AltNext
        BY DEF Inv, ConsumerStep, AltNext, vBar
  <2>3. UNCHANGED vars => UNCHANGED <<vBar, x>>
        BY DEF vars, vBar
  <2>4. QED
        BY <2>1, <2>2, <2>3 DEF Next
<1>3. QED
      BY <1>1, <1>2, InvariantHolds DEF Spec, AltSpec
=================================================================================