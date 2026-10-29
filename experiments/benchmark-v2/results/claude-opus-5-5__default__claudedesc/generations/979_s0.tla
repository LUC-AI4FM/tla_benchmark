------------------------------ MODULE MCTwoPhase ------------------------------
(***************************************************************************)
(* Model-checking configuration for the TwoPhase specification.  The        *)
(* general TwoPhase module is parameterized by two constant operators,      *)
(* XInit and XAct, that describe the initial value and the steps of the     *)
(* auxiliary variable x.  This module chooses x to start at 0 and never     *)
(* change, then instantiates TwoPhase with those definitions.               *)
(*                                                                         *)
(* TLC configuration:                                                       *)
(*     SPECIFICATION Spec                                                   *)
(*     INVARIANT     Inv                                                    *)
(***************************************************************************)
EXTENDS Naturals

  ----------------------------- MODULE TwoPhase -----------------------------
  (*************************************************************************)
  (* The general two-phase handshake protocol.  A producer and a consumer   *)
  (* alternate steps: the producer may step when p = c, and the consumer    *)
  (* may step when p # c.  Each step also performs an XAct step on the      *)
  (* auxiliary state x, where the first argument identifies the stepper     *)
  (* (0 = producer, 1 = consumer).                                          *)
  (*************************************************************************)
  EXTENDS Naturals

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

  Inv == TypeOK
  ===========================================================================