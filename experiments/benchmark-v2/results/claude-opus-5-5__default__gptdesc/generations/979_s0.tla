---------------------------- MODULE MCTwoPhase ----------------------------
(***************************************************************************)
(* A small wrapper around the TwoPhase specification.  It declares the     *)
(* variables p, c, and x, and defines the two helper operators XInit and   *)
(* XAct, which instantiate the constant parameters of module TwoPhase.     *)
(* XInit requires its argument to equal 0, and XAct is a trivial           *)
(* next-state relation that sets xNext equal to xInit.                     *)
(***************************************************************************)
EXTENDS Naturals

VARIABLES p, c, x

vars == << p, c, x >>

(***************************************************************************)
(* Initial-state predicate for x: its argument must equal 0.               *)
(***************************************************************************)
XInit(v) == v = 0

(***************************************************************************)
(* Trivial action on x: the new value equals the old value.  The first     *)
(* argument identifies the phase or process (0 for producer, 1 for         *)
(* consumer) and is ignored here.                                          *)
(***************************************************************************)
XAct(i, xInit, xNext) == xNext = xInit

(***************************************************************************)
(* Instantiate TwoPhase.  The constants XInit, XAct and the variables      *)
(* p, c, x are substituted implicitly by the identically named             *)
(* definitions and variables of this module.                               *)
(***************************************************************************)
TP == INSTANCE TwoPhase

(***************************************************************************)
(* Local Init, Next, and Spec, written in terms of the helper operators.   *)
(* These mirror the two-phase handshake: the producer acts when p = c,     *)
(* the consumer acts when p # c.                                           *)
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

=============================================================================