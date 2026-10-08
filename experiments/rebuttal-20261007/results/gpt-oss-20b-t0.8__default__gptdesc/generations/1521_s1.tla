------------------------------ MODULE CoffeeCan ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS MAX, InitialBlack, InitialWhite
VARIABLE beans

(* ------------------------------------------------------------------------- *)
(* Initial state *)
Init == 
    /\ beans = [black |-> InitialBlack, white |-> InitialWhite]

(* ------------------------------------------------------------------------- *)
(* Actions *)

TwoBlack ==
    /\ beans.black >= 2
    /\ beans'.black = beans.black - 1
    /\ beans'.white = beans.white

TwoWhite ==
    /\ beans.white >= 2
    /\ beans'.black = beans.black + 1
    /\ beans'.white = beans.white - 2

OneEach ==
    /\ beans.black >= 1
    /\ beans.white >= 1
    /\ beans'.black = beans.black - 1
    /\ beans'.white = beans.white

Stutter ==
    /\ beans.black + beans.white = 1
    /\ beans' = beans

Next == TwoBlack \/ TwoWhite \/ OneEach \/ Stutter

(* ------------------------------------------------------------------------- *)
(* Invariants *)

TypeInvariant ==
    /\ beans.black \in 0..MAX
    /\ beans.white \in 0..MAX

ParityInvariant ==
    /\ (beans.white MOD 2) = (InitialWhite MOD 2)

TotalBounded ==
    /\ (beans.black + beans.white) <= MAX

(* ------------------------------------------------------------------------- *)
(* Final state according to parity hypothesis *)

FinalState ==
    ((InitialWhite MOD 2 = 0) /\ (beans.black + beans.white = 1) /\ (beans.black = 1)) \/
    ((InitialWhite MOD 2 = 1) /\ (beans.black + beans.white = 1) /\ (beans.white = 1))

(* ------------------------------------------------------------------------- *)
(* Specification *)

Spec ==
    Init
    /\ [][Next]_beans
    /\ WF/ENABLED (TwoBlack \/ TwoWhite \/ OneEach)
    /\ TypeInvariant
    /\ ParityInvariant
    /\ TotalBounded
    /\ EVENTUALLY FinalState

=============================================================================