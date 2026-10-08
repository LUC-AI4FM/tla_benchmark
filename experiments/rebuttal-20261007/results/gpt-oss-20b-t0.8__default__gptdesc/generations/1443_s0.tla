---------------------------- MODULE SmallSM ----------------------------
EXTENDS Naturals, TLC

VARIABLE x

(* Helper predicates *)
IsOne == (x = 1)
Done   == (x = 2)

WrapTransition ==
    /\ x' = 0
    /\ x = 2

Init == 
    /\ x = 0

Next ==
    \/ x' = (x + 1) MOD 3
    \/ x' = x        (* stuttering *)

Spec == Init /\ [] Next

(* Invariant that x always stays within {0,1,2} *)
Inv == x \in {0,1,2}
Safety == Inv

(* Coverage checks *)
COVER (x = 1) BY "IsOne"
COVER (x = 2) BY "Done"
COVER ((x' = 0) /\ (x = 2)) BY "Wrap"

CoverCheck ==
    TLCGet("IsOne") = 1
    /\ TLCGet("Done") = 1
    /\ TLCGet("Wrap") = 1

THEOREM CoverCheckSpec == Spec => [] CoverCheck

=============================================================================