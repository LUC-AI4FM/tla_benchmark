------------------------------ MODULE DieHard ------------------------------
EXTENDS Naturals, TLC

(*--------------------------------------------------------------------------*)
(* CONSTANTS *)
CONSTANTS SmallCap, BigCap          \* Capacities of the small and big jugs.
(* Example values for the configuration: SmallCap = 3, BigCap = 5 *)

(*--------------------------------------------------------------------------*)
(* VARIABLES *)
VARIABLES smallJug, bigJug, totalDrawn

(*--------------------------------------------------------------------------*)
(* TYPE INVARIANT *)
TypeInvariant == 
    /\ smallJug \in 0..SmallCap
    /\ bigJug   \in 0..BigCap

(*--------------------------------------------------------------------------*)
(* INITIAL STATE *)
Init ==
    /\ smallJug = 0
    /\ bigJug   = 0
    /\ totalDrawn = 0
    /\ TypeInvariant

(*--------------------------------------------------------------------------*)
(* ACTIONS *)

FillSmall == 
    /\ smallJug' = SmallCap
    /\ bigJug'   = bigJug
    /\ totalDrawn' = totalDrawn + SmallCap
    /\ smallJug' \in 0..SmallCap
    /\ bigJug'   \in 0..BigCap

EmptySmall ==
    /\ smallJug' = 0
    /\ bigJug'   = bigJug
    /\ totalDrawn' = totalDrawn
    /\ smallJug' \in 0..SmallCap
    /\ bigJug'   \in 0..BigCap

FillBig == 
    /\ bigJug' = BigCap
    /\ smallJug' = smallJug
    /\ totalDrawn' = totalDrawn + BigCap
    /\ smallJug' \in 0..SmallCap
    /\ bigJug'   \in 0..BigCap

EmptyBig ==
    /\ bigJug' = 0
    /\ smallJug' = smallJug
    /\ totalDrawn' = totalDrawn
    /\ smallJug' \in 0..SmallCap
    /\ bigJug'   \in 0..BigCap

PourSmallToBig == 
    LET transfer == MIN(smallJug, BigCap - bigJug) IN
    /\ smallJug' = smallJug - transfer
    /\ bigJug'   = bigJug + transfer
    /\ totalDrawn' = totalDrawn
    /\ smallJug' \in 0..SmallCap
    /\ bigJug'   \in 0..BigCap

PourBigToSmall == 
    LET transfer == MIN(bigJug, SmallCap - smallJug) IN
    /\ bigJug'   = bigJug - transfer
    /\ smallJug' = smallJug + transfer
    /\ totalDrawn' = totalDrawn
    /\ smallJug' \in 0..SmallCap
    /\ bigJug'   \in 0..BigCap

(*--------------------------------------------------------------------------*)
(* NEXT STATE *)
Next == 
    \/ FillSmall
    \/ EmptySmall
    \/ FillBig
    \/ EmptyBig
    \/ PourSmallToBig
    \/ PourBigToSmall

(*--------------------------------------------------------------------------*)
(* SPECIFICATION *)
Spec == Init /\ [][Next]_<<smallJug, bigJug, totalDrawn>>

(*--------------------------------------------------------------------------*)
(* PREDICATES FOR ANALYSIS *)

BigJugFour == (bigJug = 4)

BothChanged ==
    /\ smallJug' != smallJug
    /\ bigJug'   != bigJug

=============================================================================