MODULE CoffeeCan
EXTENDS Naturals

CONSTANT MAX

VARIABLES B, W, initW

(* --- Initialization ----------------------------------------------------- *)
Init == /\ B \in Nat
        /\ W \in Nat
        /\ B + W <= MAX
        /\ B + W >= 1
        /\ initW = W

(* --- Actions ------------------------------------------------------------ *)
BB == /\ B >= 2
      /\ B' = B - 1
      /\ W' = W
      /\ initW' = initW

BW == /\ B >= 1
      /\ W >= 1
      /\ B' = B - 1
      /\ W' = W
      /\ initW' = initW

WW == /\ W >= 2
      /\ B' = B + 1
      /\ W' = W - 2
      /\ initW' = initW

Next == BB \/ BW \/ WW

(* --- Safety Invariants ------------------------------------------------- *)
DecreaseTotal == [] ((B + W > 1) => (B' + W') = B + W - 1)

ParityInvariant == [] ((W mod 2) = (W' mod 2))

(* --- Liveness Properties ----------------------------------------------- *)
Termination == <> (B + W = 1)

FinalColor == <> (B + W = 1
                  /\ ((initW mod 2 = 0) => (B=1 /\ W=0))
                  /\ ((initW mod 2 = 1) => (B=0 /\ W=1)))

(* --- Specification ----------------------------------------------------- *)
Spec == Init
        /\ [][Next]_<<B,W,initW>>
        /\ WF(Next)

=============================================================================
END MODULE

