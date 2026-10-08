MODULE StoneCutting
EXTENDS Naturals, Sequences, TLC, SETS

CONSTANTS W, N

VARIABLE solution

(* --------------------------------------------------------------------- *)
(* Helper: all possible ordered partitions of n pieces summing to w     *)
Partitions(n,w) ==
    IF n = 0 THEN
        IF w = 0 THEN { <> } ELSE {}
    ELSE
        \E first \in 1..W :
            (first <= w) /\ 
            \E rest \in Partitions(n-1, w - first) : rest ^ <<first>>

(* --------------------------------------------------------------------- *)
(* Set of possible coefficients on the scale                             *)
CoeffsSet == {-1,0,1}

(* --------------------------------------------------------------------- *)
(* A partition can balance every weight 1..W using coefficients in      *)
(* {-1,0,1}                                                             *)
Balanced(p) ==
    \A t \in 1..W :
        \E coeffs \in {c \in Seq(CoeffsSet) : Len(c) = Len(p)} :
            (\sum i \in 1..Len(p) : coeffs[i] * p[i]) = t

(* --------------------------------------------------------------------- *)
(* Initial state: solution may be any valid partition                     *)
Init == solution \in Union(Partitions(N,W))

(* No change in the system                                                 *)
Next == solution' = solution

(* Full specification                                                     *)
Spec == Init /\ []Next

(* --------------------------------------------------------------------- *)
(* Safety invariant: all partitions considered are of correct length and *)
(* sum                                                               *)
SafetyInvariant ==
    \A p \in Partitions(N, W) :
        Len(p) = N /\ (\sum i \in 1..N : p[i]) = W

(* Ensure the safety invariant holds in every state                      *)
Spec == Init /\ []Next /\ SafetyInvariant

(* --------------------------------------------------------------------- *)
(* Liveness property: eventually either a solution is found or we know    *)
(* that none exists (handled by the ASSUME formulas below)               *)

ASSUME
    \E p \in Partitions(N, W) :
        Balanced(p) /\ PrintT("solution", p)

ASSUME
    ~(\E p \in Partitions(N, W) : Balanced(p)) =>
        PrintT("no solution", TRUE)
===============================================================================