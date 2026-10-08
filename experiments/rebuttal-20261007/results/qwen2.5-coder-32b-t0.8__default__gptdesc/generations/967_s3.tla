```tla
MODULE BalanceScale

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS W, N

VARIABLES pieces, target, coefficients

Init == 
  /\ pieces = << >>
  /\ target = 1

Next ==
  \/ /\ Len(pieces) < N
     /\ \E p \in 1..W - Sum(pieces): 
          /\ p > 0
          /\ pieces' = Append(pieces, p)
          /\ coefficients' = << >> 
          /\ target' = target
  \/ /\ Len(pieces) = N
     /\ target <= W
     /\ coefficients' \in [1..Len(pieces) -> {-1, 0, 1}]
     /\ Sum(<< i \in 1..Len(pieces): pieces[i] * coefficients'[i] >>) = target
     /\ target' = target + 1
     /\ pieces' = pieces

Spec ==
  Init /\ [][Next]_<<pieces, target, coefficients>> /\ WF_next(<<pieces, target, coefficients>>)

WF_next(vars) == 
  \A s \in vars: \/ Len(s.pieces) < N
                  \/ /\ Len(s.pieces) = N
                     /\ \E coeffs \in [1..Len(s.pieces) -> {-1, 0, 1}]: Sum(<< i \in 1..Len(s.pieces): s.pieces[i] * coeffs[i] >>) = s.target

Invariants ==
  /\ Len(pieces) <= N
  /\ Sum(pieces) <= W
  /\ target >= 1
  /\ target <= W + 1

Liveness ==
  \/ target > W
  \/ \E coeffs \in [1..N -> {-1, 0, 1}]: 
       /\ Sum(<< i \in 1..N: pieces[i] * coeffs[i] >>) = W

CONSTRAINT Invariants
ASSUME Liveness

Fairness ==
  WF_next(<<pieces, target, coefficients>>)

====

\* TLC-oriented ASSUME formulas with PrintT to search for and display a solution or report that no solution exists.
ASSUME \/ \E s \in StateSets : s.target = W + 1
       /\ PrintT("Solution found:", << i \in 1..N: pieces[i] * coefficients[i] >>)
       \/ \A s \in StateSets : s.target <= W
          /\ PrintT("No solution exists")
```