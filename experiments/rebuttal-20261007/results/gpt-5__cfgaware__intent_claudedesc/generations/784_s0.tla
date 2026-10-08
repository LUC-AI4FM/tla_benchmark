------------------------------ MODULE GameOfLife ------------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANT N

ASSUME N \in Nat \ {0}

(***************************************************************************)
(* State                                                                  *)
(***************************************************************************)

VARIABLES board

X == 1..N
Y == 1..N
Positions == X \X Y

vars == << board >>

(***************************************************************************)
(* Helpers                                                                *)
(***************************************************************************)

Deltas ==
  { <<di, dj>> \in (-1..1) \X (-1..1) : ~(di = 0 /\ dj = 0) }

Add(p, d) == << p[1] + d[1], p[2] + d[2] >>

LiveNeighbors(p, b) ==
  Cardinality({ d \in Deltas :
                  LET q == Add(p, d) IN q \in Positions /\ b[q] })

NextVal(p) ==
  IF board[p]
  THEN LiveNeighbors(p, board) \in {2, 3}
  ELSE LiveNeighbors(p, board) = 3

(***************************************************************************)
(* Initialization and Next-state relation                                  *)
(***************************************************************************)

Init == board \in [Positions -> BOOLEAN]

Next == board' = [ p \in Positions |-> NextVal(p) ]

(***************************************************************************)
(* Properties                                                             *)
(***************************************************************************)

TypeOK == board \in [Positions -> BOOLEAN]

Spec == Init /\ [][Next]_vars

=============================================================================