```tla
---- MODULE GameOfLife ----
EXTENDS Naturals

CONSTANT N

VARIABLES grid

(* Type invariant *)
TypeOK == /\ grid \in [1..N -> [1..N -> BOOLEAN]]

(* Initial state: any assignment of booleans to each cell *)
Init == TypeOK

(* Helper function: contribution from a cell at (i,j) *)
sc(i, j) ==
  IF i \in 1..N /\ j \in 1..N THEN
      IF grid[i][j] THEN 1 ELSE 0
  ELSE 0

(* Count live neighbors of cell (i,j) *)
score(i, j) ==
  SUM <<di, dj>> \in {<<-1,-1>>, <<-1,0>>, <<-1,1>>,
                      <<0,-1>>,          <<0,1>>,
                      <<1,-1>>,  <<1,0>>,  <<1,1>>} :
      sc(i + di, j + dj)

(* Next-state relation *)
Next ==
  /\ grid' = [i \in 1..N |-> [j \in 1..N |
        IF grid[i][j] THEN score(i,j) \in {2,3}
        ELSE score(i,j) = 3]]

vars == {grid}

Spec == Init /\ [] [Next]_vars

(* Optional invariant *)
Inv == TypeOK
```