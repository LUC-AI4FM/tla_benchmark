MODULE GameOfLife
EXTENDS Naturals, TLC

CONSTANT N

VARIABLES grid

(* Set of positions on the N×N grid *)
Pos == { <<i,j>> : i \in 1..N /\ j \in 1..N }

(* Type invariant: grid is a function from Pos to BOOLEAN *)
TypeOK == grid \in [Pos -> BOOLEAN]

(* Helper: score of a cell (0 or 1) *)
sc(cell) == IF cell THEN 1 ELSE 0

(* Count live neighbors for a given position, treating out-of-bounds as dead *)
Score(pos) ==
  LET
    i == [pos]_1
    j == [pos]_2
    neighs == { <<i+dx, j+dy>> : dx \in {-1,0,1} /\ dy \in {-1,0,1} /\ (dx \/ dy) }
  IN Sum_{n \in neighs} IF n \in Pos THEN sc(grid[n]) ELSE 0

(* Next-state relation: update the entire grid simultaneously *)
Next ==
  LET newGrid == [pos \in Pos |-> 
                    IF Score(pos)=3 THEN TRUE
                    ELSE IF Score(pos)=2 THEN grid[pos]
                    ELSE FALSE ]
  IN grid' = newGrid

Init == TypeOK

Spec == Init /\ [] Next

THEOREM Spec => []TypeOK