---------------------------- MODULE GameOfLife ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE grid

TypeOK == (grid \in [1..N -> {<<0, 0>>, <<1, 0>>, <<2, 0>>, <<3, 0>>}])

LiveNeighbors(x, y) ==
  LET neighbors == {<<x', y'>> : x' \in {x-1, x, x+1} /\ y' \in {y-1, y, y+1}
                     /\ (x' # x \/ y' # y) /\ x' \in 1..N /\ y' \in 1..N}
  IN {<<x', y'>> : <<x', y'>> \in neighbors /\ grid[<<x', y'>>] = <<2, 0>>}

NextGrid(x, y) ==
  IF grid[<<x, y>>] = <<2, 0>>
  THEN IF Card(LiveNeighbors(x, y)) \in {2, 3}
       THEN <<2, 0>>
       ELSE <<1, 0>>
  ELSE IF Card(LiveNeighbors(x, y)) = 3
       THEN <<2, 0>>
       ELSE <<1, 0>>

Spec == 
  /\ TypeOK
  /\ [][ grid' = [grid EXCEPT !<<x, y>> = NextGrid(x, y) : x \in 1..N /\ y \in 1..N] ]

=============================================================================