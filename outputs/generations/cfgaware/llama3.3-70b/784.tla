```
MODULE GameOfLife
VARIABLE grid

Constant N

TypeOK == grid \in [1..N -> BOOLEAN]

LiveNeighbors(x, y) ==
  LET neighbors == {<<x', y'>> : x' \in {x-1, x, x+1} /\ y' \in {y-1, y, y+1}
                     /\ (x' # x \/ y' # y)
                     /\ x' >= 1 /\ x' <= N
                     /\ y' >= 1 /\ y' <= N}
  IN Sum({grid[<<x', y'>>] : <<x', y'>> \in neighbors})

Sum(S) == IF S = {} THEN 0 ELSE LET s == CHOOSE x \in S : TRUE
                                  IN x + Sum(S \ {s})

Next ==
  /\ grid' = [x \in 1..N, y \in 1..N |-> 
              IF grid[<<x, y>>] 
              THEN (LiveNeighbors(x, y) = 2 \/ LiveNeighbors(x, y) = 3)
              ELSE LiveNeighbors(x, y) = 3]
  /\ UNCHANGED << >>

Spec == Init /\ [][Next]_grid

Init == grid = [x \in 1..N, y \in 1..N |-> FALSE]

THEOREM Spec => []TypeOK
```
Note: The `UNCHANGED` operator is used to specify that no other variables are changed in the next-state relation. However, since there's only one variable (`grid`) in this specification, it could be omitted without changing the meaning of the spec. It has been included here for clarity and consistency with typical TLA+ specifications.