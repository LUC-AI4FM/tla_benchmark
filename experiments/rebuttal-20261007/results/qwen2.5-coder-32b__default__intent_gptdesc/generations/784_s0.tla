------------------------------- MODULE ConwayGameOfLife -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, WRAPPING \* WRAPPING is a boolean indicating toroidal topology

VARIABLES grid

Init == /\ grid \in [1..N -> 1..N -> BOOLEAN]
      /\ \/ WRAPPING
         \/ \A i \in 1..N, j \in 1..N: 
              LET neighbors == {grid[i'][j'] : i' \in (i-1)..(i+1), j' \in (j-1)..(j+1) \ {i,j}}
              IN \/ grid[i][j] = FALSE
                 \/ Cardinality({b \in neighbors: b}) \in {2, 3}

Next == /\ \E newGrid \in [1..N -> 1..N -> BOOLEAN]:
            /\ \A i \in 1..N, j \in 1..N:
                LET liveNeighbors ==
                    IF WRAPPING THEN
                        Cardinality({grid[i' % N + (i' < 0 ? N : 0)][j' % N + (j' < 0 ? N : 0)] :
                                     i' \in {i-1, i, i+1}, j' \in {j-1, j, j+1} \ {(i,j)})
                    ELSE
                        Cardinality({grid[i'][j'] : i' \in (i-1)..(i+1), j' \in (j-1)..(j+1) \ {(i,j)},
                                     grid[i'][j'] = TRUE})
                IN newGrid[i][j] =
                   IF grid[i][j] THEN liveNeighbors \in {2, 3}
                   ELSE liveNeighbors = 3
            /\ grid' = newGrid

Spec == Init /\ [][Next]_<<grid>>

TypeCorrectness == \A i \in 1..N, j \in 1..N: grid[i][j] \in BOOLEAN

UpdateDeterminism ==
    \A s, s' \in [1..N -> 1..N -> BOOLEAN]:
        /\ s = [EXCEPT ![grid |-> s]]
        /\ s' = [EXCEPT ![grid |-> s']]
        => \/ s' /= Next
           \/ \A i \in 1..N, j \in 1..N:
                LET liveNeighbors ==
                    IF WRAPPING THEN
                        Cardinality({s[i' % N + (i' < 0 ? N : 0)][j' % N + (j' < 0 ? N : 0)] :
                                     i' \in {i-1, i, i+1}, j' \in {j-1, j, j+1} \ {(i,j)})
                    ELSE
                        Cardinality({s[i'][j'] : i' \in (i-1)..(i+1), j' \in (j-1)..(j+1) \ {(i,j)},
                                     s[i'][j'] = TRUE})
                IN s'[i][j] =
                   IF s[i][j] THEN liveNeighbors \in {2, 3}
                   ELSE liveNeighbors = 3

Invariance == \A i \in 1..N, j \in 1..N: grid[i][j] \in BOOLEAN

Conservation ==
    /\ \A stillLife \in [1..N -> 1..N -> BOOLEAN]:
        /\ \A i \in 1..N, j \in 1..N:
            LET liveNeighbors ==
                IF WRAPPING THEN
                    Cardinality({stillLife[i' % N + (i' < 0 ? N : 0)][j' % N + (j' < 0 ? N : 0)] :
                                 i' \in {i-1, i, i+1}, j' \in {j-1, j, j+1} \ {(i,j)})
                ELSE
                    Cardinality({stillLife[i'][j'] : i' \in (i-1)..(i+1), j' \in (j-1)..(j+1) \ {(i,j)},
                                 stillLife[i'][j'] = TRUE})
            IN \/ stillLife[i][j] /\ liveNeighbors \in {2, 3}
               \/ ~stillLife[i][j] /\ liveNeighbors /= 3
        => [][grid' = stillLife]_<<grid>>
    /\ \A oscillator \in [1..N -> 1..N -> BOOLEAN], period \in Nat \ {0}:
        /\ \A i \in 1..N, j \in 1..N:
            LET liveNeighbors ==
                IF WRAPPING THEN
                    Cardinality({oscillator[i' % N + (i' < 0 ? N : 0)][j' % N + (j' < 0 ? N : 0)] :
                                 i' \in {i-1, i, i+1}, j' \in {j-1, j, j+1} \ {(i,j)})
                ELSE
                    Cardinality({oscillator[i'][j'] : i' \in (i-1)..(i+1), j' \in (j-1)..(j+1) \ {(i,j)},
                                 oscillator[i'][j'] = TRUE})
            IN \/ oscillator[i][j] /\ liveNeighbors \in {2, 3}
               \/ ~oscillator[i][j] /\ liveNeighbors /= 3
        => <>(\E k \in 0..period: grid' = [EXCEPT ![grid |-> <<k>>[oscillator]]])_<<grid>>
    /\ \A glider \in [1..N -> 1..N -> BOOLEAN], period \in Nat \ {0}, dx, dy \in -1..1:
        /\ \A i \in 1..N, j \in 1..N:
            LET liveNeighbors ==
                IF WRAPPING THEN
                    Cardinality({glider[i' % N + (i' < 0 ? N : 0)][j' % N + (j' < 0 ? N : 0)] :
                                 i' \in {i-1, i, i+1}, j' \in {j-1, j, j+1} \ {(i,j)})
                ELSE
                    Cardinality({glider[i'][j'] : i' \in (i-1)..(i+1), j' \in (j-1)..(j+1) \ {(i,j)},
                                 glider[i'][j'] = TRUE})
            IN \/ glider[i][j] /\ liveNeighbors \in {2, 3}
               \/ ~glider[i][j] /\ liveNeighbors /= 3
        => <>(\E k \in 0..period: grid' = [EXCEPT ![grid |-> <<k>>[glider]]])_<<grid>>

Progress ==
    [](<>[](\E s \in [1..N -> 1..N -> BOOLEAN]: grid' = s))_<<grid>>

Fairness == WF_vars(Next, {grid})

THEOREM Spec => []TypeCorrectness
THEOREM Spec => []UpdateDeterminism
THEOREM Spec => []Invariance
THEOREM Spec => []Conservation
THEOREM Spec => <>Progress

=============================================================================