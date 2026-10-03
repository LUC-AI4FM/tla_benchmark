```tla
------------------------------- MODULE FastMutualExclusion -------------------------------
VARIABLES x, y, b, S

CONSTANTS N

ASSUME N \in Nat /\ N > 0

Init == 
    /\ x = 0 
    /\ y = 0 
    /\ b = [p \in 1..N -> FALSE] 
    /\ S = [p \in 1..N -> {}]

Next ==
    \/ \E p \in 1..N : 
        (b[p] = FALSE) /\ 
        (\* Begin: *)
        (x' = p) /\
        (y' = y) /\
        (b' = [b EXCEPT ![p] = TRUE]) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = [S EXCEPT ![p] = S[p] \cup {x}])
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (\* Check: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p = y) /\ 
        (\* Enter: *)
        (x' = x) /\
        (y' = y) /\
        (b' = [b EXCEPT ![p] = FALSE]) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = [S EXCEPT ![p] = S[p] \cup {x}])
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
        (b' = b) /\
        (S' = S)
    \/ \E p \in 1..N : 
        (b[p] = TRUE) /\ 
        (p # y) /\ 
        (\* Wait: *)
        (x' = x) /\
        (y' = y) /\
       