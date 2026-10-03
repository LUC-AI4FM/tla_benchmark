------------------------------ MODULE FastMutex ------------------------------
EXTENDS Naturals

CONSTANTS N, defaultInitValue

VARIABLES x, y, b, j

(* Type invariants *)
TypeInv == /\ x \in Nat
          /\ y \in Nat
          /\ b \in [1..N -> BOOLEAN]
          /\ j \in [1..N -> {0,1,2,3}]

Init ==
    /\ x = defaultInitValue
    /\ y = defaultInitValue
    /\ b = [i \in 1..N |-> FALSE]
    /\ j = [i \in 1..N |-> 0]
    /\ TypeInv

(* Actions for process i *)
TryEnter(i) ==
    /\ j[i] = 0
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ j' = [j EXCEPT ![i] = 1]

SetY(i) ==
    (/\ j[i] = 1
     /\ y = 0
     /\ y' = i
     /\ j' = [j EXCEPT ![i] = 2])
 \/ (/\ j[i] = 1
     /\ y #= i
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ x' = 0
     /\ j' = [j EXCEPT ![i] = 0])

EnterCS(i) ==
    (/\ j[i] = 2
     /\ y = i
     /\ j' = [j EXCEPT ![i] = 3])
 \/ (/\ j[i] = 2
     /\ y #= i
     /\ b' = [b EXCEPT ![i] = FALSE]
     /\ x' = 0
     /\ j' = [j EXCEPT ![i] = 0])

ExitCS(i) ==
    /\ j[i] = 3
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ y' = 0
    /\ x' = 0
    /\ j' = [j EXCEPT ![i] = 0]

Next == \E i \in 1..N :
          (TryEnter(i) \/ SetY(i) \/ EnterCS(i) \/ ExitCS(i))

Spec ==
    Init
    /\ [][Next]_(<<x, y, b, j>>)
    /\ WF_vars(Next)

Invariant ==
    \A i, k \in 1..N :
        (i #= k) => ~(j[i] = 3 /\ j[k] = 3)

Liveness ==
    \E i \in 1..N : []<>(j[i] = 3)
=============================================================================