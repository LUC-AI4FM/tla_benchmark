MODULE RingAlg
EXTENDS Naturals, TLC

CONSTANT N \in Nat

VARIABLES x, y, pc

(* Left neighbor function *)
L(i) == IF i = 1 THEN N ELSE i-1

TypeInv ==
    /\ x \in [1..N -> BOOLEAN]
    /\ y \in [1..N -> BOOLEAN]
    /\ pc \in [1..N -> {0,1,2}]
    /\ N > 0

Init ==
    /\ TypeInv
    /\ x = [i \in 1..N |-> FALSE]
    /\ y = [i \in 1..N |-> FALSE]
    /\ pc = [i \in 1..N |-> 0]

Next ==
    \E i \in 1..N :
          (pc[i] = 0
           /\ x' = [x EXCEPT ![i] = TRUE]
           /\ y' = y
           /\ pc' = [pc EXCEPT ![i] = 1])
        \/ (pc[i] = 1
            /\ y' = [y EXCEPT ![i] = x[L(i)]]
            /\ x' = x
            /\ pc' = [pc EXCEPT ![i] = 2])
        \/ (pc[i] = 2
            /\ UNCHANGED <<x, y, pc>>)

vars == <<x, y, pc>>

Inv ==
    /\ TypeInv
    /\ \A i \in 1..N : (pc[i] >= 1) => x[i] = TRUE

SafetyInvariant ==
    [] ((\A i \in 1..N : pc[i] = 2) => (\E j \in 1..N : y[j] = TRUE))

Termination ==
    <> (\A i \in 1..N : pc[i] = 2)

Spec == Init /\ [][Next]_vars /\ Termination

THEOREM Inv_Is_Invariant:
    Spec => []Inv
(* Proof omitted *)

THEOREM Safety_Theorem:
    Spec => SafetyInvariant
(* Proof omitted *)

END RingAlg