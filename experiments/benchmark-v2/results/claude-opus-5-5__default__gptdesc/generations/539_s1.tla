---------------------------- MODULE Session6funcMC ----------------------------
EXTENDS Naturals, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

-----------------------------------------------------------------------------
(* The algorithm imported from Session6func:                               *)
(*   a: while (i <= n) {                                                    *)
(*   b:    x[i] := i * i; i := i + 1 }                                      *)
-----------------------------------------------------------------------------

Init == /\ n \in 0..N
        /\ x = [k \in 0..n |-> 0]
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i <= n
           THEN pc' = "b"
           ELSE pc' = "Done"
     /\ UNCHANGED << n, x, i >>

b == /\ pc = "b"
     /\ x' = [x EXCEPT ![i] = i * i]
     /\ i' = i + 1
     /\ pc' = "a"
     /\ UNCHANGED n

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(a \/ b)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------
(* Model-checking predicates and invariants                                 *)
-----------------------------------------------------------------------------

Squares(m) == \A j \in 0..m : x[j] = j * j

PostCondition == (pc = "Done") => Squares(n)

TypeOK == /\ n \in Nat
          /\ x \in [0..n -> Nat]
          /\ i \in 0..(n + 1)
          /\ pc \in {"a", "b", "Done"}

Inv == /\ TypeOK
       /\ (pc = "a")    => /\ i \in 0..(n + 1)
                           /\ \A j \in 0..(i - 1) : x[j] = j * j
       /\ (pc = "b")    => /\ i \in 0..n
                           /\ \A j \in 0..(i - 1) : x[j] = j * j
       /\ (pc = "Done") => /\ i = n + 1
                           /\ Squares(n)

THEOREM Spec => [](TypeOK /\ Inv /\ PostCondition)
THEOREM Spec => Termination
=============================================================================