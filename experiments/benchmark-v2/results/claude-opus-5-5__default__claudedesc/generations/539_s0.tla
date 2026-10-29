---------------------------- MODULE MC_Session6func ----------------------------
EXTENDS Naturals, TLC

\* Model-checking configuration for the Session6func algorithm, which computes
\* the squares of 0..n into an array x. The base specification is inlined here
\* so that the module is self-contained.

CONSTANT NSet

ASSUME NSet \subseteq Nat

\* Model value for NSet used during model checking.
ConstNSet == {2, 7, 0}

VARIABLES n, x, i, pc

vars == << n, x, i, pc >>

-----------------------------------------------------------------------------
\* Base algorithm (Session6func)
\*
\*   variables n \in NSet, x = [j \in 0..n |-> 0], i = 0;
\*   a: while (i < n) {
\*        i := i + 1;
\*   b:   x[i] := x[i-1] + 2*i - 1;
\*      }

Init == /\ n \in NSet
        /\ x = [j \in 0..n |-> 0]
        /\ i = 0
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF i < n
           THEN /\ i' = i + 1
                /\ pc' = "b"
           ELSE /\ pc' = "Done"
                /\ i' = i
     /\ UNCHANGED << n, x >>

b == /\ pc = "b"
     /\ x' = [x EXCEPT ![i] = x[i-1] + 2*i - 1]
     /\ pc' = "a"
     /\ UNCHANGED << n, i >>

Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

-----------------------------------------------------------------------------
\* Invariants

TypeOK == /\ n \in Nat
          /\ x \in [0..n -> 0..(n*n)]
          /\ i \in 0..n
          /\ pc \in {"a", "b", "Done"}

SquareCorrect == (pc = "Done") => \A j \in 0..n : x[j] = j * j

ReachableStateInv ==
    /\ (pc = "a") => x[i] = i * i
    /\ (pc = "b") => /\ i > 0
                     /\ x[i-1] = (i-1) * (i-1)
    /\ (pc = "Done") => /\ \A j \in 0..n : x[j] = j * j
                        /\ i = n

=============================================================================