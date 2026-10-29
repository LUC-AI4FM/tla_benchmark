------------------------------ MODULE Quicksort ------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen
ASSUME ArrayLen \in Nat

CONSTANT defaultInitValue

(***************************************************************************)
(* PermsOf(Arr) is the set of all permutations of the array Arr.           *)
(***************************************************************************)
PermsOf(Arr) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

(***************************************************************************)
(* Partitions(B, pvt, lo, hi) is the set of permutations C of B that keep  *)
(* elements outside lo..hi unchanged and in which every value at or before *)
(* pvt in lo..hi is <= every value after pvt in lo..hi.                    *)
(***************************************************************************)
Partitions(B, pvt, lo, hi) ==
  { C \in PermsOf(B) :
      /\ \A i \in (1..ArrayLen) \ (lo..hi) : C[i] = B[i]
      /\ \A i \in lo..pvt, j \in (pvt+1)..hi : C[i] <= C[j] }

IsSorted(B) == \A i, j \in 1..ArrayLen : i < j => B[i] <= B[j]

(***************************************************************************
--algorithm Quicksort {
  variables A \in [1..ArrayLen -> 1..ArrayLen], Ainit = A;

  procedure QS(qlo, qhi)
    variable pivot = 1;
  {
    qs1: if (qlo < qhi) {
           with (piv \in qlo..(qhi-1)) {
             pivot := piv;
             A :\in Partitions(A, piv, qlo, qhi)
           };
    qs2:   call QS(qlo, pivot);
    qs3:   call QS(pivot+1, qhi)
         };
    qs4: return
  }

  {
    main: call QS(1, ArrayLen);
    test: assert A \in PermsOf(Ainit) /\ IsSorted(A)
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES A, Ainit, pc, stack, qlo, qhi, pivot

vars == << A, Ainit, pc, stack, qlo, qhi, pivot >>

Init == /\ A \in [1..ArrayLen -> 1..ArrayLen]
        /\ Ainit = A
        /\ qlo = defaultInitValue
        /\ qhi = defaultInitValue
        /\ pivot = 1
        /\ stack = << >>
        /\ pc = "main"

qs1 == /\ pc = "qs1"
       /\ IF qlo < qhi
             THEN /\ \E piv \in qlo..(qhi-1):
                       /\ pivot' = piv
                       /\ A' \in Partitions(A, piv, qlo, qhi)
                  /\ pc' = "qs2"
             ELSE /\ pc' = "qs4"
                  /\ UNCHANGED << A, pivot >>
       /\ UNCHANGED << Ainit, stack, qlo, qhi >>

qs2 == /\ pc = "qs2"
       /\ qlo' = qlo
       /\ qhi' = pivot
       /\ stack' = << [ procedure |-> "QS",
                        pc        |-> "qs3",
                        pivot     |-> pivot,
                        qlo       |-> qlo,
                        qhi       |-> qhi ] >>
                    \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << A, Ainit >>

qs3 == /\ pc = "qs3"
       /\ qlo' = pivot + 1
       /\ qhi' = qhi
       /\ stack' = << [ procedure |-> "QS",
                        pc        |-> "qs4",
                        pivot     |-> pivot,
                        qlo       |-> qlo,
                        qhi       |-> qhi ] >>
                    \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << A, Ainit >>

qs4 == /\ pc = "qs4"
       /\ pc' = Head(stack).pc
       /\ pivot' = Head(stack).pivot
       /\ qlo' = Head(stack).qlo
       /\ qhi' = Head(stack).qhi
       /\ stack' = Tail(stack)
       /\ UNCHANGED << A, Ainit >>

QS == qs1 \/ qs2 \/ qs3 \/ qs4

main == /\ pc = "main"
        /\ qlo' = 1
        /\ qhi' = ArrayLen
        /\ stack' = << [ procedure |-> "QS",
                         pc        |-> "test",
                         pivot     |-> pivot,
                         qlo       |-> qlo,
                         qhi       |-> qhi ] >>
                     \o stack
        /\ pivot' = 1
        /\ pc' = "qs1"
        /\ UNCHANGED << A, Ainit >>

test == /\ pc = "test"
        /\ Assert(A \in PermsOf(Ainit) /\ IsSorted(A),
                  "Failure of assertion at line test.")
        /\ pc' = "Done"
        /\ UNCHANGED << A, Ainit, stack, qlo, qhi, pivot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == QS \/ main \/ test \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

(***************************************************************************)
(* Safety: when the algorithm is done, A is a sorted permutation of Ainit. *)
(***************************************************************************)
Correctness == (pc = "Done") => (A \in PermsOf(Ainit) /\ IsSorted(A))

=============================================================================