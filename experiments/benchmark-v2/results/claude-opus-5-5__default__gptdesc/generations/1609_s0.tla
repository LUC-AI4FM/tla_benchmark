------------------------------- MODULE QuickSort -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

(***************************************************************************)
(* PermsOf(Arr) is the set of all permutations of the array Arr.           *)
(***************************************************************************)
PermsOf(Arr) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

(***************************************************************************)
(* Partitions(I, p, Arr) is the set of permutations B of Arr that leave    *)
(* elements outside the index set I unchanged and such that every element  *)
(* of B at an index in I at or before p is less than or equal to every     *)
(* element of B at an index in I after p.                                  *)
(***************************************************************************)
Partitions(I, p, Arr) ==
  { B \in PermsOf(Arr) :
      /\ \A i \in (DOMAIN Arr) \ I : B[i] = Arr[i]
      /\ \A i, j \in I : (i =< p) /\ (p < j) => (B[i] =< B[j]) }

IsSorted(Arr) == \A i \in 1..(ArrayLen - 1) : Arr[i] =< Arr[i+1]

(***************************************************************************
--algorithm QuickSort {
  variables A \in [1..ArrayLen -> 1..ArrayLen] ;
            A0 = A ;

  procedure QS(lo = 0, hi = 0)
    variable pivot = 0 ; {
    qs1: if (lo < hi) {
           with (piv \in lo..(hi-1)) {
             pivot := piv ;
             with (Ap \in Partitions(lo..hi, piv, A)) { A := Ap }
           } ;
    qs2:   call QS(lo, pivot) ;
    qs3:   call QS(pivot + 1, hi)
         } ;
    qs4: return
  }

  {
    main: call QS(1, ArrayLen) ;
    test: assert A \in PermsOf(A0) /\ IsSorted(A)
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES A, A0, pc, stack, lo, hi, pivot

vars == << A, A0, pc, stack, lo, hi, pivot >>

Init == /\ A \in [1..ArrayLen -> 1..ArrayLen]
        /\ A0 = A
        /\ lo = 0
        /\ hi = 0
        /\ pivot = 0
        /\ stack = << >>
        /\ pc = "main"

qs1 == /\ pc = "qs1"
       /\ IF lo < hi
            THEN /\ \E piv \in lo..(hi-1) :
                      /\ pivot' = piv
                      /\ \E Ap \in Partitions(lo..hi, piv, A) :
                            A' = Ap
                 /\ pc' = "qs2"
            ELSE /\ pc' = "qs4"
                 /\ UNCHANGED << A, pivot >>
       /\ UNCHANGED << A0, stack, lo, hi >>

qs2 == /\ pc = "qs2"
       /\ /\ lo' = lo
          /\ hi' = pivot
          /\ stack' = << [ procedure |-> "QS",
                           pc        |-> "qs3",
                           pivot     |-> pivot,
                           lo        |-> lo,
                           hi        |-> hi ] >>
                       \o stack
       /\ pivot' = 0
       /\ pc' = "qs1"
       /\ UNCHANGED << A, A0 >>

qs3 == /\ pc = "qs3"
       /\ /\ lo' = pivot + 1
          /\ hi' = hi
          /\ stack' = << [ procedure |-> "QS",
                           pc        |-> "qs4",
                           pivot     |-> pivot,
                           lo        |-> lo,
                           hi        |-> hi ] >>
                       \o stack
       /\ pivot' = 0
       /\ pc' = "qs1"
       /\ UNCHANGED << A, A0 >>

qs4 == /\ pc = "qs4"
       /\ pc' = Head(stack).pc
       /\ pivot' = Head(stack).pivot
       /\ lo' = Head(stack).lo
       /\ hi' = Head(stack).hi
       /\ stack' = Tail(stack)
       /\ UNCHANGED << A, A0 >>

QS == qs1 \/ qs2 \/ qs3 \/ qs4

main == /\ pc = "main"
        /\ /\ lo' = 1
           /\ hi' = ArrayLen
           /\ stack' = << [ procedure |-> "QS",
                            pc        |-> "test",
                            pivot     |-> pivot,
                            lo        |-> lo,
                            hi        |-> hi ] >>
                        \o stack
        /\ pivot' = 0
        /\ pc' = "qs1"
        /\ UNCHANGED << A, A0 >>

test == /\ pc = "test"
        /\ Assert(A \in PermsOf(A0) /\ IsSorted(A),
                  "Failure of assertion at line test.")
        /\ pc' = "Done"
        /\ UNCHANGED << A, A0, stack, lo, hi, pivot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == QS \/ main \/ test \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: when the algorithm is done, A is a sorted permutation of A0.    *)
(***************************************************************************)
TypeOK == /\ A \in [1..ArrayLen -> 1..ArrayLen]
          /\ A0 \in [1..ArrayLen -> 1..ArrayLen]
          /\ pc \in {"main", "qs1", "qs2", "qs3", "qs4", "test", "Done"}

PartialCorrectness == (pc = "Done") => (A \in PermsOf(A0) /\ IsSorted(A))

THEOREM Spec => [](TypeOK /\ PartialCorrectness)
THEOREM Spec => Termination
=============================================================================