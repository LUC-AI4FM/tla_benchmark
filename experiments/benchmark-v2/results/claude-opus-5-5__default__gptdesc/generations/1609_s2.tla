------------------------------ MODULE QuickSort ------------------------------
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
(* Partitions(B, pivot, lo, hi) is the set of arrays that are permutations *)
(* of B, leave elements outside lo..hi unchanged, and partition lo..hi so  *)
(* that every value at or before pivot is <= every value after pivot.      *)
(***************************************************************************)
Partitions(B, pivot, lo, hi) ==
  { C \in PermsOf(B) :
      /\ \A i \in (1..(lo-1)) \cup ((hi+1)..Len(B)) : C[i] = B[i]
      /\ \A i \in lo..pivot, j \in (pivot+1)..hi : C[i] <= C[j] }

IsSorted(B) == \A i, j \in DOMAIN B : (i < j) => (B[i] <= B[j])

(***************************************************************************
--algorithm QuickSort {
  variables Ainit \in [1..ArrayLen -> 1..ArrayLen] ; A = Ainit ;

  procedure QS(lo = 1, hi = 1)
    variable pivot = 1 ;
  {
    qs1: if (lo < hi) {
           with (piv \in lo..(hi-1)) {
             pivot := piv ;
             with (Ap \in Partitions(A, piv, lo, hi)) { A := Ap }
           } ;
    qs2:   call QS(lo, pivot) ;
    qs3:   call QS(pivot+1, hi)
         } ;
    qs4: return
  }

  {
    main: call QS(1, ArrayLen) ;
    test: assert A \in PermsOf(Ainit) /\ IsSorted(A)
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES Ainit, A, pc, stack, lo, hi, pivot

vars == << Ainit, A, pc, stack, lo, hi, pivot >>

Init == /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]
        /\ A = Ainit
        /\ lo = 1
        /\ hi = 1
        /\ pivot = 1
        /\ stack = << >>
        /\ pc = "main"

qs1 == /\ pc = "qs1"
       /\ IF lo < hi
            THEN /\ \E piv \in lo..(hi-1) :
                      /\ pivot' = piv
                      /\ \E Ap \in Partitions(A, piv, lo, hi) : A' = Ap
                 /\ pc' = "qs2"
            ELSE /\ pc' = "qs4"
                 /\ UNCHANGED << A, pivot >>
       /\ UNCHANGED << Ainit, stack, lo, hi >>

qs2 == /\ pc = "qs2"
       /\ lo' = lo
       /\ hi' = pivot
       /\ stack' = << [ procedure |-> "QS",
                        pc        |-> "qs3",
                        pivot     |-> pivot,
                        lo        |-> lo,
                        hi        |-> hi ] >> \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << Ainit, A >>

qs3 == /\ pc = "qs3"
       /\ lo' = pivot + 1
       /\ hi' = hi
       /\ stack' = << [ procedure |-> "QS",
                        pc        |-> "qs4",
                        pivot     |-> pivot,
                        lo        |-> lo,
                        hi        |-> hi ] >> \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << Ainit, A >>

qs4 == /\ pc = "qs4"
       /\ pc' = Head(stack).pc
       /\ pivot' = Head(stack).pivot
       /\ lo' = Head(stack).lo
       /\ hi' = Head(stack).hi
       /\ stack' = Tail(stack)
       /\ UNCHANGED << Ainit, A >>

QS == qs1 \/ qs2 \/ qs3 \/ qs4

main == /\ pc = "main"
        /\ lo' = 1
        /\ hi' = ArrayLen
        /\ stack' = << [ procedure |-> "QS",
                         pc        |-> "test",
                         pivot     |-> pivot,
                         lo        |-> lo,
                         hi        |-> hi ] >> \o stack
        /\ pivot' = 1
        /\ pc' = "qs1"
        /\ UNCHANGED << Ainit, A >>

test == /\ pc = "test"
        /\ Assert(A \in PermsOf(Ainit) /\ IsSorted(A),
                  "Failure of assertion at line test.")
        /\ pc' = "Done"
        /\ UNCHANGED << Ainit, A, stack, lo, hi, pivot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == QS \/ main \/ test \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

(***************************************************************************)
(* Additional properties                                                   *)
(***************************************************************************)
TypeOK == /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]
          /\ A \in [1..ArrayLen -> 1..ArrayLen]
          /\ pc \in {"main", "qs1", "qs2", "qs3", "qs4", "test", "Done"}

PermInvariant == A \in PermsOf(Ainit)

SortedWhenDone == (pc = "Done") => (A \in PermsOf(Ainit) /\ IsSorted(A))

==============================================================================