------------------------------- MODULE QuickSort -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen
ASSUME ArrayLen \in Nat

PermsOf(Arr) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

Partitions(B, pivot, lo, hi) ==
  { C \in PermsOf(B) :
       /\ \A i \in (1..(lo-1)) \cup ((hi+1)..ArrayLen) : C[i] = B[i]
       /\ \A i \in lo..pivot, j \in (pivot+1)..hi : C[i] <= C[j] }

IsSorted(Arr) == \A i \in 1..(ArrayLen-1) : Arr[i] <= Arr[i+1]

(***************************************************************************
--algorithm QuickSort {
  variables A \in [1..ArrayLen -> 1..ArrayLen],
            Ainit = A;

  procedure QS(lo = 1, hi = 1)
    variable pivot = 1;
  { qs1: if (lo < hi) {
           with (piv \in lo..(hi-1), B \in Partitions(A, piv, lo, hi)) {
             pivot := piv;
             A := B
           };
     qs2:  call QS(lo, pivot);
     qs3:  call QS(pivot+1, hi)
         };
    qs4: return
  }

  { main: call QS(1, ArrayLen);
    test: assert A \in PermsOf(Ainit) /\ IsSorted(A)
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES A, Ainit, pc, stack, lo, hi, pivot

vars == << A, Ainit, pc, stack, lo, hi, pivot >>

Init == (* Global variables *)
        /\ A \in [1..ArrayLen -> 1..ArrayLen]
        /\ Ainit = A
        (* Procedure QS *)
        /\ lo = 1
        /\ hi = 1
        /\ pivot = 1
        /\ stack = << >>
        /\ pc = "main"

qs1 == /\ pc = "qs1"
       /\ IF lo < hi
             THEN /\ \E piv \in lo..(hi-1):
                       \E B \in Partitions(A, piv, lo, hi):
                          /\ pivot' = piv
                          /\ A' = B
                  /\ pc' = "qs2"
             ELSE /\ pc' = "qs4"
                  /\ UNCHANGED << A, pivot >>
       /\ UNCHANGED << Ainit, stack, lo, hi >>

qs2 == /\ pc = "qs2"
       /\ /\ hi' = pivot
          /\ lo' = lo
          /\ stack' = << [ procedure |-> "QS",
                           pc        |-> "qs3",
                           pivot     |-> pivot,
                           lo        |-> lo,
                           hi        |-> hi ] >>
                       \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << A, Ainit >>

qs3 == /\ pc = "qs3"
       /\ /\ hi' = hi
          /\ lo' = pivot + 1
          /\ stack' = << [ procedure |-> "QS",
                           pc        |-> "qs4",
                           pivot     |-> pivot,
                           lo        |-> lo,
                           hi        |-> hi ] >>
                       \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << A, Ainit >>

qs4 == /\ pc = "qs4"
       /\ pc' = Head(stack).pc
       /\ pivot' = Head(stack).pivot
       /\ lo' = Head(stack).lo
       /\ hi' = Head(stack).hi
       /\ stack' = Tail(stack)
       /\ UNCHANGED << A, Ainit >>

QS == qs1 \/ qs2 \/ qs3 \/ qs4

main == /\ pc = "main"
        /\ /\ hi' = ArrayLen
           /\ lo' = 1
           /\ stack' = << [ procedure |-> "QS",
                            pc        |-> "test",
                            pivot     |-> pivot,
                            lo        |-> lo,
                            hi        |-> hi ] >>
                        \o stack
        /\ pivot' = 1
        /\ pc' = "qs1"
        /\ UNCHANGED << A, Ainit >>

test == /\ pc = "test"
        /\ Assert(A \in PermsOf(Ainit) /\ IsSorted(A),
                  "Failure of assertion at line 'test'.")
        /\ pc' = "Done"
        /\ UNCHANGED << A, Ainit, stack, lo, hi, pivot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == QS \/ main \/ test
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Safety: once finished, the array is a sorted permutation of the input.  *)
(***************************************************************************)
TypeOK == /\ A \in [1..ArrayLen -> 1..ArrayLen]
          /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]

PermInvariant == A \in PermsOf(Ainit)

Correctness == (pc = "Done") => (A \in PermsOf(Ainit) /\ IsSorted(A))

THEOREM Spec => [](TypeOK /\ PermInvariant /\ Correctness)
THEOREM Spec => Termination
================================================================================