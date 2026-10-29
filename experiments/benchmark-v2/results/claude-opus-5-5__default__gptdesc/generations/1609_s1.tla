------------------------------- MODULE Quicksort -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

PermsOf(Arr) ==
  LET Automorphism(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphism(DOMAIN Arr) }

Partitions(B, pivot, lo, hi) ==
  { C \in PermsOf(B) :
      /\ \A i \in (1..(lo-1)) \cup ((hi+1)..Len(B)) : C[i] = B[i]
      /\ \A i \in lo..pivot, j \in (pivot+1)..hi : C[i] <= C[j] }

(***************************************************************************
--algorithm Quicksort
  variables A \in [1..ArrayLen -> 1..ArrayLen],
            Ainit = A;

  procedure QS(lo = 0, hi = 0)
    variable pivot = 1 ;
  begin
    qs1: if lo < hi
           then with piv \in lo..(hi-1) do
                  pivot := piv ;
                  with Ap \in Partitions(A, pivot, lo, hi) do
                    A := Ap
                  end with ;
                end with ;
                qs2: call QS(lo, pivot) ;
                qs3: call QS(pivot+1, hi) ;
         end if ;
    qs4: return ;
  end procedure

  begin
    main: call QS(1, Len(A)) ;
    test: assert /\ A \in PermsOf(Ainit)
                 /\ \A i, j \in 1..ArrayLen : (i < j) => (A[i] <= A[j])
  end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES A, Ainit, pc, stack, lo, hi, pivot

vars == << A, Ainit, pc, stack, lo, hi, pivot >>

Init == (* Global variables *)
        /\ A \in [1..ArrayLen -> 1..ArrayLen]
        /\ Ainit = A
        (* Procedure QS *)
        /\ lo = 0
        /\ hi = 0
        /\ pivot = 1
        /\ stack = << >>
        /\ pc = "main"

qs1 == /\ pc = "qs1"
       /\ IF lo < hi
             THEN /\ \E piv \in lo..(hi-1):
                       /\ pivot' = piv
                       /\ \E Ap \in Partitions(A, pivot', lo, hi):
                            A' = Ap
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
        /\ /\ hi' = Len(A)
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
        /\ Assert(/\ A \in PermsOf(Ainit)
                  /\ \A i, j \in 1..ArrayLen : (i < j) => (A[i] <= A[j]),
                  "Failure of assertion at line test.")
        /\ pc' = "Done"
        /\ UNCHANGED << A, Ainit, stack, lo, hi, pivot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == QS \/ main \/ test \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

(* Safety: when the algorithm finishes, the array is a sorted permutation. *)
SortedWhenDone ==
  (pc = "Done") =>
     /\ A \in PermsOf(Ainit)
     /\ \A i, j \in 1..ArrayLen : (i < j) => (A[i] <= A[j])

THEOREM Spec => []SortedWhenDone
THEOREM Spec => Termination
================================================================================