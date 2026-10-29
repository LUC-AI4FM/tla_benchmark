------------------------------ MODULE QuickSort ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

(***************************************************************************)
(* PermsOf(Arr) is the set of all permutations of the array Arr.          *)
(***************************************************************************)
PermsOf(Arr) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      Compose(f, g) == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Compose(Arr, f) : f \in Automorphisms(DOMAIN Arr) }

(***************************************************************************
--algorithm QuickSort
  variables Ainit \in [1..ArrayLen -> 1..ArrayLen];
            A = Ainit;

  procedure QS(qlo = 1, qhi = 1)
    variable pivot = 1;
  begin
    qs1: if qlo < qhi then
           with piv \in qlo..(qhi-1),
                Ap \in {B \in PermsOf(A) :
                          /\ \A i \in (1..ArrayLen) \ (qlo..qhi) : B[i] = A[i]
                          /\ \A i \in qlo..piv, j \in (piv+1)..qhi :
                                B[i] <= B[j]} do
             A := Ap;
             pivot := piv
           end with;
    qs2:   call QS(qlo, pivot);
    qs3:   call QS(pivot+1, qhi)
         end if;
    qs4: return
  end procedure;

  begin
    main: call QS(1, Len(A));
    test: assert /\ A \in PermsOf(Ainit)
                 /\ \A i, j \in 1..ArrayLen : (i < j) => (A[i] <= A[j])
end algorithm
 ***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES Ainit, A, pc, stack, qlo, qhi, pivot

vars == << Ainit, A, pc, stack, qlo, qhi, pivot >>

Init == (* Global variables *)
        /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]
        /\ A = Ainit
        (* Procedure QS *)
        /\ qlo = 1
        /\ qhi = 1
        /\ pivot = 1
        /\ stack = << >>
        /\ pc = "main"

qs1 == /\ pc = "qs1"
       /\ IF qlo < qhi
             THEN /\ \E piv \in qlo..(qhi-1):
                       \E Ap \in {B \in PermsOf(A) :
                                    /\ \A i \in (1..ArrayLen) \ (qlo..qhi) :
                                          B[i] = A[i]
                                    /\ \A i \in qlo..piv, j \in (piv+1)..qhi :
                                          B[i] <= B[j]}:
                         /\ A' = Ap
                         /\ pivot' = piv
                  /\ pc' = "qs2"
             ELSE /\ pc' = "qs4"
                  /\ UNCHANGED << A, pivot >>
       /\ UNCHANGED << Ainit, stack, qlo, qhi >>

qs2 == /\ pc = "qs2"
       /\ /\ qhi' = pivot
          /\ qlo' = qlo
          /\ stack' = << [ procedure |-> "QS",
                           pc        |-> "qs3",
                           pivot     |-> pivot,
                           qlo       |-> qlo,
                           qhi       |-> qhi ] >>
                       \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << Ainit, A >>

qs3 == /\ pc = "qs3"
       /\ /\ qhi' = qhi
          /\ qlo' = pivot + 1
          /\ stack' = << [ procedure |-> "QS",
                           pc        |-> "qs4",
                           pivot     |-> pivot,
                           qlo       |-> qlo,
                           qhi       |-> qhi ] >>
                       \o stack
       /\ pivot' = 1
       /\ pc' = "qs1"
       /\ UNCHANGED << Ainit, A >>

qs4 == /\ pc = "qs4"
       /\ pc' = Head(stack).pc
       /\ pivot' = Head(stack).pivot
       /\ qlo' = Head(stack).qlo
       /\ qhi' = Head(stack).qhi
       /\ stack' = Tail(stack)
       /\ UNCHANGED << Ainit, A >>

QS == qs1 \/ qs2 \/ qs3 \/ qs4

main == /\ pc = "main"
        /\ /\ qhi' = Len(A)
           /\ qlo' = 1
           /\ stack' = << [ procedure |-> "QS",
                            pc        |-> "test",
                            pivot     |-> pivot,
                            qlo       |-> qlo,
                            qhi       |-> qhi ] >>
                        \o stack
        /\ pivot' = 1
        /\ pc' = "qs1"
        /\ UNCHANGED << Ainit, A >>

test == /\ pc = "test"
        /\ Assert(/\ A \in PermsOf(Ainit)
                  /\ \A i, j \in 1..ArrayLen : (i < j) => (A[i] <= A[j]),
                  "Failure of assertion at line test.")
        /\ pc' = "Done"
        /\ UNCHANGED << Ainit, A, stack, qlo, qhi, pivot >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == QS \/ main \/ test
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================