------------------------------- MODULE QuickSort -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

PermsOf(Arr) ==
  LET Automorphisms(S) == { f \in [S -> S] : \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

(*****************************************************************************
--algorithm QuickSort
  variables A \in [1..ArrayLen -> 1..ArrayLen],
            Ainit = A;

  procedure QS(qlo = 1, qhi = 1)
    variable pivot = 1;
  begin
    qs1: if qlo < qhi then
           with piv \in qlo..(qhi-1) do
             pivot := piv;
             with Ap \in {AA \in PermsOf(A) :
                            (\A i \in (1..ArrayLen) \ (qlo..qhi) : AA[i] = A[i])
                            /\ \A i \in qlo..piv, j \in (piv+1)..qhi : AA[i] <= AA[j]} do
               A := Ap
             end with
           end with;
    qs2:   call QS(qlo, pivot);
    qs3:   call QS(pivot + 1, qhi);
         end if;
    qs4: return;
  end procedure;

  begin
    main: call QS(1, ArrayLen);
    test: assert A \in PermsOf(Ainit)
                 /\ \A i, j \in 1..ArrayLen : (i < j) => A[i] <= A[j];
end algorithm
*****************************************************************************)

\* BEGIN TRANSLATION
VARIABLES A, Ainit, pc, stack, qlo, qhi, pivot

vars == << A, Ainit, pc, stack, qlo, qhi, pivot >>

Init == /\ A \in [1..ArrayLen -> 1..ArrayLen]
        /\ Ainit = A
        /\ qlo = 1
        /\ qhi = 1
        /\ pivot = 1
        /\ stack = << >>
        /\ pc = "main"

qs1 == /\ pc = "qs1"
       /\ IF qlo < qhi
             THEN /\ \E piv \in qlo..(qhi-1):
                       /\ pivot' = piv
                       /\ \E Ap \in {AA \in PermsOf(A) :
                                       (\A i \in (1..ArrayLen) \ (qlo..qhi) : AA[i] = A[i])
                                       /\ \A i \in qlo..piv, j \in (piv+1)..qhi : AA[i] <= AA[j]}:
                            A' = Ap
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
        /\ Assert(A \in PermsOf(Ainit)
                  /\ \A i, j \in 1..ArrayLen : (i < j) => A[i] <= A[j],
                  "Failure of assertion at line test.")
        /\ pc' = "Done"
        /\ UNCHANGED << A, Ainit, stack, qlo, qhi, pivot >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == QS \/ main \/ test \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

=============================================================================