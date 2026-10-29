---------------------------- MODULE QuicksortRec ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT ArrayLen

ASSUME ArrayLen \in Nat

PermsOf(Arr) ==
  LET Automorphisms(S) == { f \in [S -> S] :
                              \A y \in S : \E x \in S : f[x] = y }
      f ** g == [x \in DOMAIN g |-> f[g[x]]]
  IN  { Arr ** f : f \in Automorphisms(DOMAIN Arr) }

(***************************************************************************
--algorithm QuicksortRec
  variables Ainit \in [1..ArrayLen -> 1..ArrayLen], A = Ainit;

  procedure QS(qlo, qhi)
    variable pivot = 0;
  {
   qs1: if (qlo < qhi) {
          with (piv \in qlo..(qhi-1),
                Ap \in { B \in PermsOf(A) :
                          /\ \A i \in (1..ArrayLen) \ (qlo..qhi) : B[i] = A[i]
                          /\ \A i \in qlo..piv, j \in (piv+1)..qhi :
                                 B[i] <= B[j] }) {
            pivot := piv;
            A := Ap
          };
   qs2:   call QS(qlo, pivot);
   qs3:   call QS(pivot+1, qhi)
        };
   qs4: return
  }

  {
   main: call QS(1, Len(A));
   test: assert A \in PermsOf(Ainit)
                /\ \A i \in 1..(ArrayLen-1) : A[i] <= A[i+1]
  }
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES Ainit, A, pc, stack, qlo, qhi, pivot

vars == << Ainit, A, pc, stack, qlo, qhi, pivot >>

Init == /\ Ainit \in [1..ArrayLen -> 1..ArrayLen]
        /\ A = Ainit
        /\ qlo = 0
        /\ qhi = 0
        /\ pivot = 0
        /\ stack = << >>
        /\ pc = "main"

qs1 == /\ pc = "qs1"
       /\ IF qlo < qhi
             THEN /\ \E piv \in qlo..(qhi-1) :
                       \E Ap \in { B \in PermsOf(A) :
                                    /\ \A i \in (1..ArrayLen) \ (qlo..qhi) :
                                           B[i] = A[i]
                                    /\ \A i \in qlo..piv, j \in (piv+1)..qhi :
                                           B[i] <= B[j] } :
                          /\ pivot' = piv
                          /\ A' = Ap
                  /\ pc' = "qs2"
             ELSE /\ pc' = "qs4"
                  /\ UNCHANGED << A, pivot >>
       /\ UNCHANGED << Ainit, stack, qlo, qhi >>

qs2 == /\ pc = "qs2"
       /\ stack' = << [ procedure |-> "QS",
                        pc        |-> "qs3",
                        pivot     |-> pivot,
                        qlo       |-> qlo,
                        qhi       |-> qhi ] >> \o stack
       /\ qlo' = qlo
       /\ qhi' = pivot
       /\ pivot' = 0
       /\ pc' = "qs1"
       /\ UNCHANGED << Ainit, A >>

qs3 == /\ pc = "qs3"
       /\ stack' = << [ procedure |-> "QS",
                        pc        |-> "qs4",
                        pivot     |-> pivot,
                        qlo       |-> qlo,
                        qhi       |-> qhi ] >> \o stack
       /\ qlo' = pivot + 1
       /\ qhi' = qhi
       /\ pivot' = 0
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
        /\ stack' = << [ procedure |-> "QS",
                         pc        |-> "test",
                         pivot     |-> pivot,
                         qlo       |-> qlo,
                         qhi       |-> qhi ] >> \o stack
        /\ qlo' = 1
        /\ qhi' = Len(A)
        /\ pivot' = 0
        /\ pc' = "qs1"
        /\ UNCHANGED << Ainit, A >>

test == /\ pc = "test"
        /\ Assert(/\ A \in PermsOf(Ainit)
                  /\ \A i \in 1..(ArrayLen-1) : A[i] <= A[i+1],
                  "Failure of assertion at line test.")
        /\ pc' = "Done"
        /\ UNCHANGED << Ainit, A, stack, qlo, qhi, pivot >>

Terminating == pc = "Done" /\ UNCHANGED vars

Next == QS \/ main \/ test \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")

\* END TRANSLATION
=============================================================================