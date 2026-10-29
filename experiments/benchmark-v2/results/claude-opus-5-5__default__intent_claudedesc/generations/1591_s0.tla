------------------------------ MODULE EvenOdd ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N

ASSUME NAssumption == N \in Nat

(* N = 6 is the concrete test case for model checking. *)
TestN == 6

VARIABLES pc, stack, n, result, output, oddCount, evenToOddCount

vars == << pc, stack, n, result, output, oddCount, evenToOddCount >>

Labels == {"Main", "Print", "E1", "ERet", "O1", "ORet", "Done"}

TypeOK ==
    /\ pc \in Labels
    /\ n \in Nat
    /\ result \in BOOLEAN
    /\ output \in BOOLEAN \cup {"none"}
    /\ oddCount \in Nat
    /\ evenToOddCount \in Nat

Init ==
    /\ pc = "Main"
    /\ stack = << >>
    /\ n = 0
    /\ result = FALSE
    /\ output = "none"
    /\ oddCount = 0
    /\ evenToOddCount = 0

(* Main program: call Even(N) *)
Main ==
    /\ pc = "Main"
    /\ stack' = << [ret |-> "Print", n |-> n] >> \o stack
    /\ n' = N
    /\ pc' = "E1"
    /\ UNCHANGED << result, output, oddCount, evenToOddCount >>

(* Main program: print the resulting boolean *)
Print ==
    /\ pc = "Print"
    /\ output' = result
    /\ PrintT(result)
    /\ pc' = "Done"
    /\ UNCHANGED << stack, n, result, oddCount, evenToOddCount >>

(* Generic return from a procedure *)
Return ==
    /\ stack /= << >>
    /\ pc' = Head(stack).ret
    /\ n' = Head(stack).n
    /\ stack' = Tail(stack)

(* Procedure Even *)
E1 ==
    /\ pc = "E1"
    /\ IF n = 0
         THEN /\ result' = TRUE
              /\ Return
              /\ UNCHANGED << output, oddCount, evenToOddCount >>
         ELSE /\ stack' = << [ret |-> "ERet", n |-> n] >> \o stack
              /\ n' = n - 1
              /\ pc' = "O1"
              /\ oddCount' = oddCount + 1
              /\ evenToOddCount' = evenToOddCount + 1
              /\ UNCHANGED << result, output >>

ERet ==
    /\ pc = "ERet"
    /\ Return
    /\ UNCHANGED << result, output, oddCount, evenToOddCount >>

(* Procedure Odd *)
O1 ==
    /\ pc = "O1"
    /\ IF n = 0
         THEN /\ result' = FALSE
              /\ Return
              /\ UNCHANGED << output, oddCount, evenToOddCount >>
         ELSE /\ stack' = << [ret |-> "ORet", n |-> n] >> \o stack
              /\ n' = n - 1
              /\ pc' = "E1"
              /\ UNCHANGED << result, output, oddCount, evenToOddCount >>

ORet ==
    /\ pc = "ORet"
    /\ Return
    /\ UNCHANGED << result, output, oddCount, evenToOddCount >>

(* Allow infinite stuttering after termination *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Main
    \/ Print
    \/ E1
    \/ ERet
    \/ O1
    \/ ORet
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety invariants *)

(* For N = 6, Odd is never entered more than 3 times, and Even->Odd
   transitions never exceed 3. *)
OddCountBound ==
    N = TestN => oddCount <= 3

EvenToOddBound ==
    N = TestN => evenToOddCount <= 3

(* For N = 6, upon completion Odd was entered exactly 3 times and the
   Even->Odd transition happened exactly 3 times; result is TRUE. *)
CallPatternAtTermination ==
    (N = TestN /\ pc = "Done") =>
        /\ oddCount = 3
        /\ evenToOddCount = 3
        /\ output = TRUE

(* General correctness: printed result reflects evenness of N *)
CorrectResult ==
    pc = "Done" => output = ((N % 2) = 0)

(* Odd is only ever entered from Even *)
OddOnlyFromEven ==
    oddCount = evenToOddCount

-----------------------------------------------------------------------------
(* Liveness properties *)

(* The computation always eventually completes *)
Termination == <>(pc = "Done")

(* For N = 6, eventually the counts settle at exactly 3 *)
EventuallyThreeOddCalls ==
    N = TestN => <>[](oddCount = 3 /\ evenToOddCount = 3)

=============================================================================