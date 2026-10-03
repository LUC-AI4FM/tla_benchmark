---- MODULE PlusCalProcedures ----
EXTENDS Integers, Strings, Sequences, TLC

CONSTANT defaultInitValue

VARIABLES pc, stack, i, j, sum, s, a, b, n, res

vars == << pc, stack, i, j, sum, s, a, b, n, res >>

Init ==
  /\ pc = "Main"
  /\ stack = << >>
  /\ i = defaultInitValue
  /\ j = defaultInitValue
  /\ sum = defaultInitValue
  /\ s = defaultInitValue
  /\ a = defaultInitValue
  /\ b = defaultInitValue
  /\ n = defaultInitValue
  /\ res = defaultInitValue

(* Main process actions *)
Main ==
  /\ pc = "Main"
  /\ i' = 4
  /\ j' = 6
  /\ pc' = "Call_Add"
  /\ UNCHANGED <<stack, sum, s, a, b, n, res>>

Call_Add ==
  /\ pc = "Call_Add"
  /\ stack' = Prepend([pc |-> "Return_Add"], stack)
  /\ a' = i
  /\ b' = j
  /\ pc' = "Add_Start"
  /\ UNCHANGED <<i, j, sum, s, n, res>>

Return_Add ==
  /\ pc = "Return_Add"
  /\ sum' = res
  /\ pc' = "Call_ToString"
  /\ UNCHANGED <<stack, i, j, s, a, b, n, res>>

Call_ToString ==
  /\ pc = "Call_ToString"
  /\ stack' = Prepend([pc |-> "Return_ToString"], stack)
  /\ n' = sum
  /\ pc' = "ToString_Start"
  /\ UNCHANGED <<i, j, sum, s, a, b, res>>

Return_ToString ==
  /\ pc = "Return_ToString"
  /\ s' = res
  /\ pc' = "Final"
  /\ UNCHANGED <<stack, i, j, sum, a, b, n, res>>

Final ==
  /\ pc = "Final"
  /\ Assert(s = "10", "Assertion failed: final string is not '10'")
  /\ pc' = "Done"
  /\ UNCHANGED <<stack, i, j, sum, s, a, b, n, res>>

(* Add procedure actions *)
Add_Start ==
  /\ pc = "Add_Start"
  /\ res' = a + b
  /\ pc' = "Add_Return"
  /\ UNCHANGED <<stack, i, j, sum, s, a, b, n>>

Add_Return ==
  /\ pc = "Add_Return"
  /\ Len(stack) > 0
  /\ LET frame == Head(stack)
     IN /\ pc' = frame.pc
        /\ stack' = Tail(stack)
  /\ UNCHANGED <<i, j, sum, s, a, b, n, res>>

(* ToString procedure actions *)
ToString_Start ==
  /\ pc = "ToString_Start"
  /\ Assert(n = 10, "Assertion failed: integer passed to ToString is not 10")
  /\ res' = IF n = 10 THEN "10" ELSE "other"
  /\ pc' = "ToString_Return"
  /\ UNCHANGED <<stack, i, j, sum, s, a, b, n>>

ToString_Return ==
  /\ pc = "ToString_Return"
  /\ Len(stack) > 0
  /\ LET frame == Head(stack)
     IN /\ pc' = frame.pc
        /\ stack' = Tail(stack)
  /\ UNCHANGED <<i, j, sum, s, a, b, n, res>>

(* Terminal state *)
Done ==
  /\ pc = "Done"
  /\ UNCHANGED vars

(* Process definition *)
P ==
  \/ Main
  \/ Call_Add
  \/ Return_Add
  \/ Call_ToString
  \/ Return_ToString
  \/ Final
  \/ Add_Start
  \/ Add_Return
  \/ ToString_Start
  \/ ToString_Return

Next == P \/ Done

Fairness == WF_vars(P)

Spec == Init /\ [][Next]_vars /\ Fairness

Termination == <>(pc = "Done")

=============================================================================