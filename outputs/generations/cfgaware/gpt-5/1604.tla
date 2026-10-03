---- MODULE ProcCalls ----
EXTENDS Naturals, Sequences, TLC

CONSTANT defaultInitValue

VARIABLES pc, stack, add_a, add_b, add_sum, str_i, str_s, retVal, main_res, outStr

Proc == {0}

PC ==
  {"Main_L1", "Main_AfterAdd", "Main_CallToStr", "Main_AfterStr",
   "Add_Entry", "Add_Compute", "Add_Return",
   "Str_Entry", "Str_AssertArg", "Str_Set", "Str_Return",
   "Done"}

Frame == [retpc: PC]

vars == << pc, stack, add_a, add_b, add_sum, str_i, str_s, retVal, main_res, outStr >>

Init ==
  /\ pc = [i \in Proc |-> "Main_L1"]
  /\ stack = [i \in Proc |-> << >>]
  /\ add_a = [i \in Proc |-> defaultInitValue]
  /\ add_b = [i \in Proc |-> defaultInitValue]
  /\ add_sum = [i \in Proc |-> defaultInitValue]
  /\ str_i = [i \in Proc |-> defaultInitValue]
  /\ str_s = [i \in Proc |-> defaultInitValue]
  /\ retVal = [i \in Proc |-> defaultInitValue]
  /\ main_res = [i \in Proc |-> defaultInitValue]
  /\ outStr = defaultInitValue

PStep(i) ==
  \/ /\ pc[i] = "Main_L1"
     /\ add_a' = [add_a EXCEPT ![i] = 4]
     /\ add_b' = [add_b EXCEPT ![i] = 6]
     /\ stack' = [stack EXCEPT ![i] = Append(stack[i], [retpc |-> "Main_AfterAdd"])]
     /\ pc' = [pc EXCEPT ![i] = "Add_Entry"]
     /\ UNCHANGED << add_sum, str_i, str_s, retVal, main_res, outStr >>
  \/ /\ pc[i] = "Add_Entry"
     /\ pc' = [pc EXCEPT ![i] = "Add_Compute"]
     /\ UNCHANGED << stack, add_a, add_b, add_sum, str_i, str_s, retVal, main_res, outStr >>
  \/ /\ pc[i] = "Add_Compute"
     /\ LET s == add_a[i] + add_b[i] IN
           /\ add_sum' = [add_sum EXCEPT ![i] = s]
           /\ retVal' = [retVal EXCEPT ![i] = s]
           /\ pc' = [pc EXCEPT ![i] = "Add_Return"]
           /\ UNCHANGED << stack, add_a, add_b, str_i, str_s, main_res, outStr >>
  \/ /\ pc[i] = "Add_Return"
     /\ LET n == Len(stack[i]) IN
           /\ n > 0
           /\ pc' = [pc EXCEPT ![i] = stack[i][n].retpc]
           /\ stack' = [stack EXCEPT ![i] = SubSeq(stack[i], 1, n-1)]
           /\ UNCHANGED << add_a, add_b, add_sum, str_i, str_s, retVal, main_res, outStr >>
  \/ /\ pc[i] = "Main_AfterAdd"
     /\ main_res' = [main_res EXCEPT ![i] = retVal[i]]
     /\ pc' = [pc EXCEPT ![i] = "Main_CallToStr"]
     /\ UNCHANGED << stack, add_a, add_b, add_sum, str_i, str_s, retVal, outStr >>
  \/ /\ pc[i] = "Main_CallToStr"
     /\ str_i' = [str_i EXCEPT ![i] = main_res[i]]
     /\ stack' = [stack EXCEPT ![i] = Append(stack[i], [retpc |-> "Main_AfterStr"])]
     /\ pc' = [pc EXCEPT ![i] = "Str_Entry"]
     /\ UNCHANGED << add_a, add_b, add_sum, str_s, retVal, main_res, outStr >>
  \/ /\ pc[i] = "Str_Entry"
     /\ pc' = [pc EXCEPT ![i] = "Str_AssertArg"]
     /\ UNCHANGED << stack, add_a, add_b, add_sum, str_i, str_s, retVal, main_res, outStr >>
  \/ /\ pc[i] = "Str_AssertArg"
     /\ Assert(str_i[i] = 10, "Assertion failed: toStr argument is not 10")
     /\ pc' = [pc EXCEPT ![i] = "Str_Set"]
     /\ UNCHANGED << stack, add_a, add_b, add_sum, str_i, str_s, retVal, main_res, outStr >>
  \/ /\ pc[i] = "Str_Set"
     /\ LET s == "10" IN
           /\ str_s' = [str_s EXCEPT ![i] = s]
           /\ retVal' = [retVal EXCEPT ![i] = s]
           /\ pc' = [pc EXCEPT ![i] = "Str_Return"]
           /\ UNCHANGED << stack, add_a, add_b, add_sum, str_i, main_res, outStr >>
  \/ /\ pc[i] = "Str_Return"
     /\ LET n == Len(stack[i]) IN
           /\ n > 0
           /\ pc' = [pc EXCEPT ![i] = stack[i][n].retpc]
           /\ stack' = [stack EXCEPT ![i] = SubSeq(stack[i], 1, n-1)]
           /\ UNCHANGED << add_a, add_b, add_sum, str_i, str_s, retVal, main_res, outStr >>
  \/ /\ pc[i] = "Main_AfterStr"
     /\ Assert(retVal[i] = "10", "Assertion failed: expected return string '10'")
     /\ outStr' = retVal[i]
     /\ pc' = [pc EXCEPT ![i] = "Done"]
     /\ UNCHANGED << stack, add_a, add_b, add_sum, str_i, str_s, retVal, main_res >>
  \/ /\ pc[i] = "Done"
     /\ Assert(outStr = "10", "Assertion failed: final output string is not '10'")
     /\ UNCHANGED vars

Next == ∃ i \in Proc: PStep(i)

Spec == Init /\ [][Next]_vars /\ \A i \in Proc: WF_vars(PStep(i))

Termination == <> (pc[0] = "Done")

====