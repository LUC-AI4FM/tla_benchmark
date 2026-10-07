----------------------------- MODULE SequentialProcPlayground -----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANT MainId
ASSUME MainId = 1

VARIABLES stack, retval, output

vars == << stack, retval, output >>

Top(s) == s[Len(s)]

IsDone(s) == /\ Len(s) = 1
             /\ s[1].name = "main"
             /\ s[1].pc = "Done"

Init ==
  /\ stack = << [name |-> "main", pc |-> "L1", pid |-> MainId] >>
  /\ retval = 0
  /\ output = ""

MainAct ==
  /\ Len(stack) >= 1
  /\ Top(stack).name = "main"
  /\ \/
     /\ Top(stack).pc = "L1"
     /\ stack' = Append(stack, [name |-> "add", a |-> 3, b |-> 7, retpc |-> "L2"])
     /\ retval' = retval
     /\ output' = output
  \/ /\ Top(stack).pc = "L2"
     /\ stack' = Append(stack, [name |-> "to_string", x |-> retval, retpc |-> "L3"])
     /\ retval' = retval
     /\ output' = output
  \/ /\ Top(stack).pc = "L3"
     /\ stack' = [stack EXCEPT ![Len(stack)].pc = "L4"]
     /\ retval' = retval
     /\ output' = retval
  \/ /\ Top(stack).pc = "L4"
     /\ Assert(output = "10", "Final assert failed: output must equal \"10\"")
     /\ stack' = [stack EXCEPT ![Len(stack)].pc = "Done"]
     /\ retval' = retval
     /\ output' = output

AddAct ==
  /\ Len(stack) >= 2
  /\ Top(stack).name = "add"
  /\ LET cal == Top(stack)
         i == Len(stack) - 1
         caller == stack[i]
     IN /\ caller.name = "main"
        /\ retval' = cal.a + cal.b
        /\ stack' = [ j \in 1..i |-> IF j = i THEN [caller EXCEPT !.pc = cal.retpc] ELSE stack[j] ]
        /\ output' = output

ToStringAct ==
  /\ Len(stack) >= 2
  /\ Top(stack).name = "to_string"
  /\ LET cal == Top(stack)
         i == Len(stack) - 1
         caller == stack[i]
     IN /\ caller.name = "main"
        /\ Assert(cal.x = 10, "to_string precondition failed: argument must be 10")
        /\ retval' = "10"
        /\ stack' = [ j \in 1..i |-> IF j = i THEN [caller EXCEPT !.pc = cal.retpc] ELSE stack[j] ]
        /\ output' = output

Next == MainAct \/ AddAct \/ ToStringAct

Spec == Init /\ [][Next]_vars /\ WF_vars(MainAct) /\ WF_vars(AddAct) /\ WF_vars(ToStringAct)

Safety ==
  /\ (Len(stack) >= 1 /\ Top(stack).name = "to_string") => Top(stack).x = 10
  /\ IsDone(stack) => output = "10"

Termination == <> IsDone(stack)

Liveness == Termination

==========================================================================================