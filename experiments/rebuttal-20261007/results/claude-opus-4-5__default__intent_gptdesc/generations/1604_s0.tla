---------------------------- MODULE CallStackModel ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS
    ARG1,           \* First argument to Add procedure (integer)
    ARG2,           \* Second argument to Add procedure (integer)
    EXPECTED_SUM,   \* Expected sum of ARG1 + ARG2
    EXPECTED_STRING \* Expected string output

VARIABLES
    pc,             \* Program counter - current location in execution
    stack,          \* Call stack - sequence of frames
    locals,         \* Current local variables (record)
    returnValue,    \* Return value from callee to caller
    output          \* Global output variable

vars == <<pc, stack, locals, returnValue, output>>

-----------------------------------------------------------------------------
(* Type definitions for documentation:
   Frame == [returnPC : String, savedLocals : Record]
   Stack == Seq(Frame)
*)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ pc = "main_start"
    /\ stack = <<>>
    /\ locals = [a |-> 0, b |-> 0, sumResult |-> 0]
    /\ returnValue = 0
    /\ output = ""

-----------------------------------------------------------------------------
(* Main program steps *)

(* Step 1: Main calls Add procedure with ARG1 and ARG2 *)
MainCallAdd ==
    /\ pc = "main_start"
    /\ stack' = Append(stack, [returnPC |-> "main_after_add", savedLocals |-> locals])
    /\ locals' = [a |-> ARG1, b |-> ARG2, sumResult |-> 0]
    /\ pc' = "add_entry"
    /\ UNCHANGED <<returnValue, output>>

(* Step 2: After Add returns, main stores result and calls IntToString *)
MainAfterAdd ==
    /\ pc = "main_after_add"
    /\ locals' = [locals EXCEPT !.sumResult = returnValue]
    /\ pc' = "main_call_tostring"
    /\ UNCHANGED <<stack, returnValue, output>>

(* Step 3: Main calls IntToString with the sum result *)
MainCallToString ==
    /\ pc = "main_call_tostring"
    /\ stack' = Append(stack, [returnPC |-> "main_after_tostring", savedLocals |-> locals])
    /\ locals' = [n |-> locals.sumResult]
    /\ pc' = "tostring_entry"
    /\ UNCHANGED <<returnValue, output>>

(* Step 4: After IntToString returns, main stores result in output *)
MainAfterToString ==
    /\ pc = "main_after_tostring"
    /\ output' = returnValue
    /\ pc' = "main_assert"
    /\ UNCHANGED <<stack, locals, returnValue>>

(* Step 5: Main asserts output equals expected string *)
MainAssert ==
    /\ pc = "main_assert"
    /\ output = EXPECTED_STRING  \* Assertion - only enabled if true
    /\ pc' = "Done"
    /\ UNCHANGED <<stack, locals, returnValue, output>>

-----------------------------------------------------------------------------
(* Add procedure: computes a + b and returns result *)

AddEntry ==
    /\ pc = "add_entry"
    /\ pc' = "add_compute"
    /\ UNCHANGED <<stack, locals, returnValue, output>>

AddCompute ==
    /\ pc = "add_compute"
    /\ returnValue' = locals.a + locals.b
    /\ pc' = "add_return"
    /\ UNCHANGED <<stack, locals, output>>

AddReturn ==
    /\ pc = "add_return"
    /\ Len(stack) > 0
    /\ LET frame == stack[Len(stack)]
       IN /\ pc' = frame.returnPC
          /\ locals' = frame.savedLocals
          /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
    /\ UNCHANGED <<returnValue, output>>

-----------------------------------------------------------------------------
(* IntToString procedure: converts integer to string *)
(* Only handles EXPECTED_SUM, fails assertion otherwise *)

ToStringEntry ==
    /\ pc = "tostring_entry"
    /\ locals.n = EXPECTED_SUM  \* Assertion - fails if n != EXPECTED_SUM
    /\ pc' = "tostring_compute"
    /\ UNCHANGED <<stack, locals, returnValue, output>>

ToStringCompute ==
    /\ pc = "tostring_compute"
    /\ returnValue' = EXPECTED_STRING
    /\ pc' = "tostring_return"
    /\ UNCHANGED <<stack, locals, output>>

ToStringReturn ==
    /\ pc = "tostring_return"
    /\ Len(stack) > 0
    /\ LET frame == stack[Len(stack)]
       IN /\ pc' = frame.returnPC
          /\ locals' = frame.savedLocals
          /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
    /\ UNCHANGED <<returnValue, output>>

-----------------------------------------------------------------------------
(* Combined actions *)

MainActions ==
    \/ MainCallAdd
    \/ MainAfterAdd
    \/ MainCallToString
    \/ MainAfterToString
    \/ MainAssert

AddActions ==
    \/ AddEntry
    \/ AddCompute
    \/ AddReturn

ToStringActions ==
    \/ ToStringEntry
    \/ ToStringCompute
    \/ ToStringReturn

Next ==
    \/ MainActions
    \/ AddActions
    \/ ToStringActions

-----------------------------------------------------------------------------
(* Fairness conditions *)

Fairness ==
    /\ WF_vars(MainCallAdd)
    /\ WF_vars(MainAfterAdd)
    /\ WF_vars(MainCallToString)
    /\ WF_vars(MainAfterToString)
    /\ WF_vars(MainAssert)
    /\ WF_vars(AddEntry)
    /\ WF_vars(AddCompute)
    /\ WF_vars(AddReturn)
    /\ WF_vars(ToStringEntry)
    /\ WF_vars(ToStringCompute)
    /\ WF_vars(ToStringReturn)

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

(* Type invariant for basic type checking *)
TypeOK ==
    /\ pc \in {"main_start", "main_after_add", "main_call_tostring", 
               "main_after_tostring", "main_assert", "Done",
               "add_entry", "add_compute", "add_return",
               "tostring_entry", "tostring_compute", "tostring_return"}
    /\ stack \in Seq([returnPC : STRING, savedLocals : [a : Int, b : Int, sumResult : Int] \cup [n : Int]])

(* Stack is empty when Done *)
StackEmptyWhenDone ==
    pc = "Done" => Len(stack) = 0

(* Safety: When done, output equals expected string *)
SafetyOutputCorrect ==
    pc = "Done" => output = EXPECTED_STRING

(* Combined safety invariant *)
SafetyInvariant ==
    /\ StackEmptyWhenDone
    /\ SafetyOutputCorrect

-----------------------------------------------------------------------------
(* Liveness Properties *)

(* Terminal state definition *)
Terminated ==
    /\ pc = "Done"
    /\ Len(stack) = 0

(* Termination: eventually reach Done state *)
Termination == <>(Terminated)

(* Main process eventually terminates *)
MainEventuallyTerminates == <>(pc = "Done")

-----------------------------------------------------------------------------
(* Theorems to verify *)

THEOREM Spec => []SafetyInvariant
THEOREM Spec => Termination
THEOREM Spec => MainEventuallyTerminates

=============================================================================