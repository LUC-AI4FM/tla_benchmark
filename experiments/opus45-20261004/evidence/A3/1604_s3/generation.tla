---------------------------- MODULE PlusCalProcedures ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS MaxInt

VARIABLES pc, stack, x, y, result, input, output

vars == <<pc, stack, x, y, result, input, output>>

(* 
   This specification models a PlusCal program with one fair process
   that calls two procedures in sequence:
   1. An addition procedure that adds two numbers
   2. A procedure that converts the resulting integer to a string
   
   The process passes values such that the addition yields 10,
   then converts 10 to the string "10".
*)

(* Helper function to convert an integer to string representation *)
IntToString(n) == 
    IF n = 0 THEN "0"
    ELSE IF n = 1 THEN "1"
    ELSE IF n = 2 THEN "2"
    ELSE IF n = 3 THEN "3"
    ELSE IF n = 4 THEN "4"
    ELSE IF n = 5 THEN "5"
    ELSE IF n = 6 THEN "6"
    ELSE IF n = 7 THEN "7"
    ELSE IF n = 8 THEN "8"
    ELSE IF n = 9 THEN "9"
    ELSE IF n = 10 THEN "10"
    ELSE IF n = 11 THEN "11"
    ELSE IF n = 12 THEN "12"
    ELSE "other"

(* Program counter values:
   - "start"      : initial state, about to call Add
   - "call_add"   : setting up call to Add procedure
   - "in_add"     : executing Add procedure body
   - "ret_add"    : returning from Add procedure
   - "call_tostr" : setting up call to IntToStr procedure  
   - "in_tostr"   : executing IntToStr procedure body
   - "assert_input": asserting input to IntToStr is 10
   - "ret_tostr"  : returning from IntToStr procedure
   - "assert_output": asserting final output is "10"
   - "done"       : process has terminated
*)

Init ==
    /\ pc = "start"
    /\ stack = << >>
    /\ x = 0           \* First parameter to Add
    /\ y = 0           \* Second parameter to Add
    /\ result = 0      \* Result of Add procedure
    /\ input = 0       \* Input parameter to IntToStr
    /\ output = ""     \* Output of IntToStr procedure

(* Main process calls Add(3, 7) *)
CallAdd ==
    /\ pc = "start"
    /\ x' = 3
    /\ y' = 7
    /\ stack' = Append(stack, [returnPC |-> "after_add", savedResult |-> result])
    /\ pc' = "in_add"
    /\ UNCHANGED <<result, input, output>>

(* Add procedure body: result := x + y *)
ExecAdd ==
    /\ pc = "in_add"
    /\ result' = x + y
    /\ pc' = "ret_add"
    /\ UNCHANGED <<stack, x, y, input, output>>

(* Return from Add procedure *)
ReturnAdd ==
    /\ pc = "ret_add"
    /\ Len(stack) > 0
    /\ pc' = Head(stack).returnPC
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<x, y, result, input, output>>

(* After Add returns, prepare to call IntToStr *)
AfterAdd ==
    /\ pc = "after_add"
    /\ pc' = "call_tostr"
    /\ UNCHANGED <<stack, x, y, result, input, output>>

(* Call IntToStr(result) - first assert input will be 10 *)
CallIntToStr ==
    /\ pc = "call_tostr"
    /\ input' = result
    /\ stack' = Append(stack, [returnPC |-> "after_tostr", savedInput |-> input])
    /\ pc' = "assert_input"
    /\ UNCHANGED <<x, y, result, output>>

(* Assert that input to IntToStr is 10 *)
AssertInput ==
    /\ pc = "assert_input"
    /\ Assert(input = 10, "Assertion failed: input to IntToStr must be 10")
    /\ pc' = "in_tostr"
    /\ UNCHANGED <<stack, x, y, result, input, output>>

(* IntToStr procedure body: output := string representation of input *)
ExecIntToStr ==
    /\ pc = "in_tostr"
    /\ output' = IntToString(input)
    /\ pc' = "ret_tostr"
    /\ UNCHANGED <<stack, x, y, result, input>>

(* Return from IntToStr procedure *)
ReturnIntToStr ==
    /\ pc = "ret_tostr"
    /\ Len(stack) > 0
    /\ pc' = Head(stack).returnPC
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<x, y, result, input, output>>

(* After IntToStr returns, assert output is "10" then terminate *)
AfterIntToStr ==
    /\ pc = "after_tostr"
    /\ pc' = "assert_output"
    /\ UNCHANGED <<stack, x, y, result, input, output>>

(* Assert final output is "10" *)
AssertOutput ==
    /\ pc = "assert_output"
    /\ Assert(output = "10", "Assertion failed: output must be \"10\"")
    /\ pc' = "done"
    /\ UNCHANGED <<stack, x, y, result, input, output>>

(* Process terminates - stuttering allowed *)
Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ CallAdd
    \/ ExecAdd
    \/ ReturnAdd
    \/ AfterAdd
    \/ CallIntToStr
    \/ AssertInput
    \/ ExecIntToStr
    \/ ReturnIntToStr
    \/ AfterIntToStr
    \/ AssertOutput
    \/ Terminated

(* Fair process - weak fairness on the next-state relation *)
Fairness == WF_vars(Next /\ pc # "done")

Spec == Init /\ [][Next]_vars /\ Fairness

(* -------------- Safety Invariants -------------- *)

(* Type invariant *)
TypeOK ==
    /\ pc \in {"start", "in_add", "ret_add", "after_add", 
               "call_tostr", "assert_input", "in_tostr", "ret_tostr", 
               "after_tostr", "assert_output", "done"}
    /\ x \in Int
    /\ y \in Int
    /\ result \in Int
    /\ input \in Int
    /\ output \in STRING

(* After Add completes, result should be x + y = 3 + 7 = 10 *)
AddResultCorrect ==
    (pc \in {"after_add", "call_tostr", "assert_input", "in_tostr", 
             "ret_tostr", "after_tostr", "assert_output", "done"}) 
    => (result = 10)

(* When we enter IntToStr, input must be 10 *)
InputIs10 ==
    (pc \in {"assert_input", "in_tostr", "ret_tostr", "after_tostr", 
             "assert_output", "done"}) 
    => (input = 10)

(* When process is done, output must be "10" *)
OutputIs10 ==
    (pc = "done") => (output = "10")

(* Stack is bounded *)
StackBounded ==
    Len(stack) <= 2

(* Combined safety invariant *)
SafetyInvariant ==
    /\ TypeOK
    /\ AddResultCorrect
    /\ InputIs10
    /\ OutputIs10
    /\ StackBounded

(* -------------- Liveness Properties -------------- *)

(* Termination: the process eventually reaches "done" *)
Termination == <>(pc = "done")

(* Progress: from start, we eventually call Add *)
ProgressToAdd == (pc = "start") ~> (pc = "in_add")

(* Progress: after Add, we eventually call IntToStr *)
ProgressToIntToStr == (pc = "after_add") ~> (pc = "in_tostr")

(* Progress: once in IntToStr, we eventually finish *)
ProgressToCompletion == (pc = "in_tostr") ~> (pc = "done")

(* The result will eventually be 10 *)
EventuallyResultIs10 == <>(result = 10)

(* The output will eventually be "10" *)
EventuallyOutputIs10 == <>(output = "10")

=============================================================================