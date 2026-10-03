---------------------------- MODULE TwoProcs ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS defaultInitValue

VARIABLES pc, stack, a, b, result, n, str, output

vars == << pc, stack, a, b, result, n, str, output >>

Init ==
    /\ pc = "Start"
    /\ stack = << >>
    /\ a = defaultInitValue
    /\ b = defaultInitValue
    /\ result = defaultInitValue
    /\ n = defaultInitValue
    /\ str = defaultInitValue
    /\ output = defaultInitValue

(* Procedure Add: adds two numbers and stores result *)
Add(arg_a, arg_b) ==
    /\ pc = "CallAdd"
    /\ a' = arg_a
    /\ b' = arg_b
    /\ pc' = "DoAdd"
    /\ UNCHANGED << stack, result, n, str, output >>

DoAdd ==
    /\ pc = "DoAdd"
    /\ result' = a + b
    /\ pc' = "ReturnAdd"
    /\ UNCHANGED << stack, a, b, n, str, output >>

ReturnAdd ==
    /\ pc = "ReturnAdd"
    /\ pc' = "AfterAdd"
    /\ UNCHANGED << stack, a, b, result, n, str, output >>

(* Procedure IntToString: converts integer to string *)
CallIntToString ==
    /\ pc = "CallIntToString"
    /\ n' = result
    /\ pc' = "CheckN"
    /\ UNCHANGED << stack, a, b, result, str, output >>

CheckN ==
    /\ pc = "CheckN"
    /\ Assert(n = 10, "Assertion failed: n should be 10")
    /\ pc' = "DoIntToString"
    /\ UNCHANGED << stack, a, b, result, n, str, output >>

DoIntToString ==
    /\ pc = "DoIntToString"
    /\ str' = IF n = 10 THEN "10"
              ELSE IF n = 0 THEN "0"
              ELSE "other"
    /\ pc' = "ReturnIntToString"
    /\ UNCHANGED << stack, a, b, result, n, output >>

ReturnIntToString ==
    /\ pc = "ReturnIntToString"
    /\ output' = str
    /\ pc' = "AfterIntToString"
    /\ UNCHANGED << stack, a, b, result, n, str >>

(* Main process flow *)
Start ==
    /\ pc = "Start"
    /\ stack' = << [procedure |-> "main", pc |-> "Done"] >>
    /\ a' = 3
    /\ b' = 7
    /\ pc' = "CallAdd"
    /\ UNCHANGED << result, n, str, output >>

AfterAdd ==
    /\ pc = "AfterAdd"
    /\ pc' = "CallIntToString"
    /\ UNCHANGED << stack, a, b, result, n, str, output >>

AfterIntToString ==
    /\ pc = "AfterIntToString"
    /\ Assert(output = "10", "Assertion failed: output should be \"10\"")
    /\ pc' = "CheckFinal"
    /\ UNCHANGED << stack, a, b, result, n, str, output >>

CheckFinal ==
    /\ pc = "CheckFinal"
    /\ pc' = "Done"
    /\ UNCHANGED << stack, a, b, result, n, str, output >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ DoAdd
    \/ ReturnAdd
    \/ AfterAdd
    \/ CallIntToString
    \/ CheckN
    \/ DoIntToString
    \/ ReturnIntToString
    \/ AfterIntToString
    \/ CheckFinal
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(* Safety Invariants *)
TypeOK ==
    /\ pc \in {"Start", "CallAdd", "DoAdd", "ReturnAdd", "AfterAdd",
               "CallIntToString", "CheckN", "DoIntToString", 
               "ReturnIntToString", "AfterIntToString", "CheckFinal", "Done"}
    /\ stack \in Seq([procedure : {"main"}, pc : {"Done"}])

ResultIs10WhenComputed ==
    pc \in {"CallIntToString", "CheckN", "DoIntToString", 
            "ReturnIntToString", "AfterIntToString", "CheckFinal", "Done"} 
    => result = 10

NIs10WhenSet ==
    pc \in {"CheckN", "DoIntToString", "ReturnIntToString", 
            "AfterIntToString", "CheckFinal", "Done"} 
    => n = 10

OutputIs10WhenSet ==
    pc \in {"AfterIntToString", "CheckFinal", "Done"} => output = "10"

SafetyInvariant ==
    /\ TypeOK
    /\ ResultIs10WhenComputed
    /\ NIs10WhenSet
    /\ OutputIs10WhenSet

(* Liveness Properties *)
Termination == <>(pc = "Done")

EventuallyOutput10 == <>(output = "10")

Progress == [](pc = "Start" => <>(pc = "Done"))

=============================================================================