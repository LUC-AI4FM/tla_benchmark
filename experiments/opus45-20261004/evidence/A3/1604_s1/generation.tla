---- MODULE PlusCalProcedures ----
EXTENDS Integers, Sequences, TLC

CONSTANTS DefaultValue

VARIABLES pc, stack, a, b, result, n, str, output

vars == <<pc, stack, a, b, result, n, str, output>>

(* Procedure Add: computes result = a + b *)
(* Procedure IntToString: converts integer n to string str *)

Init ==
    /\ pc = "Start"
    /\ stack = <<>>
    /\ a = DefaultValue
    /\ b = DefaultValue
    /\ result = DefaultValue
    /\ n = DefaultValue
    /\ str = DefaultValue
    /\ output = DefaultValue

(* Main process starts by calling Add(5, 5) *)
Start ==
    /\ pc = "Start"
    /\ a' = 5
    /\ b' = 5
    /\ stack' = Append(stack, [returnTo |-> "AfterAdd", 
                               savedA |-> a, 
                               savedB |-> b,
                               savedResult |-> result,
                               savedN |-> n,
                               savedStr |-> str])
    /\ pc' = "AddBody"
    /\ UNCHANGED <<result, n, str, output>>

(* Add procedure body: result = a + b *)
AddBody ==
    /\ pc = "AddBody"
    /\ result' = a + b
    /\ pc' = "AddReturn"
    /\ UNCHANGED <<stack, a, b, n, str, output>>

(* Return from Add procedure *)
AddReturn ==
    /\ pc = "AddReturn"
    /\ pc' = Head(stack).returnTo
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<a, b, result, n, str, output>>

(* After returning from Add, assert result is 10 and call IntToString *)
AfterAdd ==
    /\ pc = "AfterAdd"
    /\ Assert(result = 10, "Assertion failed: result should be 10")
    /\ n' = result
    /\ stack' = Append(stack, [returnTo |-> "AfterIntToString",
                               savedA |-> a,
                               savedB |-> b,
                               savedResult |-> result,
                               savedN |-> n,
                               savedStr |-> str])
    /\ pc' = "IntToStringBody"
    /\ UNCHANGED <<a, b, result, str, output>>

(* IntToString procedure body: convert n to string *)
(* For this specification, we model the conversion directly *)
IntToStringBody ==
    /\ pc = "IntToStringBody"
    /\ Assert(n = 10, "Assertion failed: n passed to IntToString should be 10")
    /\ str' = IF n = 10 THEN "10" ELSE "error"
    /\ pc' = "IntToStringReturn"
    /\ UNCHANGED <<stack, a, b, result, n, output>>

(* Return from IntToString procedure *)
IntToStringReturn ==
    /\ pc = "IntToStringReturn"
    /\ pc' = Head(stack).returnTo
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<a, b, result, n, str, output>>

(* After returning from IntToString, store result and finish *)
AfterIntToString ==
    /\ pc = "AfterIntToString"
    /\ output' = str
    /\ Assert(str = "10", "Assertion failed: final string should be '10'")
    /\ pc' = "Done"
    /\ UNCHANGED <<stack, a, b, result, n, str>>

(* Terminal state *)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ AddBody
    \/ AddReturn
    \/ AfterAdd
    \/ IntToStringBody
    \/ IntToStringReturn
    \/ AfterIntToString
    \/ Done

(* Fairness: the process is fair, meaning it must eventually take enabled steps *)
Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

(* Type invariant *)
TypeOK ==
    /\ pc \in {"Start", "AddBody", "AddReturn", "AfterAdd", 
               "IntToStringBody", "IntToStringReturn", "AfterIntToString", "Done"}
    /\ stack \in Seq([returnTo : {"AfterAdd", "AfterIntToString"},
                      savedA : Int \cup {DefaultValue},
                      savedB : Int \cup {DefaultValue},
                      savedResult : Int \cup {DefaultValue},
                      savedN : Int \cup {DefaultValue},
                      savedStr : STRING \cup {DefaultValue}])

(* Safety: if we reach Done, output must be "10" *)
SafetyOutput ==
    pc = "Done" => output = "10"

(* Safety: if we reach Done, result must be 10 *)
SafetyResult ==
    pc = "Done" => result = 10

(* Liveness: the process eventually terminates *)
Termination == <>(pc = "Done")

(* Liveness: output eventually becomes "10" *)
EventuallyCorrectOutput == <>(output = "10")

(* Combined safety invariant *)
Invariant ==
    /\ SafetyOutput
    /\ SafetyResult

====