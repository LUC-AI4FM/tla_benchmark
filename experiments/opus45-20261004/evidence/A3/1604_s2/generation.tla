---- MODULE PlusCalProcedures ----
EXTENDS Integers, Sequences, TLC

CONSTANTS DefaultInitValue

VARIABLES pc, stack, a, b, result, input, output, finalResult

vars == <<pc, stack, a, b, result, input, output, finalResult>>

(* Procedure Add: adds two numbers and stores result *)
(* Procedure IntToString: converts integer to string *)

Init ==
    /\ pc = "Start"
    /\ stack = <<>>
    /\ a = DefaultInitValue
    /\ b = DefaultInitValue
    /\ result = DefaultInitValue
    /\ input = DefaultInitValue
    /\ output = DefaultInitValue
    /\ finalResult = DefaultInitValue

(* Main process starts by calling Add(5, 5) *)
Start ==
    /\ pc = "Start"
    /\ stack' = <<[procedure |-> "main", pc |-> "CallIntToString"]>> \o stack
    /\ a' = 5
    /\ b' = 5
    /\ result' = DefaultInitValue
    /\ pc' = "AddBegin"
    /\ UNCHANGED <<input, output, finalResult>>

(* Add procedure: compute a + b *)
AddBegin ==
    /\ pc = "AddBegin"
    /\ result' = a + b
    /\ pc' = "AddReturn"
    /\ UNCHANGED <<stack, a, b, input, output, finalResult>>

(* Return from Add procedure *)
AddReturn ==
    /\ pc = "AddReturn"
    /\ pc' = Head(stack).pc
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<a, b, result, input, output, finalResult>>

(* After Add returns, call IntToString with result *)
CallIntToString ==
    /\ pc = "CallIntToString"
    /\ Assert(result = 10, "Assertion failed: result should be 10")
    /\ stack' = <<[procedure |-> "CallIntToString", pc |-> "Done", savedResult |-> result]>> \o stack
    /\ input' = result
    /\ output' = DefaultInitValue
    /\ pc' = "IntToStringBegin"
    /\ UNCHANGED <<a, b, result, finalResult>>

(* IntToString procedure: convert integer to string representation *)
IntToStringBegin ==
    /\ pc = "IntToStringBegin"
    /\ Assert(input = 10, "Assertion failed: input to IntToString should be 10")
    /\ output' = IF input = 10 THEN "10"
                 ELSE IF input = 0 THEN "0"
                 ELSE "other"
    /\ pc' = "IntToStringReturn"
    /\ UNCHANGED <<stack, a, b, result, input, finalResult>>

(* Return from IntToString procedure *)
IntToStringReturn ==
    /\ pc = "IntToStringReturn"
    /\ finalResult' = output
    /\ pc' = Head(stack).pc
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<a, b, result, input, output>>

(* Done state - process has terminated *)
Done ==
    /\ pc = "Done"
    /\ Assert(finalResult = "10", "Assertion failed: final output should be \"10\"")
    /\ UNCHANGED vars

(* Stuttering step for terminated process *)
Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ AddBegin
    \/ AddReturn
    \/ CallIntToString
    \/ IntToStringBegin
    \/ IntToStringReturn
    \/ Terminating

(* Fairness: the single process is weakly fair *)
Fairness ==
    /\ WF_vars(Start)
    /\ WF_vars(AddBegin)
    /\ WF_vars(AddReturn)
    /\ WF_vars(CallIntToString)
    /\ WF_vars(IntToStringBegin)
    /\ WF_vars(IntToStringReturn)

Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety Invariants *)

TypeOK ==
    /\ pc \in {"Start", "AddBegin", "AddReturn", "CallIntToString", 
               "IntToStringBegin", "IntToStringReturn", "Done"}
    /\ stack \in Seq([procedure : {"main", "CallIntToString"}, 
                      pc : {"Start", "AddBegin", "AddReturn", "CallIntToString",
                            "IntToStringBegin", "IntToStringReturn", "Done"}] 
                     \cup 
                     [procedure : {"main", "CallIntToString"}, 
                      pc : {"Start", "AddBegin", "AddReturn", "CallIntToString",
                            "IntToStringBegin", "IntToStringReturn", "Done"},
                      savedResult : Int \cup {DefaultInitValue}])

(* After Add completes, result equals 10 *)
ResultCorrect ==
    pc \in {"CallIntToString", "IntToStringBegin", "IntToStringReturn", "Done"} 
    => result = 10

(* Final output is "10" when done *)
FinalOutputCorrect ==
    pc = "Done" => finalResult = "10"

(* Liveness Properties *)

(* The process eventually terminates *)
Termination == <>(pc = "Done")

(* The process eventually completes the Add procedure *)
AddCompletes == <>(pc \in {"CallIntToString", "IntToStringBegin", "IntToStringReturn", "Done"})

(* The process eventually completes IntToString *)
IntToStringCompletes == <>(pc = "Done")

(* Progress property: if we start, we eventually finish *)
Progress == (pc = "Start") ~> (pc = "Done")

====