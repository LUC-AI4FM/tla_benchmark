---------------------------- MODULE Playground ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS defaultInitValue

VARIABLES pc, stack, retval, output, a, b, x

vars == <<pc, stack, retval, output, a, b, x>>

Init ==
    /\ pc = "Lbl_1"
    /\ stack = <<>>
    /\ retval = defaultInitValue
    /\ output = defaultInitValue
    /\ a = defaultInitValue
    /\ b = defaultInitValue
    /\ x = defaultInitValue

(* Procedure add(a, b) - adds two numbers and returns result in retval *)
add_call(arg_a, arg_b, return_label) ==
    /\ stack' = <<[procedure |-> "add", pc |-> return_label, a |-> a, b |-> b]>> \o stack
    /\ a' = arg_a
    /\ b' = arg_b
    /\ pc' = "add_body"
    /\ UNCHANGED <<retval, output, x>>

add_body ==
    /\ pc = "add_body"
    /\ retval' = a + b
    /\ pc' = "add_return"
    /\ UNCHANGED <<stack, output, a, b, x>>

add_return ==
    /\ pc = "add_return"
    /\ stack # <<>>
    /\ Head(stack).procedure = "add"
    /\ pc' = Head(stack).pc
    /\ a' = Head(stack).a
    /\ b' = Head(stack).b
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<retval, output, x>>

(* Procedure to_string(x) - asserts x = 10 and returns "10" in retval *)
to_string_call(arg_x, return_label) ==
    /\ stack' = <<[procedure |-> "to_string", pc |-> return_label, x |-> x]>> \o stack
    /\ x' = arg_x
    /\ pc' = "to_string_body"
    /\ UNCHANGED <<retval, output, a, b>>

to_string_body ==
    /\ pc = "to_string_body"
    /\ Assert(x = 10, "Assert failed: to_string argument must equal 10")
    /\ retval' = "10"
    /\ pc' = "to_string_return"
    /\ UNCHANGED <<stack, output, a, b, x>>

to_string_return ==
    /\ pc = "to_string_return"
    /\ stack # <<>>
    /\ Head(stack).procedure = "to_string"
    /\ pc' = Head(stack).pc
    /\ x' = Head(stack).x
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<retval, output, a, b>>

(* Main process steps *)
Lbl_1 == \* Call add(3, 7)
    /\ pc = "Lbl_1"
    /\ stack' = <<[procedure |-> "add", pc |-> "Lbl_2", a |-> a, b |-> b]>> \o stack
    /\ a' = 3
    /\ b' = 7
    /\ pc' = "add_body"
    /\ UNCHANGED <<retval, output, x>>

Lbl_2 == \* Call to_string(retval)
    /\ pc = "Lbl_2"
    /\ stack' = <<[procedure |-> "to_string", pc |-> "Lbl_3", x |-> x]>> \o stack
    /\ x' = retval
    /\ pc' = "to_string_body"
    /\ UNCHANGED <<retval, output, a, b>>

Lbl_3 == \* Copy retval to output
    /\ pc = "Lbl_3"
    /\ output' = retval
    /\ pc' = "Lbl_4"
    /\ UNCHANGED <<stack, retval, a, b, x>>

Lbl_4 == \* Final assertion and termination
    /\ pc = "Lbl_4"
    /\ Assert(output = "10", "Assert failed: output must equal \"10\"")
    /\ pc' = "Done"
    /\ UNCHANGED <<stack, retval, output, a, b, x>>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

(* Next state relation *)
Next ==
    \/ Lbl_1
    \/ add_body
    \/ add_return
    \/ Lbl_2
    \/ to_string_body
    \/ to_string_return
    \/ Lbl_3
    \/ Lbl_4
    \/ Done

(* Fairness conditions *)
Fairness ==
    /\ WF_vars(Lbl_1)
    /\ WF_vars(Lbl_2)
    /\ WF_vars(Lbl_3)
    /\ WF_vars(Lbl_4)
    /\ WF_vars(add_body)
    /\ WF_vars(add_return)
    /\ WF_vars(to_string_body)
    /\ WF_vars(to_string_return)

(* Specification *)
Spec == Init /\ [][Next]_vars /\ Fairness

(* Safety Invariants *)
TypeOK ==
    /\ pc \in {"Lbl_1", "Lbl_2", "Lbl_3", "Lbl_4", "add_body", "add_return", "to_string_body", "to_string_return", "Done"}
    /\ stack \in Seq([procedure : {"add", "to_string"}, pc : STRING, a : Int \cup {defaultInitValue}, b : Int \cup {defaultInitValue}, x : Int \cup {defaultInitValue}])

(* After add returns, retval should be 10 *)
AddResultCorrect ==
    (pc = "Lbl_2") => (retval = 10)

(* After to_string returns, retval should be "10" *)
ToStringResultCorrect ==
    (pc = "Lbl_3") => (retval = "10")

(* Final output correct *)
FinalOutputCorrect ==
    (pc = "Done") => (output = "10")

(* Liveness Properties *)
Termination == <>(pc = "Done")

Liveness == Termination

=============================================================================