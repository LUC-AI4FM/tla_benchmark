---------------------------- MODULE specification ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANT defaultInitValue

VARIABLES pc, stack, retval, output, a, b, x

vars == << pc, stack, retval, output, a, b, x >>

Init == 
    /\ pc = "Lbl_1"
    /\ stack = << >>
    /\ retval = defaultInitValue
    /\ output = defaultInitValue
    /\ a = defaultInitValue
    /\ b = defaultInitValue
    /\ x = defaultInitValue

(* Procedure add(a, b) - adds two numbers and stores result in retval *)
add_entry == 
    /\ pc = "add_start"
    /\ retval' = a + b
    /\ pc' = "add_return"
    /\ UNCHANGED << stack, output, a, b, x >>

add_return ==
    /\ pc = "add_return"
    /\ \E frame \in {stack[1]} :
        /\ a' = frame.a
        /\ b' = frame.b
        /\ pc' = frame.pc
        /\ stack' = Tail(stack)
    /\ UNCHANGED << retval, output, x >>

(* Procedure to_string(x) - asserts x = 10 and stores "10" in retval *)
to_string_entry ==
    /\ pc = "to_string_start"
    /\ Assert(x = 10, "Assertion failed: x must equal 10")
    /\ retval' = "10"
    /\ pc' = "to_string_return"
    /\ UNCHANGED << stack, output, a, b, x >>

to_string_return ==
    /\ pc = "to_string_return"
    /\ \E frame \in {stack[1]} :
        /\ x' = frame.x
        /\ pc' = frame.pc
        /\ stack' = Tail(stack)
    /\ UNCHANGED << retval, output, a, b >>

(* Main process steps *)
Lbl_1 == 
    /\ pc = "Lbl_1"
    /\ stack' = << [pc |-> "Lbl_2", a |-> a, b |-> b] >> \o stack
    /\ a' = 3
    /\ b' = 7
    /\ pc' = "add_start"
    /\ UNCHANGED << retval, output, x >>

Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ stack' = << [pc |-> "Lbl_3", x |-> x] >> \o stack
    /\ x' = retval
    /\ pc' = "to_string_start"
    /\ UNCHANGED << retval, output, a, b >>

Lbl_3 ==
    /\ pc = "Lbl_3"
    /\ output' = retval
    /\ pc' = "Lbl_4"
    /\ UNCHANGED << stack, retval, a, b, x >>

Lbl_4 ==
    /\ pc = "Lbl_4"
    /\ Assert(output = "10", "Assertion failed: output must equal \"10\"")
    /\ pc' = "Done"
    /\ UNCHANGED << stack, retval, output, a, b, x >>

Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == 
    \/ Lbl_1
    \/ Lbl_2
    \/ Lbl_3
    \/ Lbl_4
    \/ add_entry
    \/ add_return
    \/ to_string_entry
    \/ to_string_return
    \/ Done

Spec == Init /\ [][Next]_vars 
        /\ WF_vars(Lbl_1)
        /\ WF_vars(Lbl_2)
        /\ WF_vars(Lbl_3)
        /\ WF_vars(Lbl_4)
        /\ WF_vars(add_entry)
        /\ WF_vars(add_return)
        /\ WF_vars(to_string_entry)
        /\ WF_vars(to_string_return)

Termination == <>(pc = "Done")

Liveness == Termination

=============================================================================