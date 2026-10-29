---------------------------- MODULE CallStackProgram ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT defaultInitValue

VARIABLES pc, stack, a, b, n, rv, output

vars == << pc, stack, a, b, n, rv, output >>

ExpectedOutput == "3"

Init ==
    /\ a = defaultInitValue
    /\ b = defaultInitValue
    /\ n = defaultInitValue
    /\ rv = defaultInitValue
    /\ output = defaultInitValue
    /\ stack = << >>
    /\ pc = "M1"

(***************************************************************************)
(* Procedure Add(a, b): returns a + b via rv, pops frame, restores locals  *)
(***************************************************************************)
Add_ ==
    /\ pc = "Add_"
    /\ stack # << >>
    /\ rv' = a + b
    /\ pc' = Head(stack).pc
    /\ a' = Head(stack).a
    /\ b' = Head(stack).b
    /\ stack' = Tail(stack)
    /\ UNCHANGED << n, output >>

Add == Add_

(***************************************************************************)
(* Procedure IntToStr(n): only handles the adder's result (3)              *)
(***************************************************************************)
IntToStr_ ==
    /\ pc = "IntToStr_"
    /\ stack # << >>
    /\ Assert(n = 3, "IntToStr invoked on an unsupported integer")
    /\ rv' = "3"
    /\ pc' = Head(stack).pc
    /\ n' = Head(stack).n
    /\ stack' = Tail(stack)
    /\ UNCHANGED << a, b, output >>

IntToStr == IntToStr_

(***************************************************************************)
(* Main sequence                                                           *)
(***************************************************************************)
M1 ==
    /\ pc = "M1"
    /\ a' = 1
    /\ b' = 2
    /\ stack' = << [ procedure |-> "Add",
                     pc        |-> "M2",
                     a         |-> a,
                     b         |-> b ] >> \o stack
    /\ pc' = "Add_"
    /\ UNCHANGED << n, rv, output >>

M2 ==
    /\ pc = "M2"
    /\ n' = rv
    /\ stack' = << [ procedure |-> "IntToStr",
                     pc        |-> "M3",
                     n         |-> n ] >> \o stack
    /\ pc' = "IntToStr_"
    /\ UNCHANGED << a, b, rv, output >>

M3 ==
    /\ pc = "M3"
    /\ output' = rv
    /\ pc' = "M4"
    /\ UNCHANGED << stack, a, b, n, rv >>

M4 ==
    /\ pc = "M4"
    /\ Assert(output = ExpectedOutput, "Output does not equal expected string")
    /\ pc' = "Done"
    /\ UNCHANGED << stack, a, b, n, rv, output >>

main == M1 \/ M2 \/ M3 \/ M4

Terminating ==
    /\ pc = "Done"
    /\ stack = << >>
    /\ UNCHANGED vars

Next == main \/ Add \/ IntToStr \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(main)
    /\ WF_vars(Add)
    /\ WF_vars(IntToStr)

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
OutputCorrect == (pc = "Done") => (output = ExpectedOutput /\ stack = << >>)

Termination == <>(pc = "Done")

MainTerminates == <>(pc = "Done" /\ stack = << >>)

THEOREM Spec => []OutputCorrect
THEOREM Spec => Termination
=============================================================================