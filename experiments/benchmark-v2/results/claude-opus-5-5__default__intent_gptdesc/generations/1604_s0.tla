---------------------------- MODULE CallStackProgram ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT defaultInitValue

VARIABLES pc, stack, a, b, n, ret, output

vars == << pc, stack, a, b, n, ret, output >>

Expected == "3"

Labels == { "Lbl_1", "Lbl_2", "Lbl_3", "Lbl_4", "Add_1", "ToStr_1", "Done" }

TypeOK ==
    /\ pc \in Labels
    /\ stack \in Seq([procedure : {"Add", "ToString"},
                      pc        : Labels,
                      a         : Int \cup {defaultInitValue},
                      b         : Int \cup {defaultInitValue},
                      n         : Int \cup {defaultInitValue}])
    /\ ret \in Int \cup STRING \cup {defaultInitValue}
    /\ output \in STRING \cup {defaultInitValue}

Init ==
    /\ a = defaultInitValue
    /\ b = defaultInitValue
    /\ n = defaultInitValue
    /\ ret = defaultInitValue
    /\ output = defaultInitValue
    /\ stack = << >>
    /\ pc = "Lbl_1"

----------------------------------------------------------------------------
(* Procedure Add(a, b): returns a + b                                      *)

Add_1 ==
    /\ pc = "Add_1"
    /\ ret' = a + b
    /\ pc' = Head(stack).pc
    /\ a' = Head(stack).a
    /\ b' = Head(stack).b
    /\ stack' = Tail(stack)
    /\ UNCHANGED << n, output >>

Add == Add_1

(* Procedure ToString(n): only handles n = 3                               *)

ToStr_1 ==
    /\ pc = "ToStr_1"
    /\ Assert(n = 3, "Failure of assertion: ToString invoked on unsupported integer")
    /\ ret' = "3"
    /\ pc' = Head(stack).pc
    /\ n' = Head(stack).n
    /\ stack' = Tail(stack)
    /\ UNCHANGED << a, b, output >>

ToString == ToStr_1

----------------------------------------------------------------------------
(* Main sequence                                                           *)

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ stack' = << [ procedure |-> "Add",
                     pc        |-> "Lbl_2",
                     a         |-> a,
                     b         |-> b,
                     n         |-> n ] >> \o stack
    /\ a' = 1
    /\ b' = 2
    /\ pc' = "Add_1"
    /\ UNCHANGED << n, ret, output >>

Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ stack' = << [ procedure |-> "ToString",
                     pc        |-> "Lbl_3",
                     a         |-> a,
                     b         |-> b,
                     n         |-> n ] >> \o stack
    /\ n' = ret
    /\ pc' = "ToStr_1"
    /\ UNCHANGED << a, b, ret, output >>

Lbl_3 ==
    /\ pc = "Lbl_3"
    /\ output' = ret
    /\ pc' = "Lbl_4"
    /\ UNCHANGED << stack, a, b, n, ret >>

Lbl_4 ==
    /\ pc = "Lbl_4"
    /\ Assert(output = Expected, "Failure of assertion: output /= expected string")
    /\ pc' = "Done"
    /\ UNCHANGED << stack, a, b, n, ret, output >>

MainProc == Lbl_1 \/ Lbl_2 \/ Lbl_3 \/ Lbl_4

----------------------------------------------------------------------------

Terminating == pc = "Done" /\ UNCHANGED vars

Next == MainProc \/ Add \/ ToString \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(MainProc)
    /\ WF_vars(Add)
    /\ WF_vars(ToString)

----------------------------------------------------------------------------
(* Properties                                                              *)

\* Safety: whenever the program has finished, the output is the expected
\* string and the call stack is empty.
OutputCorrect == (pc = "Done") => (output = Expected /\ stack = << >>)

\* Safety: ToString is only ever entered with the integer 3.
ToStringArgOK == (pc = "ToStr_1") => (n = 3)

\* Liveness: the main process eventually terminates.
Termination == <>(pc = "Done")

\* Liveness: eventually reaches Done with an empty stack and the expected output.
EventuallyDoneCorrect == <>(pc = "Done" /\ stack = << >> /\ output = Expected)

THEOREM Spec => [](TypeOK /\ OutputCorrect /\ ToStringArgOK)
THEOREM Spec => Termination
=============================================================================