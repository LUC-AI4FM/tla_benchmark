------------------------------ MODULE EvenOdd ------------------------------

EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES pc, stack, result

Top(s) == s[Len(s)]

Pop(s) == SubSeq(s, 1, Len(s) - 1)

ReplaceTop(s, x) == [ i \in 1..Len(s) |-> IF i < Len(s) THEN s[i] ELSE x ]

Push(s, x) == Append(s, x)

Init ==
    /\ pc = "Start"
    /\ stack = << >>
    /\ result \in BOOLEAN
    /\ N \in Nat

StartStep ==
    /\ pc = "Start"
    /\ pc' = "Step"
    /\ stack' = << [proc |-> "Even", phase |-> "enter", xEven |-> N] >>
    /\ UNCHANGED result

StepToDone ==
    /\ pc = "Step"
    /\ stack = << >>
    /\ pc' = "Done"
    /\ UNCHANGED << stack, result >>

StepEvenEnterZero ==
    /\ pc = "Step"
    /\ stack # << >>
    /\ LET f == Top(stack) IN /\ f.proc = "Even" /\ f.phase = "enter" /\ f.xEven = 0
    /\ result' = TRUE
    /\ stack' = Pop(stack)
    /\ pc' = "Step"

StepEvenEnterNonZero ==
    /\ pc = "Step"
    /\ stack # << >>
    /\ LET f == Top(stack) IN /\ f.proc = "Even" /\ f.phase = "enter" /\ f.xEven \in Nat /\ f.xEven > 0
    /\ stack' =
        Push(
          ReplaceTop(stack, [proc |-> "Even", phase |-> "wait", xEven |-> f.xEven]),
          [proc |-> "Odd", phase |-> "enter", xOdd |-> f.xEven - 1]
        )
    /\ UNCHANGED result
    /\ pc' = "Step"

StepEvenWait ==
    /\ pc = "Step"
    /\ stack # << >>
    /\ LET f == Top(stack) IN /\ f.proc = "Even" /\ f.phase = "wait"
    /\ stack' = Pop(stack)
    /\ UNCHANGED result
    /\ pc' = "Step"

StepOddEnterZero ==
    /\ pc = "Step"
    /\ stack # << >>
    /\ LET f == Top(stack) IN /\ f.proc = "Odd" /\ f.phase = "enter" /\ f.xOdd = 0
    /\ result' = FALSE
    /\ stack' = Pop(stack)
    /\ pc' = "Step"

StepOddEnterNonZero ==
    /\ pc = "Step"
    /\ stack # << >>
    /\ LET f == Top(stack) IN /\ f.proc = "Odd" /\ f.phase = "enter" /\ f.xOdd \in Nat /\ f.xOdd > 0
    /\ stack' =
        Push(
          ReplaceTop(stack, [proc |-> "Odd", phase |-> "wait", xOdd |-> f.xOdd]),
          [proc |-> "Even", phase |-> "enter", xEven |-> f.xOdd - 1]
        )
    /\ UNCHANGED result
    /\ pc' = "Step"

StepOddWait ==
    /\ pc = "Step"
    /\ stack # << >>
    /\ LET f == Top(stack) IN /\ f.proc = "Odd" /\ f.phase = "wait"
    /\ stack' = Pop(stack)
    /\ UNCHANGED result
    /\ pc' = "Step"

Next ==
    StartStep
    \/ StepToDone
    \/ StepEvenEnterZero
    \/ StepEvenEnterNonZero
    \/ StepEvenWait
    \/ StepOddEnterZero
    \/ StepOddEnterNonZero
    \/ StepOddWait

vars == << pc, stack, result >>

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

Termination ==
    <> (pc = "Done")

=============================================================================