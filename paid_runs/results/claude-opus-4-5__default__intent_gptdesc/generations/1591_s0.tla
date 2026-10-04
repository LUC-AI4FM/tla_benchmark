---------------------------- MODULE ParityChecker ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N

ASSUME N \in Nat

VARIABLES
    pc,           \* Program counter: "start", "in_even", "in_odd", "return", "done"
    stack,        \* Call stack: sequence of records [caller: STRING, arg: Nat]
    currentArg,   \* Current argument being processed
    result,       \* Final boolean result (TRUE if even)
    currentProc   \* Current procedure: "even" or "odd" or "none"

vars == <<pc, stack, currentArg, result, currentProc>>

TypeOK ==
    /\ pc \in {"start", "in_even", "in_odd", "return", "done"}
    /\ stack \in Seq([caller: {"even", "odd"}, arg: Nat])
    /\ currentArg \in Nat
    /\ result \in BOOLEAN \cup {NULL}
    /\ currentProc \in {"even", "odd", "none"}

NULL == CHOOSE x : x \notin BOOLEAN

Init ==
    /\ pc = "start"
    /\ stack = <<>>
    /\ currentArg = N
    /\ result = NULL
    /\ currentProc = "none"

StartEven ==
    /\ pc = "start"
    /\ pc' = "in_even"
    /\ currentProc' = "even"
    /\ UNCHANGED <<stack, currentArg, result>>

EvenBaseCase ==
    /\ pc = "in_even"
    /\ currentArg = 0
    /\ result' = TRUE
    /\ pc' = "return"
    /\ UNCHANGED <<stack, currentArg, currentProc>>

EvenRecursiveCall ==
    /\ pc = "in_even"
    /\ currentArg > 0
    /\ stack' = Append(stack, [caller |-> "even", arg |-> currentArg])
    /\ currentArg' = currentArg - 1
    /\ pc' = "in_odd"
    /\ currentProc' = "odd"
    /\ UNCHANGED <<result>>

OddBaseCase ==
    /\ pc = "in_odd"
    /\ currentArg = 0
    /\ result' = FALSE
    /\ pc' = "return"
    /\ UNCHANGED <<stack, currentArg, currentProc>>

OddRecursiveCall ==
    /\ pc = "in_odd"
    /\ currentArg > 0
    /\ stack' = Append(stack, [caller |-> "odd", arg |-> currentArg])
    /\ currentArg' = currentArg - 1
    /\ pc' = "in_even"
    /\ currentProc' = "even"
    /\ UNCHANGED <<result>>

ReturnToEven ==
    /\ pc = "return"
    /\ Len(stack) > 0
    /\ Head(Reverse(stack)).caller = "even"
    /\ currentArg' = Head(Reverse(stack)).arg
    /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
    /\ pc' = "return"
    /\ currentProc' = "even"
    /\ UNCHANGED <<result>>

ReturnToOdd ==
    /\ pc = "return"
    /\ Len(stack) > 0
    /\ Head(Reverse(stack)).caller = "odd"
    /\ currentArg' = Head(Reverse(stack)).arg
    /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
    /\ pc' = "return"
    /\ currentProc' = "odd"
    /\ UNCHANGED <<result>>

ReturnToMain ==
    /\ pc = "return"
    /\ Len(stack) = 0
    /\ pc' = "done"
    /\ currentProc' = "none"
    /\ UNCHANGED <<stack, currentArg, result>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ StartEven
    \/ EvenBaseCase
    \/ EvenRecursiveCall
    \/ OddBaseCase
    \/ OddRecursiveCall
    \/ ReturnToEven
    \/ ReturnToOdd
    \/ ReturnToMain
    \/ Done

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

StackBounded == Len(stack) <= N

StackElementsValid ==
    \A i \in 1..Len(stack) :
        /\ stack[i].caller \in {"even", "odd"}
        /\ stack[i].arg \in 1..N
        /\ stack[i].arg >= i

MonotonicArguments ==
    \A i \in 1..(Len(stack) - 1) :
        stack[i].arg > stack[i + 1].arg

CurrentArgBounded == currentArg <= N

AlternatingCallers ==
    \A i \in 1..(Len(stack) - 1) :
        stack[i].caller /= stack[i + 1].caller

StackIntegrity ==
    /\ StackBounded
    /\ StackElementsValid
    /\ CurrentArgBounded
    /\ (Len(stack) > 1 => AlternatingCallers)

ResultStableAfterDone ==
    (pc = "done") => (result /= NULL)

NoProcActiveWhenDone ==
    (pc = "done") => (currentProc = "none" /\ Len(stack) = 0)

FunctionalCorrectness ==
    (pc = "done") => (result = (N % 2 = 0))

SafetyInvariant ==
    /\ TypeOK
    /\ StackIntegrity
    /\ ResultStableAfterDone
    /\ NoProcActiveWhenDone
    /\ FunctionalCorrectness

Termination == <>(pc = "done")

EventualResult == <>(result /= NULL)

StackEventuallyEmpty == <>(Len(stack) = 0 /\ pc = "done")

LivenessProperties ==
    /\ Termination
    /\ EventualResult
    /\ StackEventuallyEmpty

=============================================================================