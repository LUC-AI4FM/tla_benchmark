---------------------------- MODULE ParityChecker ----------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N

VARIABLES pc, arg, result, stack

vars == <<pc, arg, result, stack>>

(* Initial state: invoke IsEven on input N *)
Init ==
    /\ pc = "call_even"
    /\ arg = N
    /\ result = FALSE
    /\ stack = <<>>

(* Call IsEven: if arg = 0, return TRUE; else call IsOdd(arg-1) *)
CallEven ==
    /\ pc = "call_even"
    /\ IF arg = 0
       THEN /\ result' = TRUE
            /\ IF stack = <<>>
               THEN pc' = "done"
               ELSE /\ pc' = Head(stack).returnTo
                    /\ stack' = Tail(stack)
                    /\ arg' = Head(stack).savedArg
       ELSE /\ stack' = Append(stack, [savedArg |-> arg, returnTo |-> "ret_from_odd"])
            /\ arg' = arg - 1
            /\ pc' = "call_odd"
            /\ result' = result

(* Call IsOdd: if arg = 0, return FALSE; else call IsEven(arg-1) *)
CallOdd ==
    /\ pc = "call_odd"
    /\ IF arg = 0
       THEN /\ result' = FALSE
            /\ IF stack = <<>>
               THEN pc' = "done"
               ELSE /\ pc' = Head(stack).returnTo
                    /\ stack' = Tail(stack)
                    /\ arg' = Head(stack).savedArg
       ELSE /\ stack' = Append(stack, [savedArg |-> arg, returnTo |-> "ret_from_even"])
            /\ arg' = arg - 1
            /\ pc' = "call_even"
            /\ result' = result

(* Return from IsOdd call back to IsEven: propagate result *)
ReturnFromOdd ==
    /\ pc = "ret_from_odd"
    /\ IF stack = <<>>
       THEN /\ pc' = "done"
            /\ UNCHANGED <<arg, result, stack>>
       ELSE /\ pc' = Head(stack).returnTo
            /\ arg' = Head(stack).savedArg
            /\ stack' = Tail(stack)
            /\ UNCHANGED result

(* Return from IsEven call back to IsOdd: propagate result *)
ReturnFromEven ==
    /\ pc = "ret_from_even"
    /\ IF stack = <<>>
       THEN /\ pc' = "done"
            /\ UNCHANGED <<arg, result, stack>>
       ELSE /\ pc' = Head(stack).returnTo
            /\ arg' = Head(stack).savedArg
            /\ stack' = Tail(stack)
            /\ UNCHANGED result

(* Terminal state: do nothing *)
Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ CallEven
    \/ CallOdd
    \/ ReturnFromOdd
    \/ ReturnFromEven
    \/ Done

(* Fairness: ensure progress when not done *)
Fairness ==
    /\ WF_vars(CallEven)
    /\ WF_vars(CallOdd)
    /\ WF_vars(ReturnFromOdd)
    /\ WF_vars(ReturnFromEven)

Spec == Init /\ [][Next]_vars /\ Fairness

(* Type invariant *)
TypeOK ==
    /\ pc \in {"call_even", "call_odd", "ret_from_odd", "ret_from_even", "done"}
    /\ arg \in Nat
    /\ result \in BOOLEAN
    /\ stack \in Seq([savedArg: Nat, returnTo: {"ret_from_odd", "ret_from_even"}])

(* Stack depth is bounded by the argument at each call plus pending returns *)
StackBounded ==
    Len(stack) <= N

(* When done, the stack must be empty *)
StackEmptyWhenDone ==
    pc = "done" => stack = <<>>

(* No procedure is active after termination *)
NoActiveAfterDone ==
    pc = "done" => pc' = "done"

(* Functional correctness: when done, result is TRUE iff N is even *)
FunctionalCorrectness ==
    pc = "done" => (result = (N % 2 = 0))

(* Combined safety invariant *)
SafetyInvariant ==
    /\ TypeOK
    /\ StackBounded
    /\ StackEmptyWhenDone
    /\ FunctionalCorrectness

(* Liveness: the system eventually terminates *)
Termination == <>(pc = "done")

(* Additional invariant: stack entries preserve valid return locations *)
StackIntegrity ==
    \A i \in 1..Len(stack): 
        stack[i].returnTo \in {"ret_from_odd", "ret_from_even"}

(* Result stability: once done, result doesn't change *)
ResultStable ==
    [](pc = "done" => [](result = (N % 2 = 0)))

=============================================================================