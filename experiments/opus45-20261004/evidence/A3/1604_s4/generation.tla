---------------------------- MODULE PlusCalProcedures ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS MaxInt

VARIABLES pc, stack, x, y, result, n, str, output

vars == <<pc, stack, x, y, result, n, str, output>>

\* Process identifiers
ProcSet == {"main"}

\* Initial state
Init ==
    /\ pc = [self \in ProcSet |-> "Start"]
    /\ stack = [self \in ProcSet |-> << >>]
    /\ x = [self \in ProcSet |-> 0]
    /\ y = [self \in ProcSet |-> 0]
    /\ result = [self \in ProcSet |-> 0]
    /\ n = [self \in ProcSet |-> 0]
    /\ str = [self \in ProcSet |-> ""]
    /\ output = [self \in ProcSet |-> ""]

\* Helper function to convert integer to string
IntToString(i) ==
    CASE i = 0 -> "0"
      [] i = 1 -> "1"
      [] i = 2 -> "2"
      [] i = 3 -> "3"
      [] i = 4 -> "4"
      [] i = 5 -> "5"
      [] i = 6 -> "6"
      [] i = 7 -> "7"
      [] i = 8 -> "8"
      [] i = 9 -> "9"
      [] i = 10 -> "10"
      [] i = 11 -> "11"
      [] i = 12 -> "12"
      [] OTHER -> "?"

\* Main process starts and calls Add procedure
Start(self) ==
    /\ pc[self] = "Start"
    /\ x' = [x EXCEPT ![self] = 3]
    /\ y' = [y EXCEPT ![self] = 7]
    /\ stack' = [stack EXCEPT ![self] = <<[procedure |-> "Add",
                                            pc |-> "CallToString",
                                            x |-> x[self],
                                            y |-> y[self],
                                            result |-> result[self]]>> \o stack[self]]
    /\ pc' = [pc EXCEPT ![self] = "AddStart"]
    /\ UNCHANGED <<result, n, str, output>>

\* Add procedure: start
AddStart(self) ==
    /\ pc[self] = "AddStart"
    /\ result' = [result EXCEPT ![self] = x[self] + y[self]]
    /\ pc' = [pc EXCEPT ![self] = "AddReturn"]
    /\ UNCHANGED <<stack, x, y, n, str, output>>

\* Add procedure: return
AddReturn(self) ==
    /\ pc[self] = "AddReturn"
    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
    /\ x' = [x EXCEPT ![self] = Head(stack[self]).x]
    /\ y' = [y EXCEPT ![self] = Head(stack[self]).y]
    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
    /\ UNCHANGED <<result, n, str, output>>

\* After Add returns, call ToString procedure
CallToString(self) ==
    /\ pc[self] = "CallToString"
    \* Assertion: the integer passed to ToString should be 10
    /\ Assert(result[self] = 10, "Assertion failed: result should be 10 before calling ToString")
    /\ n' = [n EXCEPT ![self] = result[self]]
    /\ stack' = [stack EXCEPT ![self] = <<[procedure |-> "ToString",
                                            pc |-> "Finish",
                                            n |-> n[self],
                                            str |-> str[self]]>> \o stack[self]]
    /\ pc' = [pc EXCEPT ![self] = "ToStringStart"]
    /\ UNCHANGED <<x, y, result, str, output>>

\* ToString procedure: start
ToStringStart(self) ==
    /\ pc[self] = "ToStringStart"
    /\ str' = [str EXCEPT ![self] = IntToString(n[self])]
    /\ pc' = [pc EXCEPT ![self] = "ToStringReturn"]
    /\ UNCHANGED <<stack, x, y, result, n, output>>

\* ToString procedure: return
ToStringReturn(self) ==
    /\ pc[self] = "ToStringReturn"
    /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
    /\ n' = [n EXCEPT ![self] = Head(stack[self]).n]
    /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
    /\ UNCHANGED <<x, y, result, str, output>>

\* Finish: store output and verify assertion
Finish(self) ==
    /\ pc[self] = "Finish"
    /\ output' = [output EXCEPT ![self] = str[self]]
    \* Assertion: the final output string should be "10"
    /\ Assert(str[self] = "10", "Assertion failed: output string should be \"10\"")
    /\ pc' = [pc EXCEPT ![self] = "Done"]
    /\ UNCHANGED <<stack, x, y, result, n, str>>

\* Termination state
Done(self) ==
    /\ pc[self] = "Done"
    /\ FALSE
    /\ UNCHANGED vars

\* Next state relation for process
main(self) ==
    \/ Start(self)
    \/ AddStart(self)
    \/ AddReturn(self)
    \/ CallToString(self)
    \/ ToStringStart(self)
    \/ ToStringReturn(self)
    \/ Finish(self)

\* Combined Next state relation
Next ==
    \/ \E self \in ProcSet: main(self)
    \/ (* Disjunct to prevent deadlock on termination *)
       (\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars

\* Fairness condition for the main process
Fairness == \A self \in ProcSet: WF_vars(main(self))

\* Specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Termination property
Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* Type invariant
TypeOK ==
    /\ pc \in [ProcSet -> {"Start", "AddStart", "AddReturn", "CallToString", 
                           "ToStringStart", "ToStringReturn", "Finish", "Done"}]
    /\ x \in [ProcSet -> Int]
    /\ y \in [ProcSet -> Int]
    /\ result \in [ProcSet -> Int]
    /\ n \in [ProcSet -> Int]
    /\ str \in [ProcSet -> STRING]
    /\ output \in [ProcSet -> STRING]

\* Safety invariant: result is always non-negative after computation
ResultNonNegative ==
    \A self \in ProcSet:
        pc[self] \in {"CallToString", "ToStringStart", "ToStringReturn", "Finish", "Done"}
        => result[self] >= 0

\* Safety invariant: when at CallToString, result must be 10
ResultIsTen ==
    \A self \in ProcSet:
        pc[self] = "CallToString" => result[self] = 10

\* Safety invariant: when finished, output must be "10"
OutputIsTenString ==
    \A self \in ProcSet:
        pc[self] = "Done" => output[self] = "10"

\* Liveness: eventually the result becomes 10
EventuallyResultIsTen ==
    <>(\E self \in ProcSet: result[self] = 10)

\* Liveness: eventually the output is "10"
EventuallyOutputIsTen ==
    <>(\E self \in ProcSet: output[self] = "10")

\* Progress property: from Start we eventually reach Done
Progress ==
    \A self \in ProcSet:
        pc[self] = "Start" ~> pc[self] = "Done"

===============================================================================