---------------------------- MODULE ProcedureCalls ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANT Proc            \* identifier of the single process

VARIABLES result, output, pc, stack, a, b, n

vars == << result, output, pc, stack, a, b, n >>

ProcSet == {Proc}

\* Integer to string conversion helpers
Digit(d) == CASE d = 0 -> "0" [] d = 1 -> "1" [] d = 2 -> "2" [] d = 3 -> "3"
              [] d = 4 -> "4" [] d = 5 -> "5" [] d = 6 -> "6" [] d = 7 -> "7"
              [] d = 8 -> "8" [] d = 9 -> "9"

RECURSIVE IntToStr(_)
IntToStr(x) == IF x < 0 THEN "-" \o IntToStr(-x)
               ELSE IF x < 10 THEN Digit(x)
               ELSE IntToStr(x \div 10) \o Digit(x % 10)

Init == /\ result = 0
        /\ output = ""
        /\ a = [self \in ProcSet |-> 0]
        /\ b = [self \in ProcSet |-> 0]
        /\ n = [self \in ProcSet |-> 0]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Main1"]

----------------------------------------------------------------------------
\* procedure Add(a, b) { Add1: result := a + b; return; }
Add1(self) == /\ pc[self] = "Add1"
              /\ result' = a[self] + b[self]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ a' = [a EXCEPT ![self] = Head(stack[self]).a]
              /\ b' = [b EXCEPT ![self] = Head(stack[self]).b]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << output, n >>

Add(self) == Add1(self)

\* procedure ToStr(n) { ToStr1: assert n = 10; output := IntToStr(n); return; }
ToStr1(self) == /\ pc[self] = "ToStr1"
                /\ Assert(n[self] = 10,
                          "Failure of assertion: integer passed to ToStr is not 10")
                /\ output' = IntToStr(n[self])
                /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                /\ n' = [n EXCEPT ![self] = Head(stack[self]).n]
                /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                /\ UNCHANGED << result, a, b >>

ToStr(self) == ToStr1(self)

----------------------------------------------------------------------------
\* fair process main
Main1(self) == /\ pc[self] = "Main1"
               /\ stack' = [stack EXCEPT ![self] =
                              << [ procedure |-> "Add",
                                   pc        |-> "Main2",
                                   a         |-> a[self],
                                   b         |-> b[self] ] >> \o stack[self]]
               /\ a' = [a EXCEPT ![self] = 3]
               /\ b' = [b EXCEPT ![self] = 7]
               /\ pc' = [pc EXCEPT ![self] = "Add1"]
               /\ UNCHANGED << result, output, n >>

Main2(self) == /\ pc[self] = "Main2"
               /\ stack' = [stack EXCEPT ![self] =
                              << [ procedure |-> "ToStr",
                                   pc        |-> "Main3",
                                   n         |-> n[self] ] >> \o stack[self]]
               /\ n' = [n EXCEPT ![self] = result]
               /\ pc' = [pc EXCEPT ![self] = "ToStr1"]
               /\ UNCHANGED << result, output, a, b >>

Main3(self) == /\ pc[self] = "Main3"
               /\ Assert(output = "10",
                         "Failure of assertion: final output is not \"10\"")
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << result, output, stack, a, b, n >>

main(self) == Main1(self) \/ Main2(self) \/ Main3(self)

\* Allow infinite stuttering to prevent deadlock on termination
Terminating == /\ \A self \in ProcSet : pc[self] = "Done"
               /\ UNCHANGED vars

Next == \/ \E self \in ProcSet : Add(self) \/ ToStr(self) \/ main(self)
        \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in ProcSet : WF_vars(main(self) \/ Add(self) \/ ToStr(self))

----------------------------------------------------------------------------
\* Safety properties

TypeOK == /\ result \in Int
          /\ output \in {"", "10"}
          /\ pc \in [ProcSet -> {"Main1", "Main2", "Main3", "Add1", "ToStr1", "Done"}]
          /\ a \in [ProcSet -> Int]
          /\ b \in [ProcSet -> Int]
          /\ n \in [ProcSet -> Int]

ToStrArgIsTen == \A self \in ProcSet : pc[self] = "ToStr1" => n[self] = 10

OutputCorrect == \A self \in ProcSet :
                    pc[self] \in {"Main3", "Done"} => output = "10"

StackBounded == \A self \in ProcSet : Len(stack[self]) <= 1

\* Liveness properties

Termination == <>(\A self \in ProcSet : pc[self] = "Done")

EventuallyOutput == <>(output = "10")

ResultLeadsToOutput == (result = 10) ~> (output = "10")

ProgressFromStart == \A self \in ProcSet :
                        (pc[self] = "Main1") ~> (pc[self] = "Done")

=============================================================================