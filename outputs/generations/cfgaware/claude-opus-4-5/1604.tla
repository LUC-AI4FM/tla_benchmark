---------------------------- MODULE specification ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANT defaultInitValue

VARIABLES pc, stack, x, y, result, n, output

vars == <<pc, stack, x, y, result, n, output>>

Init ==
    /\ pc = "start"
    /\ stack = <<>>
    /\ x = defaultInitValue
    /\ y = defaultInitValue
    /\ result = defaultInitValue
    /\ n = defaultInitValue
    /\ output = defaultInitValue

CallAdd ==
    /\ pc = "start"
    /\ stack' = <<[procedure |-> "Add", pc |-> "callIntToString", x |-> x, y |-> y, result |-> result]>> \o stack
    /\ x' = 5
    /\ y' = 5
    /\ result' = defaultInitValue
    /\ pc' = "addBody"
    /\ UNCHANGED <<n, output>>

AddBody ==
    /\ pc = "addBody"
    /\ result' = x + y
    /\ pc' = "addReturn"
    /\ UNCHANGED <<stack, x, y, n, output>>

AddReturn ==
    /\ pc = "addReturn"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
       IN /\ pc' = frame.pc
          /\ x' = frame.x
          /\ y' = frame.y
          /\ stack' = Tail(stack)
    /\ UNCHANGED <<result, n, output>>

CallIntToString ==
    /\ pc = "callIntToString"
    /\ Assert(result = 10, "Assertion failed: result should be 10 before IntToString")
    /\ stack' = <<[procedure |-> "IntToString", pc |-> "final", n |-> n, output |-> output]>> \o stack
    /\ n' = result
    /\ output' = defaultInitValue
    /\ pc' = "intToStringBody"
    /\ UNCHANGED <<x, y, result>>

IntToStringBody ==
    /\ pc = "intToStringBody"
    /\ output' = IF n = 10 THEN "10"
                 ELSE IF n = 0 THEN "0"
                 ELSE "other"
    /\ pc' = "intToStringReturn"
    /\ UNCHANGED <<stack, x, y, result, n>>

IntToStringReturn ==
    /\ pc = "intToStringReturn"
    /\ stack # <<>>
    /\ LET frame == Head(stack)
       IN /\ pc' = frame.pc
          /\ n' = frame.n
          /\ stack' = Tail(stack)
    /\ UNCHANGED <<x, y, result, output>>

Final ==
    /\ pc = "final"
    /\ Assert(output = "10", "Assertion failed: output should be '10'")
    /\ pc' = "Done"
    /\ UNCHANGED <<stack, x, y, result, n, output>>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ CallAdd
    \/ AddBody
    \/ AddReturn
    \/ CallIntToString
    \/ IntToStringBody
    \/ IntToStringReturn
    \/ Final
    \/ Terminating

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

Termination == <>(pc = "Done")

TypeOK ==
    /\ pc \in {"start", "addBody", "addReturn", "callIntToString", "intToStringBody", "intToStringReturn", "final", "Done"}
    /\ stack \in Seq([procedure : {"Add", "IntToString"}, pc : {"start", "addBody", "addReturn", "callIntToString", "intToStringBody", "intToStringReturn", "final", "Done"}, x : Int \cup {defaultInitValue}, y : Int \cup {defaultInitValue}, result : Int \cup {defaultInitValue}, n : Int \cup {defaultInitValue}, output : STRING \cup {defaultInitValue}])

=============================================================================