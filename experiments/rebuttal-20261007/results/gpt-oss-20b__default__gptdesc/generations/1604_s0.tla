MODULE ProcSpec
EXTENDS Naturals, Sequences, TLC, String

VARIABLES pc, stack, result, outStr

vars == <<pc, stack, result, outStr>>

Push(rec) == stack' = Append(stack, rec)
Pop()    == stack' = SubSeq(stack, 1, Len(stack)-1)

Init ==
    /\ pc = 0
    /\ stack = <<>>
    /\ result = 0
    /\ outStr = ""

StartCallAdd ==
    /\ pc = 0
    /\ Push([proc |-> "add", ret |-> 2])
    /\ pc' = 1

AddProc ==
    /\ pc = 1
    /\ LET rec == stack[Len(stack)] IN
       /\ rec.proc = "add"
    /\ result' = 10
    /\ Pop()
    /\ pc' = 2

StartCallStr ==
    /\ pc = 2
    /\ LET prevRec == stack[Len(stack)] IN
       /\ prevRec.proc = "add"
    /\ Push([proc |-> "str", ret |-> 3])
    /\ pc' = 20

StrProc ==
    /\ pc = 20
    /\ LET rec == stack[Len(stack)] IN
       /\ rec.proc = "str"
    /\ outStr' = ToString(result)
    /\ Pop()
    /\ pc' = 3

End ==
    /\ pc = 3
    /\ UNCHANGED <<pc, stack, result, outStr>>

Next ==
    \/ StartCallAdd
    \/ AddProc
    \/ StartCallStr
    \/ StrProc
    \/ End

IntPassedInvariant ==
    /\ pc = 2
    /\ result = 10

OutputInvariant ==
    /\ pc = 3
    /\ outStr = "10"

Safety == IntPassedInvariant /\ OutputInvariant

TerminationLiveness == []<>(pc = 3)

FairnessProgress   == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Safety /\ TerminationLiveness /\ FairnessProgress

============================================================================