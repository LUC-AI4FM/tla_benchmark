---------------------------- MODULE ProcedureComposition ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS StringTen

VARIABLES pc, stack, retVal, output, arg1, arg2, argN

vars == <<pc, stack, retVal, output, arg1, arg2, argN>>

(* 
--algorithm ProcedureComposition
variables retVal = 0, output = "";

procedure Add(a, b)
begin
    AddStep:
        retVal := a + b;
        assert retVal = 10;
        return;
end procedure;

procedure IntToString(n)
begin
    ConvertStep:
        if n = 10 then
            retVal := "10";
        else
            retVal := "unknown";
        end if;
        assert retVal = "10";
        return;
end procedure;

fair process Main = 0
begin
    CallAdd:
        call Add(3, 7);
    
    PassResult:
        call IntToString(retVal);
    
    StoreOutput:
        output := retVal;
        assert output = "10";
    
    Done:
        skip;
end process;

end algorithm;
*)

\* BEGIN TRANSLATION
Init == 
    /\ retVal = 0
    /\ output = ""
    /\ arg1 = 0
    /\ arg2 = 0
    /\ argN = 0
    /\ stack = <<>>
    /\ pc = "CallAdd"

AddStep ==
    /\ pc = "AddStep"
    /\ retVal' = arg1 + arg2
    /\ Assert(retVal' = 10, "Assertion failed: retVal = 10 in Add")
    /\ pc' = Head(stack).pc
    /\ arg1' = Head(stack).arg1
    /\ arg2' = Head(stack).arg2
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<output, argN>>

ConvertStep ==
    /\ pc = "ConvertStep"
    /\ IF argN = 10
       THEN retVal' = "10"
       ELSE retVal' = "unknown"
    /\ Assert(retVal' = "10", "Assertion failed: retVal = \"10\" in IntToString")
    /\ pc' = Head(stack).pc
    /\ argN' = Head(stack).argN
    /\ stack' = Tail(stack)
    /\ UNCHANGED <<output, arg1, arg2>>

CallAdd ==
    /\ pc = "CallAdd"
    /\ stack' = <<[pc |-> "PassResult", arg1 |-> arg1, arg2 |-> arg2, argN |-> argN]>> \o stack
    /\ arg1' = 3
    /\ arg2' = 7
    /\ pc' = "AddStep"
    /\ UNCHANGED <<retVal, output, argN>>

PassResult ==
    /\ pc = "PassResult"
    /\ stack' = <<[pc |-> "StoreOutput", arg1 |-> arg1, arg2 |-> arg2, argN |-> argN]>> \o stack
    /\ argN' = retVal
    /\ pc' = "ConvertStep"
    /\ UNCHANGED <<retVal, output, arg1, arg2>>

StoreOutput ==
    /\ pc = "StoreOutput"
    /\ output' = retVal
    /\ Assert(output' = "10", "Assertion failed: output = \"10\"")
    /\ pc' = "Done"
    /\ UNCHANGED <<retVal, stack, arg1, arg2, argN>>

DoneStep ==
    /\ pc = "Done"
    /\ TRUE
    /\ pc' = "Terminated"
    /\ UNCHANGED <<retVal, output, stack, arg1, arg2, argN>>

Terminated ==
    /\ pc = "Terminated"
    /\ UNCHANGED vars

Next == 
    \/ AddStep
    \/ ConvertStep
    \/ CallAdd
    \/ PassResult
    \/ StoreOutput
    \/ DoneStep
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* END TRANSLATION

(* Safety Invariants *)

TypeOK ==
    /\ pc \in {"CallAdd", "AddStep", "PassResult", "ConvertStep", "StoreOutput", "Done", "Terminated"}
    /\ output \in STRING \cup {""}

CorrectOutput ==
    pc = "Terminated" => output = "10"

(* Liveness Properties *)

EventuallyCompleted ==
    <>(pc = "Terminated")

EventuallyHasOutput ==
    <>(output = "10")

=============================================================================