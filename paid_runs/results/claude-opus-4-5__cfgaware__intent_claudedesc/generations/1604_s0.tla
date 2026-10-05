---------------------------- MODULE specification ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANT defaultInitValue

(* --algorithm ProceduralComposition

variables
    \* Shared return value variables for procedure "returns"
    numResult = defaultInitValue,
    strResult = defaultInitValue,
    \* Output variable to store final result
    output = defaultInitValue;

procedure Add(a, b)
begin
    AddStep:
        numResult := a + b;
        assert numResult = 10;
        return;
end procedure;

procedure IntToString(n)
begin
    ConvertStep:
        \* Only handling the specific value 10 as per requirements
        if n = 10 then
            strResult := "10";
        else
            strResult := "unknown";
        end if;
        assert strResult = "10";
        return;
end procedure;

fair process Main = 0
begin
    CallAdd:
        call Add(3, 7);
    
    CallConvert:
        call IntToString(numResult);
    
    StoreResult:
        output := strResult;
        assert output = "10";
    
    Done:
        skip;
end process;

end algorithm; *)

\* BEGIN TRANSLATION - theass output is defined below.  DO NOT EDIT.
CONSTANT defaultInitValue
VARIABLES numResult, strResult, output, pc, stack, a, b, n

vars == << numResult, strResult, output, pc, stack, a, b, n >>

ProcSet == {0}

Init == (* Global variables *)
        /\ numResult = defaultInitValue
        /\ strResult = defaultInitValue
        /\ output = defaultInitValue
        (* Procedure Add *)
        /\ a = defaultInitValue
        /\ b = defaultInitValue
        (* Procedure IntToString *)
        /\ n = defaultInitValue
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "CallAdd"]

AddStep(self) == /\ pc[self] = "AddStep"
                 /\ numResult' = a + b
                 /\ Assert(numResult' = 10, 
                           "Failure of assertion at line 19, column 9.")
                 /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                 /\ a' = Head(stack[self]).a
                 /\ b' = Head(stack[self]).b
                 /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                 /\ UNCHANGED << strResult, output, n >>

Add(self) == AddStep(self)

ConvertStep(self) == /\ pc[self] = "ConvertStep"
                     /\ IF n = 10
                           THEN /\ strResult' = "10"
                           ELSE /\ strResult' = "unknown"
                     /\ Assert(strResult' = "10", 
                               "Failure of assertion at line 30, column 9.")
                     /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                     /\ n' = Head(stack[self]).n
                     /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                     /\ UNCHANGED << numResult, output, a, b >>

IntToString(self) == ConvertStep(self)

CallAdd == /\ pc[0] = "CallAdd"
           /\ /\ a' = 3
              /\ b' = 7
              /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "Add",
                                                    pc        |->  "CallConvert",
                                                    a         |->  a,
                                                    b         |->  b ] >>
                                                \o stack[0]]
           /\ pc' = [pc EXCEPT ![0] = "AddStep"]
           /\ UNCHANGED << numResult, strResult, output, n >>

CallConvert == /\ pc[0] = "CallConvert"
               /\ /\ n' = numResult
                  /\ stack' = [stack EXCEPT ![0] = << [ procedure |->  "IntToString",
                                                        pc        |->  "StoreResult",
                                                        n         |->  n ] >>
                                                    \o stack[0]]
               /\ pc' = [pc EXCEPT ![0] = "ConvertStep"]
               /\ UNCHANGED << numResult, strResult, output, a, b >>

StoreResult == /\ pc[0] = "StoreResult"
               /\ output' = strResult
               /\ Assert(output' = "10", 
                         "Failure of assertion at line 45, column 9.")
               /\ pc' = [pc EXCEPT ![0] = "Done"]
               /\ UNCHANGED << numResult, strResult, stack, a, b, n >>

Done == /\ pc[0] = "Done"
        /\ TRUE
        /\ pc' = [pc EXCEPT ![0] = "Finished"]
        /\ UNCHANGED << numResult, strResult, output, stack, a, b, n >>

Main == CallAdd \/ CallConvert \/ StoreResult \/ Done

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Finished"
               /\ UNCHANGED vars

Next == Main \/ Add(0) \/ IntToString(0)
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Main)
        /\ WF_vars(Add(0))
        /\ WF_vars(IntToString(0))

Termination == <>(\A self \in ProcSet: pc[self] = "Finished")

\* END TRANSLATION

=============================================================================