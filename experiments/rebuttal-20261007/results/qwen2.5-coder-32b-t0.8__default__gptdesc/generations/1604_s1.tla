------------------------------ MODULE PlusCalProgram ------------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS MaxInt

VARIABLES pc, result, strResult, stack, localVars

(*--algorithm PlusCalAlgorithm

variables result = 0, strResult = "", stack = <<>>, localVars = [<<>> -> [<<"result">> |-> 0]]

fair process (P \in {1})
begin
Addition:
    localVars[stack] := localVars[stack] @ ["result" :> 5 + 5]
    stack := Append(stack, <<>>)
    pc := "ConvertToString"
    
ConvertToString:
    result := localVars[stack]["result"]
    assert result = 10;
    strResult := IntToString(result)
    assert strResult = "10";
    stack := Tail(stack)
    pc := "Done"

Done:
    skip
end process

end algorithm*)

Init == /\ pc = "Addition"
        /\ result = 0
        /\ strResult = ""
        /\ stack = <<>>
        /\ localVars = [<<>> -> [<<"result">> |-> 0]]

Next ==
    \/ /\ pc = "Addition"
       /\ result' = result
       /\ strResult' = strResult
       /\ stack' = Append(stack, <<>>)
       /\ localVars' = [stack' EXCEPT ![stack'] = [<<"result">> |-> 5 + 5]]
       /\ pc' = "ConvertToString"
    \/ /\ pc = "ConvertToString"
       /\ result' \in Integers
       /\ strResult' \in {"", "10"}
       /\ stack' = Tail(stack)
       /\ localVars' = [stack EXCEPT ![stack] = <<>>]
       /\ pc' = "Done"
       /\ UNCHANGED <<result, strResult>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<result, strResult, stack, localVars>>
       /\ pc' = "Done"

Spec == Init /\ [][Next]_<<pc>>

Fairness == WF_next(<<pc>>)

Termination ==
  <>(pc = "Done" /\ result = 10 /\ strResult = "10")

Theorem == Spec => []<>Termination

================================================================================