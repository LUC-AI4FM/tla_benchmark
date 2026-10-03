------------------------------- MODULE PlusCalExample ------------------------------

CONSTANTS defaultInitValue

VARIABLES pc, localVars, stack

(*--algorithm PlusCalExample
variables x = 0, y = 0, resultStr = "";

fair process Main = 
1: x := 5;
2: call Add(x, y);
3: assert x = 10;
4: call ConvertToString(x);
5: assert resultStr = "10";
6: end;

procedure Add(a, b)
begin
    x := a + b;
    return;
end procedure;

procedure ConvertToString(n)
begin
    if n = 10 then
        resultStr := "10";
    else
        resultStr := "?";
    end if;
    return;
end procedure;
end algorithm;*)

\* BEGIN TRANSLATION

Spec ==
  /\ pc \in [Main \in {"1", "2", "3", "4", "5", "6"}]
  /\ localVars \in [Main \in ["x" \-> Nat, "y" \-> Nat, "resultStr" \-> STRING]]
  /\ stack \in Seq(<<p \in {"Add", "ConvertToString"}, args \in [<<"a">> \-> Nat]>>)

Init ==
  /\ pc = [Main \-> "1"]
  /\ localVars = [Main \-> ["x" \-> defaultInitValue, "y" \-> defaultInitValue, "resultStr" \-> ""]]
  /\ stack = <<>>

Next ==
  \/ /\ pc[Main] = "1"
     /\ localVars' = [localVars EXCEPT ![Main]["x"] = 5]
     /\ pc' = [pc EXCEPT ![Main] = "2"]
     /\ UNCHANGED stack
  \/ /\ pc[Main] = "2"
     /\ LET args == <<localVars[Main]["x"], localVars[Main]["y"]>> IN
        /\ stack' = Append(stack, <<p \-> "Add", args \-> ["a" \-> args[1]]>>)
     /\ pc' = [pc EXCEPT ![Main] = "2"]
  \/ /\ pc[Main] = "3"
     /\ LET top == Head(stack) IN
        /\ localVars' = [localVars EXCEPT ![Main]["x"] = top.args["a"]]
     /\ stack' = Tail(stack)
     /\ pc' = [pc EXCEPT ![Main] = "4"]
  \/ /\ pc[Main] = "3"
     /\ localVars[Main]["x"] = 10
     /\ pc' = [pc EXCEPT ![Main] = "5"]
     /\ UNCHANGED stack
  \/ /\ pc[Main] = "4"
     /\ LET args == <<localVars[Main]["x"]>> IN
        /\ stack' = Append(stack, <<p \-> "ConvertToString", args \-> ["a" \-> args[1]]>>)
     /\ pc' = [pc EXCEPT ![Main] = "4"]
  \/ /\ pc[Main] = "5"
     /\ LET top == Head(stack) IN
        /\ localVars' = [localVars EXCEPT ![Main]["resultStr"] = IF top.args["a"] = 10 THEN "10" ELSE "?"]
     /\ stack' = Tail(stack)
     /\ pc' = [pc EXCEPT ![Main] = "6"]
  \/ /\ pc[Main] = "5"
     /\ localVars[Main]["resultStr"] = "10"
     /\ pc' = [pc EXCEPT ![Main] = "6"]
     /\ UNCHANGED stack

Spec ==
  Init /\ [][Next]_<<pc, localVars, stack>>

\* END TRANSLATION
=============================================================================