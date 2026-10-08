```
MODULE PlusCalExample
EXTENDS Integers, Strings

CONSTANTS ProcSet
VARIABLES pc, 
          localVars, 
          stack, 
          outputString,
          x

Init == (pc = "Start") /\ (localVars = [i |-> 0]) /\ (stack = <<>> ) /\ (outputString = "") /\ (x = 0)

TypeInvariant == pc \in ProcSet /\ localVars \in [ProcSet -> Int] /\ stack \in Seq(ProcSet) /\ outputString \in String

Next == IF pc = "Start" THEN
            (* call addition procedure *)
            pc' = "Addition"
          ELSE IF pc = "Addition" THEN
            (* perform addition and push result onto stack *)
            x' = 10
          ELSE IF pc = "AdditionDone" THEN
            (* pop result from stack, call string conversion procedure *)
            pc' = "StringConversion"
          ELSE IF pc = "StringConversion" THEN
            (* convert integer to string *)
            outputString' = "10"
          ELSE 
            (* return from procedures *)
            pc' = "Done"
          END

Spec == Init /\ [][Next]_<<pc, localVars, stack, outputString, x>>
           /\ WF-vars(Next) <<pc, localVars, stack, outputString, x>>

THEOREM Spec => []TypeInvariant
THEOREM Spec => <>(outputString = "10")
THEOREM Spec => <>[](x = 10)
```