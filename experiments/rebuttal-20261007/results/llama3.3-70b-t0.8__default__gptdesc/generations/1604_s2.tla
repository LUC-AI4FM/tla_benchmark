```
MODULE PlusCalExample
EXTENDS Integers, Strings

CONSTANTS ProcSet
VARIABLES pc, 
          x, 
          stack, 
          outputString

Init == 
  (pc = [i \in ProcSet |-> "Start"]) 
  /\ (x = [i \in ProcSet |-> 0]) 
  /\ (stack = [i \in ProcSet |-> <<>>]) 
  /\ (outputString = "")

Next == 
  (\E i \in ProcSet : 
    (pc[i] = "Start") 
      /\ (pc' = [pc EXCEPT ![i] = "Add"])
      /\ (x' = [x EXCEPT ![i] = 5])
      /\ (stack' = [stack EXCEPT ![i] = <<5>>])
      /\ (outputString' = outputString)
    \/ 
    (pc[i] = "Add") 
      /\ (pc' = [pc EXCEPT ![i] = "ConvertToString"])
      /\ (x' = [x EXCEPT ![i] = 10])
      /\ (stack' = stack)
      /\ (outputString' = outputString)
    \/ 
    (pc[i] = "ConvertToString") 
      /\ (pc' = [pc EXCEPT ![i] = "Done"])
      /\ (x' = x)
      /\ (stack' = stack)
      /\ (outputString' = "10")
  )

Spec == Init /\ [][Next]_<<pc, x, stack, outputString>>
           /\ WF_<<pc, x, stack, outputString>>(Next)

THEOREM Spec => []<>(pc["Process"] = "Done")
THEOREM Spec => <>[](outputString = "10" /\ pc["Process"] = "Done")
INVARIANT x["Process"] = 10
INVARIANT outputString = "10"
```