```
MODULE PlusCalExample
EXTENDS Integers, Strings

CONSTANTS ProcSet
VARIABLES pc, 
          x, 
          s, 
          stack

Init ==
  /\ pc = [i \in ProcSet |-> "Start"]
  /\ x = [i \in ProcSet |-> 0]
  /\ s = [i \in ProcSet |-> ""]
  /\ stack = [i \in ProcSet |-> <<>>]

Next == 
  /\ \E i \in ProcSet : 
    (pc[i] = "Start" /\ 
     pc' = [pc EXCEPT ![i] = "Add"]
     /\ x' = [x EXCEPT ![i] = 5 + 5]
     /\ s' = s
     /\ stack' = [stack EXCEPT ![i] = <<("Add", 10)>> @ stack[i]])
    \lor 
    (pc[i] = "Add" /\ 
     pc' = [pc EXCEPT ![i] = "ToString"]
     /\ x' = x
     /\ s' = [s EXCEPT ![i] = IntToStr(10)]
     /\ stack' = [stack EXCEPT ![i] = <<>>])
    \lor 
    (pc[i] = "ToString" /\ pc' = [pc EXCEPT ![i] = "Done"]
                   /\ x' = x
                   /\ s' = s
                   /\ stack' = stack)
  /\ \A j \in ProcSet \ {i} : 
      pc'[j] = pc[j]
      /\ x'[j] = x[j]
      /\ s'[j] = s[j]
      /\ stack'[j] = stack[j]

Spec == Init /\ [][Next]_<<pc, x, s, stack>>

THEOREM Spec => []<>(\A i \in ProcSet : pc[i] = "Done" /\ x[i] = 10 /\ s[i] = "10")
```
Note: The `IntToStr` function used in the specification is assumed to be defined elsewhere.