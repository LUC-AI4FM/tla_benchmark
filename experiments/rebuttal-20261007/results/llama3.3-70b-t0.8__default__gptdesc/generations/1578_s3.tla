```
MODULE DequeSpec
EXTENDS Integers, Sequences, Bags

CONSTANTS Addr, Val, NullNode, MaxProc
VARIABLES mem, leftHat, rightHat, freelist, 
          procVars, pc, valBag, testDone

Init ==
  /\ mem = [i \in Addr |-> NullNode]
  /\ leftHat = NullAddr
  /\ rightHat = NullAddr
  /\ freelist = Seq(Addr)
  /\ procVars = [i \in 1..MaxProc |-> <<>>, <<>>]
  /\ pc = [i \in 1..MaxProc |-> "T0"]
  /\ valBag = {}
  /\ testDone = FALSE

PushLeft ==
  /\ pc' = [pc EXCEPT ![1] = "T2"]
  /\ WITH p == procVars[1], node == CHOOSE n : n \notin freelist
        /\ mem' = [mem EXCEPT ![node] = [left |-> leftHat, right |-> NullAddr, val |-> p.val]]
        /\ leftHat' = node
        /\ freelist' = Append(freelist, node)
  /\ UNCHANGED rightHat
  /\ UNCHANGED procVars[2..MaxProc]
  /\ UNCHANGED pc[2..MaxProc]

PushRight ==
  /\ pc' = [pc EXCEPT ![1] = "T2"]
  /\ WITH p == procVars[1], node == CHOOSE n : n \notin freelist
        /\ mem' = [mem EXCEPT ![node] = [left |-> NullAddr, right |-> rightHat, val |-> p.val]]
        /\ rightHat' = node
        /\ freelist' = Append(freelist, node)
  /\ UNCHANGED leftHat
  /\ UNCHANGED procVars[2..MaxProc]
  /\ UNCHANGED pc[2..MaxProc]

PopLeft ==
  /\ pc' = [pc EXCEPT ![1] = "T3"]
  /\ WITH p == procVars[1], node == leftHat
        /\ mem' = [mem EXCEPT ![node] = NullNode]
        /\ leftHat' = mem[node].right
        /\ freelist' = Prepend(freelist, node)
        /\ valBag' = valBag \cup {p.val}
  /\ UNCHANGED rightHat
  /\ UNCHANGED procVars[2..MaxProc]
  /\ UNCHANGED pc[2..MaxProc]

PopRight ==
  /\ pc' = [pc EXCEPT ![1] = "T3"]
  /\ WITH p == procVars[1], node == rightHat
        /\ mem' = [mem EXCEPT ![node] = NullNode]
        /\ rightHat' = mem[node].left
        /\ freelist' = Prepend(freelist, node)
        /\ valBag' = valBag \cup {p.val}
  /\ UNCHANGED leftHat
  /\ UNCHANGED procVars[2..MaxProc]
  /\ UNCHANGED pc[2..MaxProc]

TestProcess ==
  \/ PushLeft
  \/ PushRight
  \/ PopLeft
  \/ PopRight

Next ==
  TestProcess

Spec == Init /\ [][Next]_<<mem, leftHat, rightHat, freelist, procVars, pc, valBag, testDone>>
            /\ WF_vars(TestProcess) <<mem, leftHat, rightHat, freelist, procVars, pc, valBag, testDone>>
            /\ [](valBag = {p.val : p \in ProcVars})

THEOREM Spec => []<>pc[1] = "T1"
```