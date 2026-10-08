---- MODULE ProcedureCallSpec ----

EXTENDS Integers, Sequences, TLC

CONSTANTS pcInit, pcAdd, pcConvert, pcDone

VARIABLES 
    pc,        \* Program counter
    stack,     \* Stack of activation records
    localVar,  \* Local variables for each process
    result     \* Final output string

Init == 
    /\ pc = pcInit
    /\ stack = << >>
    /\ localVar = [pcInit |-> 0]
    /\ result = ""

Next == 
    \/ /\ pc = pcInit
       /\ pc' = pcAdd
       /\ stack' = Append(stack, [returnPc \-> pcDone])
       /\ localVar' = [localVar EXCEPT ![pcAdd] = 5 + 5]
       /\ UNCHANGED result
    \/ /\ pc = pcAdd
       /\ LET topRecord == Head(stack)
          IN /\ pc' = topRecord.returnPc
             /\ stack' = Tail(stack)
             /\ localVar' = [localVar EXCEPT ![pcDone] = IntToString(localVar[pcAdd])]
             /\ result' = localVar[pcDone]
    \/ /\ pc = pcDone
       /\ UNCHANGED <<pc, stack, localVar, result>>

Spec == 
    Init /\ [][Next]_<<pc, stack, localVar, result>> /\ WF_next(Next)

Fairness == 
    WF_pc(pcInit)

Termination ==
    <>(pc = pcDone) 

CorrectOutput ==
    [](result = "10")

AssertInteger ==
    \A s \in SUBSEQS(stack) : 
        LET topRecord == IF s = << >> THEN [returnPc \-> pcDone] ELSE Head(s)
        IN /\ (topRecord.returnPc = pcAdd => localVar[topRecord.returnPc] = 10)

Invariant ==
    \/ pc = pcInit
    \/ pc = pcAdd
    \/ pc = pcDone

THEOREM Spec => [](Invariant)

====