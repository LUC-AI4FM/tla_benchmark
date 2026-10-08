------------------------------- MODULE DoubleEndedQueue -------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC, PCal

CONSTANTS NumProcs, MemSize

VARIABLES mem, leftHat, rightHat, freeList, valBag, \* Shared state
            pc, opnd, opDone, localPtrL, localPtrR, tempPtr, prevNode, nextNode, \* Per-process local variables
            testPc                                  \* Test process program counter

ProcVars == <<pc, opnd, opDone, localPtrL, localPtrR, tempPtr, prevNode, nextNode>>

Init == /\ mem = [a \in 0..MemSize -> <<NIL, NIL>>]
        /\ leftHat = 0
        /\ rightHat = 1
        /\ freeList = {2 .. MemSize}
        /\ valBag = {}
        /\ testPc = "T1"
        /\ \A p \in 1..NumProcs : ProcVars'p = <<"PushLeft", 0, FALSE, NIL, NIL, NIL, NIL, NIL>>

Next == \/ \E p \in 1..NumProcs : pc[p] = "PushLeft" /\ PushLeft(p)
        \/ \E p \in 1..NumProcs : pc[p] = "PushRight" /\ PushRight(p)
        \/ \E p \in 1..NumProcs : pc[p] = "PopLeft" /\ PopLeft(p)
        \/ \E p \in 1..NumProcs : pc[p] = "PopRight" /\ PopRight(p)
        \/ testPc = "T1" /\ TestPushPop

PushLeft(p) == 
    /\ opnd'p = CHOOSE v \in {0 .. MemSize} : TRUE
    /\ localPtrL'p = leftHat
    /\ tempPtr'p = mem[leftHat][2]
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][1] = leftHat THEN
               /\ prevNode'p = localPtrL'p
               /\ nextNode'p = tempPtr'p
             ELSE
               /\ prevNode'p = tempPtr'p
               /\ nextNode'p = mem[prevNode'p][2]
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][1] = leftHat THEN
               /\ leftHat' = CHOOSE x \in freeList : TRUE
               /\ freeList' = freeList \ {leftHat'}
               /\ mem[leftHat']' = <<prevNode'p, nextNode'p>>
             ELSE
               /\ leftHat' = localPtrL'p
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][1] = leftHat THEN
               /\ valBag' = valBag \cup {opnd'p}
             ELSE
               /\ valBag' = valBag
    /\ pc[p]' = "PushLeft"
    /\ opDone'p = TRUE

PushRight(p) == 
    /\ opnd'p = CHOOSE v \in {0 .. MemSize} : TRUE
    /\ localPtrR'p = rightHat
    /\ tempPtr'p = mem[rightHat][1]
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][2] = rightHat THEN
               /\ prevNode'p = localPtrR'p
               /\ nextNode'p = tempPtr'p
             ELSE
               /\ prevNode'p = tempPtr'p
               /\ nextNode'p = mem[prevNode'p][1]
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][2] = rightHat THEN
               /\ rightHat' = CHOOSE x \in freeList : TRUE
               /\ freeList' = freeList \ {rightHat'}
               /\ mem[rightHat']' = <<prevNode'p, nextNode'p>>
             ELSE
               /\ rightHat' = localPtrR'p
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][2] = rightHat THEN
               /\ valBag' = valBag \cup {opnd'p}
             ELSE
               /\ valBag' = valBag
    /\ pc[p]' = "PushRight"
    /\ opDone'p = TRUE

PopLeft(p) ==
    /\ localPtrL'p = leftHat
    /\ tempPtr'p = mem[leftHat][2]
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][1] = leftHat THEN
               /\ prevNode'p = localPtrL'p
               /\ nextNode'p = tempPtr'p
             ELSE
               /\ prevNode'p = tempPtr'p
               /\ nextNode'p = mem[prevNode'p][2]
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][1] = leftHat THEN
               /\ opDone'p = FALSE
             ELSE
               /\ opDone'p = TRUE
               /\ valBag' = valBag \ {mem[nextNode'p][2]}
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][1] = leftHat THEN
               /\ leftHat' = localPtrL'p
             ELSE
               /\ leftHat' = nextNode'p
    /\ pc[p]' = "PopLeft"

PopRight(p) ==
    /\ localPtrR'p = rightHat
    /\ tempPtr'p = mem[rightHat][1]
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][2] = rightHat THEN
               /\ prevNode'p = localPtrR'p
               /\ nextNode'p = tempPtr'p
             ELSE
               /\ prevNode'p = tempPtr'p
               /\ nextNode'p = mem[prevNode'p][1]
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][2] = rightHat THEN
               /\ opDone'p = FALSE
             ELSE
               /\ opDone'p = TRUE
               /\ valBag' = valBag \ {mem[prevNode'p][1]}
    /\ IF \/ tempPtr'p = NIL
           \/ /\ tempPtr'p /= NIL
              /\ mem[tempPtr'p][2] = rightHat THEN
               /\ rightHat' = localPtrR'p
             ELSE
               /\ rightHat' = prevNode'p
    /\ pc[p]' = "PopRight"

TestPushPop ==
    /\ testPc' \in {"T1", "PushLeft", "PopLeft", "PushRight", "PopRight"}
    /\ IF testPc' = "PushLeft" THEN PushLeft(NumProcs + 1)
    /\ IF testPc' = "PopLeft" THEN PopLeft(NumProcs + 1)
    /\ IF testPc' = "PushRight" THEN PushRight(NumProcs + 1)
    /\ IF testPc' = "PopRight" THEN PopRight(NumProcs + 1)

Spec == Init /\ [][Next]_<<mem, leftHat, rightHat, freeList, valBag>> \* Shared state
                        /\ _/\A p \in 1..NumProcs : [][Next]_<ProcVars'p> \* Per-process local variables
                        /\ <><testPc = "T1">_<<mem, leftHat, rightHat, freeList, valBag>> \* Test process liveness

Invariant == /\ valBag \subseteq {0 .. MemSize}
             /\ \A a \in 0..MemSize : mem[a] \in (0..MemSize) \X (0..MemSize)

WFSpec == Spec /\ WF_<<mem, leftHat, rightHat, freeList, valBag>>_(<>Next)
                /\ _/\A p \in 1..NumProcs : WF_<ProcVars'p>_(<>Next)
                /\ WF_testPc_<>(<>Next)

=============================================================================