----------------------------- MODULE DoubleEndedQueue -----------------------------

EXTENDS TLC, Sequences, FiniteSets, Integers

CONSTANTS NumProcesses, MaxAddress

VARIABLES mem, leftHat, rightHat, freeList, pc, valBag

Init == /\ mem = [a \in 1..MaxAddress -> <<NIL, NIL>>]
        /\ leftHat = 0
        /\ rightHat = 0
        /\ freeList = {a \in 1..MaxAddress}
        /\ pc = [p \in 1..NumProcesses -> "T1"]
        /\ valBag = {}

Next == 
    \/ \E p \in 1..NumProcesses : pc[p] = "T1" /\ \E x \in {0, 1} :
        LET op == IF x=0 THEN "pushLeft" ELSE "pushRight"
        IN /\ freeList /= {}
           /\ PCSet(p, op)
    \/ \E p \in 1..NumProcesses : pc[p] = "pushLeft" /\
        LET addr == Choose(freeList) 
            newHat == <<addr, leftHat>>
        IN /\ mem' = [mem EXCEPT ![addr] = <<NIL, leftHat>>]
           /\ freeList' = freeList \ {addr}
           /\ leftHat' = addr
           /\ PCSet(p, "T1")
    \/ \E p \in 1..NumProcesses : pc[p] = "pushRight" /\
        LET addr == Choose(freeList) 
            newHat == <<rightHat, addr>>
        IN /\ mem' = [mem EXCEPT ![addr] = <<rightHat, NIL>>]
           /\ freeList' = freeList \ {addr}
           /\ rightHat' = addr
           /\ PCSet(p, "T1")
    \/ \E p \in 1..NumProcesses : pc[p] = "T1" /\ \E x \in {0, 1} :
        LET op == IF x=0 THEN "popLeft" ELSE "popRight"
        IN /\ (leftHat # rightHat)
           /\ PCSet(p, op)
    \/ \E p \in 1..NumProcesses : pc[p] = "popLeft" /\
        LET oldAddr == leftHat
            nextAddr == mem[leftHat][2]
        IN /\ mem' = [mem EXCEPT ![leftHat] = <<NIL, NIL>>]
           /\ freeList' = freeList \cup {oldAddr}
           /\ leftHat' = nextAddr
           /\ valBag' = valBag \ {mem[oldAddr][1]}
           /\ PCSet(p, "T1")
    \/ \E p \in 1..NumProcesses : pc[p] = "popRight" /\
        LET oldAddr == rightHat
            prevAddr == mem[rightHat][1]
        IN /\ mem' = [mem EXCEPT ![rightHat] = <<NIL, NIL>>]
           /\ freeList' = freeList \cup {oldAddr}
           /\ rightHat' = prevAddr
           /\ valBag' = valBag \ {mem[oldAddr][1]}
           /\ PCSet(p, "T1")

PCSet(p, op) ==
    /\ pc' = [pc EXCEPT ![p] = op]

Spec == Init /\ [][Next]_<<pc>>

Safety == 
    \/ leftHat # rightHat => mem[leftHat][2] /= NIL
    \/ leftHat # rightHat => mem[rightHat][1] /= NIL

Liveness ==
    \A p \in 1..NumProcesses : WF_next(p, "T1")

WF_next(p, s) == 
    <>(/\ pc[p] = s)

THEOREM Spec => []Safety /\ <>Liveness

=============================================================================