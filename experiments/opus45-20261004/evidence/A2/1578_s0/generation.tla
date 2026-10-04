-------------------------------- MODULE Snark --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Procs, Address, Val, Dummy, NIL

ASSUME Dummy \in Address
ASSUME NIL \notin Address

(* Memory fields *)
Left == "left"
Right == "right"
Value == "value"

(* Special return values *)
Empty == "empty"
Full == "full"

VARIABLES Mem, freeList, LeftHat, RightHat, rVal, valBag, pc, stack, temp

vars == <<Mem, freeList, LeftHat, RightHat, rVal, valBag, pc, stack, temp>>

(* Addresses excluding Dummy for allocation *)
AllocAddress == Address \ {Dummy}

(* Initialize memory node *)
InitNode == [left |-> NIL, right |-> NIL, value |-> NIL]

(* Type definitions *)
MemType == [Address -> [left: Address \cup {NIL}, right: Address \cup {NIL}, value: Val \cup {NIL}]]

(* Helper: Bag operations *)
BagAdd(bag, v) == [bag EXCEPT ![v] = @ + 1]
BagRemove(bag, v) == [bag EXCEPT ![v] = @ - 1]
BagIn(v, bag) == bag[v] > 0

(* Labels for each process *)
Labels == {"T1", "PushRight_1", "PushRight_2", "PushRight_3", "PushRight_4", "PushRight_Done",
           "PushLeft_1", "PushLeft_2", "PushLeft_3", "PushLeft_4", "PushLeft_Done",
           "PopRight_1", "PopRight_2", "PopRight_3", "PopRight_4", "PopRight_Done",
           "PopLeft_1", "PopLeft_2", "PopLeft_3", "PopLeft_4", "PopLeft_Done",
           "HandleResult"}

Init ==
    /\ Mem = [a \in Address |-> IF a = Dummy 
                                THEN [left |-> Dummy, right |-> Dummy, value |-> NIL]
                                ELSE InitNode]
    /\ freeList = AllocAddress
    /\ LeftHat = Dummy
    /\ RightHat = Dummy
    /\ rVal = [p \in Procs |-> NIL]
    /\ valBag = [v \in Val |-> 0]
    /\ pc = [p \in Procs |-> "T1"]
    /\ stack = [p \in Procs |-> <<>>]
    /\ temp = [p \in Procs |-> [node |-> NIL, rh |-> NIL, lh |-> NIL, 
                                 rhR |-> NIL, lhL |-> NIL, val |-> NIL, op |-> NIL]]

(* Allocate a node from free list *)
Allocate(p) ==
    IF freeList = {}
    THEN /\ rVal' = [rVal EXCEPT ![p] = Full]
         /\ UNCHANGED <<freeList, Mem>>
    ELSE \E addr \in freeList:
         /\ freeList' = freeList \ {addr}
         /\ temp' = [temp EXCEPT ![p].node = addr]
         /\ Mem' = [Mem EXCEPT ![addr] = InitNode]
         /\ rVal' = [rVal EXCEPT ![p] = NIL]

(* Free a node back to free list *)
Free(addr) ==
    freeList' = freeList \cup {addr}

(* DCAS: Double Compare-and-Swap *)
(* Atomically: if Mem[a1][f1] = old1 and Mem[a2][f2] = old2, 
   set Mem[a1][f1] = new1 and Mem[a2][f2] = new2, return TRUE
   else return FALSE *)
DCAS(a1, f1, old1, new1, a2, f2, old2, new2) ==
    IF Mem[a1][f1] = old1 /\ Mem[a2][f2] = old2
    THEN /\ Mem' = [Mem EXCEPT ![a1][f1] = new1, ![a2][f2] = new2]
         /\ TRUE
    ELSE /\ UNCHANGED Mem
         /\ FALSE

(* ====================