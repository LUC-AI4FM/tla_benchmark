------------------------------- MODULE DoubleEndedQueue -------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NumProcesses

VARIABLES mem, leftHat, rightHat, freeList, valBag, progs

vars == <<mem, leftHat, rightHat, freeList, valBag, progs>>

Init ==
  /\ mem = [a \in Nat -> <<NIL, NIL>>] 
  /\ leftHat = 0
  /\ rightHat = 1
  /\ freeList = {2..}
  /\ valBag = {}
  /\ progs = [p \in 1..NumProcesses -> "T1"]

Next ==
  \/ \E p \in 1..NumProcesses :
     /\ progs[p] = "T1"
     /\ (\/ mem[leftHat][2] # NIL
         /\ freeList # {}
         -> /\ valBag' = valBag \cup {x}
            /\ LET newAddr == CHOOSE addr \in freeList : TRUE
               newMem == [mem EXCEPT ![leftHat] = <<NIL, newAddr>>, ![newAddr] = <<NIL, leftHat>>]
               newLeftHat == newAddr
               newFreeList == freeList \ {newAddr}
            IN /\ mem' = newMem
               /\ leftHat' = newLeftHat
               /\ freeList' = newFreeList
               /\ progs'[p] = "T2"
         \/ mem[rightHat][1] # NIL
         /\ freeList # {}
         -> /\ valBag' = valBag \cup {x}
            /\ LET newAddr == CHOOSE addr \in freeList : TRUE
               newMem == [mem EXCEPT ![rightHat] = <<newAddr, NIL>>, ![newAddr] = <<rightHat, NIL>>]
               newRightHat == newAddr
               newFreeList == freeList \ {newAddr}
            IN /\ mem' = newMem
               /\ rightHat' = newRightHat
               /\ freeList' = newFreeList
               /\ progs'[p] = "T3"
         \/ mem[leftHat][2] # NIL
         -> /\ valBag' = valBag \ {x}
            /\ LET oldAddr == leftHat
               [oldNode, nextAddr] == mem[oldAddr]
               newMem == [mem EXCEPT ![nextAddr] = <<NIL, mem[nextAddr][2]]>]
               newLeftHat == nextAddr
               newFreeList == freeList \cup {oldAddr}
            IN /\ mem' = newMem
               /\ leftHat' = newLeftHat
               /\ freeList' = newFreeList
               /\ progs'[p] = "T4"
         \/ mem[rightHat][1] # NIL
         -> /\ valBag' = valBag \ {x}
            /\ LET oldAddr == rightHat
               [prevAddr, oldNode] == mem[oldAddr]
               newMem == [mem EXCEPT ![prevAddr] = <<mem[prevAddr][1], NIL>>]]
               newRightHat == prevAddr
               newFreeList == freeList \cup {oldAddr}
            IN /\ mem' = newMem
               /\ rightHat' = newRightHat
               /\ freeList' = newFreeList
               /\ progs'[p] = "T5"
         \/ TRUE
         -> /\ valBag' = valBag
            /\ mem' = mem
            /\ leftHat' = leftHat
            /\ rightHat' = rightHat
            /\ freeList' = freeList
            /\ progs'[p] = "T1")
  \/ \E p \in 1..NumProcesses :
     /\ progs[p] \in {"T2", "T3", "T4", "T5"}
     /\ valBag' = valBag
     /\ mem' = mem
     /\ leftHat' = leftHat
     /\ rightHat' = rightHat
     /\ freeList' = freeList
     /\ progs'[p] = "T1"

Spec ==
  WF_vars(Init, Next) /\ 
  \A p \in 1..NumProcesses : SF_vars("T1", progs[p])

THEOREM Spec => []<>[]progs[1] = "T1"
=============================================================================