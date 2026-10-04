---------------------------- MODULE spec ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS defaultInitValue, Val

CONSTANTS Procs, Addrs

Null == CHOOSE n : n \notin Addrs

VARIABLES
    mem,
    leftHat,
    rightHat,
    freeList,
    pc,
    op,
    localVal,
    localAddr,
    localLeft,
    localRight,
    localLeftNext,
    localRightPrev,
    result,
    pushedVals,
    poppedVals

vars == <<mem, leftHat, rightHat, freeList, pc, op, localVal, localAddr,
          localLeft, localRight, localLeftNext, localRightPrev, result,
          pushedVals, poppedVals>>

ProcVars == <<pc, op, localVal, localAddr, localLeft, localRight,
              localLeftNext, localRightPrev, result>>

Status == {"okay", "empty", "full", "pending"}

TypeOK ==
    /\ mem \in [Addrs -> [left: Addrs \cup {Null}, right: Addrs \cup {Null}, val: Val \cup {defaultInitValue}]]
    /\ leftHat \in Addrs \cup {Null}
    /\ rightHat \in Addrs \cup {Null}
    /\ freeList \subseteq Addrs
    /\ pc \in [Procs -> {"idle", "pushLeft1", "pushLeft2", "pushRight1", "pushRight2",
                         "popLeft1", "popLeft2", "popRight1", "popRight2", "done"}]
    /\ op \in [Procs -> {"pushLeft", "pushRight", "popLeft", "popRight", "none"}]
    /\ localVal \in [Procs -> Val \cup {defaultInitValue}]
    /\ localAddr \in [Procs -> Addrs \cup {Null}]
    /\ localLeft \in [Procs -> Addrs \cup {Null}]
    /\ localRight \in [Procs -> Addrs \cup {Null}]
    /\ localLeftNext \in [Procs -> Addrs \cup {Null}]
    /\ localRightPrev \in [Procs -> Addrs \cup {Null}]
    /\ result \in [Procs -> Status]
    /\ pushedVals \in SUBSET (Procs \times Val)
    /\ poppedVals \in SUBSET (Procs \times Val)

DummyAddr == CHOOSE a \in Addrs : TRUE

Init ==
    /\ mem = [a \in Addrs |-> [left |-> Null, right |-> Null, val |-> defaultInitValue]]
    /\ leftHat = DummyAddr
    /\ rightHat = DummyAddr
    /\ freeList = Addrs \ {DummyAddr}
    /\ pc = [p \in Procs |-> "idle"]
    /\ op = [p \in Procs |-> "none"]
    /\ localVal = [p \in Procs |-> defaultInitValue]
    /\ localAddr = [p \in Procs |-> Null]
    /\ localLeft = [p \in Procs |-> Null]
    /\ localRight = [p \in Procs |-> Null]
    /\ localLeftNext = [p \in Procs |-> Null]
    /\ localRightPrev = [p \in Procs |-> Null]
    /\ result = [p \in Procs |-> "pending"]
    /\ pushedVals = {}
    /\ poppedVals = {}

Alloc(p) ==
    IF freeList = {}
    THEN <<Null, freeList>>
    ELSE LET addr == CHOOSE a \in freeList : TRUE
         IN <<addr, freeList \ {addr}>>

Free(addr, fl) ==
    IF addr = Null \/ addr = DummyAddr
    THEN fl
    ELSE fl \cup {addr}

StartOp(p, operation, v) ==
    /\ pc[p] = "idle"
    /\ op' = [op EXCEPT ![p] = operation]
    /\ localVal' = [localVal EXCEPT ![p] = v]
    /\ result' = [result EXCEPT ![p] = "pending"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freeList, localAddr, localLeft,
                   localRight, localLeftNext, localRightPrev, pushedVals, poppedVals>>

StartPushLeft(p, v) ==
    /\ StartOp(p, "pushLeft", v)
    /\ pc' = [pc EXCEPT ![p] = "pushLeft1"]

StartPushRight(p, v) ==
    /\ StartOp(p, "pushRight", v)
    /\ pc' = [pc EXCEPT ![p] = "pushRight1"]

StartPopLeft(p) ==
    /\ StartOp(p, "popLeft", defaultInitValue)
    /\ pc' = [pc EXCEPT ![p] = "popLeft1"]

StartPopRight(p) ==
    /\ StartOp(p, "popRight", defaultInitValue)
    /\ pc' = [pc EXCEPT ![p] = "popRight1"]

PushLeft1(p) ==
    /\ pc[p] = "pushLeft1"
    /\ LET allocResult == Alloc(p)
           addr == allocResult[1]
           newFreeList == allocResult[2]
       IN IF addr = Null
          THEN /\ result' = [result EXCEPT ![p] = "full"]
               /\ pc' = [pc EXCEPT ![p] = "done"]
               /\ UNCHANGED <<mem, leftHat, rightHat, freeList, localAddr,
                              localLeft, localRight, localLeftNext, localRightPrev,
                              pushedVals, poppedVals, op, localVal>>
          ELSE /\ localAddr' = [localAddr EXCEPT ![p] = addr]
               /\ freeList' = newFreeList
               /\ localLeft' = [localLeft EXCEPT ![p] = leftHat]
               /\ localRight' = [localRight EXCEPT ![p] = rightHat]
               /\ pc' = [pc EXCEPT ![p] = "pushLeft2"]
               /\ UNCHANGED <<mem, leftHat, rightHat, result, localLeftNext,
                              localRightPrev, pushedVals, poppedVals, op, localVal>>

PushLeft2(p) ==
    /\ pc[p] = "pushLeft2"
    /\ LET lh == localLeft[p]
           rh == localRight[p]
           nd == localAddr[p]
           v == localVal[p]
       IN IF lh = leftHat /\ rh = rightHat
          THEN IF lh = rh
               THEN /\ mem' = [mem EXCEPT ![nd] = [left |-> Null, right |-> Null, val |-> v]]
                    /\ leftHat' = nd
                    /\ rightHat' = nd
                    /\ result' = [result EXCEPT ![p] = "okay"]
                    /\ pc' = [pc EXCEPT ![p] = "done"]
                    /\ pushedVals' = pushedVals \cup {<<p, v>>}
                    /\ UNCHANGED <<freeList, localAddr, localLeft, localRight,
                                   localLeftNext, localRightPrev, poppedVals, op, localVal>>
               ELSE /\ mem' = [mem EXCEPT ![nd] = [left |-> Null, right |-> lh, val |-> v],
                                          ![lh] = [@ EXCEPT !.left = nd]]
                    /\ leftHat' = nd
                    /\ result' = [result EXCEPT ![p] = "okay"]
                    /\ pc' = [pc EXCEPT ![p] = "done"]
                    /\ pushedVals' = pushedVals \cup {<<p, v>>}
                    /\ UNCHANGED <<rightHat, freeList, localAddr, localLeft, localRight,
                                   localLeftNext, localRightPrev, poppedVals, op, localVal>>
          ELSE /\ localLeft' = [localLeft EXCEPT ![p] = leftHat]
               /\ localRight' = [localRight EXCEPT ![p] = rightHat]
               /\ UNCHANGED <<mem, leftHat, rightHat, freeList, pc, result, localAddr,
                              localLeftNext, localRightPrev, pushedVals, poppedVals, op, localVal>>

PushRight1(p) ==
    /\ pc[p] = "pushRight1"
    /\ LET allocResult == Alloc(p)
           addr == allocResult[1]
           newFreeList == allocResult[2]
       IN IF addr = Null
          THEN /\ result' = [result EXCEPT ![p] = "full"]
               /\ pc' = [pc EXCEPT ![p] = "done"]
               /\ UNCHANGED <<mem, leftHat, rightHat, freeList, localAddr,
                              localLeft, localRight, localLeftNext, localRightPrev,
                              pushedVals, poppedVals, op, localVal>>
          ELSE /\ localAddr' = [localAddr EXCEPT ![p] = addr]
               /\ freeList' = newFreeList
               /\ localLeft' = [localLeft EXCEPT ![p] = leftHat]
               /\ localRight' = [localRight EXCEPT ![p] = rightHat]
               /\ pc' = [pc EXCEPT ![p] = "pushRight2"]
               /\ UNCHANGED <<mem, leftHat, rightHat, result, localLeftNext,
                              localRightPrev, pushedVals, poppedVals, op, localVal>>

PushRight2(p) ==
    /\ pc[p] = "pushRight2"
    /\ LET lh == localLeft[p]
           rh == localRight[p]
           nd == localAddr[p]
           v == localVal[p]
       IN IF lh = leftHat /\ rh = rightHat
          THEN IF lh = rh
               THEN /\ mem' = [mem EXCEPT ![nd] = [left |-> Null, right |-> Null, val |-> v]]
                    /\ leftHat' = nd
                    /\ rightHat' = nd
                    /\ result' = [result EXCEPT ![p] = "okay"]
                    /\ pc' = [pc EXCEPT ![p] = "done"]
                    /\ pushedVals' = pushedVals \cup {<<p, v>>}
                    /\ UNCHANGED <<freeList, localAddr, localLeft, localRight,
                                   localLeftNext, localRightPrev, poppedVals, op, localVal>>
               ELSE /\ mem' = [mem EXCEPT ![nd] = [left |-> rh, right |-> Null, val |-> v],
                                          ![rh] = [@ EXCEPT !.right = nd]]
                    /\ rightHat' = nd
                    /\ result' = [result EXCEPT ![p] = "okay"]
                    /\ pc' = [pc EXCEPT ![p] = "done"]
                    /\ pushedVals' = pushedVals \cup {<<p, v>>}
                    /\ UNCHANGED <<leftHat, freeList, localAddr, localLeft, localRight,
                                   localLeftNext, localRightPrev, poppedVals, op, localVal>>
          ELSE /\ localLeft' = [localLeft EXCEPT ![p] = leftHat]
               /\ localRight' = [localRight EXCEPT ![p] = rightHat]
               /\ UNCHANGED <<mem, leftHat, rightHat, freeList, pc, result, localAddr,
                              localLeftNext, localRightPrev, pushedVals, poppedVals, op, localVal>>

PopLeft1(p) ==
    /\ pc[p] = "popLeft1"
    /\ localLeft' = [localLeft EXCEPT ![p] = leftHat]
    /\ localRight' = [localRight EXCEPT ![p] = rightHat]
    /\ IF leftHat = DummyAddr /\ rightHat = DummyAddr
       THEN /\ result' = [result EXCEPT ![p] = "empty"]
            /\ pc' = [pc EXCEPT ![p] = "done"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freeList, localAddr,
                           localLeftNext, localRightPrev, pushedVals, poppedVals, op, localVal>>
       ELSE /\ localLeftNext' = [localLeftNext EXCEPT ![p] = mem[leftHat].right]
            /\ localVal' = [localVal EXCEPT ![p] = mem[leftHat].val]
            /\ pc' = [pc EXCEPT ![p] = "popLeft2"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freeList, result, localAddr,
                           localRightPrev, pushedVals, poppedVals, op>>

PopLeft2(p) ==
    /\ pc[p] = "popLeft2"
    /\ LET lh == localLeft[p]
           rh == localRight[p]
           lhNext == localLeftNext[p]
           v == localVal[p]
       IN IF lh = leftHat /\ rh = rightHat
          THEN IF lh = rh
               THEN /\ leftHat' = DummyAddr
                    /\ rightHat' = DummyAddr
                    /\ freeList' = Free(lh, freeList)
                    /\ result' = [result EXCEPT ![p] = "okay"]
                    /\ pc' = [pc EXCEPT ![p] = "done"]
                    /\ poppedVals' = poppedVals \cup {<<p, v>>}
                    /\ UNCHANGED <<mem, localAddr, localLeft, localRight,
                                   localLeftNext, localRightPrev, pushedVals, op, localVal>>
               ELSE /\ mem' = [mem EXCEPT ![lhNext] = [@ EXCEPT !.left = Null]]
                    /\ leftHat' = lhNext
                    /\ freeList' = Free(lh, freeList)
                    /\ result' = [result EXCEPT ![p] = "okay"]
                    /\ pc' = [pc EXCEPT ![p] = "done"]
                    /\ poppedVals' = poppedVals \cup {<<p, v>>}
                    /\ UNCHANGED <<rightHat, localAddr, localLeft, localRight,
                                   localLeftNext, localRightPrev, pushedVals, op, localVal>>
          ELSE /\ pc' = [pc EXCEPT ![p] = "popLeft1"]
               /\ UNCHANGED <<mem, leftHat, rightHat, freeList, result, localAddr,
                              localLeft, localRight, localLeftNext, localRightPrev,
                              pushedVals, poppedVals, op, localVal>>

PopRight1(p) ==
    /\ pc[p] = "popRight1"
    /\ localLeft' = [localLeft EXCEPT ![p] = leftHat]
    /\ localRight' = [localRight EXCEPT ![p] = rightHat]
    /\ IF leftHat = DummyAddr /\ rightHat = DummyAddr
       THEN /\ result' = [result EXCEPT ![p] = "empty"]
            /\ pc' = [pc EXCEPT ![p] = "done"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freeList, localAddr,
                           localLeftNext, localRightPrev, pushedVals, poppedVals, op, localVal>>
       ELSE /\ localRightPrev' = [localRightPrev EXCEPT ![p] = mem[rightHat].left]
            /\ localVal' = [localVal EXCEPT ![p] = mem[rightHat].val]
            /\ pc' = [pc EXCEPT ![p] = "popRight2"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freeList, result, localAddr,
                           localLeftNext, pushedVals, poppedVals, op>>

PopRight2(p) ==
    /\ pc[p] = "popRight2"
    /\ LET lh == localLeft[p]
           rh == localRight[p]
           rhPrev == localRightPrev[p]
           v == localVal[p]
       IN IF lh = leftHat /\ rh = rightHat
          THEN IF lh = rh
               THEN /\ leftHat' = DummyAddr
                    /\ rightHat' = DummyAddr
                    /\ freeList' = Free(rh, freeList)
                    /\ result' = [result EXCEPT ![p] = "okay"]
                    /\ pc' = [pc EXCEPT ![p] = "done"]
                    /\ poppedVals' = poppedVals \cup {<<p, v>>}
                    /\ UNCHANGED <<mem, localAddr, localLeft, localRight,
                                   localLeftNext, localRightPrev, pushedVals, op, localVal>>
               ELSE /\ mem' = [mem EXCEPT ![rhPrev] = [@ EXCEPT !.right = Null]]
                    /\ rightHat' = rhPrev
                    /\ freeList' = Free(rh, freeList)
                    /\ result' = [result EXCEPT ![p] = "okay"]
                    /\ pc' = [pc EXCEPT ![p] = "done"]
                    /\ poppedVals' = poppedVals \cup {<<p, v>>}
                    /\ UNCHANGED <<leftHat, localAddr, localLeft, localRight,
                                   localLeftNext, localRightPrev, pushedVals, op, localVal>>
          ELSE /\ pc' = [pc EXCEPT ![p] = "popRight1"]
               /\ UNCHANGED <<mem, leftHat, rightHat, freeList, result, localAddr,
                              localLeft, localRight, localLeftNext, localRightPrev,
                              pushedVals, poppedVals, op, localVal>>

ReturnToIdle(p) ==
    /\ pc[p] = "done"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ op' = [op EXCEPT ![p] = "none"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freeList, localVal, localAddr,
                   localLeft, localRight, localLeftNext, localRightPrev, result,
                   pushedVals, poppedVals>>

Next ==
    \E p \in Procs :
        \/ \E v \in Val : StartPushLeft(p, v)
        \/ \E v \in Val : StartPushRight(p, v)
        \/ StartPopLeft(p)
        \/ StartPopRight(p)
        \/ PushLeft1(p)
        \/ PushLeft2(p)
        \/ PushRight1(p)
        \/ PushRight2(p)
        \/ PopLeft1(p)
        \/ PopLeft2(p)
        \/ PopRight1(p)
        \/ PopRight2(p)
        \/ ReturnToIdle(p)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

PoppedWerePushed ==
    \A pair \in poppedVals : \E ppair \in pushedVals : ppair[2] = pair[2]

NoDuplicatePops ==
    \A p1, p2 \in Procs :
        p1 /= p2 =>
            \A pair1 \in {pp \in poppedVals : pp[1] = p1} :
                \A pair2 \in {pp \in poppedVals : pp[1] = p2} :
                    pair1[2] /= pair2[2]

DequeConsistency ==
    /\ PoppedWerePushed
    /\ NoDuplicatePops

=============================================================================