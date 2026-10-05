-------------------------------- MODULE MergeSort --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT MaxLen

VARIABLES a, b, pc, stack, lo, hi, mid, i, j, k

vars == <<a, b, pc, stack, lo, hi, mid, i, j, k>>

Nat0ToMax == 0..MaxLen

AllArrays == UNION {[0..(n-1) -> Nat0ToMax] : n \in 0..MaxLen}

TypeOK ==
    /\ a \in AllArrays
    /\ b \in [0..MaxLen -> Nat0ToMax \cup {0}]
    /\ pc \in {"start", "check", "split", "recurse_left", "recurse_right", 
               "copy_to_b", "merge", "done"}
    /\ stack \in Seq([lo: Int, hi: Int, ret: {"recurse_right", "merge"}])
    /\ lo \in Int
    /\ hi \in Int
    /\ mid \in Int
    /\ i \in Int
    /\ j \in Int
    /\ k \in Int

Init ==
    /\ a \in AllArrays
    /\ b = [x \in 0..MaxLen |-> 0]
    /\ pc = "start"
    /\ stack = <<>>
    /\ lo = 0
    /\ hi = 0
    /\ mid = 0
    /\ i = 0
    /\ j = 0
    /\ k = 0

Start ==
    /\ pc = "start"
    /\ lo' = 0
    /\ hi' = Len(a) - 1
    /\ pc' = "check"
    /\ UNCHANGED <<a, b, stack, mid, i, j, k>>

Check ==
    /\ pc = "check"
    /\ IF lo >= hi
       THEN
           IF stack = <<>>
           THEN /\ pc' = "done"
                /\ UNCHANGED <<lo, hi, mid, i, j, k, stack>>
           ELSE LET frame == Head(stack)
                IN /\ lo' = frame.lo
                   /\ hi' = frame.hi
                   /\ pc' = frame.ret
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED <<mid, i, j, k>>
       ELSE /\ pc' = "split"
            /\ UNCHANGED <<lo, hi, mid, i, j, k, stack>>
    /\ UNCHANGED <<a, b>>

Split ==
    /\ pc = "split"
    /\ mid' = (lo + hi) \div 2
    /\ pc' = "recurse_left"
    /\ UNCHANGED <<a, b, stack, lo, hi, i, j, k>>

RecurseLeft ==
    /\ pc = "recurse_left"
    /\ stack' = <<[lo |-> lo, hi |-> hi, ret |-> "recurse_right"]>> \o stack
    /\ hi' = mid
    /\ pc' = "check"
    /\ UNCHANGED <<a, b, lo, mid, i, j, k>>

RecurseRight ==
    /\ pc = "recurse_right"
    /\ stack' = <<[lo |-> lo, hi |-> hi, ret |-> "merge"]>> \o stack
    /\ mid' = (lo + hi) \div 2
    /\ lo' = mid' + 1
    /\ pc' = "check"
    /\ UNCHANGED <<a, b, hi, i, j, k>>

CopyToB ==
    /\ pc = "copy_to_b"
    /\ mid' = (lo + hi) \div 2
    /\ LET newB == [x \in DOMAIN b |->
                     IF x >= lo /\ x <= mid
                     THEN a[x]
                     ELSE IF x > mid /\ x <= hi
                          THEN a[hi - (x - mid - 1)]
                          ELSE b[x]]
       IN b' = newB
    /\ i' = lo
    /\ j' = hi
    /\ k' = lo
    /\ pc' = "merge"
    /\ UNCHANGED <<a, stack, lo, hi>>

Merge ==
    /\ pc = "merge"
    /\ LET currentMid == (lo + hi) \div 2
       IN IF k > hi
          THEN
              IF stack = <<>>
              THEN /\ pc' = "done"
                   /\ UNCHANGED <<a, b, lo, hi, mid, i, j, k, stack>>
              ELSE LET frame == Head(stack)
                   IN /\ lo' = frame.lo
                      /\ hi' = frame.hi
                      /\ pc' = frame.ret
                      /\ stack' = Tail(stack)
                      /\ UNCHANGED <<a, b, mid, i, j, k>>
          ELSE IF b[i] <= b[j]
               THEN /\ a' = [a EXCEPT ![k] = b[i]]
                    /\ i' = i + 1
                    /\ k' = k + 1
                    /\ UNCHANGED <<b, pc, stack, lo, hi, mid, j>>
               ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                    /\ j' = j - 1
                    /\ k' = k + 1
                    /\ UNCHANGED <<b, pc, stack, lo, hi, mid, i>>

MergeStep ==
    /\ pc = "recurse_right"
    /\ stack' = <<[lo |-> lo, hi |-> hi, ret |-> "merge"]>> \o stack
    /\ LET currentMid == (lo + hi) \div 2
       IN /\ mid' = currentMid
          /\ lo' = currentMid + 1
    /\ pc' = "check"
    /\ UNCHANGED <<a, b, hi, i, j, k>>

StartMerge ==
    /\ pc = "merge"
    /\ LET currentMid == (lo + hi) \div 2
       IN /\ LET newB == [x \in DOMAIN b |->
                           IF x >= lo /\ x <= currentMid
                           THEN a[x]
                           ELSE IF x > currentMid /\ x <= hi
                                THEN a[hi - (x - currentMid - 1)]
                                ELSE b[x]]
             IN b' = newB
          /\ i' = lo
          /\ j' = hi
          /\ k' = lo
          /\ mid' = currentMid
    /\ pc' = "merging"
    /\ UNCHANGED <<a, stack, lo, hi>>

Merging ==
    /\ pc = "merging"
    /\ IF k > hi
       THEN
           IF stack = <<>>
           THEN /\ pc' = "done"
                /\ UNCHANGED <<a, b, lo, hi, mid, i, j, k, stack>>
           ELSE LET frame == Head(stack)
                IN /\ lo' = frame.lo
                   /\ hi' = frame.hi
                   /\ pc' = frame.ret
                   /\ stack' = Tail(stack)
                   /\ UNCHANGED <<a, b, mid, i, j, k>>
       ELSE IF b[i] <= b[j]
            THEN /\ a' = [a EXCEPT ![k] = b[i]]
                 /\ i' = i + 1
                 /\ k' = k + 1
                 /\ UNCHANGED <<b, pc, stack, lo, hi, mid, j>>
            ELSE /\ a' = [a EXCEPT ![k] = b[j]]
                 /\ j' = j - 1
                 /\ k' = k + 1
                 /\ UNCHANGED <<b, pc, stack, lo, hi, mid, i>>

Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ Start
    \/ Check
    \/ Split
    \/ RecurseLeft
    \/ RecurseRight
    \/ StartMerge
    \/ Merging
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

IsSorted ==
    \A x, y \in DOMAIN a : x < y => a[x] <= a[y]

Terminated == pc = "done"

SafetyInvariant ==
    Terminated => IsSorted

Liveness ==
    <>Terminated

================================================================================