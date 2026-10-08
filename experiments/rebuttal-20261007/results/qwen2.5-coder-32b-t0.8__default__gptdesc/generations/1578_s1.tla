---- MODULE DEque ----
EXTENDS TLC, Integers, Sequences, FiniteSets

CONSTANTS 
    NumProcesses,                  \* Number of test processes
    MaxMemAddr,                    \* Maximum memory address for nodes
    InitialValBag                  \* Initial multiset of values in the deque

VARIABLES 
    mem,                           \* Memory mapping from addresses to node records
    leftHat,                       \* Left hat pointer
    rightHat,                      \* Right hat pointer
    freeList,                      \* Free list for allocation
    valBag,                        \* Multiset of values in the deque
    pc,                            \* Program counters for each process

\* Node record type
Node == [val: Int, left: Int, right: Int]

\* Initial state predicate
Init ==
    /\ mem = [a \in 1..MaxMemAddr -> <<0, 0>>]
    /\ leftHat = 0
    /\ rightHat = 0
    /\ freeList = {1..MaxMemAddr}
    /\ valBag = {}
    /\ pc = [p \in 1..NumProcesses -> "T1"]

\* Next-state relation for a single process
PushLeft(p) ==
    /\ pc[p] = "PL1"
    /\ LET addr == CHOOSE a \in freeList : TRUE
       IN /\ freeList' = freeList \ {addr}
          /\ mem' = [mem EXCEPT ![addr] = <<0, leftHat>>]
          /\ IF leftHat = 0
             THEN /\ leftHat' = addr
                  /\ rightHat' = addr
             ELSE /\ mem[leftHat][2]' = addr
                  /\ leftHat' = addr
          /\ valBag' = valBag \cup {mem[addr][1]}
          /\ pc'[p] = "T1"

PushRight(p) ==
    /\ pc[p] = "PR1"
    /\ LET addr == CHOOSE a \in freeList : TRUE
       IN /\ freeList' = freeList \ {addr}
          /\ mem' = [mem EXCEPT ![addr] = <<rightHat, 0>>]
          /\ IF rightHat = 0
             THEN /\ leftHat' = addr
                  /\ rightHat' = addr
             ELSE /\ mem[rightHat][1]' = addr
                  /\ rightHat' = addr
          /\ valBag' = valBag \cup {mem[addr][1]}
          /\ pc'[p] = "T1"

PopLeft(p) ==
    /\ pc[p] = "PL2"
    /\ leftHat # 0
    /\ LET addr == leftHat
       IN /\ freeList' = freeList \cup {addr}
          /\ IF mem[addr][2] = 0
             THEN /\ leftHat' = 0
                  /\ rightHat' = 0
             ELSE /\ leftHat' = mem[addr][2]
                  /\ mem[leftHat'][1]' = 0
          /\ valBag' = valBag \ {mem[addr][1]}
          /\ pc'[p] = "T1"

PopRight(p) ==
    /\ pc[p] = "PR2"
    /\ rightHat # 0
    /\ LET addr == rightHat
       IN /\ freeList' = freeList \cup {addr}
          /\ IF mem[addr][1] = 0
             THEN /\ leftHat' = 0
                  /\ rightHat' = 0
             ELSE /\ rightHat' = mem[addr][1]
                  /\ mem[rightHat'][2]' = 0
          /\ valBag' = valBag \ {mem[addr][1]}
          /\ pc'[p] = "T1"

Next ==
    \/ \E p \in 1..NumProcesses : 
        \/ /\ pc[p] = "T1"
           /\ \/ pc'[p] = "PL1" 
              \/ pc'[p] = "PR1"
              \/ pc'[p] = "PL2"
              \/ pc'[p] = "PR2"
              /\ mem' = mem
              /\ leftHat' = leftHat
              /\ rightHat' = rightHat
              /\ freeList' = freeList
              /\ valBag' = valBag
           \/ pc[p] = "PL1" /\ PushLeft(p)
           \/ pc[p] = "PR1" /\ PushRight(p)
           \/ pc[p] = "PL2" /\ PopLeft(p)
           \/ pc[p] = "PR2" /\ PopRight(p)
        \/ /\ pc' = [pc EXCEPT ![p] = "T1"]
           /\ mem' = mem
           /\ leftHat' = leftHat
           /\ rightHat' = rightHat
           /\ freeList' = freeList
           /\ valBag' = valBag

\* Liveness property: every test process returns to control location T1 infinitely often
Spec ==
    /\ Init
    /\ [][Next]_<<mem, leftHat, rightHat, freeList, valBag, pc>>
    /\ \A p \in 1..NumProcesses : WF_next(<<p>>, pc)

\* Safety invariants
TypeInvariant ==
    /\ mem \in [1..MaxMemAddr -> <<Int, Int>>]
    /\ leftHat \in 0..MaxMemAddr
    /\ rightHat \in 0..MaxMemAddr
    /\ freeList \in SUBSET (1..MaxMemAddr)
    /\ valBag \in SUBSETEQ InitialValBag

ValidDeque ==
    LET validChain(addr, prev) == 
            \/ addr = 0
            \/ mem[addr][2] = prev /\ validChain(mem[addr][1], addr)
        leftToRight == 
            LET rec(addr) == 
                    IF addr = 0 THEN <<>>
                    ELSE LET v == mem[addr][1]
                         IN rec(mem[addr][1]) \o <<v>>
            IN rec(leftHat)
    IN /\ validChain(leftHat, 0)
       /\ validChain(rightHat, 0)
       /\ Cardinality(valBag) = Len(leftToRight)
       /\ valBag = Multiset(leftToRight)

Invariant ==
    /\ TypeInvariant
    /\ ValidDeque

THEOREM Spec => []Invariant
====