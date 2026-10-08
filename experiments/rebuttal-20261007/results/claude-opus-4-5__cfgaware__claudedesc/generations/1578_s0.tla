---------------------------- MODULE Snark ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS Procs, Address, Val, Dummy, defaultInitValue

VARIABLES Mem, freeList, LeftHat, RightHat, rVal, valBag, pc, stack
VARIABLES nd, oldL, oldR, r, v, l

vars == <<Mem, freeList, LeftHat, RightHat, rVal, valBag, pc, stack, nd, oldL, oldR, r, v, l>>

NULL == CHOOSE x : x \notin Address

NodeFields == [L : Address \cup {NULL}, R : Address \cup {NULL}, V : Val \cup {defaultInitValue}]

TypeOK ==
    /\ Mem \in [Address -> NodeFields]
    /\ freeList \subseteq Address
    /\ LeftHat \in Address
    /\ RightHat \in Address
    /\ rVal \in [Procs -> Val \cup {"empty", defaultInitValue}]
    /\ pc \in [Procs -> STRING]

BagAdd(bag, elem) == [bag EXCEPT ![elem] = @ + 1]
BagRemove(bag, elem) == [bag EXCEPT ![elem] = @ - 1]
BagIn(elem, bag) == bag[elem] > 0

Init ==
    /\ Mem = [a \in Address |-> [L |-> NULL, R |-> NULL, V |-> defaultInitValue]]
    /\ freeList = Address \ {Dummy}
    /\ LeftHat = Dummy
    /\ RightHat = Dummy
    /\ rVal = [p \in Procs |-> defaultInitValue]
    /\ valBag = [v2 \in Val |-> 0]
    /\ pc = [p \in Procs |-> "T1"]
    /\ stack = [p \in Procs |-> <<>>]
    /\ nd = [p \in Procs |-> defaultInitValue]
    /\ oldL = [p \in Procs |-> defaultInitValue]
    /\ oldR = [p \in Procs |-> defaultInitValue]
    /\ r = [p \in Procs |-> defaultInitValue]
    /\ v = [p \in Procs |-> defaultInitValue]
    /\ l = [p \in Procs |-> defaultInitValue]

Alloc(p) ==
    IF freeList = {}
    THEN /\ nd' = [nd EXCEPT ![p] = NULL]
         /\ UNCHANGED freeList
    ELSE \E a \in freeList:
         /\ nd' = [nd EXCEPT ![p] = a]
         /\ freeList' = freeList \ {a}

Free(a) ==
    freeList' = freeList \cup {a}

DCAS(addr1, field1, old1, new1, addr2, field2, old2, new2) ==
    /\ Mem[addr1][field1] = old1
    /\ Mem[addr2][field2] = old2
    /\ Mem' = [Mem EXCEPT ![addr1][field1] = new1, ![addr2][field2] = new2]

PushRight_P1(p) ==
    /\ pc[p] = "PushRight_P1"
    /\ Alloc(p)
    /\ pc' = [pc EXCEPT ![p] = "PushRight_P2"]
    /\ UNCHANGED <<Mem, LeftHat, RightHat, rVal, valBag, stack, oldL, oldR, r, v, l>>

PushRight_P2(p) ==
    /\ pc[p] = "PushRight_P2"
    /\ IF nd[p] = NULL
       THEN /\ rVal' = [rVal EXCEPT ![p] = "empty"]
            /\ valBag' = BagRemove(valBag, v[p])
            /\ pc' = [pc EXCEPT ![p] = "PushRight_Done"]
            /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat>>
       ELSE /\ Mem' = [Mem EXCEPT ![nd[p]].V = v[p], ![nd[p]].L = NULL, ![nd[p]].R = NULL]
            /\ pc' = [pc EXCEPT ![p] = "PushRight_P3"]
            /\ UNCHANGED <<freeList, LeftHat, RightHat, rVal, valBag>>
    /\ UNCHANGED <<stack, nd, oldL, oldR, r, v, l>>

PushRight_P3(p) ==
    /\ pc[p] = "PushRight_P3"
    /\ r' = [r EXCEPT ![p] = RightHat]
    /\ pc' = [pc EXCEPT ![p] = "PushRight_P4"]
    /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, v, l>>

PushRight_P4(p) ==
    /\ pc[p] = "PushRight_P4"
    /\ Mem' = [Mem EXCEPT ![nd[p]].L = r[p]]
    /\ pc' = [pc EXCEPT ![p] = "PushRight_P5"]
    /\ UNCHANGED <<freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, r, v, l>>

PushRight_P5(p) ==
    /\ pc[p] = "PushRight_P5"
    /\ IF Mem[r[p]].R = NULL
       THEN IF RightHat = r[p]
            THEN /\ Mem' = [Mem EXCEPT ![r[p]].R = nd[p]]
                 /\ RightHat' = nd[p]
                 /\ rVal' = [rVal EXCEPT ![p] = v[p]]
                 /\ pc' = [pc EXCEPT ![p] = "PushRight_Done"]
                 /\ UNCHANGED <<freeList, LeftHat>>
            ELSE /\ pc' = [pc EXCEPT ![p] = "PushRight_P3"]
                 /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "PushRight_P3"]
            /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal>>
    /\ UNCHANGED <<valBag, stack, nd, oldL, oldR, r, v, l>>

PushRight_Done(p) ==
    /\ pc[p] = "PushRight_Done"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, r, v, l>>

PushLeft_P1(p) ==
    /\ pc[p] = "PushLeft_P1"
    /\ Alloc(p)
    /\ pc' = [pc EXCEPT ![p] = "PushLeft_P2"]
    /\ UNCHANGED <<Mem, LeftHat, RightHat, rVal, valBag, stack, oldL, oldR, r, v, l>>

PushLeft_P2(p) ==
    /\ pc[p] = "PushLeft_P2"
    /\ IF nd[p] = NULL
       THEN /\ rVal' = [rVal EXCEPT ![p] = "empty"]
            /\ valBag' = BagRemove(valBag, v[p])
            /\ pc' = [pc EXCEPT ![p] = "PushLeft_Done"]
            /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat>>
       ELSE /\ Mem' = [Mem EXCEPT ![nd[p]].V = v[p], ![nd[p]].L = NULL, ![nd[p]].R = NULL]
            /\ pc' = [pc EXCEPT ![p] = "PushLeft_P3"]
            /\ UNCHANGED <<freeList, LeftHat, RightHat, rVal, valBag>>
    /\ UNCHANGED <<stack, nd, oldL, oldR, r, v, l>>

PushLeft_P3(p) ==
    /\ pc[p] = "PushLeft_P3"
    /\ l' = [l EXCEPT ![p] = LeftHat]
    /\ pc' = [pc EXCEPT ![p] = "PushLeft_P4"]
    /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, r, v>>

PushLeft_P4(p) ==
    /\ pc[p] = "PushLeft_P4"
    /\ Mem' = [Mem EXCEPT ![nd[p]].R = l[p]]
    /\ pc' = [pc EXCEPT ![p] = "PushLeft_P5"]
    /\ UNCHANGED <<freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, r, v, l>>

PushLeft_P5(p) ==
    /\ pc[p] = "PushLeft_P5"
    /\ IF Mem[l[p]].L = NULL
       THEN IF LeftHat = l[p]
            THEN /\ Mem' = [Mem EXCEPT ![l[p]].L = nd[p]]
                 /\ LeftHat' = nd[p]
                 /\ rVal' = [rVal EXCEPT ![p] = v[p]]
                 /\ pc' = [pc EXCEPT ![p] = "PushLeft_Done"]
                 /\ UNCHANGED <<freeList, RightHat>>
            ELSE /\ pc' = [pc EXCEPT ![p] = "PushLeft_P3"]
                 /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "PushLeft_P3"]
            /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal>>
    /\ UNCHANGED <<valBag, stack, nd, oldL, oldR, r, v, l>>

PushLeft_Done(p) ==
    /\ pc[p] = "PushLeft_Done"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, r, v, l>>

PopRight_P1(p) ==
    /\ pc[p] = "PopRight_P1"
    /\ r' = [r EXCEPT ![p] = RightHat]
    /\ pc' = [pc EXCEPT ![p] = "PopRight_P2"]
    /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, v, l>>

PopRight_P2(p) ==
    /\ pc[p] = "PopRight_P2"
    /\ IF r[p] = Dummy
       THEN /\ rVal' = [rVal EXCEPT ![p] = "empty"]
            /\ pc' = [pc EXCEPT ![p] = "PopRight_Done"]
            /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, valBag, l>>
       ELSE /\ l' = [l EXCEPT ![p] = Mem[r[p]].L]
            /\ pc' = [pc EXCEPT ![p] = "PopRight_P3"]
            /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag>>
    /\ UNCHANGED <<stack, nd, oldL, oldR, r, v>>

PopRight_P3(p) ==
    /\ pc[p] = "PopRight_P3"
    /\ IF l[p] = NULL
       THEN /\ pc' = [pc EXCEPT ![p] = "PopRight_P1"]
            /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag>>
       ELSE IF RightHat = r[p] /\ Mem[l[p]].R = r[p]
            THEN /\ Mem' = [Mem EXCEPT ![l[p]].R = NULL]
                 /\ RightHat' = l[p]
                 /\ LET retVal == Mem[r[p]].V
                    IN /\ Assert(BagIn(retVal, valBag), "PopRight: value not in bag")
                       /\ valBag' = BagRemove(valBag, retVal)
                       /\ rVal' = [rVal EXCEPT ![p] = retVal]
                 /\ freeList' = freeList \cup {r[p]}
                 /\ pc' = [pc EXCEPT ![p] = "PopRight_Done"]
                 /\ UNCHANGED LeftHat
            ELSE /\ pc' = [pc EXCEPT ![p] = "PopRight_P1"]
                 /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag>>
    /\ UNCHANGED <<stack, nd, oldL, oldR, r, v, l>>

PopRight_Done(p) ==
    /\ pc[p] = "PopRight_Done"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, r, v, l>>

PopLeft_P1(p) ==
    /\ pc[p] = "PopLeft_P1"
    /\ l' = [l EXCEPT ![p] = LeftHat]
    /\ pc' = [pc EXCEPT ![p] = "PopLeft_P2"]
    /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, r, v>>

PopLeft_P2(p) ==
    /\ pc[p] = "PopLeft_P2"
    /\ IF l[p] = Dummy
       THEN /\ rVal' = [rVal EXCEPT ![p] = "empty"]
            /\ pc' = [pc EXCEPT ![p] = "PopLeft_Done"]
            /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, valBag, r>>
       ELSE /\ r' = [r EXCEPT ![p] = Mem[l[p]].R]
            /\ pc' = [pc EXCEPT ![p] = "PopLeft_P3"]
            /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag>>
    /\ UNCHANGED <<stack, nd, oldL, oldR, v, l>>

PopLeft_P3(p) ==
    /\ pc[p] = "PopLeft_P3"
    /\ IF r[p] = NULL
       THEN /\ pc' = [pc EXCEPT ![p] = "PopLeft_P1"]
            /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag>>
       ELSE IF LeftHat = l[p] /\ Mem[r[p]].L = l[p]
            THEN /\ Mem' = [Mem EXCEPT ![r[p]].L = NULL]
                 /\ LeftHat' = r[p]
                 /\ LET retVal == Mem[l[p]].V
                    IN /\ Assert(BagIn(retVal, valBag), "PopLeft: value not in bag")
                       /\ valBag' = BagRemove(valBag, retVal)
                       /\ rVal' = [rVal EXCEPT ![p] = retVal]
                 /\ freeList' = freeList \cup {l[p]}
                 /\ pc' = [pc EXCEPT ![p] = "PopLeft_Done"]
                 /\ UNCHANGED RightHat
            ELSE /\ pc' = [pc EXCEPT ![p] = "PopLeft_P1"]
                 /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag>>
    /\ UNCHANGED <<stack, nd, oldL, oldR, r, v, l>>

PopLeft_Done(p) ==
    /\ pc[p] = "PopLeft_Done"
    /\ pc' = [pc EXCEPT ![p] = "T1"]
    /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, r, v, l>>

T1(p) ==
    /\ pc[p] = "T1"
    /\ \/ /\ \E val \in Val:
               /\ v' = [v EXCEPT ![p] = val]
               /\ valBag' = BagAdd(valBag, val)
          /\ pc' = [pc EXCEPT ![p] = "PushRight_P1"]
          /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, stack, nd, oldL, oldR, r, l>>
       \/ /\ \E val \in Val:
               /\ v' = [v EXCEPT ![p] = val]
               /\ valBag' = BagAdd(valBag, val)
          /\ pc' = [pc EXCEPT ![p] = "PushLeft_P1"]
          /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, stack, nd, oldL, oldR, r, l>>
       \/ /\ pc' = [pc EXCEPT ![p] = "PopRight_P1"]
          /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, r, v, l>>
       \/ /\ pc' = [pc EXCEPT ![p] = "PopLeft_P1"]
          /\ UNCHANGED <<Mem, freeList, LeftHat, RightHat, rVal, valBag, stack, nd, oldL, oldR, r, v, l>>

proc(p) ==
    \/ T1(p)
    \/ PushRight_P1(p) \/ PushRight_P2(p) \/ PushRight_P3(p) \/ PushRight_P4(p) \/ PushRight_P5(p) \/ PushRight_Done(p)
    \/ PushLeft_P1(p) \/ PushLeft_P2(p) \/ PushLeft_P3(p) \/ PushLeft_P4(p) \/ PushLeft_P5(p) \/ PushLeft_Done(p)
    \/ PopRight_P1(p) \/ PopRight_P2(p) \/ PopRight_P3(p) \/ PopRight_Done(p)
    \/ PopLeft_P1(p) \/ PopLeft_P2(p) \/ PopLeft_P3(p) \/ PopLeft_Done(p)

Next == \E p \in Procs: proc(p)

Spec == Init /\ [][Next]_vars

Liveness == \A p \in Procs: []<>(pc[p] = "T1")

Symmetry == UNION {Permutations(Address \ {Dummy}), Permutations(Procs)}

=============================================================================