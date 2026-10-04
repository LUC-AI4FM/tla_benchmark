---------------------------- MODULE ConcurrentDeque ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS NumProcs, NumNodes, Values, Null

ASSUME NumProcs \in Nat /\ NumProcs > 0
ASSUME NumNodes \in Nat /\ NumNodes > 0
ASSUME Null \notin Values

Addresses == 1..NumNodes
Procs == 1..NumProcs

(* Node record structure: [value: Values \cup {Null}, left: Addresses \cup {Null}, right: Addresses \cup {Null}] *)

VARIABLES
    mem,           \* Memory: Addresses -> Node records
    leftHat,       \* Left hat pointer
    rightHat,      \* Right hat pointer
    freelist,      \* Set of free addresses
    valBag,        \* Multiset of values in deque (for consistency check)
    
    \* Per-process local variables
    pc,            \* Program counter for each process
    op,            \* Current operation type
    val,           \* Value being pushed/popped
    node,          \* Newly allocated node
    lh,            \* Local copy of leftHat
    rh,            \* Local copy of rightHat
    lhR,           \* Right pointer of left hat node
    rhL,           \* Left pointer of right hat node
    result,        \* Result of operation
    temp           \* Temporary variable

vars == <<mem, leftHat, rightHat, freelist, valBag, pc, op, val, node, lh, rh, lhR, rhL, result, temp>>

TypeOK ==
    /\ mem \in [Addresses -> [value: Values \cup {Null}, left: Addresses \cup {Null}, right: Addresses \cup {Null}]]
    /\ leftHat \in Addresses \cup {Null}
    /\ rightHat \in Addresses \cup {Null}
    /\ freelist \subseteq Addresses
    /\ pc \in [Procs -> {"T1", "PushL1", "PushL2", "PushL3", "PushL4", "PushL5",
                         "PushR1", "PushR2", "PushR3", "PushR4", "PushR5",
                         "PopL1", "PopL2", "PopL3", "PopL4", "PopL5", "PopL6",
                         "PopR1", "PopR2", "PopR3", "PopR4", "PopR5", "PopR6",
                         "Done"}]

InitNode == [value |-> Null, left |-> Null, right |-> Null]

Init ==
    /\ mem = [a \in Addresses |-> InitNode]
    /\ leftHat = Null
    /\ rightHat = Null
    /\ freelist = Addresses
    /\ valBag = [v \in Values |-> 0]
    /\ pc = [p \in Procs |-> "T1"]
    /\ op = [p \in Procs |-> "none"]
    /\ val = [p \in Procs |-> Null]
    /\ node = [p \in Procs |-> Null]
    /\ lh = [p \in Procs |-> Null]
    /\ rh = [p \in Procs |-> Null]
    /\ lhR = [p \in Procs |-> Null]
    /\ rhL = [p \in Procs |-> Null]
    /\ result = [p \in Procs |-> Null]
    /\ temp = [p \in Procs |-> Null]

\* Allocate a node from freelist
Allocate(p) ==
    /\ freelist /= {}
    /\ \E a \in freelist:
        /\ node' = [node EXCEPT ![p] = a]
        /\ freelist' = freelist \ {a}
        /\ mem' = [mem EXCEPT ![a] = InitNode]

\* Free a node back to freelist
Free(p, addr) ==
    /\ addr /= Null
    /\ freelist' = freelist \cup {addr}

\* Test process: nondeterministically choose operation
Test(p) ==
    /\ pc[p] = "T1"
    /\ \/ \E v \in Values:
          /\ pc' = [pc EXCEPT ![p] = "PushL1"]
          /\ op' = [op EXCEPT ![p] = "pushLeft"]
          /\ val' = [val EXCEPT ![p] = v]
          /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, node, lh, rh, lhR, rhL, result, temp>>
       \/ \E v \in Values:
          /\ pc' = [pc EXCEPT ![p] = "PushR1"]
          /\ op' = [op EXCEPT ![p] = "pushRight"]
          /\ val' = [val EXCEPT ![p] = v]
          /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, node, lh, rh, lhR, rhL, result, temp>>
       \/ /\ pc' = [pc EXCEPT ![p] = "PopL1"]
          /\ op' = [op EXCEPT ![p] = "popLeft"]
          /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, val, node, lh, rh, lhR, rhL, result, temp>>
       \/ /\ pc' = [pc EXCEPT ![p] = "PopR1"]
          /\ op' = [op EXCEPT ![p] = "popRight"]
          /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, val, node, lh, rh, lhR, rhL, result, temp>>

\* PushLeft operation
PushL1(p) ==
    /\ pc[p] = "PushL1"
    /\ freelist /= {}
    /\ \E a \in freelist:
        /\ node' = [node EXCEPT ![p] = a]
        /\ freelist' = freelist \ {a}
        /\ mem' = [mem EXCEPT ![a] = [value |-> val[p], left |-> Null, right |-> Null]]
        /\ pc' = [pc EXCEPT ![p] = "PushL2"]
    /\ UNCHANGED <<leftHat, rightHat, valBag, op, val, lh, rh, lhR, rhL, result, temp>>

PushL2(p) ==
    /\ pc[p] = "PushL2"
    /\ lh' = [lh EXCEPT ![p] = leftHat]
    /\ rh' = [rh EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PushL3"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, op, val, node, lhR, rhL, result, temp>>

PushL3(p) ==
    /\ pc[p] = "PushL3"
    /\ IF lh[p] = Null
       THEN \* Empty deque case - DCAS on both hats
            /\ IF leftHat = Null /\ rightHat = Null
               THEN /\ leftHat' = node[p]
                    /\ rightHat' = node[p]
                    /\ valBag' = [valBag EXCEPT ![val[p]] = @ + 1]
                    /\ pc' = [pc EXCEPT ![p] = "T1"]
               ELSE /\ pc' = [pc EXCEPT ![p] = "PushL2"]
                    /\ UNCHANGED <<leftHat, rightHat, valBag>>
            /\ UNCHANGED <<mem, freelist, lhR>>
       ELSE \* Non-empty case
            /\ mem' = [mem EXCEPT ![node[p]].right = lh[p]]
            /\ pc' = [pc EXCEPT ![p] = "PushL4"]
            /\ UNCHANGED <<leftHat, rightHat, freelist, valBag, lhR>>
    /\ UNCHANGED <<op, val, node, lh, rh, rhL, result, temp>>

PushL4(p) ==
    /\ pc[p] = "PushL4"
    /\ lh[p] /= Null
    /\ lhR' = [lhR EXCEPT ![p] = mem[lh[p]].left]
    /\ pc' = [pc EXCEPT ![p] = "PushL5"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, op, val, node, lh, rh, rhL, result, temp>>

PushL5(p) ==
    /\ pc[p] = "PushL5"
    /\ IF lhR[p] /= Null
       THEN \* Retry - someone else modified
            /\ pc' = [pc EXCEPT ![p] = "PushL2"]
            /\ UNCHANGED <<mem, leftHat, rightHat, valBag>>
       ELSE \* DCAS: update leftHat and lh.left atomically
            /\ IF leftHat = lh[p] /\ mem[lh[p]].left = Null
               THEN /\ leftHat' = node[p]
                    /\ mem' = [mem EXCEPT ![lh[p]].left = node[p]]
                    /\ valBag' = [valBag EXCEPT ![val[p]] = @ + 1]
                    /\ pc' = [pc EXCEPT ![p] = "T1"]
               ELSE /\ pc' = [pc EXCEPT ![p] = "PushL2"]
                    /\ UNCHANGED <<mem, leftHat, valBag>>
    /\ UNCHANGED <<rightHat, freelist, op, val, node, lh, rh, lhR, rhL, result, temp>>

\* PushRight operation
PushR1(p) ==
    /\ pc[p] = "PushR1"
    /\ freelist /= {}
    /\ \E a \in freelist:
        /\ node' = [node EXCEPT ![p] = a]
        /\ freelist' = freelist \ {a}
        /\ mem' = [mem EXCEPT ![a] = [value |-> val[p], left |-> Null, right |-> Null]]
        /\ pc' = [pc EXCEPT ![p] = "PushR2"]
    /\ UNCHANGED <<leftHat, rightHat, valBag, op, val, lh, rh, lhR, rhL, result, temp>>

PushR2(p) ==
    /\ pc[p] = "PushR2"
    /\ lh' = [lh EXCEPT ![p] = leftHat]
    /\ rh' = [rh EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PushR3"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, op, val, node, lhR, rhL, result, temp>>

PushR3(p) ==
    /\ pc[p] = "PushR3"
    /\ IF rh[p] = Null
       THEN \* Empty deque case
            /\ IF leftHat = Null /\ rightHat = Null
               THEN /\ leftHat' = node[p]
                    /\ rightHat' = node[p]
                    /\ valBag' = [valBag EXCEPT ![val[p]] = @ + 1]
                    /\ pc' = [pc EXCEPT ![p] = "T1"]
               ELSE /\ pc' = [pc EXCEPT ![p] = "PushR2"]
                    /\ UNCHANGED <<leftHat, rightHat, valBag>>
            /\ UNCHANGED <<mem, freelist, rhL>>
       ELSE \* Non-empty case
            /\ mem' = [mem EXCEPT ![node[p]].left = rh[p]]
            /\ pc' = [pc EXCEPT ![p] = "PushR4"]
            /\ UNCHANGED <<leftHat, rightHat, freelist, valBag, rhL>>
    /\ UNCHANGED <<op, val, node, lh, rh, lhR, result, temp>>

PushR4(p) ==
    /\ pc[p] = "PushR4"
    /\ rh[p] /= Null
    /\ rhL' = [rhL EXCEPT ![p] = mem[rh[p]].right]
    /\ pc' = [pc EXCEPT ![p] = "PushR5"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, op, val, node, lh, rh, lhR, result, temp>>

PushR5(p) ==
    /\ pc[p] = "PushR5"
    /\ IF rhL[p] /= Null
       THEN /\ pc' = [pc EXCEPT ![p] = "PushR2"]
            /\ UNCHANGED <<mem, rightHat, valBag>>
       ELSE /\ IF rightHat = rh[p] /\ mem[rh[p]].right = Null
               THEN /\ rightHat' = node[p]
                    /\ mem' = [mem EXCEPT ![rh[p]].right = node[p]]
                    /\ valBag' = [valBag EXCEPT ![val[p]] = @ + 1]
                    /\ pc' = [pc EXCEPT ![p] = "T1"]
               ELSE /\ pc' = [pc EXCEPT ![p] = "PushR2"]
                    /\ UNCHANGED <<mem, rightHat, valBag>>
    /\ UNCHANGED <<leftHat, freelist, op, val, node, lh, rh, lhR, rhL, result, temp>>

\* PopLeft operation
PopL1(p) ==
    /\ pc[p] = "PopL1"
    /\ lh' = [lh EXCEPT ![p] = leftHat]
    /\ rh' = [rh EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PopL2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, op, val, node, lhR, rhL, result, temp>>

PopL2(p) ==
    /\ pc[p] = "PopL2"
    /\ IF lh[p] = Null
       THEN \* Empty deque
            /\ result' = [result EXCEPT ![p] = Null]
            /\ pc' = [pc EXCEPT ![p] = "T1"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, lhR>>
       ELSE /\ IF lh[p] = rh[p]
               THEN \* Single element case
                    /\ pc' = [pc EXCEPT ![p] = "PopL3"]
                    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, result, lhR>>
               ELSE \* Multiple elements
                    /\ lhR' = [lhR EXCEPT ![p] = mem[lh[p]].right]
                    /\ pc' = [pc EXCEPT ![p] = "PopL4"]
                    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, result>>
    /\ UNCHANGED <<op, val, node, lh, rh, rhL, temp>>

PopL3(p) ==
    /\ pc[p] = "PopL3"
    /\ IF leftHat = lh[p] /\ rightHat = rh[p]
       THEN /\ leftHat' = Null
            /\ rightHat' = Null
            /\ result' = [result EXCEPT ![p] = mem[lh[p]].value]
            /\ valBag' = [valBag EXCEPT ![mem[lh[p]].value] = @ - 1]
            /\ freelist' = freelist \cup {lh[p]}
            /\ pc' = [pc EXCEPT ![p] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "PopL1"]
            /\ UNCHANGED <<leftHat, rightHat, freelist, valBag, result>>
    /\ UNCHANGED <<mem, op, val, node, lh, rh, lhR, rhL, temp>>

PopL4(p) ==
    /\ pc[p] = "PopL4"
    /\ IF lhR[p] = Null
       THEN /\ pc' = [pc EXCEPT ![p] = "PopL1"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, result>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "PopL5"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, result>>
    /\ UNCHANGED <<op, val, node, lh, rh, lhR, rhL, temp>>

PopL5(p) ==
    /\ pc[p] = "PopL5"
    /\ IF leftHat = lh[p] /\ mem[lhR[p]].left = lh[p]
       THEN /\ leftHat' = lhR[p]
            /\ mem' = [mem EXCEPT ![lhR[p]].left = Null]
            /\ result' = [result EXCEPT ![p] = mem[lh[p]].value]
            /\ valBag' = [valBag EXCEPT ![mem[lh[p]].value] = @ - 1]
            /\ freelist' = freelist \cup {lh[p]}
            /\ pc' = [pc EXCEPT ![p] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "PopL1"]
            /\ UNCHANGED <<mem, leftHat, freelist, valBag, result>>
    /\ UNCHANGED <<rightHat, op, val, node, lh, rh, lhR, rhL, temp>>

\* PopRight operation
PopR1(p) ==
    /\ pc[p] = "PopR1"
    /\ lh' = [lh EXCEPT ![p] = leftHat]
    /\ rh' = [rh EXCEPT ![p] = rightHat]
    /\ pc' = [pc EXCEPT ![p] = "PopR2"]
    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, op, val, node, lhR, rhL, result, temp>>

PopR2(p) ==
    /\ pc[p] = "PopR2"
    /\ IF rh[p] = Null
       THEN /\ result' = [result EXCEPT ![p] = Null]
            /\ pc' = [pc EXCEPT ![p] = "T1"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, rhL>>
       ELSE /\ IF lh[p] = rh[p]
               THEN /\ pc' = [pc EXCEPT ![p] = "PopR3"]
                    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, result, rhL>>
               ELSE /\ rhL' = [rhL EXCEPT ![p] = mem[rh[p]].left]
                    /\ pc' = [pc EXCEPT ![p] = "PopR4"]
                    /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, result>>
    /\ UNCHANGED <<op, val, node, lh, rh, lhR, temp>>

PopR3(p) ==
    /\ pc[p] = "PopR3"
    /\ IF leftHat = lh[p] /\ rightHat = rh[p]
       THEN /\ leftHat' = Null
            /\ rightHat' = Null
            /\ result' = [result EXCEPT ![p] = mem[rh[p]].value]
            /\ valBag' = [valBag EXCEPT ![mem[rh[p]].value] = @ - 1]
            /\ freelist' = freelist \cup {rh[p]}
            /\ pc' = [pc EXCEPT ![p] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "PopR1"]
            /\ UNCHANGED <<leftHat, rightHat, freelist, valBag, result>>
    /\ UNCHANGED <<mem, op, val, node, lh, rh, lhR, rhL, temp>>

PopR4(p) ==
    /\ pc[p] = "PopR4"
    /\ IF rhL[p] = Null
       THEN /\ pc' = [pc EXCEPT ![p] = "PopR1"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, result>>
       ELSE /\ pc' = [pc EXCEPT ![p] = "PopR5"]
            /\ UNCHANGED <<mem, leftHat, rightHat, freelist, valBag, result>>
    /\ UNCHANGED <<op, val, node, lh, rh, lhR, rhL, temp>>

PopR5(p) ==
    /\ pc[p] = "PopR5"
    /\ IF rightHat = rh[p] /\ mem[rhL[p]].right = rh[p]
       THEN /\ rightHat' = rhL[p]
            /\ mem' = [mem EXCEPT ![rhL[p]].right = Null]
            /\ result' = [result EXCEPT ![p] = mem[rh[p]].value]
            /\ valBag' = [valBag EXCEPT ![mem[rh[p]].value] = @ - 1]
            /\ freelist' = freelist \cup {rh[p]}
            /\ pc' = [pc EXCEPT ![p] = "T1"]
       ELSE /\ pc' = [pc EXCEPT ![p] = "PopR1"]
            /\ UNCHANGED <<mem, rightHat, freelist, valBag, result>>
    /\ UNCHANGED <<leftHat, op, val, node, lh, rh, lhR, rhL, temp>>

\* Process step
Step(p) ==
    \/ Test(p)
    \/ PushL1(p)
    \/ PushL2(p)
    \/ PushL3(p)
    \/ PushL4(p)
    \/ PushL5(p)
    \/ PushR1(p)
    \/ PushR2(p)
    \/ PushR3(p)
    \/ PushR4(p)
    \/ PushR5(p)
    \/ PopL1(p)
    \/ PopL2(p)
    \/ PopL3(p)
    \/ PopL4(p)
    \/ PopL5(p)
    \/ PopR1(p)
    \/ PopR2(p)
    \/ PopR3(p)
    \/ PopR4(p)
    \/ PopR5(p)

Next == \E p \in Procs: Step(p)

\* Fairness: weak fairness for each process
Fairness == \A p \in Procs: WF_vars(Step(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety invariants

\* Values in valBag are non-negative
ValBagNonNegative == \A v \in Values: valBag[v] >= 0

\* Liveness property: every test process returns to T1 infinitely often
ReturnsToT1 == \A p \in Procs: []<>(pc[p] = "T1")

================================================================================