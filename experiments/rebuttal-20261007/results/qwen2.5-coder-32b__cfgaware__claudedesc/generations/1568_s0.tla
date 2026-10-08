------------------------------- MODULE Bakery -------------------------------

CONSTANTS NumProcs, MaxNum

VARIABLES num, choosing, pc

Proc == 1..NumProcs

Init == /\ num = [i \in Proc |-> 0]
        /\ choosing = [i \in Proc |-> FALSE]
        /\ pc = [i \in Proc |-> "loop"]

Next ==
    \/ \E i \in Proc : 
        (pc[i] = "loop" /\ 
         \/ /\ choosing' = [choosing EXCEPT ![i] = TRUE]
            /\ pc' = [pc EXCEPT ![i] = "d1"]
        \/ /\ pc[i] = "d1"
           /\ max \in Nat
           /\ read \in Proc
           /\ (read = i => max = 0)
           /\ (read # i => max = num[read])
           /\ pc' = [pc EXCEPT ![i] = IF read < NumProcs THEN "d1" ELSE "d2"]
        \/ /\ pc[i] = "d2"
           /\ nxt \in Nat
           /\ nxt = max + 1
           /\ num' = [num EXCEPT ![i] = nxt]
           /\ pc' = [pc EXCEPT ![i] = "d3"]
        \/ /\ pc[i] = "d3"
           /\ choosing' = [choosing EXCEPT ![i] = FALSE]
           /\ pc' = [pc EXCEPT ![i] = "w1"])
    \/ \E i \in Proc :
        (pc[i] = "w1" /\
         \/ \E j \in Proc \ {i} :
            (/\ choosing[j]
             /\ pc' = [pc EXCEPT ![i] = "w1"])
         \/ \A j \in Proc \ {i} :
            (/\ ~choosing[j]
             /\ (\A k \in Proc \ {i, j} : ~choosing[k])
             /\ (num[j] = 0 \/ num[i] < num[j] \/ (num[i] = num[j] /\ i < j))
             /\ pc' = [pc EXCEPT ![i] = IF j < NumProcs THEN "w1" ELSE "cs"]))
    \/ \E i \in Proc :
        (pc[i] = "cs" /\
         /\ num' = [num EXCEPT ![i] = 0]
         /\ pc' = [pc EXCEPT ![i] = "loop"])

Spec == Init /\ [][Next]_<<num, choosing, pc>>

Invariant ==
    \A i, j \in Proc : i # j => ~ (pc[i] = "cs" /\ pc[j] = "cs")

Constraint ==
    \A i \in Proc : num[i] <= MaxNum

InCS == Cardinality({i \in Proc : pc[i] = "cs"}) = 1

ChooseNumber ==
    Cardinality({<<i, j>> \in [Proc -> Proc] : pc[i] = "d2" /\ choosing[j]}) = NumProcs

PossibleCounts ==
    <>(InCS) /\ <>(ChooseNumber)

=============================================================================