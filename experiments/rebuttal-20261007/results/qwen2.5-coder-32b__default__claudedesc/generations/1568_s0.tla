------------------------------- MODULE Bakery -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS NumProcs, MaxNum
ASSUME NumProcs \in Nat /\ NumProcs > 0
ASSUME MaxNum \in Nat /\ MaxNum > 0

VARIABLES num, choosing, read, max, nxt, label

Proc == 1..NumProcs

Init == 
    /\ num = [i \in Proc |-> 0]
    /\ choosing = [i \in Proc |-> FALSE]
    /\ read \notin Proc
    /\ max \in Nat
    /\ nxt \in Nat
    /\ label \in {"loop", "d1", "d2", "d3", "w1", "w2", "cs"}

Next == 
    \/ \/ /\ label = "loop"
           /\ \/ \/ read = 0
                  /\ max = 0
                  /\ nxt = 0
                  /\ \E i \in Proc : choosing[i]
                  /\ \/ \A j \in (Proc \ {i}) : ~choosing[j] /\ num[j] <= max
                     /\ \/ \A k \in (Proc \ {i}) : ~choosing[k] /\ num[k] < nxt
                        \/ \E l \in (Proc \ {i}) : ~choosing[l] /\ num[l] = nxt /\ l > i
                  /\ label' = "d1"
                     /\ read' = i
                     /\ max' = max
                     /\ nxt' = nxt
                     /\ choosing' = [choosing EXCEPT ![read'] = TRUE]
                        \/ \A j \in (Proc \ {i}) : ~choosing[j] /\ num[j] <= max
                           /\ \/ \A k \in (Proc \ {i}) : ~choosing[k] /\ num[k] < nxt
                              \/ \E l \in (Proc \ {i}) : ~choosing[l] /\ num[l] = nxt /\ l > i
                           /\ label' = "d2"
                           /\ read' = 0
                           /\ max' = max
                           /\ nxt' = nxt + 1
                           /\ choosing' = [choosing EXCEPT ![read'] = TRUE]
                     \/ \E j \in (Proc \ {i}) : choosing[j] \/ num[j] > max
                        /\ label' = "d1"
                        /\ read' = i
                        /\ max' = [MAXIMUM {num[j]: j \in Proc}]
                        /\ nxt' = max + 1
                        /\ choosing' = [choosing EXCEPT ![read'] = TRUE]
           \/ read \in Proc
              /\ label = "d1"
              /\ \/ \A j \in (Proc \ {read}) : ~choosing[j] /\ num[j] <= max
                 /\ \/ \A k \in (Proc \ {read}) : ~choosing[k] /\ num[k] < nxt
                    \/ \E l \in (Proc \ {read}) : ~choosing[l] /\ num[l] = nxt /\ l > read
                 /\ label' = "d2"
                 /\ read' = 0
                 /\ max' = max
                 /\ nxt' = nxt
                 /\ choosing' = [choosing EXCEPT ![read'] = TRUE]
                    \/ \E j \in (Proc \ {read}) : choosing[j] \/ num[j] > max
                       /\ label' = "d1"
                       /\ read' = read
                       /\ max' = [MAXIMUM {num[j]: j \in Proc}]
                       /\ nxt' = max + 1
                       /\ choosing' = [choosing EXCEPT ![read'] = TRUE]
           \/ label = "d2"
              /\ label' = "d3"
              /\ num' = [num EXCEPT ![read] = nxt]
              /\ choosing' = [choosing EXCEPT ![read] = FALSE]
              /\ read' = 0
              /\ max' = max
              /\ nxt' = nxt
        \/ label = "d3"
           /\ label' = "w1"
           /\ read' = 1
        \/ read \in Proc
           /\ label = "w1"
           /\ \/ choosing[read]
              /\ label' = "w1"
              /\ read' = (read % NumProcs) + 1
                 \/ ~choosing[read]
                    /\ \/ num[read] = 0
                       /\ label' = "w1"
                       /\ read' = (read % NumProcs) + 1
                          \/ num[read] > num[i]
                             /\ label' = "w1"
                             /\ read' = (read % NumProcs) + 1
                                \/ num[read] = num[i]
                                   /\ read > i
                                   /\ label' = "w1"
                                   /\ read' = (read % NumProcs) + 1
                                      \/ num[read] = num[i]
                                         /\ read <= i
                                         /\ label' = "w2"
        \/ label = "w2"
           /\ label' = "cs"
        \/ label = "cs"
           /\ label' = "loop"
           /\ num' = [num EXCEPT ![i] = 0]

Spec == Init /\ [][Next]_<<num, choosing, read, max, nxt, label>>

Invariant ==
    \A i, j \in Proc : i # j => \/ label[i] # "cs" \/ label[j] # "cs"

Constraint ==
    \A i \in Proc : num[i] <= MaxNum

PossibleCounts ==
    /\ Cardinality({s \in [][Next]_<<num, choosing, read, max, nxt, label>>: s.label = "cs"}) = 113
    /\ Cardinality({s \in [][Next]_<<num, choosing, read, max, nxt, label>>: s.label = "d2"}) = 180

=============================================================================