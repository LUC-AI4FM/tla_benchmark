------------------------------- MODULE CBakery -------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS NumProcs, MaxNum

VARIABLES num, choosing

vars == <<num, choosing>>

Init == /\ num \in [1..NumProcs -> 0]
        /\ choosing \in [1..NumProcs -> FALSE]

Next ==
    \/ \E i \in 1..NumProcs :
        /\ choosing[i] = FALSE
        /\ \/ \/ \E j \in 1..NumProcs : num[j] > num[i]
           \/ \A j \in 1..NumProcs : num[j] <= num[i]
        /\ \/ \/ \E j \in 1..NumProcs : choosing[j]
           \/ \A j \in 1..NumProcs : ~choosing[j]
        /\ LET read == [j \in 1..NumProcs |-> num[j]]
           max == Max(read)
           nxt == IF max = 0 THEN 1 ELSE max + 1
        IN \/ /\ choosing' = [choosing EXCEPT ![i] = TRUE]
             /\ UNCHANGED <<num - i>>
           \/ /\ choosing' = [choosing EXCEPT ![i] = FALSE]
              /\ num' = [num EXCEPT ![i] = nxt]
              /\ UNCHANGED <<choosing - i>>
    \/ \E i \in 1..NumProcs :
        /\ choosing[i] = TRUE
        /\ \A j \in 1..NumProcs \ {i} : ~choosing[j]
        /\ LET read == [j \in 1..NumProcs |-> num[j]]
           max == Max(read)
           nxt == IF max = 0 THEN 1 ELSE max + 1
        IN \/ /\ choosing' = [choosing EXCEPT ![i] = FALSE]
             /\ num' = [num EXCEPT ![i] = nxt]
             /\ UNCHANGED <<choosing - i>>
    \/ \E i \in 1..NumProcs :
        /\ choosing[i] = FALSE
        /\ LET read == [j \in 1..NumProcs |-> num[j]]
           max == Max(read)
           nxt == IF max = 0 THEN 1 ELSE max + 1
        IN \/ /\ \A j \in 1..NumProcs \ {i} :
                \/ ~choosing[j]
                \/ num[j] > num[i]
                \/ num[j] = num[i] /\ j > i
             /\ UNCHANGED vars

Spec == Init /\ [][Next]_vars

MutualExclusion ==
    \A i, j \in 1..NumProcs :
        i # j => ~(\E s \in StateTrace : s.num[i] = s.num[j] /\ s.num[i] > 0)

StateConstraint ==
    \A i \in 1..NumProcs : num[i] \leq MaxNum

=============================================================================