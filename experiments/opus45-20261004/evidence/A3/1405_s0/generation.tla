---- MODULE Outer ----
EXTENDS Integers, Sequences

CONSTANTS Input

VARIABLES result, seq

\* Inner module defined inline, then instantiated with renamed variables
Inner_result == result
Inner_seq == seq

\* The filtering predicate for SelectSeq
FilterPred(x) == x # result'

\* Inner action: changes result from 0 to 1 and filters out elements equal to new result
InnerStep ==
    /\ result = 0
    /\ result' = 1
    /\ seq' = SelectSeq(seq, LAMBDA x: x # 1)

\* Initial state predicate
Init ==
    /\ result = 0
    /\ seq = Input

\* Next state relation: either take the inner step or stutter when disabled
Next ==
    \/ InnerStep
    \/ (ENABLED InnerStep = FALSE /\ UNCHANGED <<result, seq>>)

\* Specification with weak fairness on InnerStep
Spec == Init /\ [][Next]_<<result, seq>> /\ WF_<<result, seq>>(InnerStep)

\* Safety invariant: result is always 0 or 1
TypeInvariant ==
    /\ result \in {0, 1}

\* Liveness property: eventually InnerStep becomes permanently disabled
\* (i.e., eventually reaches a state after which InnerStep remains disabled forever)
Liveness == <>[](~ENABLED InnerStep)

====