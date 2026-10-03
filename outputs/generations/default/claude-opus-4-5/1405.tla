---------------------------- MODULE Specification ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Input

VARIABLES result, seq

\* Inner module defined inline, then instantiated with renamed variables
Inner_result == result
Inner_seq == seq

\* The inner action: changes result from 0 to 1 and filters out elements equal to new result
InnerStep ==
    /\ result = 0
    /\ result' = 1
    /\ seq' = SelectSeq(seq, LAMBDA x: x # 1)

\* Predicate for when InnerStep is enabled
InnerEnabled == result = 0

\* Initialization
Init ==
    /\ result = 0
    /\ seq = Input

\* Next state: either take the inner step or stutter when disabled
Next ==
    \/ InnerStep
    \/ /\ ~InnerEnabled
       /\ UNCHANGED <<result, seq>>

\* Specification with weak fairness on the instantiated step
Spec == Init /\ [][Next]_<<result, seq>> /\ WF_<<result, seq>>(InnerStep)

\* Safety invariant: result is always 0 or 1
TypeInvariant ==
    /\ result \in {0, 1}

\* Liveness property: eventually reaches a state after which InnerStep remains disabled forever
LivenessProperty == <>[](~InnerEnabled)

=============================================================================