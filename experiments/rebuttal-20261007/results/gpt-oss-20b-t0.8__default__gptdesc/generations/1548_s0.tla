MODULE OneStepConsensus
EXTENDS Naturals, FiniteSets

CONSTANTS N, F, T

ProcessSet  == 1..N
Values      == {0,1}
StateVals   == {"init","recv","decide"}
FaultStatusVals == {"faulty","correct"}
DecisionVals     == Values ∪ {"none"}

VARIABLE proposals, faultStatus, state, msgs, decision

CountVal(v) == #({i ∈ ProcessSet : msgs[i] = v})

Init ==
    (∀p ∈ ProcessSet : proposals[p] ∈ Values) /\
    ((∀p ∈ ProcessSet : proposals[p] = 0) \/ (∀p ∈ ProcessSet : proposals[p] = 1)) /\
    faultStatus == [p ∈ ProcessSet |-> "correct"] /\
    state       == [p ∈ ProcessSet |-> "init"] /\
    msgs        == [p ∈ ProcessSet |-> 0] /\
    decision    == [p ∈ ProcessSet |-> "none"]

Faultify ==
    ∃ p ∈ ProcessSet :
        faultStatus[p] = "correct" /\ 
        UNCHANGED <<proposals, state, msgs, decision>> /\ 
        faultStatus' = [faultStatus EXCEPT ![p] = "faulty"]

MainStep ==
    msgs'  = [p ∈ ProcessSet |-> IF faultStatus[p]="correct"
                                   THEN proposals[p]
                                   ELSE CHOOSE v ∊ Values : TRUE] /\
    state' = [p ∈ ProcessSet |-> IF state[p]="init" THEN "recv" ELSE state[p]] /\
    UNCHANGED <<proposals, faultStatus, decision>>

Decide ==
    ∃ p ∈ ProcessSet :
        /\ state[p]     = "recv"
        /\ faultStatus[p] = "correct"
        /\ LET c0 = #({i ∈ ProcessSet : msgs[i] = 0})
               c1 = #({i ∈ ProcessSet : msgs[i] = 1}) IN
           (c0 >= T \/ c1 >= T) /\
        decision' = [decision EXCEPT ![p] =
            IF c0 >= T THEN 0
            ELSE IF c1 >= T THEN 1
            ELSE "none"] /\
        state'    = [state EXCEPT ![p] = "decide"] /\
        UNCHANGED <<proposals, faultStatus, msgs>>

Next ==
    Faultify \/ MainStep \/ Decide

SafetyInvariants ==
    ∀ p,q ∈ ProcessSet :
        faultStatus[p]="correct" /\ faultStatus[q]="correct" /\
        decision[p] ≠ "none" /\ decision[q] ≠ "none"
        => decision[p] = decision[q]
    /\ #({p ∈ ProcessSet : faultStatus[p]="faulty"}) <= F

Liveness ==
    ∀ p ∈ ProcessSet :
        faultStatus[p]="correct" => ◇(state[p] = "decide")

Spec == Init /\
        [][Next]_(proposals, faultStatus, state, msgs, decision) /\ 
        SafetyInvariants /\ Liveness /\ WF_vars(MainStep)

===============================================================================