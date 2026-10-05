---------------------------- MODULE spec ----------------------------

EXTENDS Integers, Sequences

CONSTANTS InitialSeq, TargetValue

VARIABLES seq, result

vars == <<seq, result>>

TypeOK ==
    /\ seq \in Seq(Int)
    /\ result \in Int

Init ==
    /\ seq = InitialSeq
    /\ result = 0

RemoveValue(s, v) ==
    SelectSeq(s, LAMBDA x: x /= v)

InnerServiceEnabled ==
    result = 0

InnerServiceAction ==
    /\ InnerServiceEnabled
    /\ result' = TargetValue
    /\ seq' = RemoveValue(seq, TargetValue)

OuterControllerStutter ==
    /\ ~InnerServiceEnabled
    /\ UNCHANGED vars

Next ==
    \/ InnerServiceAction
    \/ OuterControllerStutter

Fairness ==
    WF_vars(InnerServiceAction)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness

SafetyResult ==
    result \in {0, TargetValue}

SafetySeq ==
    \/ seq = InitialSeq
    \/ seq = RemoveValue(InitialSeq, TargetValue)

Safety ==
    /\ SafetyResult
    /\ SafetySeq

LivenessEventuallyExecutes ==
    <>(result = TargetValue)

LivenessEventuallyDisabled ==
    <>(~InnerServiceEnabled)

Liveness ==
    /\ LivenessEventuallyExecutes
    /\ LivenessEventuallyDisabled

StableState ==
    /\ result = TargetValue
    /\ seq = RemoveValue(InitialSeq, TargetValue)

Termination ==
    <>StableState

StableStateImpliesNoProgress ==
    [](StableState => []StableState)

SpecRunsToEnd ==
    /\ Init
    /\ [][Next]_vars
    /\ Fairness
    /\ Termination

=========================================================================