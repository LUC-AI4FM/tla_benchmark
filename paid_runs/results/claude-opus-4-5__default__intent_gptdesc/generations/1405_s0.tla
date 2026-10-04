-------------------------------- MODULE TwoComponentSystem --------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS InitialSequence, UpdateValue

ASSUME InitialSequenceAssumption == 
    /\ InitialSequence \in Seq(Nat \ {0})
    /\ Len(InitialSequence) > 0

ASSUME UpdateValueAssumption ==
    /\ UpdateValue \in Nat \ {0}

VARIABLES result, sequence

vars == <<result, sequence>>

TypeInvariant ==
    /\ result \in Nat
    /\ sequence \in Seq(Nat \ {0})

Init ==
    /\ sequence = InitialSequence
    /\ result = 0

RemoveAll(seq, val) ==
    SelectSeq(seq, LAMBDA x: x /= val)

InnerServiceEnabled ==
    result = 0

InnerServiceAction ==
    /\ InnerServiceEnabled
    /\ result' = UpdateValue
    /\ sequence' = RemoveAll(sequence, UpdateValue)

OuterControllerStutter ==
    /\ ~InnerServiceEnabled
    /\ UNCHANGED vars

Next ==
    \/ InnerServiceAction
    \/ OuterControllerStutter

Fairness == WF_vars(InnerServiceAction)

Spec == Init /\ [][Next]_vars /\ Fairness

ResultOnlyChangesToUpdateValue ==
    /\ result \in {0, UpdateValue}

IsSubsequenceWithRemovals(current, original, removedVal) ==
    current = RemoveAll(original, removedVal)

SequenceConsistency ==
    \/ (result = 0 /\ sequence = InitialSequence)
    \/ (result = UpdateValue /\ sequence = RemoveAll(InitialSequence, UpdateValue))

SafetyInvariant ==
    /\ ResultOnlyChangesToUpdateValue
    /\ SequenceConsistency

ResultMonotonicity ==
    [][result = 0 \/ result = result']_result

ResultTransitionSafety ==
    [][(result = 0 /\ result' = UpdateValue) \/ (result' = result)]_result

ServiceEventuallyExecutes ==
    <>(result = UpdateValue)

ServiceEventuallyDisabled ==
    <>(~InnerServiceEnabled)

SystemReachesStableState ==
    <>[](result = UpdateValue /\ sequence = RemoveAll(InitialSequence, UpdateValue))

StableStateReached ==
    result = UpdateValue /\ sequence = RemoveAll(InitialSequence, UpdateValue)

Termination ==
    <>[](StableStateReached /\ ~InnerServiceEnabled)

NoFurtherProgress ==
    [](StableStateReached => [](StableStateReached))

ProgressToTermination ==
    (result = 0) ~> StableStateReached

=============================================================================