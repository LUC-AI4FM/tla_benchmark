---- MODULE FastPaxos ----

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Processes,       \* Set of all processes
    MaxRound         \* Maximum round number (symbolic constant)

VARIABLES 
    proposals,       \* proposals[r] = {p1, p2, ...} means process has proposed values in round r
    acceptedValues,  \* acceptedValues[p][r] = v means process p has accepted value v in round r
    decidedValue     \* The final value that was decided

Init == 
    /\ proposals = [r \in 1..MaxRound -> {}]
    /\ acceptedValues = [p \in Processes -> [r \in 1..MaxRound -> <<>>]]
    /\ decidedValue = <<>>

Next ==
    \/ \/ \E p \in Processes, r \in 1..MaxRound : 
            \/ \* Propose action
               \/ /\ ~ (proposals[r] \cap {p} /= {})
                  /\ proposals' = [proposals EXCEPT ![r] = proposals[r] \cup {p}]
                  /\ acceptedValues' = acceptedValues
                  /\ decidedValue' = decidedValue
            \/ \* Accept action
               \/ /\ proposals[r] \cap {p} /= {}
                  /\ \E v : <<v>> \notin {acceptedValues[p][r]}
                     /\ /\ acceptedValues' = [acceptedValues EXCEPT ![p][r] = <<v>>]
                        /\ proposals' = proposals
                        /\ decidedValue' = decidedValue
            \/ \* Decide action (only for the unique coordinator)
               \/ /\ \E quorum \in SUBSET Processes : Cardinality(quorum) > Cardinality(Processes) / 2
                  /\ \A p1, p2 \in quorum, r1, r2 \in 1..MaxRound :
                        acceptedValues[p1][r1] = acceptedValues[p2][r2] => acceptedValues[p1][r1] = decidedValue
                     /\ /\ decidedValue' = acceptedValues[p1][r1]
                        /\ proposals' = proposals
                        /\ acceptedValues' = acceptedValues

Spec == 
    Init /\ [][Next]_<<proposals, acceptedValues, decidedValue>>

TypeInvariants ==
    /\ \A r \in 1..MaxRound : proposals[r] \subseteq Processes
    /\ \A p \in Processes, r \in 1..MaxRound : acceptedValues[p][r] \in {<<>>, <<_>>}

SafetyProperties ==
    \/ /\ decidedValue = <<>> 
       \/ \E v : decidedValue = <<v>> /\ (\E r \in 1..MaxRound : v \in UNION {proposals[r]})

LivenessProperties ==
    []<> (decidedValue /= <<>>)

SpecWithProperties == Spec /\ TypeInvariants /\ SafetyProperties /\ LivenessProperties

====