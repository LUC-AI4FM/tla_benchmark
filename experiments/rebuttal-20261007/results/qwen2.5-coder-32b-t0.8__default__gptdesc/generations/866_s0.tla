------------------------------- MODULE FastPaxos -------------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    Processes,                \* Set of all processes including the coordinator
    Coordinator,              \* The unique coordinator process
    Values                    \* Set of possible values to be proposed

VARIABLES 
    proposals,                \* Proposed values per process, indexed by (round, process)
    acceptedValues,           \* Accepted value per round, indexed by round
    chosenValue,              \* Chosen value for consensus
    round                     \* Current round number

Init == /\ proposals = [r \in Nat, p \in Processes -> {}]
        /\ acceptedValues = [r \in Nat -> <<>>]
        /\ chosenValue = <<>>
        /\ round = 0

Prepare(r) ==
    \/ /\ round' = r
       /\ \A v \in Values : proposals[r][Coordinator] = proposals[r]'[Coordinator] \cup {v}
       /\ \A p \in Processes - {Coordinator} : proposals[r][p] = proposals[r]'[p]
       /\ acceptedValues' = acceptedValues
       /\ chosenValue' = chosenValue

Propose(r, v) ==
    \/ /\ round' = r
       /\ proposals[r][Coordinator] = proposals[r]'[Coordinator] \cup {v}
       /\ \A p \in Processes - {Coordinator} : proposals[r][p] = proposals[r]'[p]
       /\ acceptedValues' = acceptedValues
       /\ chosenValue' = chosenValue

Accept(r, v) ==
    \/ /\ round' = r
       /\ \A p \in Processes : proposals[r][p] = proposals[r]'[p]
       /\ acceptedValues'[r] = <<v>>
       /\ chosenValue' = chosenValue

Choose(v) ==
    \/ /\ round' = round
       /\ \A p \in Processes : proposals[round][p] = proposals[round]'[p]
       /\ \A r \in Nat : acceptedValues[r] = acceptedValues'[r]
       /\ chosenValue' = <<v>>

Next ==
    \/ \/ \E v \in Values : Prepare(round) 
       \/ \E v \in Values : Propose(round, v)
       \/ \E v \in Values : Accept(round, v)
       \/ \E v \in Values : Choose(v)
    \/ /\ round' = round + 1
       /\ \A r \in {round} : acceptedValues'[r] = <<>>
       /\ chosenValue' = chosenValue
       /\ \A p \in Processes : proposals[round'][p] = {}

Spec == Init /\ [][Next]_<<proposals, acceptedValues, round>>

\* Type Invariants
TypeOk ==
    /\ \A r \in Nat, p \in Processes : proposals[r][p] \subseteq Values
    /\ \A r \in Nat : Len(acceptedValues[r]) \leq 1

\* Safety Properties
NoMultipleChosen == \/ chosenValue = <<>>
                       \/ \A v \in Values : Len({r \in Nat : acceptedValues[r] = <<v>>}) > 0 => chosenValue = <<v>>

\* Liveness Property
ConsensusAchieved ==
    <>[] (chosenValue /= <<>>)

====