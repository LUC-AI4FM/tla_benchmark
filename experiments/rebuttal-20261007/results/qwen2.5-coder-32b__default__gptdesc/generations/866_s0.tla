------------------------------- MODULE FastPaxos -------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Processes,          \* Set of all processes
    QuorumSize,         \* Size of a quorum
    Values              \* Set of possible values to be agreed upon

VARIABLES 
    proposals,          \* Map from process to proposed value
    promises,           \* Map from process to promised round number
    acceptedValues,     \* Map from process to accepted value and round number
    decidedValue        \* The final decided value

Init == /\ proposals = [p \in Processes |-> <<0, "">>]
      /\ promises = [p \in Processes |-> 0]
      /\ acceptedValues = [p \in Processes |-> <<0, "">>]
      /\ decidedValue = ""

Next ==
    \/ \/ \* Propose action
          \/ \E p \in Processes, v \in Values :
             \/ proposals' = [proposals EXCEPT ![p] = <<promises[p] + 1, v>>]
                /\ promises' = promises
                /\ acceptedValues' = acceptedValues
                /\ decidedValue' = decidedValue
       \/ \/ \* Promise action
          \/ \E p \in Processes, r \in Nat :
             \/ /\ promises'[p] = Max(promises[p], r)
                /\ proposals' = proposals
                /\ acceptedValues' = acceptedValues
                /\ decidedValue' = decidedValue
       \/ \/ \* Accept action
          \/ \E p \in Processes, r \in Nat, v \in Values :
             \/ /\ promises'[p] = Max(promises[p], r)
                /\ acceptedValues'[p] = <<r, v>>
                /\ proposals' = proposals
                /\ decidedValue' = decidedValue
       \/ \/ \* Decide action
          \/ \E v \in Values :
             \/ /\ decidedValue' = v
                /\ promises' = promises
                /\ proposals' = proposals
                /\ acceptedValues' = acceptedValues

Spec == Init /\ [][Next]_<<proposals, promises, acceptedValues, decidedValue>>

\* Type invariants
TypeOK ==
    /\ \A p \in Processes : proposals[p] \in [1..QuorumSize] \X Values \/ proposals[p] = <<0, "">>
    /\ \A p \in Processes : promises[p] \in Nat
    /\ \A p \in Processes : acceptedValues[p] \in [1..QuorumSize] \X Values \/ acceptedValues[p] = <<0, "">>
    /\ decidedValue \in Values \/ decidedValue = ""

\* Safety invariants
Safety ==
    /\ TypeOK
    /\ \E v \in Values : decidedValue = v => \A p \in Processes : acceptedValues[p][2] = v

\* Liveness properties
Liveness ==
    \/ \E v \in DOMAIN proposals : \A r \in 1..QuorumSize :
       \/ \A p \in Processes : promises[p] >= r /\ acceptedValues[p][1] >= r => decidedValue = proposals[v][2]

\* Fairness conditions
Fairness == WF_next(<<proposals, promises, acceptedValues, decidedValue>>)

CompleteSpec == Spec /\ Safety /\ Liveness /\ Fairness

=============================================================================