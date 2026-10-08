---------------------------- MODULE FastPaxos ----------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    N                 \* Number of replicas (excluding coordinator)
    QuorumSize        \* Size of quorum
    Values            \* Set of possible values to be agreed upon

VARIABLES
    proposals         \* Sequence of proposed values by the coordinator
    promises          \* Array of last promised round numbers for each replica
    accepts           \* Array of accepted values and their rounds for each replica
    decidedValue      \* The value that has been decided, if any

Init == 
    /\ proposals = << >>
    /\ promises = [r \in 1..N |-> -1]
    /\ accepts = [r \in 1..N |-> << >>]   \* Pair of (round, value)
    /\ decidedValue = NULL

Next ==
    \/ \/ \* Coordinator proposes a new value
       LET newRound == IF proposals = << >> THEN 0 ELSE LEN(proposals) END
           newVal == CHOOSE v \in Values : TRUE
       IN /\ proposals' = Append(proposals, newVal)
          /\ \A r \in 1..N : promises[r]' = [promises EXCEPT ![r] = newRound]
    \/ \/ \* Replica responds to a proposal with a promise
       LET round == CHOOSE r \in 1..N : TRUE \* Any replica can respond
           val == IF accepts[round][2] # NULL THEN accepts[round][2] ELSE newVal END
       IN /\ promises'[round]' = promises[round]
          /\ \A r \in 1..N \ {round} : promises'[r]' = promises[r]
          /\ accepts'[round]' = [accepts EXCEPT ![round] = <<promises[round], val>>]
    \/ \/ \* Coordinator decides on a value
       LET quorumVals == {val \in Values | card({r \in 1..N : accepts[r][2] = val}) >= QuorumSize}
           chosenVal == IF quorumVals # {} THEN CHOOSE v \in quorumVals : TRUE ELSE NULL END
       IN /\ decidedValue' = chosenVal

Spec ==
    Init /\ [][Next]_<<proposals, promises, accepts, decidedValue>>

\* Type invariants
TypeOK ==
    /\ proposals \in Seq(Values)
    /\ promises \in [1..N -> Int]
    /\ (\A r \in 1..N : accepts[r] \in <<Int, Values>>)
    /\ decidedValue \in Values \/ decidedValue = NULL

\* Safety properties
SafetyProp ==
    \/ decidedValue = NULL
    \/ decidedValue \in {v \in Values | card({r \in 1..N : v \in {accepts[r][2]}}) >= QuorumSize}

\* Liveness property (non-triviality)
Liveness ==
    <>[](decidedValue # NULL)

====