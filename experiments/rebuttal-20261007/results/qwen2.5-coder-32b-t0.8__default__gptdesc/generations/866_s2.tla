------------------------------- MODULE FastPaxos -------------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Agents,                \* Set of all agents
    QuorumSize             \* Size of quorum for consensus

VARIABLES 
    proposals,             \* Map from agent to set of proposed values
    acceptedValues,        \* Set of values accepted by the coordinator
    decidedValue,          \* The final value decided by the system
    phase,                 \* Current phase: "Fast" or "Classic"
    roundNumber            \* Current round number

Init == 
    /\ proposals = [a \in Agents |-> {}]
    /\ acceptedValues = {}
    /\ decidedValue = NULL
    /\ phase = "Fast"
    /\ roundNumber = 0

Next ==
    \/ \/ \E a \in Agents, v \in SUBSET proposals[a] :
            /\ phase = "Fast"
            /\ acceptedValues' = acceptedValues \cup {v}
        \/ \/ \E a \in Agents, v \in SUBSET proposals[a] :
                /\ phase = "Classic"
                /\ Cardinality({a' \in Agents : v \in proposals[a']}) >= QuorumSize
                /\ acceptedValues' = acceptedValues \cup {v}
           \/ \/ \E v \in acceptedValues :
                   /\ Cardinality({a' \in Agents : v \in proposals[a']}) >= QuorumSize
                   /\ decidedValue' = v
              \/ roundNumber' = roundNumber + 1

TypeInvariant ==
    /\ \A a \in Agents : FiniteSet(proposals[a])
    /\ FiniteSet(acceptedValues)
    /\ phase \in {"Fast", "Classic"}
    /\ roundNumber \in Nat

SafetyInvariant ==
    /\ TypeInvariant
    /\ \/ decidedValue = NULL
       \/ \E v \in SUBSET acceptedValues :
              Cardinality({a' \in Agents : v \in proposals[a']}) >= QuorumSize

LivenessProperty ==
    <>[] (\E v \in UNION {proposals[a] : a \in Agents} : decidedValue = v)

Spec ==
    /\ Init
    /\ [][Next]_<<proposals, acceptedValues, decidedValue, phase, roundNumber>>
    /\ SafetyInvariant
    /\ LivenessProperty

=============================================================================