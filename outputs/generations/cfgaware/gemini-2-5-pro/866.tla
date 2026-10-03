---- MODULE FastPaxos ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Value,          \* The set of proposable values
    Acceptor,       \* The set of acceptors
    QuorumSize,     \* The size of a classic quorum
    FastQuorumSize  \* The size of a fast quorum

ASSUME
    /\ IsFiniteSet(Value)
    /\ IsFiniteSet(Acceptor)
    /\ QuorumSize \in 1..Cardinality(Acceptor)
    /\ FastQuorumSize \in 1..Cardinality(Acceptor)
    /\ 2 * QuorumSize > Cardinality(Acceptor)
    /\ QuorumSize + FastQuorumSize > Cardinality(Acceptor)

None == CHOOSE v : v \notin Value

VARIABLES
    round,          \* The current round number, 0 for fast rounds
    fastVotes,      \* [a \in Acceptor |-> v \in Value \cup {None}]
    classicRound,   \* [a \in Acceptor |-> n \in Nat], highest round promised
    acceptedValue,  \* [a \in Acceptor |-> v \in Value \cup {None}], value accepted
    acceptedRound,  \* [a \in Acceptor |-> n \in Nat], round of accepted value
    coordProposal,  \* <<round, value>> proposed by coordinator in a classic round
    chosenValue,    \* The value decided upon, or None
    proposedValues, \* The set of values that have been proposed
    allChosenValues \* The set of all values ever chosen (for verification)

vars == <<round, fastVotes, classicRound, acceptedValue, acceptedRound,
          coordProposal, chosenValue, proposedValues, allChosenValues>>

Init ==
    /\ round = 0
    /\ fastVotes = [a \in Acceptor |-> None]
    /\ classicRound = [a \in Acceptor |-> 0]
    /\ acceptedValue = [a \in Acceptor |-> None]
    /\ acceptedRound = [a \in Acceptor |-> 0]
    /\ coordProposal = <<0, None>>
    /\ chosenValue = None
    /\ proposedValues = {}
    /\ allChosenValues = {}

(* An external client proposes a value. *)
Propose(v) ==
    /\ v \in Value
    /\ proposedValues' = proposedValues \cup {v}
    /\ UNCHANGED <<round, fastVotes, classicRound, acceptedValue, acceptedRound,
                   coordProposal, chosenValue, allChosenValues>>

(* An acceptor casts a vote in a fast round. *)
FastVote(a, v) ==
    /\ a \in Acceptor
    /\ v \in proposedValues
    /\ fastVotes' = [fastVotes EXCEPT ![a] = v]
    /\ UNCHANGED <<round, classicRound, acceptedValue, acceptedRound,
                   coordProposal, chosenValue, proposedValues, allChosenValues>>

(* A value is chosen in a fast round if it gets a fast quorum of votes. *)
LearnFast(v) ==
    /\ v \in Value
    /\ LET voters == {a \in Acceptor : fastVotes[a] = v}
       IN Cardinality(voters) >= FastQuorumSize
    /\ chosenValue = None
    /\ chosenValue' = v
    /\ allChosenValues' = allChosenValues \cup {v}
    /\ UNCHANGED <<round, fastVotes, classicRound, acceptedValue, acceptedRound,
                   coordProposal, proposedValues>>

(* The coordinator starts a new classic round. *)
StartClassicRound ==
    /\ \E r \in {r_ \in Nat : r_ > round} :
        /\ round' = r
        /\ fastVotes' = [a \in Acceptor |-> None]
        /\ coordProposal' = <<0, None>>
    /\ UNCHANGED <<classicRound, acceptedValue, acceptedRound,
                   chosenValue, proposedValues, allChosenValues>>

(* In a classic round, the coordinator proposes a value. *)
ProposeClassic ==
    /\ round > 0
    /\ coordProposal = <<0, None>>  \* Can only propose once per round
    /\ LET prevAcceptedPairs == {<<acceptedRound[a], acceptedValue[a]>> : a \in Acceptor} \ {<<0, None>>}
    /\ LET maxPrevRound ==
        IF prevAcceptedPairs = {} THEN 0
        ELSE CHOOSE r \in {p[1] : p \in prevAcceptedPairs} :
            \A r2 \in {p[1] : p \in prevAcceptedPairs} : r >= r2
    /\ LET valuesWithFastVotes == {fastVotes[a] : a \in Acceptor} \ {None}
    /\ \E v \in Value :
        /\ IF maxPrevRound > 0
           THEN v = (CHOOSE p \in prevAcceptedPairs : p[1] = maxPrevRound)[2]
           ELSE v \in valuesWithFastVotes
        /\ coordProposal' = <<round, v>>
    /\ UNCHANGED <<round, fastVotes, classicRound, acceptedValue, acceptedRound,
                   chosenValue, proposedValues, allChosenValues>>

(* An acceptor accepts the coordinator's proposal. *)
AcceptClassic(a) ==
    /\ a \in Acceptor
    /\ LET <<r, v>> = coordProposal
       IN /\ r = round
          /\ v # None
          /\ r > classicRound[a]
          /\ classicRound' = [classicRound EXCEPT ![a] = r]
          /\ acceptedValue' = [acceptedValue EXCEPT ![a] = v]
          /\ acceptedRound' = [acceptedRound EXCEPT ![a] = r]
    /\ UNCHANGED <<round, fastVotes, coordProposal, chosenValue,
                   proposedValues, allChosenValues>>

(* A value is chosen in a classic round if it gets a classic quorum of accepts. *)
LearnClassic(v) ==
    /\ v \in Value
    /\ LET acceptors == {a \in Acceptor : acceptedValue[a] = v /\ acceptedRound[a] = round}
       IN Cardinality(acceptors) >= QuorumSize
    /\ chosenValue = None
    /\ chosenValue' = v
    /\ allChosenValues' = allChosenValues \cup {v}
    /\ UNCHANGED <<round, fastVotes, classicRound, acceptedValue, acceptedRound,
                   coordProposal, proposedValues>>

Next ==
    \/ \E v \in Value : Propose(v)
    \/ \E a \in Acceptor, v \in proposedValues : FastVote(a, v)
    \/ \E v \in Value : LearnFast(v)
    \/ StartClassicRound
    \/ ProposeClassic
    \/ \E a \in Acceptor : AcceptClassic(a)
    \/ \E v \in Value : LearnClassic(v)

FastSpec == Init /\ [][Next]_vars

=============================================================================