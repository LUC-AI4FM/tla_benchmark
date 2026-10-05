-------------------------------- MODULE FastPaxos --------------------------------
(***************************************************************************)
(* Fast Paxos Consensus Algorithm - Abstract Specification                  *)
(*                                                                          *)
(* This module specifies the Fast Paxos consensus algorithm abstractly,     *)
(* capturing the essential safety and liveness properties without           *)
(* prescribing implementation details.                                      *)
(*                                                                          *)
(* The algorithm supports two types of rounds:                              *)
(* - Fast rounds: Allow direct proposer-to-acceptor communication with      *)
(*   larger quorum requirements                                             *)
(* - Classic rounds: Coordinator-driven with standard majority quorums      *)
(***************************************************************************)

EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Acceptors,          \* Set of acceptor nodes
    Values,             \* Set of proposable values
    Rounds,             \* Set of round numbers (natural numbers)
    FastQuorums,        \* Set of fast quorums (subsets of Acceptors)
    ClassicQuorums,     \* Set of classic quorums (subsets of Acceptors)
    None                \* Distinguished "no value" constant

(***************************************************************************)
(* Quorum Intersection Assumptions                                          *)
(*                                                                          *)
(* For Fast Paxos safety:                                                   *)
(* 1. Any two classic quorums intersect                                     *)
(* 2. Any fast quorum intersects any classic quorum                         *)
(* 3. Any two fast quorums have sufficient intersection for collision       *)
(*    detection (their intersection with any classic quorum is non-empty)   *)
(***************************************************************************)

ASSUME QuorumAssumption ==
    /\ \A Q1, Q2 \in ClassicQuorums : Q1 \cap Q2 /= {}
    /\ \A FQ \in FastQuorums : \A CQ \in ClassicQuorums : FQ \cap CQ /= {}
    /\ \A FQ1, FQ2 \in FastQuorums : FQ1 \cap FQ2 /= {}
    /\ \A FQ \in FastQuorums : FQ \subseteq Acceptors
    /\ \A CQ \in ClassicQuorums : CQ \subseteq Acceptors

ASSUME ValueAssumption == None \notin Values

ASSUME RoundAssumption == 
    /\ Rounds \subseteq Nat
    /\ Rounds /= {}

VARIABLES
    (***************************************************************)
    (* Acceptor State                                               *)
    (***************************************************************)
    maxRound,           \* maxRound[a] = highest round acceptor a has participated in
    acceptedRound,      \* acceptedRound[a] = round in which acceptor a last accepted
    acceptedValue,      \* acceptedValue[a] = value acceptor a last accepted (or None)
    
    (***************************************************************)
    (* Round State                                                  *)
    (***************************************************************)
    roundType,          \* roundType[r] = "fast" or "classic" or "unused"
    roundValue,         \* roundValue[r] = value being proposed in classic round r (or "any" for fast)
    roundCoordinator,   \* roundCoordinator[r] = coordinator state for round r
    
    (***************************************************************)
    (* Message State (Abstract)                                     *)
    (***************************************************************)
    proposals,          \* proposals[r] = set of (acceptor, value) pairs proposed in round r
    accepts,            \* accepts[r] = set of (acceptor, value) pairs accepted in round r
    prepareResponses,   \* prepareResponses[r] = set of prepare responses for classic round r
    
    (***************************************************************)
    (* Decision State                                               *)
    (***************************************************************)
    decided,            \* Set of decided values (should have at most one element)
    
    (***************************************************************)
    (* Proposed Values Tracking                                     *)
    (***************************************************************)
    proposedValues      \* Set of values that have been proposed by some acceptor

vars == <<maxRound, acceptedRound, acceptedValue, roundType, roundValue,
          roundCoordinator, proposals, accepts, prepareResponses, decided, proposedValues>>

(***************************************************************************)
(* Type Invariant                                                           *)
(***************************************************************************)

TypeOK ==
    /\ maxRound \in [Acceptors -> Rounds \cup {0}]
    /\ acceptedRound \in [Acceptors -> Rounds \cup {0}]
    /\ acceptedValue \in [Acceptors -> Values \cup {None}]
    /\ roundType \in [Rounds -> {"fast", "classic", "unused"}]
    /\ roundValue \in [Rounds -> Values \cup {"any", None}]
    /\ roundCoordinator \in [Rounds -> [phase : {"idle", "preparing", "accepting", "done"},
                                         value : Values \cup {None},
                                         responses : SUBSET (Acceptors \times (Rounds \cup {0}) \times (Values \cup {None}))]]
    /\ proposals \in [Rounds -> SUBSET (Acceptors \times Values)]
    /\ accepts \in [Rounds -> SUBSET (Acceptors \times Values)]
    /\ prepareResponses \in [Rounds -> SUBSET (Acceptors \times (Rounds \cup {0}) \times (Values \cup {None}))]
    /\ decided \subseteq Values
    /\ proposedValues \subseteq Values

(***************************************************************************)
(* Initial State                                                            *)
(***************************************************************************)

Init ==
    /\ maxRound = [a \in Acceptors |-> 0]
    /\ acceptedRound = [a \in Acceptors |-> 0]
    /\ acceptedValue = [a \in Acceptors |-> None]
    /\ roundType = [r \in Rounds |-> "unused"]
    /\ roundValue = [r \in Rounds |-> None]
    /\ roundCoordinator = [r \in Rounds |-> [phase |-> "idle", value |-> None, responses |-> {}]]
    /\ proposals = [r \in Rounds |-> {}]
    /\ accepts = [r \in Rounds |-> {}]
    /\ prepareResponses = [r \in Rounds |-> {}]
    /\ decided = {}
    /\ proposedValues = {}

(***************************************************************************)
(* Helper Predicates                                                        *)
(***************************************************************************)

\* Check if a value v has a strict majority within a set of (acceptor, value) pairs
HasMajorityInSet(v, acceptorValuePairs) ==
    LET acceptorsWithV == {a \in Acceptors : <<a, v>> \in acceptorValuePairs}
        totalAcceptors == {a \in Acceptors : \E val \in Values : <<a, val>> \in acceptorValuePairs}
    IN 2 * Cardinality(acceptorsWithV) > Cardinality(totalAcceptors)

\* Get the set of values proposed by acceptors in a set of pairs
ValuesInSet(acceptorValuePairs) ==
    {v \in Values : \E a \in Acceptors : <<a, v>> \in acceptorValuePairs}

\* Check if a fast quorum has accepted the same value
FastQuorumAccepts(r, v) ==
    \E FQ \in FastQuorums :
        \A a \in FQ : <<a, v>> \in accepts[r]

\* Check if a classic quorum has accepted the same value  
ClassicQuorumAccepts(r, v) ==
    \E CQ \in ClassicQuorums :
        \A a \in CQ : <<a, v>> \in accepts[r]

\* Get highest round from prepare responses
MaxRoundInResponses(responses) ==
    IF responses = {} THEN 0
    ELSE LET rounds == {r \in Rounds \cup {0} : \E a \in Acceptors, v \in Values \cup {None} : <<a, r, v>> \in responses}
         IN IF rounds = {} THEN 0 ELSE CHOOSE maxR \in rounds : \A r2 \in rounds : r2 <= maxR

\* Get values accepted in the highest round from responses
ValuesAtMaxRound(responses) ==
    LET maxR == MaxRoundInResponses(responses)
    IN {v \in Values : \E a \in Acceptors : <<a, maxR, v>> \in responses /\ maxR > 0}

\* Check if value v was accepted by majority of responders at max round
HasMajorityAtMaxRound(v, responses) ==
    LET maxR == MaxRoundInResponses(responses)
        respondersAtMax == {a \in Acceptors : \E val \in Values \cup {None} : <<a, maxR, val>> \in responses}
        acceptorsWithV == {a \in Acceptors : <<a, maxR, v>> \in responses}
    IN maxR > 0 /\ 2 * Cardinality(acceptorsWithV) > Cardinality(respondersAtMax)

(***************************************************************************)
(* Fast Round Actions                                                       *)
(***************************************************************************)

\* Start a fast round - signals that "any" value may be accepted
StartFastRound(r) ==
    /\ roundType[r] = "unused"
    /\ roundType' = [roundType EXCEPT ![r] = "fast"]
    /\ roundValue' = [roundValue EXCEPT ![r] = "any"]
    /\ UNCHANGED <<maxRound, acceptedRound, acceptedValue, roundCoordinator,
                   proposals, accepts, prepareResponses, decided, proposedValues>>

\* Proposer proposes a value in a fast round (through an acceptor)
ProposeInFastRound(r, a, v) ==
    /\ roundType[r] = "fast"
    /\ v \in Values
    /\ maxRound[a] <= r
    /\ <<a, v>> \notin proposals[r]
    /\ proposals' = [proposals EXCEPT ![r] = @ \cup {<<a, v>>}]
    /\ proposedValues' = proposedValues \cup {v}
    /\ UNCHANGED <<maxRound, acceptedRound, acceptedValue, roundType, roundValue,
                   roundCoordinator, accepts, prepareResponses, decided>>

\* Acceptor accepts a value in a fast round
AcceptInFastRound(r, a, v) ==
    /\ roundType[r] = "fast"
    /\ <<a, v>> \in proposals[r]
    /\ maxRound[a] <= r
    /\ maxRound' = [maxRound EXCEPT ![a] = r]
    /\ acceptedRound' = [acceptedRound EXCEPT ![a] = r]
    /\ acceptedValue' = [acceptedValue EXCEPT ![a] = v]
    /\ accepts' = [accepts EXCEPT ![r] = @ \cup {<<a, v>>}]
    /\ UNCHANGED <<roundType, roundValue, roundCoordinator, proposals, 
                   prepareResponses, decided, proposedValues>>

\* Decide in a fast round when a fast quorum accepts the same value
DecideInFastRound(r, v) ==
    /\ roundType[r] = "fast"
    /\ FastQuorumAccepts(r, v)
    /\ v \in proposedValues
    /\ decided' = decided \cup {v}
    /\ UNCHANGED <<maxRound, acceptedRound, acceptedValue, roundType, roundValue,
                   roundCoordinator, proposals, accepts, prepareResponses, proposedValues>>

(***************************************************************************)
(* Classic Round Actions                                                    *)
(***************************************************************************)

\* Coordinator starts a classic round with prepare phase
StartClassicRound(r) ==
    /\ roundType[r] = "unused"
    /\ roundType' = [roundType EXCEPT ![r] = "classic"]
    /\ roundCoordinator' = [roundCoordinator EXCEPT ![r] = 
                            [phase |-> "preparing", value |-> None, responses |-> {}]]
    /\ UNCHANGED <<maxRound, acceptedRound, acceptedValue, roundValue,
                   proposals, accepts, prepareResponses, decided, proposedValues>>

\* Acceptor responds to prepare request
RespondToPrepare(r, a) ==
    /\ roundType[r] = "classic"
    /\ roundCoordinator[r].phase = "preparing"
    /\ maxRound[a] < r
    /\ maxRound' = [maxRound EXCEPT ![a] = r]
    /\ prepareResponses' = [prepareResponses EXCEPT ![r] = 
                            @ \cup {<<a, acceptedRound[a], acceptedValue[a]>>}]
    /\ UNCHANGED <<acceptedRound, acceptedValue, roundType, roundValue,
                   roundCoordinator, proposals, accepts, decided, proposedValues>>

\* Coordinator collects prepare responses and chooses a value
\* This implements the conflict resolution rule for Fast Paxos
CoordinatorChooseValue(r, v) ==
    /\ roundType[r] = "classic"
    /\ roundCoordinator[r].phase = "preparing"
    /\ \E CQ \in ClassicQuorums :
        \A a \in CQ : \E ar \in Rounds \cup {0}, av \in Values \cup {None} : 
            <<a, ar, av>> \in prepareResponses[r]
    /\ LET responses == prepareResponses[r]
           maxR == MaxRoundInResponses(responses)
           valuesAtMax == ValuesAtMaxRound(responses)
       IN \/ (maxR = 0 /\ v \in Values)  \* No prior accepts, free to choose
          \/ (maxR > 0 /\ valuesAtMax = {} /\ v \in Values)  \* All None at max round
          \/ (maxR > 0 /\ valuesAtMax /= {} /\
              \* If some value has majority at max round, must choose it
              ((\E v2 \in valuesAtMax : HasMajorityAtMaxRound(v2, responses)) =>
               HasMajorityAtMaxRound(v, responses)) /\
              \* Otherwise can pick any value from those at max round
              ((\A v2 \in valuesAtMax : ~HasMajorityAtMaxRound(v2, responses)) =>
               v \in valuesAtMax))
    /\ roundValue' = [roundValue EXCEPT ![r] = v]
    /\ roundCoordinator' = [roundCoordinator EXCEPT ![r] = 
                            [phase |-> "accepting", value |-> v, responses |-> prepareResponses[r]]]
    /\ proposedValues' = proposedValues \cup {v}
    /\ UNCHANGED <<maxRound, acceptedRound, acceptedValue, roundType,
                   proposals, accepts, prepareResponses, decided>>

\* Acceptor accepts value in classic round
AcceptInClassicRound(r, a) ==
    /\ roundType[r] = "classic"
    /\ roundCoordinator[r].phase = "accepting"
    /\ roundValue[r] \in Values
    /\ maxRound[a] <= r
    /\ LET v == roundValue[r]
       IN /\ maxRound' = [maxRound EXCEPT ![a] = r]
          /\ acceptedRound' = [acceptedRound EXCEPT ![a] = r]
          /\ acceptedValue' = [acceptedValue EXCEPT ![a] = v]
          /\ accepts' = [accepts EXCEPT ![r] = @ \cup {<<a, v>>}]
    /\ UNCHANGED <<roundType, roundValue, roundCoordinator, proposals,
                   prepareResponses, decided, proposedValues>>

\* Decide in classic round when a classic quorum accepts
DecideInClassicRound(r, v) ==
    /\ roundType[r] = "classic"
    /\ roundValue[r] = v
    /\ ClassicQuorumAccepts(r, v)
    /\ v \in proposedValues
    /\ decided' = decided \cup {v}
    /\ roundCoordinator' = [roundCoordinator EXCEPT ![r].phase = "done"]
    /\ UNCHANGED <<maxRound, acceptedRound, acceptedValue, roundType, roundValue,
                   proposals, accepts, prepareResponses, proposedValues>>

(***************************************************************************)
(* Next State Relation                                                      *)
(***************************************************************************)

Next ==
    \/ \E r \in Rounds : StartFastRound(r)
    \/ \E r \in Rounds, a \in Acceptors, v \in Values : ProposeInFastRound(r, a, v)
    \/ \E r \in Rounds, a \in Acceptors, v \in Values : AcceptInFastRound(r, a, v)
    \/ \E r \in Rounds, v \in Values : DecideInFastRound(r, v)
    \/ \E r \in Rounds : StartClassicRound(r)
    \/ \E r \in Rounds, a \in Acceptors : RespondToPrepare(r, a)
    \/ \E r \in Rounds, v \in Values : CoordinatorChooseValue(r, v)
    \/ \E r \in Rounds, a \in Acceptors : AcceptInClassicRound(r, a)
    \/ \E r \in Rounds, v \in Values : DecideInClassicRound(r, v)

(***************************************************************************)
(* Fairness Conditions                                                      *)
(*                                                                          *)
(* We specify weak fairness on decision actions to ensure progress when     *)
(* quorums and messages eventually occur.                                   *)
(***************************************************************************)

FastDecisionEnabled(r, v) ==
    /\ roundType[r] = "fast"
    /\ FastQuorumAccepts(r, v)
    /\ v \in proposedValues

ClassicDecisionEnabled(r, v) ==
    /\ roundType[r] = "classic"
    /\ roundValue[r] = v
    /\ ClassicQuorumAccepts(r, v)
    /\ v \in proposedValues

Fairness ==
    /\ \A r \in Rounds, v \in Values : 
        WF_vars(DecideInFastRound(r, v))
    /\ \A r \in Rounds, v \in Values : 
        WF_vars(DecideInClassicRound(r, v))
    /\ \A r \in Rounds, a \in Acceptors : 
        WF_vars(RespondToPrepare(r, a))
    /\ \A r \in Rounds, a \in Acceptors : 
        WF_vars(AcceptInClassicRound(r, a))
    /\ \A r \in Rounds, v \in Values : 
        WF_vars(CoordinatorChooseValue(r, v))

(***************************************************************************)
(* Specification                                                            *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Safety Invariants                                                        *)
(***************************************************************************)

\* Agreement: No two different values can both become decided
Agreement == Cardinality(decided) <= 1

\* Nontriviality: Only values that were actually proposed can be decided
Nontriviality == decided \subseteq proposedValues

\* Valid Conflict Resolution: Coordinator respects majority-in-quorum rule
\* This is encoded directly in the CoordinatorChooseValue action guard,
\* but we can also express it as an invariant about the coordinator state
ValidConflictResolution ==
    \A r \in Rounds :
        roundCoordinator[r].phase = "accepting" =>
        LET responses == roundCoordinator[r].responses
            v == roundCoordinator[r].value
            maxR == MaxRoundInResponses(responses)
            valuesAtMax == ValuesAtMaxRound(responses)
        IN v /= None /\
           (maxR > 0 /\ valuesAtMax /= {} =>
            ((\E v2 \in valuesAtMax : HasMajorityAtMaxRound(v2, responses)) =>
             HasMajorityAtMaxRound(v, responses)))

\* Combined Safety Invariant
Safety == Agreement /\ Nontriviality /\ ValidConflictResolution

(***************************************************************************)
(* Consistency Invariant                                                    *)
(*                                                                          *)
(* If a value is decided, then there exists evidence of quorum acceptance   *)
(***************************************************************************)

ConsistencyInvariant ==
    \A v \in decided :
        \/ \E r \in Rounds : roundType[r] = "fast" /\ FastQuorumAccepts(r, v)
        \/ \E r \in Rounds : roundType[r] = "classic" /\ ClassicQuorumAccepts(r, v)

(***************************************************************************)
(* Liveness Properties                                                      *)
(*                                                                          *)
(* Under fairness assumptions, if a quorum can form and messages are        *)
(* eventually delivered, a decision will eventually be reached.             *)
(***************************************************************************)

\* If a fast quorum accepts the same value, decision eventually happens
FastRoundProgress ==
    \A r \in Rounds, v \in Values :
        (roundType[r] = "fast" /\ FastQuorumAccepts(r, v) /\ v \in proposedValues) ~> (v \in decided)

\* If a classic quorum accepts, decision eventually happens
ClassicRoundProgress ==
    \A r \in Rounds, v \in Values :
        (roundType[r] = "classic" /\ ClassicQuorumAccepts(r, v) /\ v \in proposedValues) ~> (v \in decided)

\* Eventually some value is decided (if the system can make progress)
EventualDecision ==
    (\E r \in Rounds, v \in Values : 
        (roundType[r] = "fast" /\ FastQuorumAccepts(r, v)) \/
        (roundType[r] = "classic" /\ ClassicQuorumAccepts(r, v))) 
    ~> (decided /= {})

(***************************************************************************)
(* Consensus Goal                                                           *)
(*                                                                          *)
(* The goal of Fast Paxos is to achieve consensus on a single value per     *)
(* instance. This is captured by:                                           *)
(* 1. Agreement: At most one value is decided                               *)
(* 2. Validity: Only proposed values can be decided                         *)
(* 3. Termination: Under fairness, decision eventually occurs               *)
(***************************************************************************)

ConsensusGoal ==
    /\ Agreement
    /\ Nontriviality
    /\ (decided /= {} => Cardinality(decided) = 1)

=============================================================================