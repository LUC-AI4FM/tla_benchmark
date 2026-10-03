----------------------------- MODULE FastPaxos -----------------------------
EXTENDS Naturals, Ints, FiniteSets, TLC

CONSTANTS
    \* The set of agents (acceptors).
    Acceptor,
    \* The set of values that can be proposed.
    Value,
    \* A special value indicating no value has been chosen/voted for.
    NoValue,
    \* The size of a classic quorum.
    ClassicQuorumSize,
    \* The size of a fast quorum.
    FastQuorumSize

ASSUME
    \* Basic assumptions about the constants.
    /\ IsFiniteSet(Acceptor)
    /\ IsFiniteSet(Value)
    /\ NoValue \notin Value
    /\ Cardinality(Acceptor) > 0
    /\ Cardinality(Value) > 0
    \* Quorum size assumptions for correctness.
    /\ ClassicQuorumSize > Cardinality(Acceptor) / 2
    /\ FastQuorumSize > Cardinality(Acceptor) / 2
    /\ ClassicQuorumSize + FastQuorumSize > Cardinality(Acceptor)

VARIABLES
    \* maxRound[a] is the highest round number acceptor 'a' has participated in.
    maxRound,
    \* fastRound[a] is the round number of the last fast vote by 'a'.
    fastRound,
    \* fastValue[a] is the value of the last fast vote by 'a'.
    fastValue,
    \* acceptedRound[a] is the round number of the last classic accept by 'a'.
    acceptedRound,
    \* acceptedValue[a] is the value of the last classic accept by 'a'.
    acceptedValue,
    \* The set of values proposed by clients.
    proposedValues,
    \* The value chosen by the consensus protocol.
    chosen

vars == <<maxRound, fastRound, fastValue, acceptedRound, acceptedValue, proposedValues, chosen>>

TypeInvariant ==
    /\ maxRound \in [Acceptor -> Nat]
    /\ fastRound \in [Acceptor -> Int]
    /\ fastValue \in [Acceptor -> Value \cup {NoValue}]
    /\ acceptedRound \in [Acceptor -> Int]
    /\ acceptedValue \in [Acceptor -> Value \cup {NoValue}]
    /\ proposedValues \subseteq Value
    /\ chosen \in Value \cup {NoValue}

Init ==
    /\ maxRound = [a \in Acceptor |-> 0]
    /\ fastRound = [a \in Acceptor |-> -1]
    /\ fastValue = [a \in Acceptor |-> NoValue]
    /\ acceptedRound = [a \in Acceptor |-> -1]
    /\ acceptedValue = [a \in Acceptor |-> NoValue]
    /\ proposedValues = {}
    /\ chosen = NoValue

-----------------------------------------------------------------------------
\* Helper operator to determine the set of values a coordinator could propose
\* in a classic round, given the promises from a quorum Q.
ProposeValueForQuorum(Q) ==
    LET \* Collect all non-null classic votes from the quorum.
        ClassicVotes == { <<acceptedRound[p], acceptedValue[p]>>
                          | p \in Q, acceptedRound[p] > -1 }
    IN IF ClassicVotes /= {}
       THEN \* If there are classic votes, pick the value from the highest round.
            LET MaxClassicRound == CHOOSE r \in {cv[1] | cv \in ClassicVotes} :
                                      \A r2 \in {cv[1] | cv \in ClassicVotes} : r >= r2
            IN {cv[2] | cv \in ClassicVotes, cv[1] = MaxClassicRound}
       ELSE \* Otherwise, look at the fast votes.
            LET FastVotes == { fastValue[p] | p \in Q, fastRound[p] > -1 }
            IN IF Cardinality(FastVotes) = 1 /\ FastVotes # {NoValue}
               THEN \* If all fast votes are for the same value, propose that value.
                    FastVotes
               ELSE \* Otherwise (collision or no votes), any proposed value is possible.
                    proposedValues

-----------------------------------------------------------------------------
\* Protocol Actions

\* A client proposes a value, making it available for consensus.
ClientPropose(v) ==
    /\ v \in Value
    /\ proposedValues' = proposedValues \cup {v}
    /\ UNCHANGED <<maxRound, fastRound, fastValue, acceptedRound, acceptedValue, chosen>>

\* An acceptor 'a' receives a fast-path proposal (r,v).
FastAccept(a, r, v) ==
    /\ v \in proposedValues
    /\ r > maxRound[a]
    /\ maxRound' = [maxRound EXCEPT ![a] = r]
    /\ fastRound' = [fastRound EXCEPT ![a] = r]
    /\ fastValue' = [fastValue EXCEPT ![a] = v]
    /\ UNCHANGED <<acceptedRound, acceptedValue, proposedValues, chosen>>

\* An acceptor 'a' receives a classic-path prepare message for round 'r'.
Promise(a, r) ==
    /\ r > maxRound[a]
    /\ maxRound' = [maxRound EXCEPT ![a] = r]
    /\ UNCHANGED <<fastRound, fastValue, acceptedRound, acceptedValue, proposedValues, chosen>>

\* An acceptor 'a' receives a classic-path accept message for (r,v).
\* The value 'v' must be one that could have been legally selected by a
\* coordinator based on promises from some quorum.
ClassicAccept(a, r, v) ==
    /\ r >= maxRound[a]
    /\ acceptedRound[a] < r
    /\ EXISTS Q \subseteq Acceptor:
          /\ Cardinality(Q) >= ClassicQuorumSize
          /\ (\A p \in Q : maxRound[p] >= r)
          /\ v \in ProposeValueForQuorum(Q)
    /\ maxRound' = [maxRound EXCEPT ![a] = r]
    /\ acceptedRound' = [acceptedRound EXCEPT ![a] = r]
    /\ acceptedValue' = [acceptedValue EXCEPT ![a] = v]
    /\ UNCHANGED <<fastRound, fastValue, proposedValues, chosen>>

\* A value is chosen if a fast quorum has accepted it in the same round.
ChooseFast ==
    /\ chosen = NoValue
    /\ EXISTS r \in Nat, v \in Value:
          /\ LET S == { a \in Acceptor | fastRound[a] = r /\ fastValue[a] = v }
             IN Cardinality(S) >= FastQuorumSize
          /\ chosen' = v
          /\ UNCHANGED <<maxRound, fastRound, fastValue, acceptedRound, acceptedValue, proposedValues>>

\* A value is chosen if a classic quorum has accepted it in the same round.
ChooseClassic ==
    /\ chosen = NoValue
    /\ EXISTS r \in Nat, v \in Value:
          /\ LET S == { a \in Acceptor | acceptedRound[a] = r /\ acceptedValue[a] = v }
             IN Cardinality(S) >= ClassicQuorumSize
          /\ chosen' = v
          /\ UNCHANGED <<maxRound, fastRound, fastValue, acceptedRound, acceptedValue, proposedValues>>

-----------------------------------------------------------------------------
\* Next-state relation.

Next ==
    \/ ChooseFast
    \/ ChooseClassic
    \/ (EXISTS v \in Value: ClientPropose(v))
    \/ (EXISTS a \in Acceptor, r \in Nat:
        \/ Promise(a, r)
        \/ (EXISTS v \in Value:
            \/ FastAccept(a, r, v)
            \/ ClassicAccept(a, r, v)))

-----------------------------------------------------------------------------
\* Specification and properties.

Spec == Init /\ [][Next]_vars

\* Fairness condition to ensure progress. Weak fairness on the set of all
\* actions is sufficient for liveness.
Fairness == WF_vars(Next)

\* SAFETY: The chosen value must have been proposed by a client.
Validity == chosen = NoValue \/ chosen \in proposedValues

\* SAFETY: At most one value is ever chosen.
Agreement == \A v1, v2 \in Value: (<> (chosen = v1) /\ <> (chosen = v2)) => v1 = v2

\* LIVENESS: Eventually, a value is chosen.
Termination == <> (chosen /= NoValue)

THEOREM Spec => [](TypeInvariant /\ Validity)
THEOREM Spec /\ Fairness => Termination

=============================================================================