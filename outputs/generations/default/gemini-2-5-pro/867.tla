----------------------------- MODULE Paxos -----------------------------
EXTENDS Integers, FiniteSets, TLC

CONSTANTS
    Proposer,       \* The set of proposers
    Acceptor,       \* The set of acceptors
    Value,          \* The set of possible values to propose
    NilValue        \* A special value, not in Value

ASSUME
    /\ IsFiniteSet(Proposer)
    /\ IsFiniteSet(Acceptor)
    /\ IsFiniteSet(Value)
    /\ Proposer /= {}
    /\ Acceptor /= {}
    /\ Value /= {}
    /\ NilValue \notin Value

VARIABLES
    messages,        \* The set of all messages sent
    decision,        \* The globally decided value
    max_ballot,      \* For each acceptor, the max ballot number seen
    accepted_ballot, \* For each acceptor, the ballot number of the accepted value
    accepted_value,  \* For each acceptor, the value accepted
    proposedValues   \* The set of values proposed by proposers

vars == <<messages, decision, max_ballot, accepted_ballot, accepted_value, proposedValues>>

-----------------------------------------------------------------------------
\* Helper definitions

Quorum == {Q \subseteq Acceptor : Cardinality(Q) * 2 > Cardinality(Acceptor)}

MaxBallot(S) ==
    IF S = {} THEN -1 ELSE CHOOSE n \in S: \A m \in S: n >= m

-----------------------------------------------------------------------------
\* State machine definition

TypeOK ==
    /\ messages \subseteq
        [type: {"prepare"}, proposer: Proposer, ballot: Nat] \cup
        [type: {"promise"}, acceptor: Acceptor, proposer: Proposer, ballot: Nat,
                           accepted_ballot: Int, accepted_value: Value \cup {NilValue}] \cup
        [type: {"accept"}, proposer: Proposer, ballot: Nat, value: Value] \cup
        [type: {"accepted"}, acceptor: Acceptor, proposer: Proposer, ballot: Nat, value: Value] \cup
        [type: {"decide"}, value: Value]
    /\ decision \in Value \cup {NilValue}
    /\ max_ballot \in [Acceptor -> Nat]
    /\ accepted_ballot \in [Acceptor -> Int]
    /\ accepted_value \in [Acceptor -> Value \cup {NilValue}]
    /\ proposedValues \subseteq Value

Init ==
    /\ messages = {}
    /\ decision = NilValue
    /\ max_ballot = [a \in Acceptor |-> 0]
    /\ accepted_ballot = [a \in Acceptor |-> -1]
    /\ accepted_value = [a \in Acceptor |-> NilValue]
    /\ proposedValues = {}

\* A proposer decides to start a proposal for a value v.
ProposerProposesValue(p, v) ==
    /\ p \in Proposer
    /\ v \in Value
    /\ proposedValues' = proposedValues \cup {v}
    /\ UNCHANGED <<messages, decision, max_ballot, accepted_ballot, accepted_value>>

\* A proposer p picks a new ballot b and sends prepare messages.
ProposerSendsPrepare(p) ==
    \E b \in Nat:
        /\ \A m \in {m_ \in messages: m_.type \in {"prepare", "accept"} /\ m_.proposer = p}: b > m.ballot
        /\ messages' = messages \cup {[type |-> "prepare", proposer |-> p, ballot |-> b]}
        /\ UNCHANGED <<decision, max_ballot, accepted_ballot, accepted_value, proposedValues>>

\* An acceptor a receives a prepare message for ballot b > max_ballot[a] and sends a promise.
AcceptorSendsPromise(a) ==
    \E m_prep \in messages:
        /\ m_prep.type = "prepare"
        /\ m_prep.ballot > max_ballot[a]
        /\ \A m_prom \in messages: \* Send promise only once per ballot
              ~(m_prom.type = "promise" /\ m_prom.acceptor = a /\ m_prom.ballot = m_prep.ballot)
        /\ max_ballot' = [max_ballot EXCEPT ![a] = m_prep.ballot]
        /\ messages' = messages \cup
            {[ type |-> "promise", acceptor |-> a, proposer |-> m_prep.proposer, ballot |-> m_prep.ballot,
               accepted_ballot |-> accepted_ballot[a], accepted_value |-> accepted_value[a] ]}
        /\ UNCHANGED <<decision, accepted_ballot, accepted_value, proposedValues>>

\* Proposer p has received promises from a quorum for ballot b. It sends accept messages.
ProposerSendsAccept(p) ==
    \E b \in Nat:
        LET PromisesForB == {m \in messages: m.type = "promise" /\ m.proposer = p /\ m.ballot = b}
            PromisingAcceptors == {m.acceptor : m \in PromisesForB}
        IN \E Q \in Quorum:
            /\ Q \subseteq PromisingAcceptors
            /\ \A m_acc \in messages: \* Send accept only once per ballot
                  ~(m_acc.type = "accept" /\ m_acc.proposer = p /\ m_acc.ballot = b)
            /\ LET PromisesFromQ == {m \in PromisesForB : m.acceptor \in Q}
                   NonNilPromises == {m \in PromisesFromQ: m.accepted_ballot > -1}
               IN \/ /\ NonNilPromises = {}
                      /\ \E v \in proposedValues:
                           messages' = messages \cup {[type |-> "accept", proposer |-> p, ballot |-> b, value |-> v]}
                   \/ /\ NonNilPromises /= {}
                      /\ LET HighestAccBallot == MaxBallot({m.accepted_ballot : m \in NonNilPromises})
                             HighestPromiseVal == (CHOOSE m \in NonNilPromises: m.accepted_ballot = HighestAccBallot).accepted_value
                         IN messages' = messages \cup {[type |-> "accept", proposer |-> p, ballot |-> b, value |-> HighestPromiseVal]}
            /\ UNCHANGED <<decision, max_ballot, accepted_ballot, accepted_value, proposedValues>>

\* Acceptor a receives an accept message for ballot b >= max_ballot[a]. It accepts and sends an accepted message.
AcceptorSendsAccepted(a) ==
    \E m_acc \in messages:
        /\ m_acc.type = "accept"
        /\ m_acc.ballot >= max_ballot[a]
        /\ \A m_accd \in messages: \* Send accepted only once per ballot
              ~(m_accd.type = "accepted" /\ m_accd.acceptor = a /\ m_accd.ballot = m_acc.ballot)
        /\ max_ballot' = [max_ballot EXCEPT ![a] = m_acc.ballot]
        /\ accepted_ballot' = [accepted_ballot EXCEPT ![a] = m_acc.ballot]
        /\ accepted_value' = [accepted_value EXCEPT ![a] = m_acc.value]
        /\ messages' = messages \cup
            {[ type |-> "accepted", acceptor |-> a, proposer |-> m_acc.proposer,
               ballot |-> m_acc.ballot, value |-> m_acc.value ]}
        /\ UNCHANGED <<decision, proposedValues>>

\* A decision is made when a quorum has accepted a value v for some ballot b.
NodeDecides ==
    /\ decision = NilValue
    /\ \E b \in Nat, v \in Value:
        LET AcceptedSet == {m \in messages: m.type = "accepted" /\ m.ballot = b /\ m.value = v}
            AcceptorsOfBV == {m.acceptor : m \in AcceptedSet}
        IN \E Q \in Quorum:
            /\ Q \subseteq AcceptorsOfBV
            /\ decision' = v
            /\ messages' = messages \cup {[type |-> "decide", value |-> v]}
            /\ UNCHANGED <<max_ballot, accepted_ballot, accepted_value, proposedValues>>

Next ==
    \/ \E p \in Proposer, v \in Value: ProposerProposesValue(p, v)
    \/ \E p \in Proposer: ProposerSendsPrepare(p)
    \/ \E a \in Acceptor: AcceptorSendsPromise(a)
    \/ \E p \in Proposer: ProposerSendsAccept(p)
    \/ \E a \in Acceptor: AcceptorSendsAccepted(a)
    \/ NodeDecides

Spec == Init /\ □[Next]_vars

-----------------------------------------------------------------------------
\* Properties

\* Only values that have been proposed can be decided.
NonTriviality == decision \in proposedValues \cup {NilValue}

\* The decided value, once set, never changes.
Consistency == □(decision /= NilValue => decision' = decision)

\* The Liveness property is set to FALSE because Paxos does not guarantee
\* termination in a fully asynchronous model (as shown by the FLP impossibility
\* result). Any liveness would require additional assumptions on the model,
\* such as fairness for message delivery or process steps, which are not
\* modeled here.
Liveness == FALSE

=============================================================================