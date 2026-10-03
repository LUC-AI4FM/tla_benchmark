---- MODULE PaxosSpec ----
EXTENDS Integers, FiniteSets, TLC

CONSTANTS Proposer, Acceptor, Value, Nil

ASSUME  /\ IsFiniteSet(Proposer) /\ Proposer # {}
        /\ IsFiniteSet(Acceptor) /\ Acceptor # {}
        /\ IsFiniteSet(Value) /\ Value # {}
        /\ Nil \notin Value

IsQuorum(S) == S \subseteq Acceptor /\ 2 * Cardinality(S) > Cardinality(Acceptor)

VARIABLES
    maxBallot,      \* [acc \in Acceptor -> Int] Highest ballot promised by acceptor.
    acceptedBallot, \* [acc \in Acceptor -> Int] Highest ballot accepted by acceptor.
    acceptedValue,  \* [acc \in Acceptor -> Value \cup {Nil}] Value for acceptedBallot.
    sent,           \* The set of all messages sent.
    decision,       \* The decided value for the system, or Nil.
    proposedValues  \* The set of values introduced by clients.

vars == <<maxBallot, acceptedBallot, acceptedValue, sent, decision, proposedValues>>

(* Message Record Definitions *)
PrepareMsg(b, p) == [type |-> "prepare", bal |-> b, proposer |-> p]
PromiseMsg(a, b, pb, pv, p) == [type |-> "promise", acc |-> a, bal |-> b, prevBal |-> pb, prevVal |-> pv, proposer |-> p]
AcceptMsg(b, v, p) == [type |-> "accept", bal |-> b, val |-> v, proposer |-> p]
AcceptedMsg(a, b, v) == [type |-> "accepted", acc |-> a, bal |-> b, val |-> v]
DecideMsg(v) == [type |-> "decide", val |-> v]

PaxosTypeOK ==
    /\ maxBallot \in [Acceptor -> Int]
    /\ acceptedBallot \in [Acceptor -> Int]
    /\ acceptedValue \in [Acceptor -> Value \cup {Nil}]
    /\ decision \in Value \cup {Nil}
    /\ proposedValues \subseteq Value
    /\ \A m \in sent:
        \/ (\E b \in Int, p \in Proposer: m = PrepareMsg(b, p))
        \/ (\E a \in Acceptor, b, pb \in Int, pv \in Value \cup {Nil}, p \in Proposer: m = PromiseMsg(a, b, pb, pv, p))
        \/ (\E b \in Int, v \in Value, p \in Proposer: m = AcceptMsg(b, v, p))
        \/ (\E a \in Acceptor, b \in Int, v \in Value: m = AcceptedMsg(a, b, v))
        \/ (\E v \in Value: m = DecideMsg(v))

Init ==
    /\ maxBallot = [a \in Acceptor |-> -1]
    /\ acceptedBallot = [a \in Acceptor |-> -1]
    /\ acceptedValue = [a \in Acceptor |-> Nil]
    /\ sent = {}
    /\ decision = Nil
    /\ proposedValues = {}

ClientRequest(v) ==
    /\ v \in Value
    /\ proposedValues' = proposedValues \cup {v}
    /\ UNCHANGED <<maxBallot, acceptedBallot, acceptedValue, sent, decision>>

ProposerSendPrepare(p) ==
    /\ \E b \in Nat:
        /\ LET MsgsWithBallots == {s \in sent : s.type \in {"prepare", "promise", "accept", "accepted"}}
        /\ LET ExistingBallots == {m.bal : m \in MsgsWithBallots}
        /\ b > Max(ExistingBallots \cup {-1})
        /\ sent' = sent \cup {PrepareMsg(b, p)}
    /\ UNCHANGED <<maxBallot, acceptedBallot, acceptedValue, decision, proposedValues>>

AcceptorReceivePrepare(a) ==
    /\ \E m \in sent:
        /\ m.type = "prepare"
        /\ IF m.bal > maxBallot[a]
           THEN /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
                /\ sent' = sent \cup {PromiseMsg(a, m.bal, acceptedBallot[a], acceptedValue[a], m.proposer)}
                /\ UNCHANGED <<acceptedBallot, acceptedValue, decision, proposedValues>>
           ELSE UNCHANGED vars

ProposerSendAccept(p) ==
    /\ \E b \in Nat, v_prop \in proposedValues:
        /\ LET promises == {m \in sent : m.type = "promise" /\ m.bal = b /\ m.proposer = p}
        /\ LET acceptorsPromised == {m.acc : m \in promises}
        /\ IsQuorum(acceptorsPromised)
        /\ \A m_acc \in sent: (m_acc.type = "accept" /\ m_acc.proposer = p) => m_acc.bal # b
        /\ LET promisesWithValues == {m \in promises : m.prevBal > -1}
        /\ LET v_to_send ==
                IF promisesWithValues = {}
                THEN v_prop
                ELSE LET highestPrevBal == Max({m.prevBal : m \in promisesWithValues})
                     IN (CHOOSE m \in promisesWithValues : m.prevBal = highestPrevBal).prevVal
        /\ sent' = sent \cup {AcceptMsg(b, v_to_send, p)}
        /\ UNCHANGED <<maxBallot, acceptedBallot, acceptedValue, decision, proposedValues>>

AcceptorReceiveAccept(a) ==
    /\ \E m \in sent:
        /\ m.type = "accept"
        /\ IF m.bal >= maxBallot[a]
           THEN /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
                /\ acceptedBallot' = [acceptedBallot EXCEPT ![a] = m.bal]
                /\ acceptedValue' = [acceptedValue EXCEPT ![a] = m.val]
                /\ sent' = sent \cup {AcceptedMsg(a, m.bal, m.val)}
                /\ UNCHANGED <<decision, proposedValues>>
           ELSE UNCHANGED vars

Decide ==
    /\ \E b \in Nat, v \in Value:
        /\ LET acceptorsAccepted == {m.acc : m \in sent | m.type = "accepted" /\ m.bal = b /\ m.val = v}
        /\ IsQuorum(acceptorsAccepted)
        /\ decision = Nil
        /\ decision' = v
        /\ sent' = sent \cup {DecideMsg(v)}
        /\ UNCHANGED <<maxBallot, acceptedBallot, acceptedValue, proposedValues>>

Next ==
    \/ (\E v \in Value: ClientRequest(v))
    \/ (\E p \in Proposer: ProposerSendPrepare(p))
    \/ (\E a \in Acceptor: AcceptorReceivePrepare(a))
    \/ (\E p \in Proposer: ProposerSendAccept(p))
    \/ (\E a \in Acceptor: AcceptorReceiveAccept(a))
    \/ Decide

Spec == Init /\ [][Next]_vars

PaxosNontriviality == [] (decision # Nil => decision \in proposedValues)

PaxosConsistency == [] (decision # Nil => decision' = decision)

(*
 Liveness: Paxos does not guarantee termination under the asynchronous fault model
 (as shown by the FLP impossibility result). We model this by not requiring
 any liveness properties to hold.
*)
Liveness == FALSE

=============================================================================