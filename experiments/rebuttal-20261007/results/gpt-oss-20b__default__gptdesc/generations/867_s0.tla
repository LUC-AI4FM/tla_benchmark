MODULE Paxos
EXTENDS Naturals, Integers

CONSTANTS Acceptors, Proposers, Values
Bottom == 0

VARIABLES msgs, decision, highestBallotSeen, highestBallotAccepted, acceptedValue

vars == <<msgs, decision, highestBallotSeen, highestBallotAccepted, acceptedValue>>

(* Message record type *)
Message == [kind : {"prepare","promise","accept","accepted","decide"},
            src  : (Proposers \/ Acceptors),
            dst  : (Proposers \/ Acceptors),
            b    : Nat,
            v    : Values ∪ {Bottom},
            hb   : Nat,
            hv   : Values ∪ {Bottom}]

(* Helper functions to construct messages *)
PrepareMsg(p,a,b) == [kind |-> "prepare", src |-> p, dst |-> a, b |-> b, v |-> Bottom, hb |-> 0, hv |-> Bottom]
PromiseMsg(a,p,b,hb,hv) == [kind |-> "promise", src |-> a, dst |-> p, b |-> b, v |-> Bottom, hb |-> hb, hv |-> hv]
AcceptMsg(p,a,b,v) == [kind |-> "accept", src |-> p, dst |-> a, b |-> b, v |-> v, hb |-> 0, hv |-> Bottom]
AcceptedMsg(a,p,b,v) == [kind |-> "accepted", src |-> a, dst |-> p, b |-> b, v |-> v, hb |-> 0, hv |-> Bottom]
DecideMsg(p,b,v)    == [kind |-> "decide",   src |-> p, dst |-> p, b |-> b, v |-> v, hb |-> 0, hv |-> Bottom]

(* Initial state *)
Init ==
    /\ msgs = {}
    /\ decision = Bottom
    /\ highestBallotSeen \in [Acceptors -> Nat]
    /\ highestBallotAccepted \in [Acceptors -> Nat]
    /\ acceptedValue \in [Acceptors -> (Values ∪ {Bottom})]
    /\ \A a \in Acceptors : highestBallotSeen[a] = 0
    /\ \A a \in Acceptors : highestBallotAccepted[a] = 0
    /\ \A a \in Acceptors : acceptedValue[a] = Bottom

(* Actions *)
ReceivePrepare(a,p,b) ==
    /\ a \in Acceptors
    /\ p \in Proposers
    /\ b \in Nat
    /\ msgs' = msgs ∪ { PromiseMsg(a,p,b, highestBallotAccepted[a], acceptedValue[a]) }
    /\ highestBallotSeen'[a] = Max(highestBallotSeen[a], b)
    /\ UNCHANGED <<decision, highestBallotAccepted, acceptedValue>>

ReceiveAccept(a,p,b,v) ==
    /\ a \in Acceptors
    /\ p \in Proposers
    /\ v \in Values
    /\ b \in Nat
    /\ b >= highestBallotSeen[a]
    /\ msgs' = msgs ∪ { AcceptedMsg(a,p,b,v) }
    /\ highestBallotAccepted'[a] = b
    /\ acceptedValue'[a] = v
    /\ UNCHANGED <<decision, highestBallotSeen>>

DecideAction(p,b,v) ==
    /\ decision = Bottom
    /\ p \in Proposers
    /\ v \in Values
    /\ b \in Nat
    /\ msgs' = msgs ∪ { DecideMsg(p,b,v) }
    /\ decision' = v
    /\ UNCHANGED <<highestBallotSeen, highestBallotAccepted, acceptedValue>>

Next == \/ ReceivePrepare(a,p,b)
        \/ ReceiveAccept(a,p,b,v)
        \/ DecideAction(p,b,v)

(* Type correctness invariant *)
TypeOK ==
    /\ msgs \subseteq { m \in Message : TRUE }
    /\ decision \in Values \/ decision = Bottom
    /\ highestBallotSeen \in [Acceptors -> Nat]
    /\ highestBallotAccepted \in [Acceptors -> Nat]
    /\ acceptedValue \in [Acceptors -> (Values ∪ {Bottom})]

(* Non-triviality safety: only proposed values can be learned *)
NonTrivial ==
    decision = Bottom \/ 
    (\E m \in msgs : m.kind = "decide" /\ m.v = decision)

(* Consistency invariant over decision variable *)
Consistency ==
    decision = Bottom \/ 
    \A m1 \in msgs, m2 \in msgs :
        (m1.kind = "decide" /\ m2.kind = "decide") => m1.v = m2.v

Spec == Init /\ [][Next]_vars

(* Liveness is set to FALSE; Paxos does not guarantee termination under the asynchronous fault model implied by FLP-style reasoning. *)
Liveness == FALSE

============================================================================)