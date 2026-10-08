------------------------------- MODULE Paxos -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Proposers, Acceptors, Values

VARIABLES 
    sentMessages, decision, acceptorState

Init == /\ sentMessages = {}
        /\ decision = <<>>
        /\ acceptorState = [a \in Acceptors |> <<0, 0, _>>]

Prepare(b, p) == <<b, "prepare", p>>

Promise(a, b, hb, hv, hvv) == <<a, "promise", b, hb, hv, hvv>>

Accept(b, v, p) == <<b, "accept", v, p>>

Accepted(a, b, v, p) == <<a, "accepted", b, v, p>>

Decide(v) == <<v, "decide">>

Sent(m) == sentMessages' = sentMessages \cup {m}

Next ==
    \/ \E b \in Nat, p \in Proposers, m \notin sentMessages :
        /\ Sent(Prepare(b, p))
    \/ \E a \in Acceptors, b \in Nat, hb \in Nat, hv \in Nat, hvv \in Values, m \notin sentMessages :
        /\ Sent(Promise(a, b, hb, hv, hvv))
    \/ \E b \in Nat, v \in Values, p \in Proposers, m \notin sentMessages :
        /\ Sent(Accept(b, v, p))
    \/ \E a \in Acceptors, b \in Nat, v \in Values, p \in Proposers, m \notin sentMessages :
        /\ Sent(Accepted(a, b, v, p))
    \/ \E v \in Values :
        /\ decision' = <<v>>
        /\ \A a \in Acceptors : acceptorState'[a] = acceptorState[a]

TypeOK ==
    /\ \A m \in sentMessages :
        \/ \E b \in Nat, p \in Proposers : m = Prepare(b, p)
        \/ \E a \in Acceptors, b \in Nat, hb \in Nat, hv \in Nat, hvv \in Values : m = Promise(a, b, hb, hv, hvv)
        \/ \E b \in Nat, v \in Values, p \in Proposers : m = Accept(b, v, p)
        \/ \E a \in Acceptors, b \in Nat, v \in Values, p \in Proposers : m = Accepted(a, b, v, p)
        \/ \E v \in Values : m = Decide(v)

Safety ==
    /\ TypeOK
    /\ decision = <<>> \/ \E v \in Values : decision = <<v>>
    /\ \A a \in Acceptors :
        LET hb == acceptorState[a][1]
            hv == acceptorState[a][2]
            hvv == acceptorState[a][3]
        IN  hb \in Nat
        /\ hv \in Nat
        /\ (hv = 0 \/ hvv \in Values)
    /\ decision = <<>> \/ \E v \in Values : \A a \in Acceptors : LET hvv == acceptorState[a][3] IN hvv = _ \/ hvv = v

Liveness ==
    FALSE \* Paxos does not guarantee termination under the asynchronous fault model implied by FLP-style reasoning.

Spec ==
    /\ Init
    /\ [][Next]_<<sentMessages, decision, acceptorState>>
    /\ <>[](Safety)
    /\ Liveness

=============================================================================