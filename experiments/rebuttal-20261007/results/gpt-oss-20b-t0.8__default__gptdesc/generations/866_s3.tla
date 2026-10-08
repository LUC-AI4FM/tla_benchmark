------------------------------- MODULE FastPaxos -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Agents   \in SUBSET [0..9]          \* finite set of agent identifiers
    Values   \subseteq {True, False}   \* values that can be proposed

VARIABLES
    proposals,    \* [Agents -> (Values ∪ {"⊥"})]
    promises,     \* [Nat -> [Agents -> BOOLEAN]]
    accepts,      \* [Nat -> [Agents -> (Values ∪ {"⊥"})]]
    decided,      \* [Agents -> BOOLEAN]
    decisionVal   \* [Agents -> (Values ∪ {"⊥"})]

(* Helper constants and functions *)
Majority == (#Agents DIV 2) + 1

CountAccepts(r, v) ==
    #({ a \in Agents : accepts[r][a] = v })

(* Type invariants *)
TypeOK ==
    /\ proposals   \in [Agents -> (Values ∪ { "⊥" })]
    /\ promises    \in [Nat -> [Agents -> BOOLEAN]]
    /\ accepts     \in [Nat -> [Agents -> (Values ∪ { "⊥" })]]
    /\ decided     \in [Agents -> BOOLEAN]
    /\ decisionVal \in [Agents -> (Values ∪ { "⊥" })]

(* Initial state *)
Init ==
    /\ proposals   = [a \in Agents |-> "⊥"]
    /\ promises    = []
    /\ accepts     = []
    /\ decided     = [a \in Agents |-> FALSE]
    /\ decisionVal = [a \in Agents |-> "⊥"]

(* Actions *)

Propose(a, v) ==
    /\ a \in Agents
    /\ v \in Values
    /\ proposals'   = [proposals EXCEPT ![a] = v]
    /\ UNCHANGED <<promises, accepts, decided, decisionVal>>

InitRound(r) ==
    /\ r \notin DOMAIN accepts
    /\ accepts'     = [accepts EXCEPT ![r] = [a \in Agents |-> "⊥"]]
    /\ UNCHANGED <<promises, proposals, decided, decisionVal>>

ClassicPrepare(r) ==
    /\ r \notin DOMAIN promises
    /\ promises'   = [promises EXCEPT ![r] = [a \in Agents |-> FALSE]]
    /\ accepts'    = [accepts EXCEPT ![r] = [a \in Agents |-> "⊥"]]
    /\ UNCHANGED <<proposals, decided, decisionVal>>

RespondPrepare(a, r) ==
    /\ a \in Agents
    /\ r \in DOMAIN promises
    /\ promises[r][a] = FALSE
    /\ promises'   = [promises EXCEPT ![r][a] = TRUE]
    /\ UNCHANGED <<proposals, accepts, decided, decisionVal>>

SendAccept(a, r, v) ==
    /\ a \in Agents
    /\ v \in Values
    /\ r \in DOMAIN accepts
    /\ accepts'   = [accepts EXCEPT ![r][a] = v]
    /\ UNCHANGED <<promises, proposals, decided, decisionVal>>

FastAccept(a, r, v) ==
    /\ a \in Agents
    /\ v \in Values
    /\ r \in DOMAIN accepts
    /\ accepts'   = [accepts EXCEPT ![r][a] = v]
    /\ UNCHANGED <<promises, proposals, decided, decisionVal>>

Decide(r, v) ==
    /\ r \in DOMAIN accepts
    /\ CountAccepts(r, v) >= Majority
    /\ decisionVal' = [decisionVal EXCEPT ![a] = v]
    /\ decided'     = [decided EXCEPT ![a] = TRUE]
    /\ UNCHANGED <<proposals, promises, accepts>>

(* Next-state relation *)
Next ==
    \/ \E a \in Agents, v \in Values : Propose(a,v)
    \/ \E r \in Nat : InitRound(r)
    \/ \E r \in Nat : ClassicPrepare(r)
    \/ \E a \in Agents, r \in DOMAIN promises : RespondPrepare(a,r)
    \/ \E a \in Agents, r \in DOMAIN accepts, v \in Values : SendAccept(a,r,v)
    \/ \E a \in Agents, r \in DOMAIN accepts, v \in Values : FastAccept(a,r,v)
    \/ \E r \in DOMAIN accepts, v \in Values : Decide(r,v)

(* Safety invariant: decisions only on proposed values *)
ConsensusInvariant ==
    \A a \in Agents :
        (decided[a] => (\E i \in Agents : proposals[i] = decisionVal[a]))

Spec == Init /\ [][Next]_<<proposals, promises, accepts, decided, decisionVal>> /\ TypeOK

=============================================================================