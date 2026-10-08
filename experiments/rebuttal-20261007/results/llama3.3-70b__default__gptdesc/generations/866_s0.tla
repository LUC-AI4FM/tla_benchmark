```
MODULE FastPaxos
EXTENDS Integers, TLC

CONSTANTS Agents, Quorums, Values
VARIABLES state, round, value, proposer, acceptor

Init ==
  /\ state = [a \in Agents |-> "initial"]
  /\ round = [a \in Agents |-> 0]
  /\ value = [a \in Agents |-> nil]
  /\ proposer = [r \in Nat |-> nil]
  /\ acceptor = [r \in Nat |-> {}]

TypeInvariant ==
  /\ state \in [Agents -> {"initial", "proposing", "accepting", "accepted"}]
  /\ round \in [Agents -> Nat]
  /\ value \in [Agents -> Values \cup {nil}]
  /\ proposer \in [Nat -> Agents \cup {nil}]
  /\ acceptor \in [Nat -> SUBSET Agents]

NonTriviality ==
  \E v \in Values : \E a \in Agents : state[a] = "accepted" /\ value[a] = v

Propose(r, v) ==
  /\ ~ proposer[r] = nil
  /\ proposer' = [proposer EXCEPT ![r] = nil]
  /\ round' = [round EXCEPT ![\E a \in Agents |-> r]]
  /\ state' = [state EXCEPT ![\E a \in Agents |-> "proposing"]]
  /\ value' = [value EXCEPT ![\E a \in Agents |-> v]]
  /\ acceptor' = acceptor
  /\ UNCHANGED proposer, round, state, value

Accept(r) ==
  /\ ~ proposer[r] = nil
  /\ proposer' = proposer
  /\ round' = [round EXCEPT ![\E a \in Agents |-> r]]
  /\ state' = [state EXCEPT ![\E a \in Agents |-> "accepting"]]
  /\ value' = [value EXCEPT ![\E a \in Agents |-> proposer[r]]]
  /\ acceptor' = [acceptor EXCEPT ![r] = {a \in Agents : state[a] = "accepting"}]
  /\ UNCHANGED round, state, value

Learn(r) ==
  /\ ~ proposer[r] = nil
  /\ proposer' = proposer
  /\ round' = [round EXCEPT ![\E a \in Agents |-> r]]
  /\ state' = [state EXCEPT ![\E a \in Agents |-> "accepted"]]
  /\ value' = [value EXCEPT ![\E a \in Agents |-> proposer[r]]]
  /\ acceptor' = [acceptor EXCEPT ![r] = {}]
  /\ UNCHANGED round, state, value

Next ==
  \/ \E r \in Nat, v \in Values : Propose(r, v)
  \/ \E r \in Nat : Accept(r)
  \/ \E r \in Nat : Learn(r)

Spec == Init /\ [][Next]_state /\ WF_vars(Next)_(state, round, value, proposer, acceptor)

THEOREM Spec => []NonTriviality
```