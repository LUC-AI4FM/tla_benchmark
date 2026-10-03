--------------------------- MODULE FastPaxos ---------------------------
EXTENDS Integers, TLC

CONSTANTS Agents, Quorums, Values
VARIABLES state, proposals, acceptances, coordinator

TypeOK == /\ state \in [Agents -> {"prepare", "accept", "learn"}]
          /\ proposals \in [Agents -> (Quorums -> Values)]
          /\ acceptances \in [Agents -> (Quorums -> Values)]
          /\ coordinator \in Agents

FastTypeOK == TypeOK

Nontriviality == <>~(state = [a \in Agents |-> "learn"])

FastSpec ==
  /\ state = [a \in Agents |-> "prepare"]
  /\ proposals = [a \in Agents |-> [q \in Quorums |-> nil]]
  /\ acceptances = [a \in Agents |-> [q \in Quorums |-> nil]]
  /\ coordinator \in Agents
  /\ [][
      /\ (coordinator = "classic" => 
          /\ \E v \in Values : 
              /\ proposals' = [proposals EXCEPT ![coordinator] = [Quorums -> v]]
              /\ acceptances' = acceptances
              /\ state' = [state EXCEPT ![coordinator] = "accept"]
          \/ \E q \in Quorums :
              /\ proposals' = [proposals EXCEPT ![coordinator] = [q |-> nil]]
              /\ acceptances' = acceptances
              /\ state' = [state EXCEPT ![coordinator] = "prepare"])
      /\ (coordinator = "fast" =>
          /\ \E v \in Values :
              /\ proposals' = [proposals EXCEPT ![coordinator] = [Quorums -> v]]
              /\ acceptances' = [acceptances EXCEPT ![coordinator] = [Quorums -> v]]
              /\ state' = [state EXCEPT ![coordinator] = "learn"]
          \/ \E q \in Quorums :
              /\ proposals' = [proposals EXCEPT ![coordinator] = [q |-> nil]]
              /\ acceptances' = [acceptances EXCEPT ![coordinator] = [q |-> nil]]
              /\ state' = [state EXCEPT ![coordinator] = "prepare"])
      ]
  ]

PaxosConsistency == 
  \A v \in Values : 
    <<v>>_proposals \subseteq <<v>>_acceptances

THEOREM FastSpec => []PaxosConsistency
=============================================================================