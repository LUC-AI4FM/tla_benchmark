--------------------------- MODULE Paxos ---------------------------
EXTENDS Integers, Sequences

CONSTANT Proposers, Acceptors, Values
VARIABLE messages, decision, highestSeen, highestAccepted, acceptedValue

PaxosSpec ==
  /\ messages = <<>>
  /\ decision = NULL
  /\ highestSeen = [i \in Acceptors |-> 0]
  /\ highestAccepted = [i \in Acceptors |-> 0]
  /\ acceptedValue = [i \in Acceptors |-> NULL]

SendPrepare(b, p) ==
  /\ messages' = Append(messages, <<<<"prepare", b, p>>>)
  /\ decision' = decision
  /\ highestSeen' = [highestSeen EXCEPT ![p] = b]
  /\ highestAccepted' = highestAccepted
  /\ acceptedValue' = acceptedValue

SendPromise(b, p) ==
  /\ messages' = Append(messages, <<<<"promise", b, p>>>)
  /\ decision' = decision
  /\ highestSeen' = [highestSeen EXCEPT ![p] = b]
  /\ highestAccepted' = highestAccepted
  /\ acceptedValue' = acceptedValue

SendAccept(b, v, p) ==
  /\ messages' = Append(messages, <<<<"accept", b, v, p>>>)
  /\ decision' = decision
  /\ highestSeen' = [highestSeen EXCEPT ![p] = b]
  /\ highestAccepted' = [highestAccepted EXCEPT ![p] = b]
  /\ acceptedValue' = [acceptedValue EXCEPT ![p] = v]

SendAccepted(b, v, p) ==
  /\ messages' = Append(messages, <<<<"accepted", b, v, p>>>)
  /\ decision' = decision
  /\ highestSeen' = highestSeen
  /\ highestAccepted' = highestAccepted
  /\ acceptedValue' = acceptedValue

SendDecide(v) ==
  /\ messages' = Append(messages, <<<<"decide", v>>>)
  /\ decision' = v
  /\ highestSeen' = highestSeen
  /\ highestAccepted' = highestAccepted
  /\ acceptedValue' = acceptedValue

Next ==
  \/ \E b \in Nat, p \in Proposers : SendPrepare(b, p)
  \/ \E b \in Nat, p \in Acceptors : SendPromise(b, p)
  \/ \E b \in Nat, v \in Values, p \in Proposers : SendAccept(b, v, p)
  \/ \E b \in Nat, v \in Values, p \in Acceptors : SendAccepted(b, v, p)
  \/ \E v \in Values : SendDecide(v)

PaxosTypeOK ==
  /\ messages \in Seq(<<"prepare" | "promise" | "accept" | "accepted" | "decide">> \X Nat \X Proposers \X Values)
  /\ decision \in Values \cup {NULL}
  /\ highestSeen \in [Acceptors |-> Nat]
  /\ highestAccepted \in [Acceptors |-> Nat]
  /\ acceptedValue \in [Acceptors |-> Values \cup {NULL}]

PaxosNontriviality ==
  decision \in Values
  => decision \in {v \in Values : <<<<"accept", _, v, _>>> \in messages}

PaxosConsistency ==
  []<>(decision # NULL)
  => <>[](decision' = decision)

THEOREM PaxosSpec => []PaxosTypeOK
THEOREM PaxosSpec => []PaxosNontriviality
THEOREM PaxosSpec => PaxosConsistency

Liveness == FALSE

(* Note: Paxos does not guarantee termination under the asynchronous fault model implied by FLP-style reasoning *)
=============================================================================