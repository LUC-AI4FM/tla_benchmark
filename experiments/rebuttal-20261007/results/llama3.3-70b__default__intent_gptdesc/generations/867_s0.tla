```
MODULE Paxos
EXTENDS Integers, TLC

CONSTANTS Proposers, Acceptors, Values, Quorums
VARIABLES proposed, promised, accepted, decided

Init ==
  /\ proposed = {}
  /\ promised = [i \in Acceptors |-> <<0, None>>]
  /\ accepted = [i \in Acceptors |-> <<0, None>>]
  /\ decided = None

PrepareMessage(b) == << "Prepare", b >>
PromiseMessage(a, b, hv, vv) == << "Promise", a, b, hv, vv >>
AcceptMessage(p, b, v) == << "Accept", p, b, v >>
AcceptedMessage(a, b, v) == << "Accepted", a, b, v >>

Next ==
  \/ \E p \in Proposers, b \in Nat:
        /\ proposed' = proposed \cup {p}
        /\ promised' = [i \in Acceptors |-> IF i \in Quorums THEN <<b, None>> ELSE promised[i]]
        /\ accepted' = accepted
        /\ decided' = decided
  \/ \E a \in Acceptors, p \in Proposers, b \in Nat, hv \in Nat, vv \in Values:
        /\ promised[a] = <<hv, vv>>
        /\ promised' = [i \in Acceptors |-> IF i = a THEN <<b, None>> ELSE promised[i]]
        /\ accepted' = accepted
        /\ decided' = decided
  \/ \E p \in Proposers, b \in Nat, v \in Values:
        /\ \E Q \in Quorums: \A a \in Q: promised[a] = <<b, None>> \/ (promised[a] = <<b, Some(vv)>> /\ vv = v)
        /\ accepted' = [i \in Acceptors |-> IF i \in Quorums THEN <<b, Some(v)>> ELSE accepted[i]]
        /\ promised' = promised
        /\ decided' = decided
  \/ \E Q \in Quorums:
        /\ \A a \in Q: accepted[a] = <<b, Some(v)>>
        /\ decided' = Some(v)
        /\ promised' = promised
        /\ accepted' = accepted

Spec == Init /\ [][Next]_<<proposed, promised, accepted, decided>>

TypeInvariant ==
  /\ proposed \subseteq Proposers
  /\ DOMAIN promised = Acceptors
  /\ DOMAIN accepted = Acceptors
  /\ \A a \in Acceptors: promised[a] \in [r \in Nat, v \in Values \cup {None} |-> <<r, v>>]
  /\ \A a \in Acceptors: accepted[a] \in [r \in Nat, v \in Values \cup {None} |-> <<r, v>>]

QuorumInvariant ==
  /\ Quorums \subseteq SUBSET Acceptors
  /\ \A Q1, Q2 \in Quorums: Q1 \cap Q2 /= {}

Safety == []<>(\E v \in Values: decided = Some(v)) => [](~(\E v1, v2 \in Values: v1 /= v2 /\ decided = Some(v1) /\ decided = Some(v2)))

Validity == []<>(\E v \in Values: decided = Some(v)) => <>(\E p \in Proposers: proposed = {p} /\ \E Q \in Quorums: \A a \in Q: accepted[a] = <<b, Some(v)>>)

Monotonicity == []<>(\A a \in Acceptors: promised[a] = <<r1, v1>> /\ accepted[a] = <<r2, v2>> => r1 <= r2)

THEOREM Spec => []TypeInvariant
THEOREM Spec => []QuorumInvariant
THEOREM Spec => Safety
THEOREM Spec => Validity
THEOREM Spec => Monotonicity
```