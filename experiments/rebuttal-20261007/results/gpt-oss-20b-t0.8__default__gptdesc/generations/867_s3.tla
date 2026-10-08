---- MODULE Paxos ----
EXTENDS Naturals, TLC

CONSTANT N          \* number of acceptors
CONSTANT Values     \* set of possible proposal values
CONSTANT Ids        \* proposers identifiers

Acceptors == 1 .. N

VARIABLE sentMsgs,
          decision,
          highestSeen,
          highestAccepted,
          acceptedVal

\* Types
Ballot == Nat
Msg == [type : {"prepare","promise","accept","accepted","decide"},
        proposer : Ids,
        ballot : Ballot,
        value : Values \/ {⊥},
        acceptor : Acceptors]

makePrepare(p, b, a) ==
    [type |-> "prepare", proposer |-> p, ballot |-> b,
     value |-> ⊥, acceptor |-> a]
makePromise(m) ==
    [type |-> "promise", proposer |-> m.proposer, ballot |-> m.ballot,
     value |-> m.value, acceptor |-> m.acceptor]
makeAccept(p, b, v, a) ==
    [type |-> "accept", proposer |-> p, ballot |-> b,
     value |-> v, acceptor |-> a]
makeAccepted(m) ==
    [type |-> "accepted", proposer |-> m.proposer, ballot |-> m.ballot,
     value |-> m.value, acceptor |->