------------------------------ MODULE FastPaxos ------------------------------

EXTENDS Integers

CONSTANT Nil

Replicas == 1..4
Values   == {"v1","v2","v3"}
Ballots  == 1..5

FastBallots    == {1, 3}
ClassicBallots == Ballots \ FastBallots

Quorums ==
  { {1,2,3}, {1,2,4}, {1,3,4}, {2,3,4} }

FastQuorums    == Quorums
ClassicQuorums == Quorums

AnyVal == "any"

VARIABLES msgs, cValue, Decisions

vars == << msgs, cValue, Decisions >>

IsP2a(m) ==
  /\ m.type = "P2a"
  /\ m.bal \in Ballots
  /\ m.val \in (Values \cup {AnyVal})

IsP2b(m) ==
  /\ m.type = "P2b"
  /\ m.bal \in Ballots
  /\ m.acc \in Replicas
  /\ m.val \in Values

P2bMsg(a, b, v) ==
  [type |-> "P2b", acc |-> a, bal |-> b, val |-> v] \in msgs

NoP2bYet(a, b) ==
  ~(\E v \in Values: P2bMsg(a, b, v))

AgreeOn(b, Q, v) ==
  \A a \in Q: P2bMsg(a, b, v)

AllResponded(b, Q) ==
  \A a \in Q: \E v \in Values: P2bMsg(a, b, v)

Collided(b, Q) ==
  /\ AllResponded(b, Q)
  /\ ~(\E v \in Values: AgreeOn(b, Q, v))

MajVals(b, Q) ==
  { v \in Values :
      \E a1, a2 \in Q:
        /\ a1 # a2
        /\ P2bMsg(a1, b, v)
        /\ P2bMsg(a2, b, v)
  }

ProposedInQ(b, Q) ==
  { m.val :
      m \in msgs /\ m.type = "P2b" /\ m.bal = b /\ m.acc \in Q }

ProposedValues ==
  { m.val : m \in msgs /\ m.type = "P2b" }
  \cup { m.val : m \in msgs /\ m.type = "P2a" /\ m.val # AnyVal }

Init ==
  /\ msgs = {}
  /\ cValue = Nil
  /\ Decisions = {}

FastStart ==
  \E b \in FastBallots:
    /\ ~(\E m \in msgs: m.type = "P2a" /\ m.bal = b)
    /\ msgs' = msgs \cup { [type |-> "P2a", bal |-> b, val |-> AnyVal] }
    /\ UNCHANGED << cValue, Decisions >>

FastReply ==
  \E b \in FastBallots:
    \E a \in Replicas:
      /\ (\E m \in msgs: m.type = "P2a" /\ m.bal = b /\ m.val = AnyVal)
      /\ NoP2bYet(a, b)
      /\ \E v \in Values:
           /\ msgs' = msgs \cup { [type |-> "P2b", acc |-> a, bal |-> b, val |-> v] }
           /\ UNCHANGED << cValue, Decisions >>

FastDecide ==
  \E b \in FastBallots:
    \E Q \in FastQuorums:
      \E v \in Values:
        /\ Decisions = {}
        /\ AgreeOn(b, Q, v)
        /\ Decisions' = {v}
        /\ UNCHANGED << msgs, cValue >>

ChooseCValue ==
  \E b \in FastBallots:
    \E Q \in FastQuorums:
      /\ Collided(b, Q)
      /\ LET M == MajVals(b, Q) IN
         IF M # {} THEN
           \E v \in M:
             /\ cValue' = v
             /\ UNCHANGED << msgs, Decisions >>
         ELSE
           \E v \in ProposedInQ(b, Q):
             /\ cValue' = v
             /\ UNCHANGED << msgs, Decisions >>

ClassicStart ==
  \E b \in ClassicBallots:
    /\ cValue # Nil
    /\ ~(\E m \in msgs: m.type = "P2a" /\ m.bal = b /\ m.val = cValue)
    /\ msgs' = msgs \cup { [type |-> "P2a", bal |-> b, val |-> cValue] }
    /\ UNCHANGED << cValue, Decisions >>

ClassicReply ==
  \E a \in Replicas:
    \E b \in ClassicBallots:
      \E v \in Values:
        /\ (\E m \in msgs: m.type = "P2a" /\ m.bal = b /\ m.val = v)
        /\ NoP2bYet(a, b)
        /\ msgs' = msgs \cup { [type |-> "P2b", acc |-> a, bal |-> b, val |-> v] }
        /\ UNCHANGED << cValue, Decisions >>

ClassicDecide ==
  \E b \in ClassicBallots:
    \E Q \in ClassicQuorums:
      \E v \in Values:
        /\ Decisions = {}
        /\ AgreeOn(b, Q, v)
        /\ Decisions' = {v}
        /\ UNCHANGED << msgs, cValue >>

Next ==
  FastStart
  \/ FastReply
  \/ ChooseCValue
  \/ ClassicStart
  \/ ClassicReply
  \/ FastDecide
  \/ ClassicDecide

FastTypeOK ==
  /\ \A m \in msgs: IsP2a(m) \/ IsP2b(m)
  /\ cValue \in (Values \cup {Nil})
  /\ Decisions \subseteq Values

FastNontriviality ==
  Decisions \subseteq ProposedValues

PaxosConsistency ==
  \A v1 \in Values:
    \A v2 \in Values:
      (v1 \in Decisions /\ v2 \in Decisions) => v1 = v2

FastSpec ==
  Init /\ [][Next]_vars
  /\ SF_vars(FastDecide)
  /\ SF_vars(ClassicDecide)

============================================================================