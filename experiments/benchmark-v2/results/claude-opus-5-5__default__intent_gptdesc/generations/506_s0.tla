---------------------------- MODULE SingleDecreePaxos ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Proposers,     \* set of proposer identifiers
          Acceptors,     \* set of acceptor identifiers
          Values,        \* set of values that may be proposed
          Quorums,       \* set of quorums (sets of acceptors)
          MaxBallot,     \* largest ballot number (bounds the model)
          BallotOwner    \* assigns each ballot to exactly one proposer

Ballots == 0..MaxBallot

None == CHOOSE v : v \notin Values

\* Quorum intersection requirement: the basis of safety.
ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

\* Ballots are partitioned among proposers, so concurrent proposers never share a ballot.
ASSUME BallotAssumption ==
          /\ MaxBallot \in Nat
          /\ BallotOwner \in [Ballots -> Proposers]

-----------------------------------------------------------------------------
Messages ==
       [type : {"prepare"},  bal : Ballots]
  \cup [type : {"promise"},  acc : Acceptors, bal : Ballots,
                             mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"accept"},   bal : Ballots, val : Values]
  \cup [type : {"accepted"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES maxBal,    \* maxBal[a]: highest ballot acceptor a has promised/participated in
          maxVBal,   \* maxVBal[a]: highest ballot in which a accepted a value (-1 if none)
          maxVal,    \* maxVal[a]: the value a accepted in ballot maxVBal[a] (None if none)
          pBal,      \* pBal[p]: current ballot of proposer p (-1 if none started)
          msgs,      \* every message ever sent (history, used for reasoning)
          net        \* messages currently deliverable (subset of msgs)

vars == <<maxBal, maxVBal, maxVal, pBal, msgs, net>>

TypeOK ==
  /\ maxBal  \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVal  \in [Acceptors -> Values \cup {None}]
  /\ pBal    \in [Proposers -> Ballots \cup {-1}]
  /\ msgs \subseteq Messages
  /\ net  \subseteq msgs

Init ==
  /\ maxBal  = [a \in Acceptors |-> -1]
  /\ maxVBal = [a \in Acceptors |-> -1]
  /\ maxVal  = [a \in Acceptors |-> None]
  /\ pBal    = [p \in Proposers |-> -1]
  /\ msgs = {}
  /\ net  = {}

\* Sending adds a message to the history and to the network.
\* Receipt never removes a message, so a message may be delivered many times
\* (duplication) or at an arbitrarily later time (delay).
Send(m) == /\ msgs' = msgs \cup {m}
           /\ net'  = net  \cup {m}

-----------------------------------------------------------------------------
\* Phase 1a: a proposer starts a new round with a strictly higher ballot it owns.
Prepare(p, b) ==
  /\ BallotOwner[b] = p
  /\ b > pBal[p]
  /\ pBal' = [pBal EXCEPT ![p] = b]
  /\ Send([type |-> "prepare", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal>>

\* Phase 1b: an acceptor promises not to take part in lower ballots and
\* reports its most recently accepted proposal, if any.
Promise(a, m) ==
  /\ m \in net
  /\ m.type = "prepare"
  /\ m.bal > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
  /\ Send([type |-> "promise", acc |-> a, bal |-> m.bal,
           mbal |-> maxVBal[a], mval |-> maxVal[a]])
  /\ UNCHANGED <<maxVBal, maxVal, pBal>>

\* Phase 2a: having received promises from a quorum for its current ballot,
\* a proposer sends an accept request.  The value must be the value of the
\* highest-ballot accepted proposal reported in the promises, or any value
\* if none was reported.
Phase2a(p, Q, v) ==
  LET b == pBal[p] IN
  /\ b # -1
  /\ ~ \E m \in msgs : m.type = "accept" /\ m.bal = b
  /\ \A a \in Q : \E m \in net : /\ m.type = "promise"
                                 /\ m.acc = a
                                 /\ m.bal = b
  /\ LET Q1b  == {m \in net : m.type = "promise" /\ m.acc \in Q /\ m.bal = b}
         Q1bv == {m \in Q1b : m.mbal >= 0}
     IN  \/ Q1bv = {}
         \/ \E m \in Q1bv : /\ m.mval = v
                            /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "accept", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, pBal>>

\* Phase 2b: an acceptor accepts a request unless it has promised a higher ballot.
Phase2b(a, m) ==
  /\ m \in net
  /\ m.type = "accept"
  /\ m.bal >= maxBal[a]
  /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
  /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
  /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
  /\ Send([type |-> "accepted", acc |-> a, bal |-> m.bal, val |-> m.val])
  /\ UNCHANGED pBal

\* Unreliable network: any in-flight message may be lost.  Messages are never corrupted.
Drop(m) ==
  /\ m \in net
  /\ net' = net \ {m}
  /\ UNCHANGED <<maxBal, maxVBal, maxVal, pBal, msgs>>

Next ==
  \/ \E p \in Proposers, b \in Ballots : Prepare(p, b)
  \/ \E p \in Proposers, Q \in Quorums, v \in Values : Phase2a(p, Q, v)
  \/ \E a \in Acceptors, m \in Messages : Promise(a, m) \/ Phase2b(a, m)
  \/ \E m \in Messages : Drop(m)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Derived notions
VotedForIn(a, v, b) ==
  \E m \in msgs : /\ m.type = "accepted"
                  /\ m.acc = a /\ m.bal = b /\ m.val = v

ChosenIn(v, b) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

WontVoteIn(a, b) == /\ \A v \in Values : ~ VotedForIn(a, v, b)
                    /\ maxBal[a] > b

SafeAt(v, b) ==
  \A c \in 0..(b-1) :
     \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, c) \/ WontVoteIn(a, c)

-----------------------------------------------------------------------------
\* Safety: at most one value is chosen.
Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2

\* Acceptor invariants.
AcceptorInv ==
  /\ \A a \in Acceptors :
        /\ maxVBal[a] <= maxBal[a]
        /\ (maxVBal[a] = -1) <=> (maxVal[a] = None)
        /\ maxVBal[a] >= 0 => VotedForIn(a, maxVal[a], maxVBal[a])
        /\ \A c \in (maxVBal[a]+1)..MaxBallot :
              \A v \in Values : ~ VotedForIn(a, v, c)
  \* never accepted two different values in the same ballot
  /\ \A m1, m2 \in msgs :
        (/\ m1.type = "accepted" /\ m2.type = "accepted"
         /\ m1.acc = m2.acc /\ m1.bal = m2.bal) => m1.val = m2.val
  \* acceptances are consistent with promised ballots
  /\ \A m \in msgs : m.type = "accepted" => m.bal <= maxBal[m.acc]

\* Acceptors' promised ballots never decrease.
PromiseMonotonic == [][\A a \in Acceptors : maxBal'[a] >= maxBal[a]]_vars

\* Proposers' ballots strictly increase.
BallotMonotonic == [][\A p \in Proposers : pBal'[p] >= pBal[p]]_vars

\* Proposers pick values consistent with earlier accepted values:
\* every accept request carries a value safe at its ballot, and at most one
\* accept request is issued per ballot.
ProposerInv ==
  \A m \in msgs : m.type = "accept" =>
      /\ SafeAt(m.val, m.bal)
      /\ \A ma \in msgs : (ma.type = "accept" /\ ma.bal = m.bal) => ma = m

\* Message validity: relation between messages and acceptor state.
MsgInv ==
  \A m \in msgs :
    /\ m.type = "prepare" =>
          pBal[BallotOwner[m.bal]] >= m.bal
    /\ m.type = "promise" =>
          /\ m.bal <= maxBal[m.acc]
          /\ \/ m.mval \in Values /\ m.mbal \in Ballots /\ m.mbal < m.bal
                /\ VotedForIn(m.acc, m.mval, m.mbal)
             \/ m.mval = None /\ m.mbal = -1
          /\ \A c \in (m.mbal+1)..(m.bal-1) :
                \A v \in Values : ~ VotedForIn(m.acc, v, c)
    /\ m.type = "accept" =>
          /\ pBal[BallotOwner[m.bal]] >= m.bal
          /\ \E Q \in Quorums : \A a \in Q :
                \E mp \in msgs : mp.type = "promise" /\ mp.acc = a /\ mp.bal = m.bal
    /\ m.type = "accepted" =>
          /\ m.bal <= maxVBal[m.acc]
          /\ \E ma \in msgs : /\ ma.type = "accept"
                              /\ ma.bal = m.bal /\ ma.val = m.val

Inv == TypeOK /\ AcceptorInv /\ ProposerInv /\ MsgInv /\ Consistency

THEOREM Spec => []Inv

-----------------------------------------------------------------------------
\* Optional liveness.
Fairness ==
  /\ \A a \in Acceptors :
        /\ WF_vars(\E m \in Messages : Promise(a, m))
        /\ WF_vars(\E m \in Messages : Phase2b(a, m))
  /\ \A p \in Proposers :
        SF_vars(\E Q \in Quorums, v \in Values : Phase2a(p, Q, v))

LiveSpec == Spec /\ Fairness

\* Eventually p is the only proposer making attempts and messages stop being lost.
Stable(p) ==
  <>[][ /\ net \subseteq net'
        /\ \A q \in Proposers \ {p} : pBal'[q] = pBal[q] ]_vars

\* A majority (quorum) of acceptors keeps responding.
Responsive(Q) ==
  \A a \in Q : /\ []<><<\E m \in Messages : Promise(a, m)>>_vars
                    \/ []<>(~ ENABLED \E m \in Messages : Promise(a, m))

\* p keeps retrying with higher ballots.
Retrying(p) == []<><<\E b \in Ballots : Prepare(p, b)>>_vars

\* Progress: if a proposer repeatedly retries with higher ballots under stable
\* conditions and a quorum is responsive, then eventually a value is chosen.
Progress ==
  (\E p \in Proposers, Q \in Quorums : Stable(p) /\ Retrying(p) /\ Responsive(Q))
     => <>(\E v \in Values : Chosen(v))

=============================================================================