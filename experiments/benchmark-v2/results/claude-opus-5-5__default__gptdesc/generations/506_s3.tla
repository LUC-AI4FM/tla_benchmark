---------------------------- MODULE MCPaxos ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the Paxos consensus specification.          *)
(* It extends the Paxos module (constants Value, Acceptor, Quorum; the     *)
(* operators Ballot, None, Message, Init, Next, Spec; and the variables    *)
(* maxBal, maxVBal, maxVal, msgs).  It adds helper definitions and         *)
(* safety invariants about votes, chosen values, message validity,         *)
(* acceptor validity and consistency, and it maps Paxos onto the           *)
(* single-value Consensus abstraction.                                     *)
(*                                                                         *)
(* All helper names begin with "Mc" so that they do not clash with any     *)
(* definition that the Paxos module already makes.                        *)
(***************************************************************************)
EXTENDS Paxos, Naturals, FiniteSets

-----------------------------------------------------------------------------
(***************************************************************************)
(* Helpers about votes                                                     *)
(***************************************************************************)

\* The set of "2b" messages that the acceptors have sent.
McVoteMsgs == {m \in msgs : m.type = "2b"}

\* Acceptor a voted for value v in ballot b.
McVotedForIn(a, v, b) ==
    \E m \in McVoteMsgs : /\ m.acc = a
                          /\ m.bal = b
                          /\ m.val = v

\* For each acceptor, the set of <<ballot, value>> pairs that it voted for.
McVotes ==
    [a \in Acceptor |->
        {<<m.bal, m.val>> : m \in {mm \in McVoteMsgs : mm.acc = a}}]

\* Value v is chosen in ballot b: some quorum voted for v in ballot b.
McChosenIn(v, b) ==
    \E Q \in Quorum : \A a \in Q : McVotedForIn(a, v, b)

\* Value v is chosen in some ballot.
McChosenValue(v) ==
    \E m \in McVoteMsgs : McChosenIn(v, m.bal) /\ m.val = v

\* The set of values chosen by Paxos.
McChosen == {v \in Value : McChosenValue(v)}

\* Acceptor a cannot vote any longer in ballot b.
McCannotVoteAt(a, b) ==
    /\ maxBal[a] > b
    /\ ~ \E v \in Value : McVotedForIn(a, v, b)

\* No value other than v has been or can be chosen in ballot b.
McNoneOtherChoosableAt(b, v) ==
    \E Q \in Quorum :
        \A a \in Q : McVotedForIn(a, v, b) \/ McCannotVoteAt(a, b)

\* Value v is safe at ballot b.
McSafeAt(v, b) ==
    \A c \in 0 .. (b - 1) : McNoneOtherChoosableAt(c, v)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness                                                        *)
(***************************************************************************)

McTypeOK ==
    /\ msgs \subseteq Message
    /\ maxBal  \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVBal \in [Acceptor -> Ballot \cup {-1}]
    /\ maxVal  \in [Acceptor -> Value \cup {None}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Validity of messages                                                    *)
(***************************************************************************)

\* A "1b" message from acceptor a reports a vote that a really cast,
\* and it is sent only for a ballot at most a's current maxBal.
McOneBMsgValid(m) ==
    /\ m.bal =< maxBal[m.acc]
    /\ \/ /\ m.mbal = -1
          /\ m.mval = None
       \/ /\ m.mbal \in Ballot
          /\ m.mbal < m.bal
          /\ m.mval \in Value
          /\ McVotedForIn(m.acc, m.mval, m.mbal)
    /\ \A c \in (m.mbal + 1) .. (m.bal - 1) :
          ~ \E v \in Value : McVotedForIn(m.acc, v, c)

\* A "2a" message proposes a value that is safe at its ballot, and there
\* is at most one "2a" message per ballot.
McTwoAMsgValid(m) ==
    /\ McSafeAt(m.val, m.bal)
    /\ \A mm \in msgs :
          (mm.type = "2a" /\ mm.bal = m.bal) => mm = m

\* A "2b" message is sent only in response to a matching "2a" message,
\* and only for a ballot at most the acceptor's maxVBal.
McTwoBMsgValid(m) ==
    /\ \E mm \in msgs : /\ mm.type = "2a"
                        /\ mm.bal  = m.bal
                        /\ mm.val  = m.val
    /\ m.bal =< maxVBal[m.acc]

McMsgValid(m) ==
    CASE m.type = "1b" -> McOneBMsgValid(m)
      [] m.type = "2a" -> McTwoAMsgValid(m)
      [] m.type = "2b" -> McTwoBMsgValid(m)
      [] OTHER         -> TRUE

McMsgInv == \A m \in msgs : McMsgValid(m)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Validity of acceptor state                                              *)
(***************************************************************************)

McAccValid(a) ==
    /\ maxVBal[a] =< maxBal[a]
    /\ (maxVBal[a] = -1) <=> (maxVal[a] = None)
    /\ (maxVBal[a] >= 0) => McVotedForIn(a, maxVal[a], maxVBal[a])
    /\ \A c \in Ballot :
          c > maxVBal[a] => ~ \E v \in Value : McVotedForIn(a, v, c)

McAccInv == \A a \in Acceptor : McAccValid(a)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Consistency and voting invariants                                       *)
(***************************************************************************)

\* An acceptor votes for at most one value in any ballot.
McVotesSafe ==
    \A a \in Acceptor, b \in Ballot, v, w \in Value :
        McVotedForIn(a, v, b) /\ McVotedForIn(a, w, b) => v = w

\* Different acceptors never vote for different values in the same ballot.
McOneValuePerBallot ==
    \A a1, a2 \in Acceptor, b \in Ballot, v1, v2 \in Value :
        McVotedForIn(a1, v1, b) /\ McVotedForIn(a2, v2, b) => v1 = v2

\* Every vote is for a value that was safe at that ballot.
McVotesAreSafe ==
    \A a \in Acceptor, b \in Ballot, v \in Value :
        McVotedForIn(a, v, b) => McSafeAt(v, b)

\* At most one value is ever chosen.
McConsistency ==
    \A v, w \in Value : McChosenValue(v) /\ McChosenValue(w) => v = w

McChosenAtMostOne == Cardinality(McChosen) =< 1

\* Inductive-style combined invariant.
McInv ==
    /\ McTypeOK
    /\ McAccInv
    /\ McMsgInv

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement: Paxos implements single-value Consensus, with Consensus's   *)
(* variable "chosen" mapped to the set of values chosen by Paxos.          *)
(***************************************************************************)

C == INSTANCE Consensus WITH chosen <- McChosen

McConsensusSpec == C!Spec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking specification and properties                             *)
(***************************************************************************)

McInit == Init
McNext == Next
McSpec == Spec

THEOREM McSpec => []McTypeOK
THEOREM McSpec => []McInv
THEOREM McSpec => []McConsistency
THEOREM McSpec => []McChosenAtMostOne
THEOREM McSpec => []McVotesSafe
THEOREM McSpec => []McOneValuePerBallot
THEOREM McSpec => McConsensusSpec
=============================================================================