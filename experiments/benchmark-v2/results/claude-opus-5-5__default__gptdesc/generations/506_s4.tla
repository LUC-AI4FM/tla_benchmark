------------------------------ MODULE MCPaxos ------------------------------
(***************************************************************************)
(* Model-checking wrapper for the Paxos consensus specification.          *)
(*                                                                         *)
(* This module EXTENDS the Paxos module. Paxos is assumed to declare:     *)
(*   CONSTANTS Value, Acceptor, Quorum                                     *)
(*   VARIABLES maxBal, maxVBal, maxVal, msgs                              *)
(* and to define Ballot, None, Message, TypeOK, Init, Next, vars and      *)
(* Spec.                                                                   *)
(*                                                                         *)
(* This module adds helper definitions and safety invariants about votes, *)
(* chosen values, message validity, acceptor validity and consistency.    *)
(* It then instantiates the single-value Consensus specification, mapping *)
(* its variable `chosen` to the set of values chosen by Paxos.            *)
(***************************************************************************)
EXTENDS Paxos, Integers, FiniteSets

-----------------------------------------------------------------------------
(***************************************************************************)
(* Helper definitions about votes and chosen values.                       *)
(***************************************************************************)

\* The set of ballot numbers that appear in some message.
\* Using this set keeps every quantifier finite for TLC.
MsgBallots == { m.bal : m \in msgs }

\* Acceptor a has voted for value v in ballot b.
MCVotedForIn(a, v, b) ==
    \E m \in msgs : /\ m.type = "2b"
                    /\ m.acc  = a
                    /\ m.val  = v
                    /\ m.bal  = b

\* Value v is chosen in ballot b: a quorum of acceptors voted for v in b.
MCChosenIn(v, b) ==
    \E Q \in Quorum : \A a \in Q : MCVotedForIn(a, v, b)

\* Value v is chosen in some ballot.
MCChosen(v) ==
    \E b \in MsgBallots : MCChosenIn(v, b)

\* The set of all values chosen by Paxos.
MCChosenSet == { v \in Value : MCChosen(v) }

\* Acceptor a has not voted in ballot b and never will.
MCWontVoteIn(a, b) ==
    /\ \A v \in Value : ~ MCVotedForIn(a, v, b)
    /\ maxBal[a] > b

\* No value other than v has been or can be chosen in any ballot below b.
MCSafeAt(v, b) ==
    \A c \in 0..(b - 1) :
        \E Q \in Quorum :
            \A a \in Q : MCVotedForIn(a, v, c) \/ MCWontVoteIn(a, c)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants.                                                      *)
(***************************************************************************)

\* Type correctness (from the Paxos module).
MCTypeOK == TypeOK

\* Validity of messages.
MCMsgInv ==
    \A m \in msgs :
        /\ (m.type = "1b") =>
              /\ m.bal =< maxBal[m.acc]
              /\ \/ /\ m.mval \in Value
                    /\ m.mbal \in Ballot
                    /\ MCVotedForIn(m.acc, m.mval, m.mbal)
                 \/ /\ m.mval = None
                    /\ m.mbal = -1
              /\ \A c \in (m.mbal + 1)..(m.bal - 1) :
                    ~ \E v \in Value : MCVotedForIn(m.acc, v, c)
        /\ (m.type = "2a") =>
              /\ MCSafeAt(m.val, m.bal)
              /\ \A ma \in msgs :
                    (ma.type = "2a" /\ ma.bal = m.bal) => (ma = m)
        /\ (m.type = "2b") =>
              /\ \E ma \in msgs : /\ ma.type = "2a"
                                  /\ ma.bal  = m.bal
                                  /\ ma.val  = m.val
              /\ m.bal =< maxVBal[m.acc]

\* Validity of acceptor state.
MCAccInv ==
    \A a \in Acceptor :
        /\ (maxVal[a] = None) <=> (maxVBal[a] = -1)
        /\ maxVBal[a] =< maxBal[a]
        /\ (maxVBal[a] >= 0) => MCVotedForIn(a, maxVal[a], maxVBal[a])
        /\ \A c \in Ballot :
              c > maxVBal[a] =>
                  ~ \E v \in Value : MCVotedForIn(a, v, c)

\* Consistency: at most one value is chosen.
MCConsistency ==
    \A v, w \in Value : (MCChosen(v) /\ MCChosen(w)) => (v = w)

\* Votes in a single ballot are for a single value.
MCVoteConsistency ==
    \A a1, a2 \in Acceptor, v1, v2 \in Value, b \in MsgBallots :
        (MCVotedForIn(a1, v1, b) /\ MCVotedForIn(a2, v2, b)) => (v1 = v2)

\* Combined inductive invariant.
MCInv ==
    /\ MCTypeOK
    /\ MCMsgInv
    /\ MCAccInv

-----------------------------------------------------------------------------
(***************************************************************************)
(* Connection to the single-value consensus abstraction.                  *)
(***************************************************************************)

C == INSTANCE Consensus WITH chosen <- MCChosenSet

\* Paxos implements Consensus under the refinement mapping above.
MCRefinement == C!Spec

\* Consensus invariants lifted to the Paxos model.
MCConsensusInv == C!Inv

-----------------------------------------------------------------------------
(***************************************************************************)
(* Specification (inherited from Paxos) and theorems.                     *)
(***************************************************************************)

MCInit == Init
MCNext == Next
MCSpec == Spec

THEOREM MCSpec => []MCTypeOK
THEOREM MCSpec => []MCInv
THEOREM MCSpec => []MCConsistency
THEOREM MCSpec => []MCVoteConsistency
THEOREM MCSpec => MCRefinement
=============================================================================