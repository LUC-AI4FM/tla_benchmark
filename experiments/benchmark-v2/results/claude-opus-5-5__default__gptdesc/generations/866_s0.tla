------------------------------ MODULE FastPaxos ------------------------------
(***************************************************************************)
(* A simplified specification of Lamport's Fast Paxos consensus protocol.  *)
(*                                                                         *)
(* Simplifications:                                                        *)
(*  - There is a single, unique coordinator. It never sends two different  *)
(*    phase 2a messages for the same ballot.                               *)
(*  - Failures are not modeled explicitly. Agents are assumed to restore   *)
(*    their state from stable storage. Message loss is modeled by          *)
(*    messages never being received.                                       *)
(*  - All agents communicate directly through a shared set of messages.    *)
(*                                                                         *)
(* Ballots are partitioned into fast and classic ballots. In a fast        *)
(* ballot the coordinator may send the special value Any. Acceptors then   *)
(* vote directly for client proposals. A value is chosen in a fast ballot  *)
(* by a fast quorum and in a classic ballot by a classic quorum. When      *)
(* proposals collide in a fast ballot, the coordinator recovers in a later *)
(* ballot. It uses the quorum-intersection based value-selection rule.     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Values,          \* The set of values that may be proposed
    Acceptors,       \* The set of acceptors
    FastQuorums,     \* The set of fast quorums
    ClassicQuorums,  \* The set of classic quorums
    FastBallots,     \* The set of fast ballot numbers
    ClassicBallots,  \* The set of classic ballot numbers
    None,            \* Placeholder meaning "no value"
    Any              \* Special phase 2a value used in fast ballots

Ballots == FastBallots \cup ClassicBallots

ASSUME BallotAssumption ==
    /\ Ballots \subseteq (Nat \ {0})
    /\ FastBallots \cap ClassicBallots = {}

ASSUME ValueAssumption ==
    /\ None \notin Values
    /\ Any \notin Values
    /\ None # Any

ASSUME QuorumAssumption ==
    /\ ClassicQuorums \subseteq SUBSET Acceptors
    /\ FastQuorums \subseteq SUBSET Acceptors
    \* Any two classic quorums intersect.
    /\ \A Q1, Q2 \in ClassicQuorums : Q1 \cap Q2 # {}
    \* Any two fast quorums intersect.
    /\ \A R1, R2 \in FastQuorums : R1 \cap R2 # {}
    \* A classic quorum and a fast quorum intersect.
    /\ \A Q \in ClassicQuorums, R \in FastQuorums : Q \cap R # {}
    \* A classic quorum and any two fast quorums have a common acceptor.
    /\ \A Q \in ClassicQuorums, R1, R2 \in FastQuorums : Q \cap R1 \cap R2 # {}

\* The quorums used for voting (phase 2) in ballot b.
Quorum(b) == IF b \in FastBallots THEN FastQuorums ELSE ClassicQuorums

Message ==
         [type : {"propose"}, value : Values]
    \cup [type : {"phase1a"}, bal : Ballots]
    \cup [type : {"phase1b"}, bal : Ballots, acc : Acceptors,
          vbal : Ballots \cup {0}, vval : Values \cup {None}]
    \cup [type : {"phase2a"}, bal : Ballots, value : Values \cup {Any}]
    \cup [type : {"phase2b"}, bal : Ballots, acc : Acceptors, value : Values]

VARIABLES
    messages,   \* The set of all messages that have been sent
    maxBal,     \* maxBal[a]: highest ballot in which acceptor a participated
    maxVBal,    \* maxVBal[a]: highest ballot in which a voted (0 = none)
    maxVal,     \* maxVal[a]: value a voted for in ballot maxVBal[a]
    decision    \* The set of values learned as chosen

vars == <<messages, maxBal, maxVBal, maxVal, decision>>

TypeOK ==
    /\ messages \subseteq Message
    /\ maxBal \in [Acceptors -> Ballots \cup {0}]
    /\ maxVBal \in [Acceptors -> Ballots \cup {0}]
    /\ maxVal \in [Acceptors -> Values \cup {None}]
    /\ decision \subseteq Values

Init ==
    /\ messages = {}
    /\ maxBal = [a \in Acceptors |-> 0]
    /\ maxVBal = [a \in Acceptors |-> 0]
    /\ maxVal = [a \in Acceptors |-> None]
    /\ decision = {}

Send(m) == messages' = messages \cup {m}

\* The set of values that clients have proposed so far.
Proposed == {m.value : m \in {mm \in messages : mm.type = "propose"}}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Proposers (clients)                                                     *)
(***************************************************************************)
Propose(v) ==
    /\ Send([type |-> "propose", value |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decision>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Coordinator actions                                                     *)
(***************************************************************************)
Phase1a(b) ==
    /\ ~\E m \in messages : m.type = "phase1a" /\ m.bal = b
    /\ Send([type |-> "phase1a", bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decision>>

\* The phase 1b messages for ballot b sent by acceptors in Q.
P1bMsgs(b, Q) ==
    {m \in messages : m.type = "phase1b" /\ m.bal = b /\ m.acc \in Q}

\* Values the coordinator may send in ballot b when nothing constrains it.
FreeValues(b) ==
    IF b \in FastBallots THEN Proposed \cup {Any} ELSE Proposed

\* The value-selection rule of Fast Paxos. S is the set of phase 1b
\* messages from the classic quorum Q.
SelectableValues(b, Q, S) ==
    LET k == CHOOSE kk \in {m.vbal : m \in S} : \A m \in S : m.vbal <= kk
        Sk == {m \in S : m.vbal = k}
        V == {m.vval : m \in Sk}
        \* v may have been chosen by some fast quorum R in fast ballot k
        \* if every acceptor in R \cap Q voted for v in ballot k.
        O4(v) == \E R \in FastQuorums :
                    \A a \in R \cap Q :
                       \E m \in Sk : m.acc = a /\ m.vval = v
        W == {v \in V : O4(v)}
    IN  IF k = 0
          THEN FreeValues(b)          \* No acceptor in Q has voted.
        ELSE IF k \in ClassicBallots
          THEN V                      \* V is a singleton.
        ELSE IF W # {}
          THEN W                      \* At most one such value exists.
        ELSE FreeValues(b)            \* A collision occurred; nothing chosen at k.

Phase2a(b, v) ==
    /\ ~\E m \in messages : m.type = "phase2a" /\ m.bal = b
    /\ \E Q \in ClassicQuorums :
          LET S == P1bMsgs(b, Q)
          IN  /\ \A a \in Q : \E m \in S : m.acc = a
              /\ v \in SelectableValues(b, Q, S)
    /\ Send([type |-> "phase2a", bal |-> b, value |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, decision>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Acceptor actions                                                        *)
(***************************************************************************)
Phase1b(a) ==
    \E m \in messages :
       /\ m.type = "phase1a"
       /\ m.bal > maxBal[a]
       /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
       /\ Send([type |-> "phase1b", bal |-> m.bal, acc |-> a,
                vbal |-> maxVBal[a], vval |-> maxVal[a]])
       /\ UNCHANGED <<maxVBal, maxVal, decision>>

\* The acceptor votes for the value sent by the coordinator.
Phase2b(a) ==
    \E m \in messages :
       /\ m.type = "phase2a"
       /\ m.value \in Values
       /\ m.bal >= maxBal[a]
       /\ maxVBal[a] < m.bal
       /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
       /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
       /\ maxVal' = [maxVal EXCEPT ![a] = m.value]
       /\ Send([type |-> "phase2b", bal |-> m.bal, acc |-> a, value |-> m.value])
       /\ UNCHANGED decision

\* In a fast ballot whose phase 2a message carries Any, the acceptor
\* votes directly for a value proposed by a client.
FastAccept(a) ==
    \E m \in messages, p \in messages :
       /\ m.type = "phase2a"
       /\ m.value = Any
       /\ m.bal \in FastBallots
       /\ m.bal >= maxBal[a]
       /\ maxVBal[a] < m.bal
       /\ p.type = "propose"
       /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
       /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
       /\ maxVal' = [maxVal EXCEPT ![a] = p.value]
       /\ Send([type |-> "phase2b", bal |-> m.bal, acc |-> a, value |-> p.value])
       /\ UNCHANGED decision

-----------------------------------------------------------------------------
(***************************************************************************)
(* Learner                                                                 *)
(***************************************************************************)
ChosenIn(v, b) ==
    \E R \in Quorum(b) :
       \A a \in R :
          \E m \in messages :
             /\ m.type = "phase2b"
             /\ m.bal = b
             /\ m.acc = a
             /\ m.value = v

Learn(v, b) ==
    /\ ChosenIn(v, b)
    /\ decision' = decision \cup {v}
    /\ UNCHANGED <<messages, maxBal, maxVBal, maxVal>>

-----------------------------------------------------------------------------
Next ==
    \/ \E v \in Values : Propose(v)
    \/ \E b \in Ballots : Phase1a(b)
    \/ \E b \in Ballots, v \in Values \cup {Any} : Phase2a(b, v)
    \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a) \/ FastAccept(a)
    \/ \E v \in Values, b \in Ballots : Learn(v, b)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* Non-triviality: only a value that has been proposed can be learned.
Nontriviality ==
    \A v \in decision : \E m \in messages : m.type = "propose" /\ m.value = v

\* Consistency: at most one value is learned.
Consistency ==
    \A v1, v2 \in decision : v1 = v2

\* Each phase 2b vote is for a proposed value.
VotesProposed ==
    \A m \in messages :
       m.type = "phase2b" => m.value \in Proposed

THEOREM Spec => [](TypeOK /\ Nontriviality /\ Consistency)
=============================================================================