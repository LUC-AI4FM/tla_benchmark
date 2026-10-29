---------------------------- MODULE FastPaxos ----------------------------
(***************************************************************************)
(* Fast Paxos consensus protocol.                                          *)
(*                                                                         *)
(* A set of acceptor Replicas and a single, pre-established coordinator    *)
(* agree on one value. Ballots are split into fast and classic ballots.    *)
(*                                                                         *)
(*  - Fast round: after phase 1 with no previous votes, the coordinator    *)
(*    sends "Any". Each acceptor then proposes and votes for its own       *)
(*    value. A fast quorum voting for the same value decides it.           *)
(*  - Classic round: the coordinator runs phase 1 and picks a value. If    *)
(*    a fast round collided, it applies the collision-recovery rule:       *)
(*    a value voted by every member of Q \cap R for some fast quorum R     *)
(*    must be picked. Otherwise any value voted at that ballot may be      *)
(*    picked. Acceptors vote, and a classic quorum decides.                *)
(*                                                                         *)
(* Agents have stable storage, so a crash followed by recovery is the     *)
(* same as a pause. Message loss and duplication are modeled by a         *)
(* monotonically growing set of messages.                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Replicas,        \* the acceptors
          Values,          \* values that may be proposed
          FastBallots,     \* ballot numbers of fast rounds
          ClassicBallots,  \* ballot numbers of classic rounds
          FastQuorums,     \* fast quorums
          ClassicQuorums   \* classic quorums

VARIABLES msgs,        \* set of all messages sent so far
          maxBallot,   \* maxBallot[a]: highest ballot a has joined
          maxVBallot,  \* maxVBallot[a]: highest ballot a has voted in (0 = none)
          maxValue,    \* maxValue[a]: value a voted for in maxVBallot[a]
          proposed,    \* values proposed by acceptors in fast rounds
          decision     \* set of decided values

vars == <<msgs, maxBallot, maxVBallot, maxValue, proposed, decision>>

Ballots == FastBallots \cup ClassicBallots

none == CHOOSE v : v \notin Values
Any  == CHOOSE v : v \notin Values \cup {none}

-----------------------------------------------------------------------------
(* Assumptions *)

ASSUME BallotAssumption ==
    /\ FastBallots \cap ClassicBallots = {}
    /\ Ballots \subseteq (Nat \ {0})

ASSUME FastQuorumAssumption ==
    /\ IsFiniteSet(Replicas)
    /\ FastQuorums \subseteq SUBSET Replicas
    /\ \A F1, F2 \in FastQuorums : F1 \cap F2 # {}
    /\ \A F \in FastQuorums : 4 * Cardinality(F) >= 3 * Cardinality(Replicas)

ASSUME ClassicQuorumAssumption ==
    /\ ClassicQuorums \subseteq SUBSET Replicas
    /\ \A Q1, Q2 \in ClassicQuorums : Q1 \cap Q2 # {}
    /\ \A Q \in ClassicQuorums : \A F1, F2 \in FastQuorums :
          Q \cap F1 \cap F2 # {}

-----------------------------------------------------------------------------
(* Messages *)

Message ==
         [type : {"P1a"}, bal : Ballots]
    \cup [type : {"P1b"}, bal : Ballots, acc : Replicas,
          vbal : Ballots \cup {0}, vval : Values \cup {none}]
    \cup [type : {"P2a"}, bal : Ballots, val : Values \cup {Any}]
    \cup [type : {"P2b"}, bal : Ballots, acc : Replicas, val : Values]

TypeOK ==
    /\ msgs \subseteq Message
    /\ maxBallot \in [Replicas -> Ballots \cup {0}]
    /\ maxVBallot \in [Replicas -> Ballots \cup {0}]
    /\ maxValue \in [Replicas -> Values \cup {none}]
    /\ proposed \subseteq Values
    /\ decision \subseteq Values

Send(m) == msgs' = msgs \cup {m}

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ msgs = {}
    /\ maxBallot = [a \in Replicas |-> 0]
    /\ maxVBallot = [a \in Replicas |-> 0]
    /\ maxValue = [a \in Replicas |-> none]
    /\ proposed = {}
    /\ decision = {}

-----------------------------------------------------------------------------
(* Phase 1 (coordinator and acceptors) *)

Phase1a(b) ==
    /\ ~\E m \in msgs : m.type = "P1a" /\ m.bal = b
    /\ Send([type |-> "P1a", bal |-> b])
    /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, proposed, decision>>

Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "P1a"
        /\ m.bal > maxBallot[a]
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
        /\ Send([type |-> "P1b", bal |-> m.bal, acc |-> a,
                 vbal |-> maxVBallot[a], vval |-> maxValue[a]])
        /\ UNCHANGED <<maxVBallot, maxValue, proposed, decision>>

(* Phase-1b messages for ballot b from the members of Q *)
P1bMsgs(b, Q) ==
    {m \in msgs : m.type = "P1b" /\ m.bal = b /\ m.acc \in Q}

(* Every member of Q has answered phase 1 of ballot b *)
P1bQuorumReady(b, Q) ==
    \A a \in Q : \E m \in msgs : m.type = "P1b" /\ m.bal = b /\ m.acc = a

(* Highest ballot in which some member of Q voted, as reported in phase 1 *)
MaxReportedVBal(b, Q) == Max({m.vbal : m \in P1bMsgs(b, Q)})

(***************************************************************************)
(* Values the coordinator may safely pick for ballot b, given phase-1b     *)
(* reports from classic quorum Q. This includes the collision-recovery     *)
(* rule.                                                                   *)
(***************************************************************************)
PickSet(b, Q) ==
    LET S  == P1bMsgs(b, Q)
        k  == MaxReportedVBal(b, Q)
        Sk == {m \in S : m.vbal = k}
        Vk == {m.vval : m \in Sk}
        \* v may have been chosen in fast ballot k by fast quorum R
        O4(v) == \E R \in FastQuorums :
                    \A a \in Q \cap R :
                        \E m \in Sk : m.acc = a /\ m.vval = v
    IN  IF k = 0 THEN proposed                  \* no votes: any proposed value
        ELSE IF k \in ClassicBallots THEN Vk     \* the unique classic value
        ELSE IF \E v \in Vk : O4(v)
                THEN {v \in Vk : O4(v)}          \* value with fast-quorum majority
                ELSE Vk                          \* collision: any voted value

-----------------------------------------------------------------------------
(* Phase 2 *)

(* The coordinator starts a fast round: acceptors may propose any value. *)
StartFastRound(b) ==
    /\ b \in FastBallots
    /\ ~\E m \in msgs : m.type = "P2a" /\ m.bal = b
    /\ \E Q \in ClassicQuorums :
          /\ P1bQuorumReady(b, Q)
          /\ MaxReportedVBal(b, Q) = 0
    /\ Send([type |-> "P2a", bal |-> b, val |-> Any])
    /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, proposed, decision>>

(* The coordinator starts a classic round. This handles collision recovery. *)
StartClassicRound(b) ==
    /\ b \in ClassicBallots
    /\ ~\E m \in msgs : m.type = "P2a" /\ m.bal = b
    /\ \E Q \in ClassicQuorums :
          /\ P1bQuorumReady(b, Q)
          /\ \E v \in PickSet(b, Q) :
                Send([type |-> "P2a", bal |-> b, val |-> v])
    /\ UNCHANGED <<maxBallot, maxVBallot, maxValue, proposed, decision>>

(* In a fast round, an acceptor proposes and votes for its own value. *)
FastVote(a) ==
    \E m \in msgs, v \in Values :
        /\ m.type = "P2a"
        /\ m.val = Any
        /\ m.bal \in FastBallots
        /\ maxBallot[a] <= m.bal
        /\ maxVBallot[a] < m.bal          \* at most one vote per ballot
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.bal]
        /\ maxValue' = [maxValue EXCEPT ![a] = v]
        /\ proposed' = proposed \cup {v}
        /\ Send([type |-> "P2b", bal |-> m.bal, acc |-> a, val |-> v])
        /\ UNCHANGED decision

(* In a classic round, an acceptor votes for the coordinator's value. *)
ClassicVote(a) ==
    \E m \in msgs :
        /\ m.type = "P2a"
        /\ m.val \in Values
        /\ maxBallot[a] <= m.bal
        /\ maxVBallot[a] < m.bal
        /\ maxBallot' = [maxBallot EXCEPT ![a] = m.bal]
        /\ maxVBallot' = [maxVBallot EXCEPT ![a] = m.bal]
        /\ maxValue' = [maxValue EXCEPT ![a] = m.val]
        /\ Send([type |-> "P2b", bal |-> m.bal, acc |-> a, val |-> m.val])
        /\ UNCHANGED <<proposed, decision>>

VotedFor(a, b, v) ==
    \E m \in msgs : m.type = "P2b" /\ m.bal = b /\ m.acc = a /\ m.val = v

(* A fast quorum voted for the same value in a fast ballot. *)
FastDecide ==
    \E b \in FastBallots, R \in FastQuorums, v \in Values :
        /\ v \notin decision
        /\ \A a \in R : VotedFor(a, b, v)
        /\ decision' = decision \cup {v}
        /\ UNCHANGED <<msgs, maxBallot, maxVBallot, maxValue, proposed>>

(* A classic quorum voted for the same value in a classic ballot. *)
ClassicDecide ==
    \E b \in ClassicBallots, Q \in ClassicQuorums, v \in Values :
        /\ v \notin decision
        /\ \A a \in Q : VotedFor(a, b, v)
        /\ decision' = decision \cup {v}
        /\ UNCHANGED <<msgs, maxBallot, maxVBallot, maxValue, proposed>>

-----------------------------------------------------------------------------
(* Specification *)

Next ==
    \/ \E b \in Ballots : Phase1a(b)
    \/ \E a \in Replicas : Phase1b(a)
    \/ \E b \in Ballots : StartFastRound(b) \/ StartClassicRound(b)
    \/ \E a \in Replicas : FastVote(a) \/ ClassicVote(a)
    \/ FastDecide
    \/ ClassicDecide

Fairness ==
    /\ WF_vars(FastDecide)
    /\ WF_vars(ClassicDecide)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties *)

(* Agreement: at most one value is ever decided. *)
Agreement == \A v1, v2 \in decision : v1 = v2

(* Non-triviality: every decided value was proposed by an acceptor in a fast round. *)
NonTriviality ==
    \A v \in decision :
        \E m \in msgs : /\ m.type = "P2b"
                        /\ m.bal \in FastBallots
                        /\ m.val = v

(* Once a value is decided, the decision never changes. *)
DecisionStable == [][decision \subseteq decision']_vars

(* Liveness: whenever a decision condition is achievable, a decision is eventually reached. *)
Liveness ==
    (ENABLED FastDecide \/ ENABLED ClassicDecide) ~> (decision # {})

THEOREM Spec => [](TypeOK /\ Agreement /\ NonTriviality)
THEOREM Spec => DecisionStable
THEOREM Spec => Liveness
=============================================================================