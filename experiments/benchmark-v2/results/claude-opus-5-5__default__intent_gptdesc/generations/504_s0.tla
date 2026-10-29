------------------------------- MODULE StableLeaderPaxos -------------------------------
(***************************************************************************)
(* Single-decree (Basic) Paxos with a single, stable, distinguished leader *)
(* that is the only proposer issuing numbered ballots.  No leader election *)
(* is modelled.  Communication is asynchronous: messages are kept in a     *)
(* set, so they may be delayed, reordered or received more than once, but  *)
(* they are never corrupted.                                               *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS
    Acceptors,   \* the set of acceptors
    Values,      \* the finite set of values that may be chosen
    Quorums,     \* the set of quorums (sets of acceptors)
    MaxBallot    \* bound on ballot numbers (for finite model checking)

ASSUME QuorumAssumption ==
    /\ Quorums \subseteq SUBSET Acceptors
    /\ Quorums # {}
    /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

ASSUME BallotAssumption == MaxBallot \in Nat

Ballots == 0..MaxBallot

None == CHOOSE x : x \notin Values

Messages ==
         [type : {"1a"}, bal : Ballots]
    \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
          mbal : Ballots \cup {-1}, mval : Values \cup {None}]
    \cup [type : {"2a"}, bal : Ballots, val : Values]
    \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES
    maxBal,     \* maxBal[a]: highest ballot acceptor a has promised (or accepted)
    maxVBal,    \* maxVBal[a]: ballot of the highest-numbered proposal accepted by a
    maxVal,     \* maxVal[a]: value of that proposal
    votes,      \* votes[a]: history of all proposals <<b, v>> ever accepted by a
    msgs,       \* set of all messages sent so far
    leaderBal,  \* current ballot of the leader (-1 if none started yet)
    leaderVal,  \* value proposed by the leader in leaderBal (None if not yet)
    proposed    \* history of all proposals <<b, v>> issued by the leader

vars == <<maxBal, maxVBal, maxVal, votes, msgs, leaderBal, leaderVal, proposed>>

Send(m) == msgs' = msgs \cup {m}

TypeOK ==
    /\ maxBal    \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVBal   \in [Acceptors -> Ballots \cup {-1}]
    /\ maxVal    \in [Acceptors -> Values \cup {None}]
    /\ votes     \in [Acceptors -> SUBSET (Ballots \X Values)]
    /\ msgs      \subseteq Messages
    /\ leaderBal \in Ballots \cup {-1}
    /\ leaderVal \in Values \cup {None}
    /\ proposed  \subseteq Ballots \X Values

Init ==
    /\ maxBal    = [a \in Acceptors |-> -1]
    /\ maxVBal   = [a \in Acceptors |-> -1]
    /\ maxVal    = [a \in Acceptors |-> None]
    /\ votes     = [a \in Acceptors |-> {}]
    /\ msgs      = {}
    /\ leaderBal = -1
    /\ leaderVal = None
    /\ proposed  = {}

(***************************************************************************)
(* Phase 1a: the leader starts a new, higher-numbered ballot by sending    *)
(* prepare requests to the acceptors.                                      *)
(***************************************************************************)
Prepare(b) ==
    /\ b > leaderBal
    /\ leaderBal' = b
    /\ leaderVal' = None
    /\ Send([type |-> "1a", bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, proposed>>

(***************************************************************************)
(* Phase 1b: an acceptor receiving a prepare request for a ballot higher   *)
(* than any it has promised promises not to accept lower ballots and       *)
(* reports its highest-numbered accepted proposal (if any).                *)
(***************************************************************************)
Promise(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
                 mbal |-> maxVBal[a], mval |-> maxVal[a]])
        /\ UNCHANGED <<maxVBal, maxVal, votes, leaderBal, leaderVal, proposed>>

(***************************************************************************)
(* Phase 2a: once the leader has promises for its current ballot from a    *)
(* quorum, it picks the value of the highest-numbered accepted proposal    *)
(* reported, or any allowed value if none was reported, and sends accept   *)
(* requests.  At most one value is proposed per ballot.                    *)
(***************************************************************************)
Phase2a(b, v) ==
    /\ b \in Ballots
    /\ leaderBal = b
    /\ leaderVal = None
    /\ \E Q \in Quorums :
         LET Q1b  == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
             Q1bv == {m \in Q1b : m.mbal >= 0}
         IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
             /\ \/ /\ Q1bv = {}
                   /\ v \in Values
                \/ \E m \in Q1bv :
                     /\ m.mval = v
                     /\ \A mm \in Q1bv : m.mbal >= mm.mbal
    /\ leaderVal' = v
    /\ proposed'  = proposed \cup {<<b, v>>}
    /\ Send([type |-> "2a", bal |-> b, val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, votes, leaderBal>>

(***************************************************************************)
(* Phase 2b: an acceptor accepts an accept request unless it has promised  *)
(* a higher ballot, updating its promise and accepted proposal.            *)
(***************************************************************************)
Accepted(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]
        /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a] = m.bal]
        /\ maxVal'  = [maxVal  EXCEPT ![a] = m.val]
        /\ votes'   = [votes   EXCEPT ![a] = @ \cup {<<m.bal, m.val>>}]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])
        /\ UNCHANGED <<leaderBal, leaderVal, proposed>>

LeaderStep == \E b \in Ballots : Prepare(b)
LeaderPropose == \E v \in Values : Phase2a(leaderBal, v)

Next ==
    \/ LeaderStep
    \/ LeaderPropose
    \/ \E a \in Acceptors : Promise(a) \/ Accepted(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
AcceptedAt(a, b, v) == <<b, v>> \in votes[a]

ChosenAt(b, v) == \E Q \in Quorums : \A a \in Q : AcceptedAt(a, b, v)

Chosen(v) == \E b \in Ballots : ChosenAt(b, v)

\* (1) Agreement: no two different values are ever chosen.
Agreement == \A v, w \in Values : Chosen(v) /\ Chosen(w) => v = w

\* (1') Temporal form: once a value is chosen, no different value ever becomes chosen.
AgreementTemporal ==
    \A v \in Values : [](Chosen(v) => [](\A w \in Values : Chosen(w) => w = v))

\* (2) Integrity: only allowed values are chosen, and only if they were proposed.
Integrity ==
    \A v \in Values \cup {None} :
        Chosen(v) => /\ v \in Values
                     /\ \E b \in Ballots : <<b, v>> \in proposed

\* (3) Non-contradiction: no two different values accepted for the same ballot
\*     (neither by one acceptor nor across acceptors).
NonContradiction ==
    \A a1, a2 \in Acceptors, b \in Ballots, v, w \in Values :
        AcceptedAt(a1, b, v) /\ AcceptedAt(a2, b, w) => v = w

\* Auxiliary consistency: each acceptor's current accepted proposal is in its history
\* and its promise is never below its accepted ballot.
AcceptorConsistency ==
    \A a \in Acceptors :
        /\ maxVBal[a] <= maxBal[a]
        /\ (maxVBal[a] = -1) <=> (maxVal[a] = None)
        /\ maxVBal[a] >= 0 => <<maxVBal[a], maxVal[a]>> \in votes[a]

SafetyInvariant ==
    /\ TypeOK
    /\ Agreement
    /\ Integrity
    /\ NonContradiction
    /\ AcceptorConsistency

THEOREM Spec => []SafetyInvariant

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness (stated separately from safety).                               *)
(* Assumptions: messages are never lost (msgs only grows) and eventually   *)
(* processed (weak fairness on acceptor receive actions); the leader is    *)
(* stable and eventually proceeds with its ballot; since ballots are       *)
(* bounded by MaxBallot, the leader eventually stops starting new ballots. *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(LeaderStep)
    /\ WF_vars(LeaderPropose)
    /\ \A a \in Acceptors : WF_vars(Promise(a)) /\ WF_vars(Accepted(a))

LiveSpec == Spec /\ Fairness

EventuallyChosen == <>(\E v \in Values : Chosen(v))

ChosenStable == \A v \in Values : [](Chosen(v) => []Chosen(v))

THEOREM LiveSpec => EventuallyChosen
=============================================================================