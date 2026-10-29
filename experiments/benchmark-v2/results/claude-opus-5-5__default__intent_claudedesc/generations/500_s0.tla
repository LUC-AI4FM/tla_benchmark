------------------------------ MODULE MultiPaxos ------------------------------
(***************************************************************************)
(* Multi-Decree (Multi-) Paxos consensus.                                 *)
(*                                                                         *)
(* Proposers, acceptors and learners agree on a sequence of values, one   *)
(* per slot. Phase 1 (prepare/promise) is aggregated across all slots:    *)
(* one 1a/1b exchange for a ballot gives a proposer the right to run      *)
(* Phase 2 (accept) for any number of slots in that ballot. Messages are  *)
(* kept in a shared, monotonically growing pool. This models an           *)
(* asynchronous network with reliable but arbitrarily delayed delivery,   *)
(* duplication and reordering. An acceptor that is unresponsive simply    *)
(* takes no steps.                                                        *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Proposers,   \* set of proposers
          Acceptors,   \* set of acceptors
          Learners,    \* set of learners
          Values,      \* set of values that may be proposed
          Ballots,     \* set of ballot numbers (a subset of Nat)
          Slots,       \* set of slots / instances / decrees
          Quorums      \* set of quorums (subsets of Acceptors)

ASSUME /\ Ballots \subseteq Nat
       /\ Quorums \subseteq SUBSET Acceptors
       /\ Quorums # {}
       /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values

NoBallot == -1   \* "has never voted"; it is smaller than every ballot

VARIABLES
    maxBal,    \* maxBal[a]    : highest ballot acceptor a has promised (over all slots)
    maxVBal,   \* maxVBal[a][s]: highest ballot in which a voted for slot s
    maxVal,    \* maxVal[a][s] : value a voted for in maxVBal[a][s]
    msgs,      \* the pool of all messages ever sent
    learned    \* learned[l][s]: value learner l has learned for slot s, or None

vars == <<maxBal, maxVBal, maxVal, msgs, learned>>

-----------------------------------------------------------------------------
(* Message types *)

Vote == [vbal : Ballots \cup {NoBallot}, val : Values \cup {None}]

Message ==
       [type : {"1a"}, from : Proposers, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots, votes : [Slots -> Vote]]
  \cup [type : {"2a"}, from : Proposers, bal : Ballots, slot : Slots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, slot : Slots, val : Values]

TypeOK ==
    /\ maxBal  \in [Acceptors -> Ballots \cup {NoBallot}]
    /\ maxVBal \in [Acceptors -> [Slots -> Ballots \cup {NoBallot}]]
    /\ maxVal  \in [Acceptors -> [Slots -> Values \cup {None}]]
    /\ msgs    \subseteq Message
    /\ learned \in [Learners -> [Slots -> Values \cup {None}]]

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
Init ==
    /\ maxBal  = [a \in Acceptors |-> NoBallot]
    /\ maxVBal = [a \in Acceptors |-> [s \in Slots |-> NoBallot]]
    /\ maxVal  = [a \in Acceptors |-> [s \in Slots |-> None]]
    /\ msgs    = {}
    /\ learned = [l \in Learners |-> [s \in Slots |-> None]]

-----------------------------------------------------------------------------
(* Phase 1a: proposer p starts ballot b. The prepare covers all slots.    *)
Phase1a(p, b) ==
    /\ Send([type |-> "1a", from |-> p, bal |-> b])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, learned>>

(* Phase 1b: acceptor a promises ballot m.bal for all slots. It reports  *)
(* its latest vote in every slot.                                         *)
Phase1b(a) ==
    \E m \in msgs :
        /\ m.type = "1a"
        /\ m.bal > maxBal[a]
        /\ maxBal' = [maxBal EXCEPT ![a] = m.bal]
        /\ Send([type  |-> "1b",
                 acc   |-> a,
                 bal   |-> m.bal,
                 votes |-> [s \in Slots |->
                              [vbal |-> maxVBal[a][s], val |-> maxVal[a][s]]]])
        /\ UNCHANGED <<maxVBal, maxVal, learned>>

(* Value v is safe to propose in slot s of ballot b, given 1b messages   *)
(* Q1b from quorum Q.                                                     *)
SafeValue(Q1b, b, s, v) ==
    \/ \A m \in Q1b : m.votes[s].vbal = NoBallot
    \/ \E c \in Ballots :
          /\ c < b
          /\ \A m \in Q1b : m.votes[s].vbal <= c
          /\ \E m \in Q1b : /\ m.votes[s].vbal = c
                            /\ m.votes[s].val  = v

(* Phase 1 is complete for ballot b when a quorum of promises exists.    *)
(* That single phase 1 lets the proposer issue 2a messages for any slot.  *)
(* At most one value is proposed per (ballot, slot).                      *)
Phase2a(p, b, s) ==
    /\ \E m \in msgs : m.type = "1a" /\ m.bal = b /\ m.from = p
    /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b /\ m.slot = s
    /\ \E Q \in Quorums, v \in Values :
          LET Q1b == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}
          IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
              /\ SafeValue(Q1b, b, s, v)
              /\ Send([type |-> "2a", from |-> p, bal |-> b,
                       slot |-> s, val |-> v])
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, learned>>

(* Phase 2b: acceptor a votes for a 2a message whose ballot is at least  *)
(* its promise.                                                            *)
Phase2b(a) ==
    \E m \in msgs :
        /\ m.type = "2a"
        /\ m.bal >= maxBal[a]
        /\ maxBal'  = [maxBal  EXCEPT ![a] = m.bal]
        /\ maxVBal' = [maxVBal EXCEPT ![a][m.slot] = m.bal]
        /\ maxVal'  = [maxVal  EXCEPT ![a][m.slot] = m.val]
        /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal,
                 slot |-> m.slot, val |-> m.val])
        /\ UNCHANGED learned

(* Chosen: a quorum voted for v in the same ballot b for slot s.          *)
ChosenIn(s, b, v) ==
    \E Q \in Quorums :
        \A a \in Q :
            [type |-> "2b", acc |-> a, bal |-> b, slot |-> s, val |-> v] \in msgs

Chosen(s, v) == \E b \in Ballots : ChosenIn(s, b, v)

(* Learner l learns the value of slot s once it observes a quorum of     *)
(* matching 2b messages.                                                   *)
Learn(l, s) ==
    /\ learned[l][s] = None
    /\ \E v \in Values :
          /\ Chosen(s, v)
          /\ learned' = [learned EXCEPT ![l][s] = v]
    /\ UNCHANGED <<maxBal, maxVBal, maxVal, msgs>>

-----------------------------------------------------------------------------
Next ==
    \/ \E p \in Proposers, b \in Ballots : Phase1a(p, b)
    \/ \E p \in Proposers, b \in Ballots, s \in Slots : Phase2a(p, b, s)
    \/ \E a \in Acceptors : Phase1b(a) \/ Phase2b(a)
    \/ \E l \in Learners, s \in Slots : Learn(l, s)

Spec == Init /\ [][Next]_vars

(* Optional fairness: acceptors and learners eventually process messages *)
(* that are enabled. This models reliable delivery. Paxos does not       *)
(* guarantee progress with competing proposers (FLP), so this spec makes *)
(* no liveness claim beyond this fairness assumption.                    *)
FairSpec ==
    /\ Spec
    /\ \A a \in Acceptors : WF_vars(Phase1b(a)) /\ WF_vars(Phase2b(a))
    /\ \A l \in Learners, s \in Slots : WF_vars(Learn(l, s))

-----------------------------------------------------------------------------
(* Safety properties *)

(* Agreement: for each slot, at most one value is chosen. *)
Agreement ==
    \A s \in Slots : \A v1, v2 \in Values :
        (Chosen(s, v1) /\ Chosen(s, v2)) => v1 = v2

(* Learners never disagree about the value of a slot. *)
LearnerAgreement ==
    \A l1, l2 \in Learners, s \in Slots :
        (learned[l1][s] # None /\ learned[l2][s] # None)
            => learned[l1][s] = learned[l2][s]

(* Anything learned was actually chosen. *)
LearnedIsChosen ==
    \A l \in Learners, s \in Slots :
        learned[l][s] # None => Chosen(s, learned[l][s])

(* Validity: only proposed values can be chosen or learned. *)
Proposed(s, v) == \E m \in msgs : m.type = "2a" /\ m.slot = s /\ m.val = v

Validity ==
    /\ \A s \in Slots, v \in Values : Chosen(s, v) => Proposed(s, v)
    /\ \A l \in Learners, s \in Slots :
          learned[l][s] # None => Proposed(s, learned[l][s])

(* Each (ballot, slot) carries at most one proposed value. *)
OneValuePerBallotSlot ==
    \A m1, m2 \in msgs :
        (/\ m1.type = "2a" /\ m2.type = "2a"
         /\ m1.bal = m2.bal /\ m1.slot = m2.slot) => m1.val = m2.val

(* Consistency across slots: every slot independently has at most one   *)
(* chosen value, so the chosen log is a well-defined partial function.  *)
ChosenLogConsistent ==
    \A s \in Slots : Cardinality({v \in Values : Chosen(s, v)}) <= 1

(* Acceptor state is consistent with the votes it has sent. *)
AcceptorConsistent ==
    \A a \in Acceptors, s \in Slots :
        /\ maxVBal[a][s] <= maxBal[a]
        /\ (maxVBal[a][s] = NoBallot) <=> (maxVal[a][s] = None)
        /\ maxVBal[a][s] # NoBallot =>
              [type |-> "2b", acc |-> a, bal |-> maxVBal[a][s],
               slot |-> s, val |-> maxVal[a][s]] \in msgs

THEOREM Spec => [](TypeOK /\ Agreement /\ LearnerAgreement /\ LearnedIsChosen
                   /\ Validity /\ OneValuePerBallotSlot /\ ChosenLogConsistent
                   /\ AcceptorConsistent)
=============================================================================