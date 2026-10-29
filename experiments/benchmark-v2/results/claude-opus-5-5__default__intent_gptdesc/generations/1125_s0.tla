------------------------------ MODULE PaxosCommit ------------------------------
(***************************************************************************)
(* Paxos Commit (Gray & Lamport).  One Paxos consensus instance per        *)
(* resource manager (RM) decides that RM's local vote, "prepared" or       *)
(* "aborted".  A separate decision step announces the global outcome:      *)
(* Commit if every instance has chosen "prepared", and Abort if some       *)
(* instance has chosen "aborted".                                          *)
(*                                                                         *)
(* Messages are never lost and, once sent, stay in the set msgs.  All      *)
(* participants are asynchronous.  Leaders are not modeled as processes:   *)
(* any phase-1a or phase-2a action may be taken at any time for any        *)
(* ballot.  This allows transient, concurrent, or competing leaders.       *)
(* Ballot 0 is reserved for the RMs, which send their own phase-2a         *)
(* messages in ballot 0.                                                   *)
(*                                                                         *)
(* No liveness is required, so Spec has no fairness conditions.            *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS RM,        \* The set of resource managers (one Paxos instance each)
          Acceptor,  \* The set of acceptors
          Majority,  \* The set of "majorities" (quorums) of acceptors
          Ballot     \* The set of ballot numbers

ASSUME PCAssumptions ==
  /\ Ballot \subseteq Nat
  /\ 0 \in Ballot
  /\ Majority \subseteq SUBSET Acceptor
  /\ \A MS \in Majority : MS # {}
  /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}

Values == {"prepared", "aborted"}

Message ==
       [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}]
  \cup [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
        val : Values \cup {"none"}, acc : Acceptor]
  \cup [type : {"phase2a"}, ins : RM, bal : Ballot, val : Values]
  \cup [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,
        val : Values]
  \cup [type : {"Commit", "Abort"}]

VARIABLES
  rmState,  \* rmState[r] is the state of resource manager r
  aState,   \* aState[ins][ac] is the state of acceptor ac in instance ins
  msgs      \* The set of all messages ever sent

vars == <<rmState, aState, msgs>>

Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE x \in S : \A y \in S : x >= y

-----------------------------------------------------------------------------
(* Type invariant *)
PCTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState  \in [RM -> [Acceptor -> [mbal : Ballot,
                                      bal  : Ballot \cup {-1},
                                      val  : Values \cup {"none"}]]]
  /\ msgs \subseteq Message

PCInit ==
  /\ rmState = [r \in RM |-> "working"]
  /\ aState  = [r \in RM |->
                  [ac \in Acceptor |-> [mbal |-> 0, bal |-> -1, val |-> "none"]]]
  /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
(* Resource manager actions *)

(* An RM explicitly prepares.  It acts as ballot-0 leader of its own *)
(* instance and proposes "prepared".                                  *)
RMPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "prepared"])
  /\ UNCHANGED aState

(* An RM spontaneously aborts and proposes "aborted" in ballot 0. *)
RMChooseToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "aborted"])
  /\ UNCHANGED aState

RMRcvCommitMsg(r) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<aState, msgs>>

RMRcvAbortMsg(r) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<aState, msgs>>

-----------------------------------------------------------------------------
(* Leader actions.  Any leader may act for any ballot at any time. *)

Phase1a(bal, r) ==
  /\ Send([type |-> "phase1a", ins |-> r, bal |-> bal])
  /\ UNCHANGED <<rmState, aState>>

(* The phase-2a value must be the value with the highest accepted ballot *)
(* among the phase-1b responses from a majority.  If that majority has   *)
(* accepted no value, the leader proposes "aborted" on the RM's behalf.  *)
(* At most one phase-2a message is sent per (instance, ballot).          *)
Phase2a(bal, r) ==
  /\ ~ \E m \in msgs : /\ m.type = "phase2a"
                       /\ m.bal  = bal
                       /\ m.ins  = r
  /\ \E MS \in Majority :
       LET mset   == {m \in msgs : /\ m.type = "phase1b"
                                   /\ m.ins  = r
                                   /\ m.mbal = bal
                                   /\ m.acc  \in MS}
           maxbal == Maximum({m.bal : m \in mset})
           val    == IF maxbal = -1
                       THEN "aborted"
                       ELSE (CHOOSE m \in mset : m.bal = maxbal).val
       IN  /\ \A ac \in MS : \E m \in mset : m.acc = ac
           /\ Send([type |-> "phase2a", ins |-> r, bal |-> bal, val |-> val])
  /\ UNCHANGED <<rmState, aState>>

(* Global decision: announced once phase-2b quorums are observed. *)
Decided(r, v) ==
  \E b \in Ballot, MS \in Majority :
    \A ac \in MS : [type |-> "phase2b", ins |-> r, bal |-> b,
                    val |-> v, acc |-> ac] \in msgs

PCDecide ==
  /\ \/ /\ \A r \in RM : Decided(r, "prepared")
        /\ Send([type |-> "Commit"])
     \/ /\ \E r \in RM : Decided(r, "aborted")
        /\ Send([type |-> "Abort"])
  /\ UNCHANGED <<rmState, aState>>

-----------------------------------------------------------------------------
(* Acceptor actions *)

Phase1b(acc) ==
  /\ \E m \in msgs :
       /\ m.type = "phase1a"
       /\ aState[m.ins][acc].mbal < m.bal
       /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal]
       /\ Send([type |-> "phase1b",
                ins  |-> m.ins,
                mbal |-> m.bal,
                bal  |-> aState[m.ins][acc].bal,
                val  |-> aState[m.ins][acc].val,
                acc  |-> acc])
  /\ UNCHANGED rmState

Phase2b(acc) ==
  /\ \E m \in msgs :
       /\ m.type = "phase2a"
       /\ aState[m.ins][acc].mbal =< m.bal
       /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal,
                                   ![m.ins][acc].bal  = m.bal,
                                   ![m.ins][acc].val  = m.val]
       /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal,
                val |-> m.val, acc |-> acc])
  /\ UNCHANGED rmState

-----------------------------------------------------------------------------
PCNext ==
  \/ \E r \in RM : \/ RMPrepare(r)
                   \/ RMChooseToAbort(r)
                   \/ RMRcvCommitMsg(r)
                   \/ RMRcvAbortMsg(r)
  \/ \E bal \in Ballot \ {0}, r \in RM : Phase1a(bal, r) \/ Phase2a(bal, r)
  \/ PCDecide
  \/ \E acc \in Acceptor : Phase1b(acc) \/ Phase2b(acc)

Init == PCInit
Next == PCNext

(* Safety only: no fairness or liveness is required. *)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

Chosen(r, v) == Decided(r, v)

(* Agreement: no RM has committed while another has aborted. *)
TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

(* Commit and Abort are never both announced. *)
NoConflictingAnnouncements ==
  ~ ( [type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs )

(* Consensus safety per instance: no instance chooses two different values. *)
InstanceConsensus ==
  \A r \in RM : ~ (Chosen(r, "prepared") /\ Chosen(r, "aborted"))

(* Validity: every chosen value is a legal vote.  "prepared" can be     *)
(* chosen only if RM r itself proposed it, because only RMs propose     *)
(* "prepared" from scratch.  "aborted" is either proposed by the RM or  *)
(* proposed by a leader on the RM's behalf when no value was accepted.  *)
Validity ==
  \A r \in RM, v \in Values :
    Chosen(r, v) =>
      \/ [type |-> "phase2a", ins |-> r, bal |-> 0, val |-> v] \in msgs
      \/ /\ v = "aborted"
         /\ \E m \in msgs : /\ m.type = "phase2a"
                            /\ m.ins  = r
                            /\ m.val  = "aborted"

(* "prepared" is chosen only if RM r actually prepared. *)
PreparedValidity ==
  \A r \in RM :
    Chosen(r, "prepared") =>
      [type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "prepared"] \in msgs

(* Consistency of the global decision. *)
GlobalDecisionConsistent ==
  /\ [type |-> "Commit"] \in msgs => \A r \in RM : Chosen(r, "prepared")
  /\ [type |-> "Abort"]  \in msgs => \E r \in RM : Chosen(r, "aborted")
  /\ (\E r \in RM : Chosen(r, "aborted")) => [type |-> "Commit"] \notin msgs

(* RM final states agree with the announcements. *)
RMStateMatchesDecision ==
  \A r \in RM :
    /\ rmState[r] = "committed" => [type |-> "Commit"] \in msgs
    /\ (rmState[r] = "aborted" /\ [type |-> "Commit"] \in msgs) => FALSE

(* Acceptor state invariants *)
AcceptorStateOK ==
  \A r \in RM, ac \in Acceptor :
    /\ aState[r][ac].bal =< aState[r][ac].mbal
    /\ (aState[r][ac].bal = -1) <=> (aState[r][ac].val = "none")

Invariants ==
  /\ PCTypeOK
  /\ TCConsistent
  /\ NoConflictingAnnouncements
  /\ InstanceConsensus
  /\ Validity
  /\ PreparedValidity
  /\ GlobalDecisionConsistent
  /\ RMStateMatchesDecision
  /\ AcceptorStateOK

THEOREM Spec => []Invariants
=============================================================================