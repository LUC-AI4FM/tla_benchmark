------------------------------ MODULE PaxosCommitRM ------------------------------
(***************************************************************************)
(* A replicated commit protocol in which each resource manager (RM) has   *)
(* its own independent instance of Paxos.  That instance agrees on        *)
(* whether the RM's action is "prepared" or "aborted".  The results of    *)
(* all instances are then combined into a global Commit or Abort.         *)
(*                                                                         *)
(* Messages are records added to a global history set "msgs".  A message  *)
(* is never removed, so a message may be received at any later time, more *)
(* than once, or never.  This models delay and loss.  Each message is     *)
(* recorded only once because "msgs" is a set.                            *)
(*                                                                         *)
(* Leader election is not modelled.  Any process may start a ballot and   *)
(* may propose a value once it has enough phase 1b responses.             *)
(*                                                                         *)
(* Ballot 0 of instance r is reserved for RM r itself.  RM r proposes     *)
(* "prepared" or "aborted" there directly, with no phase 1, because no    *)
(* lower ballot exists.  Higher ballots are run by would-be leaders.      *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS RM,        \* The set of resource managers (one Paxos instance each)
          Acceptor,  \* The set of acceptors
          Majority,  \* The set of quorums of acceptors
          Ballot     \* The set of ballot numbers

ASSUME /\ Ballot \subseteq Nat
       /\ 0 \in Ballot
       /\ Majority \subseteq SUBSET Acceptor
       /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}

Values == {"prepared", "aborted"}

(***************************************************************************)
(* The set of all possible messages.                                       *)
(***************************************************************************)
Message ==
       [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}]
  \cup [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
        val : Values \cup {"none"}, acc : Acceptor]
  \cup [type : {"phase2a"}, ins : RM, bal : Ballot, val : Values]
  \cup [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,
        val : Values]
  \cup [type : {"Commit", "Abort"}]

VARIABLES rmState,  \* rmState[r] is the local state of RM r
          aState,   \* aState[r][a] is acceptor a's state for instance r
          msgs      \* The global history of every message ever sent

vars == <<rmState, aState, msgs>>

Send(m) == msgs' = msgs \cup {m}

Maximum(S) == IF S = {} THEN -1 ELSE CHOOSE n \in S : \A m \in S : n >= m

(***************************************************************************)
(* Value v has been chosen in instance r if a quorum of acceptors has     *)
(* accepted v in the same ballot.                                          *)
(***************************************************************************)
Chosen(r, v) ==
  \E b \in Ballot, MS \in Majority :
     \A ac \in MS : [type |-> "phase2b", acc |-> ac, ins |-> r,
                     bal |-> b, val |-> v] \in msgs

-----------------------------------------------------------------------------
TypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState  \in [RM -> [Acceptor -> [mbal : Ballot,
                                      bal  : Ballot \cup {-1},
                                      val  : Values \cup {"none"}]]]
  /\ msgs \subseteq Message

Init ==
  /\ rmState = [r \in RM |-> "working"]
  /\ aState  = [r \in RM |-> [ac \in Acceptor |->
                                 [mbal |-> 0, bal |-> -1, val |-> "none"]]]
  /\ msgs = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Resource manager actions                                                *)
(***************************************************************************)

(* RM r prepares locally and proposes "prepared" in ballot 0 of its own   *)
(* instance.                                                               *)
RMPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "prepared"])
  /\ UNCHANGED aState

(* RM r decides to abort locally and proposes "aborted" in ballot 0 of    *)
(* its own instance.                                                       *)
RMChooseToAbort(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "aborted"])
  /\ UNCHANGED aState

(* RM r learns the global Commit decision. *)
RMRcvCommitMsg(r) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState[r] # "aborted"
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<aState, msgs>>

(* RM r learns the global Abort decision. *)
RMRcvAbortMsg(r) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState[r] # "committed"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<aState, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Leader actions.  Any process may act as a leader.                       *)
(***************************************************************************)

(* A would-be leader starts ballot b > 0 of instance r. *)
Phase1a(b, r) ==
  /\ b \in Ballot \ {0}
  /\ Send([type |-> "phase1a", ins |-> r, bal |-> b])
  /\ UNCHANGED <<rmState, aState>>

(* A leader that has phase 1b messages for ballot b from a quorum        *)
(* proposes a value in ballot b of instance r.  It must propose the value *)
(* accepted in the highest ballot among those responses.  If the quorum   *)
(* reports no accepted value, it proposes "aborted".  At most one value   *)
(* is proposed per ballot.                                                 *)
Phase2a(b, r) ==
  /\ b \in Ballot \ {0}
  /\ ~ \E m \in msgs : /\ m.type = "phase2a"
                       /\ m.ins  = r
                       /\ m.bal  = b
  /\ \E MS \in Majority :
       LET mset   == {m \in msgs : /\ m.type = "phase1b"
                                   /\ m.ins  = r
                                   /\ m.mbal = b
                                   /\ m.acc  \in MS}
           maxbal == Maximum({m.bal : m \in mset})
           v      == IF maxbal = -1
                       THEN "aborted"
                       ELSE (CHOOSE m \in mset : m.bal = maxbal).val
       IN  /\ \A ac \in MS : \E m \in mset : m.acc = ac
           /\ Send([type |-> "phase2a", ins |-> r, bal |-> b, val |-> v])
  /\ UNCHANGED <<rmState, aState>>

(* Global decision: Commit only if every instance has chosen "prepared". *)
DecideCommit ==
  /\ \A r \in RM : Chosen(r, "prepared")
  /\ Send([type |-> "Commit"])
  /\ UNCHANGED <<rmState, aState>>

(* Global decision: Abort only if some instance has chosen "aborted". *)
DecideAbort ==
  /\ \E r \in RM : Chosen(r, "aborted")
  /\ Send([type |-> "Abort"])
  /\ UNCHANGED <<rmState, aState>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Acceptor actions                                                        *)
(***************************************************************************)

(* Acceptor ac answers a phase 1a message whose ballot is higher than any *)
(* ballot it has promised.  It promises that ballot and reports its last  *)
(* accepted ballot and value.                                             *)
Phase1b(ac) ==
  \E m \in msgs :
    /\ m.type = "phase1a"
    /\ aState[m.ins][ac].mbal < m.bal
    /\ aState' = [aState EXCEPT ![m.ins][ac].mbal = m.bal]
    /\ Send([type |-> "phase1b",
             ins  |-> m.ins,
             mbal |-> m.bal,
             bal  |-> aState[m.ins][ac].bal,
             val  |-> aState[m.ins][ac].val,
             acc  |-> ac])
    /\ UNCHANGED rmState

(* Acceptor ac accepts a phase 2a proposal if it has not promised a      *)
(* higher ballot.                                                          *)
Phase2b(ac) ==
  \E m \in msgs :
    /\ m.type = "phase2a"
    /\ aState[m.ins][ac].mbal \leq m.bal
    /\ aState' = [aState EXCEPT ![m.ins][ac].mbal = m.bal,
                                ![m.ins][ac].bal  = m.bal,
                                ![m.ins][ac].val  = m.val]
    /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal,
             val  |-> m.val, acc |-> ac])
    /\ UNCHANGED rmState

-----------------------------------------------------------------------------
Next ==
  \/ \E r \in RM :
        \/ RMPrepare(r)
        \/ RMChooseToAbort(r)
        \/ RMRcvCommitMsg(r)
        \/ RMRcvAbortMsg(r)
  \/ \E b \in Ballot \ {0}, r \in RM : Phase1a(b, r) \/ Phase2a(b, r)
  \/ DecideCommit
  \/ DecideAbort
  \/ \E ac \in Acceptor : Phase1b(ac) \/ Phase2b(ac)

(* Only safety properties are required, so no fairness is assumed. *)
Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

(* (1) In each instance, Paxos never chooses two different values. *)
PaxosConsistency ==
  \A r \in RM : \A v1, v2 \in Values :
     Chosen(r, v1) /\ Chosen(r, v2) => v1 = v2

(* (2) Commit is announced only if every instance has chosen "prepared". *)
CommitValidity ==
  [type |-> "Commit"] \in msgs => \A r \in RM : Chosen(r, "prepared")

(* (3) Abort is announced only if some instance has chosen "aborted". *)
AbortValidity ==
  [type |-> "Abort"] \in msgs => \E r \in RM : Chosen(r, "aborted")

(* The global decisions are mutually exclusive. *)
DecisionConsistency ==
  ~ ([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)

(* No RM is committed while another RM is aborted. *)
TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

(* (4) Once an RM is committed it stays committed. *)
(*     Once an RM is aborted it stays aborted.     *)
DecisionStable ==
  [][\A r \in RM :
       /\ (rmState[r] = "committed" => rmState'[r] = "committed")
       /\ (rmState[r] = "aborted"   => rmState'[r] = "aborted")]_vars

Inv ==
  /\ TypeOK
  /\ PaxosConsistency
  /\ CommitValidity
  /\ AbortValidity
  /\ DecisionConsistency
  /\ TCConsistent

THEOREM Spec => []Inv
THEOREM Spec => DecisionStable
=============================================================================