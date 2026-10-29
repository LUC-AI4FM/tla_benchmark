------------------------------ MODULE PaxosCommit ------------------------------
(***************************************************************************)
(* Paxos Commit: a transaction commit protocol that runs a separate        *)
(* instance of Paxos consensus for each resource manager (RM) to agree on  *)
(* whether that RM prepared or aborted.  The transaction commits iff every  *)
(* RM's instance chooses "prepared".  It aborts iff some RM's instance      *)
(* chooses "aborted".  Messages are modeled as a set of all sent messages.  *)
(* Leader election is not modeled: any process may act as a leader.        *)
(* Only safety is specified.                                               *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS RM,        \* The set of resource managers
          Acceptor,  \* The set of acceptors
          Majority,  \* The set of "majorities" of acceptors
          Ballot     \* The set of ballot numbers

ASSUME
  /\ Ballot \subseteq Nat
  /\ 0 \in Ballot
  /\ Majority \subseteq SUBSET Acceptor
  /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}

(***************************************************************************)
(* The set of all possible messages.                                        *)
(***************************************************************************)
Messages ==
       [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}]
  \cup [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
        val : {"prepared", "aborted", "none"}, acc : Acceptor]
  \cup [type : {"phase2a"}, ins : RM, bal : Ballot,
        val : {"prepared", "aborted"}]
  \cup [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,
        val : {"prepared", "aborted"}]
  \cup [type : {"Commit", "Abort"}]

VARIABLES rmState,  \* rmState[rm] is the state of resource manager rm
          aState,   \* aState[ins][ac] is the state of acceptor ac in instance ins
          msgs      \* The set of all messages ever sent

vars == <<rmState, aState, msgs>>

PCTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState  \in [RM -> [Acceptor -> [mbal : Ballot,
                                      bal  : Ballot \cup {-1},
                                      val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \subseteq Messages

Send(m) == msgs' = msgs \cup {m}

Maximum(S) ==
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n >= m

-----------------------------------------------------------------------------
PCInit ==
  /\ rmState = [rm \in RM |-> "working"]
  /\ aState  = [ins \in RM |->
                  [ac \in Acceptor |-> [mbal |-> 0, bal |-> -1, val |-> "none"]]]
  /\ msgs = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(*                        Resource manager actions                          *)
(***************************************************************************)
RMPrepare(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  /\ Send([type |-> "phase2a", ins |-> rm, bal |-> 0, val |-> "prepared"])
  /\ UNCHANGED aState

RMChooseToAbort(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ Send([type |-> "phase2a", ins |-> rm, bal |-> 0, val |-> "aborted"])
  /\ UNCHANGED aState

RMRcvCommitMsg(rm) ==
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  /\ UNCHANGED <<aState, msgs>>

RMRcvAbortMsg(rm) ==
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
  /\ UNCHANGED <<aState, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(*                              Leader actions                              *)
(***************************************************************************)
Phase1a(bal, rm) ==
  /\ Send([type |-> "phase1a", ins |-> rm, bal |-> bal])
  /\ UNCHANGED <<rmState, aState>>

Phase2a(bal, rm) ==
  /\ ~ \E m \in msgs : /\ m.type = "phase2a"
                       /\ m.bal = bal
                       /\ m.ins = rm
  /\ \E MS \in Majority :
       LET mset == {m \in msgs : /\ m.type = "phase1b"
                                 /\ m.ins  = rm
                                 /\ m.mbal = bal
                                 /\ m.acc \in MS}
           maxbal == Maximum({m.bal : m \in mset})
           val == IF maxbal = -1
                    THEN "aborted"
                    ELSE (CHOOSE m \in mset : m.bal = maxbal).val
       IN  /\ \A ac \in MS : \E m \in mset : m.acc = ac
           /\ Send([type |-> "phase2a", ins |-> rm, bal |-> bal, val |-> val])
  /\ UNCHANGED <<rmState, aState>>

Decided(rm, v) ==
  \E b \in Ballot, MS \in Majority :
    \A ac \in MS : [type |-> "phase2b", ins |-> rm, bal |-> b,
                    val |-> v, acc |-> ac] \in msgs

PCDecide ==
  /\ \/ /\ \A rm \in RM : Decided(rm, "prepared")
        /\ Send([type |-> "Commit"])
     \/ /\ \E rm \in RM : Decided(rm, "aborted")
        /\ Send([type |-> "Abort"])
  /\ UNCHANGED <<rmState, aState>>

-----------------------------------------------------------------------------
(***************************************************************************)
(*                             Acceptor actions                             *)
(***************************************************************************)
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
  \/ \E rm \in RM : \/ RMPrepare(rm)
                    \/ RMChooseToAbort(rm)
                    \/ RMRcvCommitMsg(rm)
                    \/ RMRcvAbortMsg(rm)
  \/ \E bal \in Ballot \ {0}, rm \in RM : Phase1a(bal, rm) \/ Phase2a(bal, rm)
  \/ PCDecide
  \/ \E acc \in Acceptor : Phase1b(acc) \/ Phase2b(acc)

PCSpec == PCInit /\ [][PCNext]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(*                          Safety properties                               *)
(***************************************************************************)

\* Consistency: never both a commit and an abort decision.
DecisionConsistent ==
  ~ ( [type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs )

\* Agreement: no RM commits while another aborts.
TCConsistent ==
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

\* Validity (commit): commit only if every RM prepared.
CommitValidity ==
  [type |-> "Commit"] \in msgs =>
     \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

\* Validity (abort): abort only if it was possible for some RM to abort,
\* i.e. some instance had "aborted" proposed.
AbortValidity ==
  [type |-> "Abort"] \in msgs =>
     \E rm \in RM : \E m \in msgs : /\ m.type = "phase2a"
                                    /\ m.ins = rm
                                    /\ m.val = "aborted"

\* Paxos-level consistency: each instance chooses at most one value.
InstanceConsistent ==
  \A rm \in RM : ~ (Decided(rm, "prepared") /\ Decided(rm, "aborted"))

Invariants ==
  /\ PCTypeOK
  /\ DecisionConsistent
  /\ TCConsistent
  /\ CommitValidity
  /\ AbortValidity
  /\ InstanceConsistent

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement: the basic Transaction Commit (TCommit) specification,       *)
(* stated over rmState, which is implemented by PCSpec.                    *)
(***************************************************************************)
TCInit == rmState = [rm \in RM |-> "working"]

canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

notCommitted == \A rm \in RM : rmState[rm] # "committed"

TCPrepare(rm) ==
  /\ rmState[rm] = "working"
  /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

TCDecide(rm) ==
  \/ /\ rmState[rm] = "prepared"
     /\ canCommit
     /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
  \/ /\ rmState[rm] \in {"working", "prepared"}
     /\ notCommitted
     /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]

TCNext == \E rm \in RM : TCPrepare(rm) \/ TCDecide(rm)

TCSpec == TCInit /\ [][TCNext]_rmState

THEOREM PCSpec => [](PCTypeOK /\ TCConsistent /\ DecisionConsistent)

THEOREM PCSpec => TCSpec
=============================================================================