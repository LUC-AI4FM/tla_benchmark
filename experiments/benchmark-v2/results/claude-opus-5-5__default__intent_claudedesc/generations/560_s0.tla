---------------------------- MODULE PaxosCommit ----------------------------
(***************************************************************************)
(* Paxos Commit: a fault-tolerant transaction commit protocol.  Each RM's  *)
(* vote (prepared / aborted) is decided by a separate instance of Paxos    *)
(* consensus.  The transaction commits iff every instance chooses          *)
(* "prepared", and aborts if any instance chooses "aborted".               *)
(*                                                                         *)
(* Simplifications: msgs is the set of all messages ever sent (no loss and *)
(* no explicit delivery).  Leader election is not modeled.  Prepare        *)
(* requests are not modeled.  Only safety properties are specified.        *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

Maximum(S) ==
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n >= m

CONSTANTS RM,        \* The set of resource managers
          Acceptor,  \* The set of acceptors
          Majority,  \* The set of quorums of acceptors
          Ballot     \* The set of ballot numbers

ASSUME
  /\ Ballot \subseteq Nat
  /\ 0 \in Ballot
  /\ Majority \subseteq SUBSET Acceptor
  /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}

Value == {"prepared", "aborted"}

Message ==
       [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}]
  \cup [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
        val : Value \cup {"none"}, acc : Acceptor]
  \cup [type : {"phase2a"}, ins : RM, bal : Ballot, val : Value]
  \cup [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,
        val : Value]
  \cup [type : {"Commit", "Abort"}]

VARIABLES rmState,  \* rmState[r] is the state of resource manager r
          aState,   \* aState[r][a] is the state of acceptor a in instance r
          msgs      \* The set of all messages ever sent

vars == <<rmState, aState, msgs>>

PCTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState \in [RM -> [Acceptor -> [mbal : Ballot,
                                     bal  : Ballot \cup {-1},
                                     val  : Value \cup {"none"}]]]
  /\ msgs \in SUBSET Message

PCInit ==
  /\ rmState = [r \in RM |-> "working"]
  /\ aState  = [r \in RM |->
                  [ac \in Acceptor |-> [mbal |-> 0, bal |-> -1, val |-> "none"]]]
  /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

---------------------------------------------------------------------------
(* Resource manager actions *)

RMPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "prepared"])
  /\ UNCHANGED aState

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

---------------------------------------------------------------------------
(* Leader actions *)

Phase1a(bal, r) ==
  /\ Send([type |-> "phase1a", ins |-> r, bal |-> bal])
  /\ UNCHANGED <<rmState, aState>>

Phase2a(bal, r) ==
  /\ ~\E m \in msgs : /\ m.type = "phase2a"
                      /\ m.bal = bal
                      /\ m.ins = r
  /\ \E MS \in Majority :
       LET mset == {m \in msgs : /\ m.type = "phase1b"
                                 /\ m.ins  = r
                                 /\ m.mbal = bal
                                 /\ m.acc  \in MS}
           maxbal == Maximum({m.bal : m \in mset})
           val == IF maxbal = -1
                    THEN "aborted"
                    ELSE (CHOOSE m \in mset : m.bal = maxbal).val
       IN  /\ \A ac \in MS : \E m \in mset : m.acc = ac
           /\ Send([type |-> "phase2a", ins |-> r, bal |-> bal, val |-> val])
  /\ UNCHANGED <<rmState, aState>>

Decided(r, v) ==
  \E b \in Ballot, MS \in Majority :
    \A ac \in MS : [type |-> "phase2b", ins |-> r, bal |-> b,
                    val |-> v, acc |-> ac] \in msgs

Decide ==
  /\ \/ /\ \A r \in RM : Decided(r, "prepared")
        /\ Send([type |-> "Commit"])
     \/ /\ \E r \in RM : Decided(r, "aborted")
        /\ Send([type |-> "Abort"])
  /\ UNCHANGED <<rmState, aState>>

---------------------------------------------------------------------------
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
       /\ aState[m.ins][acc].mbal <= m.bal
       /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal,
                                   ![m.ins][acc].bal  = m.bal,
                                   ![m.ins][acc].val  = m.val]
       /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal,
                val |-> m.val, acc |-> acc])
  /\ UNCHANGED rmState

---------------------------------------------------------------------------

PCNext ==
  \/ \E r \in RM : \/ RMPrepare(r)
                   \/ RMChooseToAbort(r)
                   \/ RMRcvCommitMsg(r)
                   \/ RMRcvAbortMsg(r)
  \/ \E bal \in Ballot \ {0}, r \in RM : Phase1a(bal, r) \/ Phase2a(bal, r)
  \/ Decide
  \/ \E acc \in Acceptor : Phase1b(acc) \/ Phase2b(acc)

Init == PCInit
Next == PCNext

PCSpec == PCInit /\ [][PCNext]_vars
Spec == PCSpec

---------------------------------------------------------------------------
(* Safety properties *)

TypeOK == PCTypeOK

\* Consistency: no RM commits while another aborts
TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

\* Validity: commit only if every RM actually prepared
CommitValidity ==
  /\ [type |-> "Commit"] \in msgs =>
        \A r \in RM : [type |-> "phase2a", ins |-> r, bal |-> 0,
                       val |-> "prepared"] \in msgs
  /\ \A r \in RM : rmState[r] = "committed" =>
        \A s \in RM : [type |-> "phase2a", ins |-> s, bal |-> 0,
                       val |-> "prepared"] \in msgs

\* Never both a Commit and an Abort decision
DecisionConsistency ==
  ~ ([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)

\* Paxos safety for each instance
VotedFor(r, a, b, v) ==
  [type |-> "phase2b", ins |-> r, bal |-> b, val |-> v, acc |-> a] \in msgs

ChosenIn(r, b, v) == \E MS \in Majority : \A a \in MS : VotedFor(r, a, b, v)

Chosen(r, v) == \E b \in Ballot : ChosenIn(r, b, v)

PaxosConsistency ==
  \A r \in RM : \A v1, v2 \in Value :
     (Chosen(r, v1) /\ Chosen(r, v2)) => v1 = v2

\* At most one phase2a message per instance and ballot
UniquePhase2a ==
  \A m1, m2 \in msgs :
     (/\ m1.type = "phase2a" /\ m2.type = "phase2a"
      /\ m1.ins = m2.ins /\ m1.bal = m2.bal) => m1 = m2

\* Every phase2b vote corresponds to a phase2a proposal
Phase2bValid ==
  \A m \in msgs :
     m.type = "phase2b" =>
        [type |-> "phase2a", ins |-> m.ins, bal |-> m.bal,
         val |-> m.val] \in msgs

\* Acceptor local state invariant
AcceptorStateOK ==
  \A r \in RM, a \in Acceptor :
     /\ aState[r][a].bal <= aState[r][a].mbal
     /\ (aState[r][a].bal = -1) <=> (aState[r][a].val = "none")

THEOREM Spec => [](TypeOK /\ TCConsistent /\ CommitValidity
                   /\ DecisionConsistency /\ PaxosConsistency
                   /\ UniquePhase2a /\ Phase2bValid /\ AcceptorStateOK)
=============================================================================