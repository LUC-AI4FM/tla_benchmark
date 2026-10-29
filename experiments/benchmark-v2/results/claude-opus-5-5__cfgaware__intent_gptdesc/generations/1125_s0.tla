---------------------------- MODULE PaxosCommit ----------------------------
EXTENDS Integers

Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S : \A m \in S : n >= m

CONSTANTS RM, Acceptor, Majority, Ballot

ASSUME /\ Ballot \subseteq Nat
       /\ 0 \in Ballot
       /\ Majority \subseteq SUBSET Acceptor
       /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}

Message ==
       [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}]
  \cup [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
        val : {"prepared", "aborted", "none"}, acc : Acceptor]
  \cup [type : {"phase2a"}, ins : RM, bal : Ballot, val : {"prepared", "aborted"}]
  \cup [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,
        val : {"prepared", "aborted"}]
  \cup [type : {"Commit", "Abort"}]

VARIABLES rmState, aState, msgs

vars == <<rmState, aState, msgs>>

PCTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState \in [RM -> [Acceptor -> [mbal : Ballot,
                                     bal  : Ballot \cup {-1},
                                     val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \subseteq Message

PCInit ==
  /\ rmState = [r \in RM |-> "working"]
  /\ aState = [r \in RM |->
                 [ac \in Acceptor |-> [mbal |-> 0, bal |-> -1, val |-> "none"]]]
  /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
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

-----------------------------------------------------------------------------
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
                                  /\ m.ins = r
                                  /\ m.mbal = bal
                                  /\ m.acc \in MS}
            maxbal == Maximum({m.bal : m \in mset})
            val == IF maxbal = -1
                     THEN "aborted"
                     ELSE (CHOOSE m \in mset : m.bal = maxbal).val
        IN  /\ \A ac \in MS : \E m \in mset : m.acc = ac
            /\ Send([type |-> "phase2a", ins |-> r, bal |-> bal, val |-> val])
  /\ UNCHANGED <<rmState, aState>>

Chosen(r, v) ==
  \E b \in Ballot, MS \in Majority :
    \A ac \in MS : [type |-> "phase2b", ins |-> r, bal |-> b,
                    val |-> v, acc |-> ac] \in msgs

PCDecide ==
  /\ \/ /\ \A r \in RM : Chosen(r, "prepared")
        /\ Send([type |-> "Commit"])
     \/ /\ \E r \in RM : Chosen(r, "aborted")
        /\ Send([type |-> "Abort"])
  /\ UNCHANGED <<rmState, aState>>

-----------------------------------------------------------------------------
(* Acceptor actions *)

Phase1b(ac) ==
  /\ \E m \in msgs :
       /\ m.type = "phase1a"
       /\ aState[m.ins][ac].mbal < m.bal
       /\ aState' = [aState EXCEPT ![m.ins][ac].mbal = m.bal]
       /\ Send([type |-> "phase1b", ins |-> m.ins, mbal |-> m.bal,
                bal |-> aState[m.ins][ac].bal,
                val |-> aState[m.ins][ac].val, acc |-> ac])
  /\ UNCHANGED rmState

Phase2b(ac) ==
  /\ \E m \in msgs :
       /\ m.type = "phase2a"
       /\ aState[m.ins][ac].mbal =< m.bal
       /\ aState' = [aState EXCEPT ![m.ins][ac].mbal = m.bal,
                                   ![m.ins][ac].bal  = m.bal,
                                   ![m.ins][ac].val  = m.val]
       /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal,
                val |-> m.val, acc |-> ac])
  /\ UNCHANGED rmState

-----------------------------------------------------------------------------

PCNext ==
  \/ \E r \in RM : \/ RMPrepare(r)
                   \/ RMChooseToAbort(r)
                   \/ RMRcvCommitMsg(r)
                   \/ RMRcvAbortMsg(r)
  \/ \E bal \in Ballot \ {0}, r \in RM : Phase1a(bal, r) \/ Phase2a(bal, r)
  \/ PCDecide
  \/ \E ac \in Acceptor : Phase1b(ac) \/ Phase2b(ac)

PCSpec == PCInit /\ [][PCNext]_vars

-----------------------------------------------------------------------------
(* Safety properties *)

PCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

NoCommitAndAbort ==
  ~ ([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)

ConsensusSafety ==
  \A r \in RM : ~ (Chosen(r, "prepared") /\ Chosen(r, "aborted"))

Validity ==
  \A r \in RM :
    Chosen(r, "prepared") =>
      [type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "prepared"] \in msgs

DecisionConsistency ==
  /\ [type |-> "Commit"] \in msgs => \A r \in RM : Chosen(r, "prepared")
  /\ (\E r \in RM : Chosen(r, "aborted")) => [type |-> "Commit"] \notin msgs

PCSafety ==
  /\ PCTypeOK
  /\ PCConsistent
  /\ NoCommitAndAbort
  /\ ConsensusSafety
  /\ Validity
  /\ DecisionConsistency

THEOREM PCSpec => [](PCTypeOK /\ PCConsistent)
=============================================================================