---------------------------- MODULE MCPaxosCommit ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS r1, r2, a1, a2, a3

RM == {r1, r2}

Acceptor == {a1, a2, a3}

Majority == {{a1, a2}, {a1, a3}, {a2, a3}}

Ballot == {0, 1}

ASSUME /\ Ballot \subseteq Nat
       /\ 0 \in Ballot
       /\ Majority \subseteq SUBSET Acceptor
       /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}

VARIABLES rmState, aState, msgs

vars == <<rmState, aState, msgs>>

Maximum(S) == IF S = {} THEN -1
                        ELSE CHOOSE n \in S : \A m \in S : n >= m

Messages ==
       [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}]
  \cup [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
        val : {"prepared", "aborted", "none"}, acc : Acceptor]
  \cup [type : {"phase2a"}, ins : RM, bal : Ballot, val : {"prepared", "aborted"}]
  \cup [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,
        val : {"prepared", "aborted"}]
  \cup [type : {"Commit", "Abort"}]

PCTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState \in [RM -> [Acceptor -> [mbal : Ballot,
                                     bal  : Ballot \cup {-1},
                                     val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \in SUBSET Messages

PCInit ==
  /\ rmState = [rm \in RM |-> "working"]
  /\ aState  = [ins \in RM |->
                  [ac \in Acceptor |-> [mbal |-> 0, bal |-> -1, val |-> "none"]]]
  /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

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

Phase1a(bal, rm) ==
  /\ Send([type |-> "phase1a", ins |-> rm, bal |-> bal])
  /\ UNCHANGED <<rmState, aState>>

Phase2a(bal, rm) ==
  /\ ~\E m \in msgs : /\ m.type = "phase2a"
                      /\ m.bal = bal
                      /\ m.ins = rm
  /\ \E MS \in Majority :
       LET mset   == {m \in msgs : /\ m.type = "phase1b"
                                   /\ m.ins  = rm
                                   /\ m.mbal = bal
                                   /\ m.acc  \in MS}
           maxbal == Maximum({m.bal : m \in mset})
           val    == IF maxbal = -1
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

PCNext ==
  \/ \E rm \in RM : \/ RMPrepare(rm)
                    \/ RMChooseToAbort(rm)
                    \/ RMRcvCommitMsg(rm)
                    \/ RMRcvAbortMsg(rm)
  \/ \E bal \in Ballot \ {0}, rm \in RM : Phase1a(bal, rm) \/ Phase2a(bal, rm)
  \/ PCDecide
  \/ \E acc \in Acceptor : Phase1b(acc) \/ Phase2b(acc)

Init == PCInit

Next == PCNext

PCSpec == PCInit /\ [][PCNext]_vars

Spec == PCSpec

-----------------------------------------------------------------------------
(* Transaction Commit specification (TCommit), stated over rmState.        *)

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

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

TCConsistent ==
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

-----------------------------------------------------------------------------
(* Properties checked: type invariant, consistency, and refinement.        *)

THEOREM PCSpec => []PCTypeOK

THEOREM PCSpec => []TCConsistent

THEOREM PCSpec => TCSpec

=============================================================================