------------------------------ MODULE PaxosCommit ------------------------------
(***************************************************************************)
(* This module specifies the Paxos Commit algorithm.  It covers only the   *)
(* safety properties, not liveness.                                        *)
(*                                                                         *)
(* Simplifications:                                                        *)
(*  - msgs is the set of all messages ever sent.  Message receipt is not   *)
(*    modeled.  An action is enabled when the right message is in msgs.    *)
(*  - Leader selection is not modeled.  Leader actions are not tied to any *)
(*    particular process.                                                  *)
(*  - RMs can spontaneously issue Prepared messages.  Prepare messages are *)
(*    ignored.                                                             *)
(***************************************************************************)
EXTENDS Integers

Maximum(S) ==
  (*************************************************************************)
  (* The maximum of a set S of numbers, or -1 if S is empty.               *)
  (*************************************************************************)
  IF S = {} THEN -1
            ELSE CHOOSE n \in S : \A m \in S : n >= m

CONSTANTS RM,        \* The set of resource managers.
          Acceptor,  \* The set of acceptors.
          Majority,  \* The set of majorities of acceptors.
          Ballot     \* The set of ballot numbers.

ASSUME
  /\ Ballot \subseteq Nat
  /\ 0 \in Ballot
  /\ Majority \subseteq SUBSET Acceptor
  /\ \A MS1, MS2 \in Majority : MS1 \cap MS2 # {}

Message ==
  (*************************************************************************)
  (* The set of all possible messages.                                     *)
  (*************************************************************************)
  [type : {"phase1a"}, ins : RM, bal : Ballot \ {0}]
      \cup
  [type : {"phase1b"}, ins : RM, mbal : Ballot, bal : Ballot \cup {-1},
   val : {"prepared", "aborted", "none"}, acc : Acceptor]
      \cup
  [type : {"phase2a"}, ins : RM, bal : Ballot, val : {"prepared", "aborted"}]
      \cup
  [type : {"phase2b"}, acc : Acceptor, ins : RM, bal : Ballot,
   val : {"prepared", "aborted"}]
      \cup
  [type : {"Commit", "Abort"}]

VARIABLES
  rmState,  \* rmState[r] is the state of resource manager r.
  aState,   \* aState[ins][ac] is the state of acceptor ac for instance ins.
  msgs      \* The set of all messages ever sent.

vars == <<rmState, aState, msgs>>

PCTypeOK ==
  (*************************************************************************)
  (* The type-correctness invariant.                                       *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState  \in [RM -> [Acceptor -> [mbal : Ballot,
                                      bal  : Ballot \cup {-1},
                                      val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \in SUBSET Message

PCInit ==
  (*************************************************************************)
  (* The initial predicate.                                                *)
  (*************************************************************************)
  /\ rmState = [r \in RM |-> "working"]
  /\ aState  = [r \in RM |->
                 [ac \in Acceptor |-> [mbal |-> 0, bal |-> -1, val |-> "none"]]]
  /\ msgs = {}

Send(m) == msgs' = msgs \cup {m}

---------------------------------------------------------------------------------
(***************************************************************************)
(*                              RM ACTIONS                                 *)
(***************************************************************************)

RMPrepare(r) ==
  (*************************************************************************)
  (* RM r prepares and sends a phase 2a message for ballot 0 with value    *)
  (* "prepared".                                                           *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "prepared"])
  /\ UNCHANGED aState

RMChooseToAbort(r) ==
  (*************************************************************************)
  (* RM r spontaneously decides to abort.  It sends a phase 2a message for *)
  (* ballot 0 with value "aborted".                                        *)
  (*************************************************************************)
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ Send([type |-> "phase2a", ins |-> r, bal |-> 0, val |-> "aborted"])
  /\ UNCHANGED aState

RMRcvCommitMsg(r) ==
  (*************************************************************************)
  (* RM r is told by the leader to commit.                                 *)
  (*************************************************************************)
  /\ [type |-> "Commit"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  /\ UNCHANGED <<aState, msgs>>

RMRcvAbortMsg(r) ==
  (*************************************************************************)
  (* RM r is told by the leader to abort.                                  *)
  (*************************************************************************)
  /\ [type |-> "Abort"] \in msgs
  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
  /\ UNCHANGED <<aState, msgs>>

---------------------------------------------------------------------------------
(***************************************************************************)
(*                            LEADER ACTIONS                               *)
(***************************************************************************)

Phase1a(bal, r) ==
  (*************************************************************************)
  (* The leader of ballot bal sends a phase 1a message for instance r.     *)
  (*************************************************************************)
  /\ Send([type |-> "phase1a", ins |-> r, bal |-> bal])
  /\ UNCHANGED <<rmState, aState>>

Phase2a(bal, r) ==
  (*************************************************************************)
  (* The leader of ballot bal sends a phase 2a message for instance r.     *)
  (* It does so after it has received phase 1b messages from a majority    *)
  (* of acceptors.                                                         *)
  (*************************************************************************)
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

Decide ==
  (*************************************************************************)
  (* A leader decides the outcome based on phase 2b messages.  It commits  *)
  (* if every instance chose "prepared".  It aborts if any instance chose  *)
  (* "aborted".                                                            *)
  (*************************************************************************)
  /\ LET Decided(r, v) ==
           \E b \in Ballot, MS \in Majority :
             \A ac \in MS : [type |-> "phase2b", ins |-> r,
                             bal |-> b, val |-> v, acc |-> ac] \in msgs
     IN  \/ /\ \A r \in RM : Decided(r, "prepared")
            /\ Send([type |-> "Commit"])
         \/ /\ \E r \in RM : Decided(r, "aborted")
            /\ Send([type |-> "Abort"])
  /\ UNCHANGED <<rmState, aState>>

---------------------------------------------------------------------------------
(***************************************************************************)
(*                           ACCEPTOR ACTIONS                              *)
(***************************************************************************)

Phase1b(acc) ==
  \E m \in msgs :
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

---------------------------------------------------------------------------------

PCNext ==
  \/ \E r \in RM : \/ RMPrepare(r)
                   \/ RMChooseToAbort(r)
                   \/ RMRcvCommitMsg(r)
                   \/ RMRcvAbortMsg(r)
  \/ \E bal \in Ballot \ {0}, r \in RM : Phase1a(bal, r) \/ Phase2a(bal, r)
  \/ Decide
  \/ \E acc \in Acceptor : Phase1b(acc) \/ Phase2b(acc)

PCSpec == PCInit /\ [][PCNext]_vars

Init == PCInit
Next == PCNext
Spec == PCSpec

THEOREM PCSpec => [](PCTypeOK)
  (*************************************************************************)
  (* The protocol maintains type correctness.                              *)
  (*************************************************************************)

---------------------------------------------------------------------------------
(***************************************************************************)
(* Paxos Commit implements the transaction commit protocol of module       *)
(* TCommit.                                                                *)
(***************************************************************************)
TC == INSTANCE TCommit

THEOREM PCSpec => TC!TCSpec
=================================================================================