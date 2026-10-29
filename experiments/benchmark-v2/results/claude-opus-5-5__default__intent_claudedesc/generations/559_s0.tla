---------------------------- MODULE PaxosCommit ----------------------------
EXTENDS Integers

CONSTANTS RM,        \* The set of resource managers
          Acceptor,  \* The set of Paxos acceptors
          Majority,  \* The set of majority quorums of acceptors
          Ballot     \* The set of ballot numbers

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

VARIABLES rmState,  \* rmState[r] is the state of resource manager r
          aState,   \* aState[ins][ac] is the state of acceptor ac for instance ins
          msgs      \* The set of all messages that have been sent

vars == <<rmState, aState, msgs>>

Maximum(S) == IF S = {} THEN -1 ELSE CHOOSE n \in S : \A m \in S : n >= m

Send(m) == msgs' = msgs \cup {m}

-----------------------------------------------------------------------------
TypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ aState \in [RM -> [Acceptor -> [mbal : Ballot,
                                     bal  : Ballot \cup {-1},
                                     val  : {"prepared", "aborted", "none"}]]]
  /\ msgs \subseteq Message

Init ==
  /\ rmState = [r \in RM |-> "working"]
  /\ aState = [ins \in RM |->
                 [ac \in Acceptor |-> [mbal |-> 0, bal |-> -1, val |-> "none"]]]
  /\ msgs = {}

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

-----------------------------------------------------------------------------
(* Acceptor actions *)

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
  \E m \in msgs :
    /\ m.type = "phase2a"
    /\ aState[m.ins][acc].mbal =< m.bal
    /\ aState' = [aState EXCEPT ![m.ins][acc].mbal = m.bal,
                                ![m.ins][acc].bal  = m.bal,
                                ![m.ins][acc].val  = m.val]
    /\ Send([type |-> "phase2b", ins |-> m.ins, bal |-> m.bal,
             val |-> m.val, acc |-> acc])
    /\ UNCHANGED rmState

-----------------------------------------------------------------------------
Next ==
  \/ Decide
  \/ \E r \in RM :
       \/ RMPrepare(r)
       \/ RMChooseToAbort(r)
       \/ RMRcvCommitMsg(r)
       \/ RMRcvAbortMsg(r)
  \/ \E bal \in Ballot \ {0}, r \in RM : Phase1a(bal, r)
  \/ \E bal \in Ballot \ {0}, r \in RM : Phase2a(bal, r)
  \/ \E acc \in Acceptor : Phase1b(acc) \/ Phase2b(acc)

Fairness ==
  /\ WF_vars(Decide)
  /\ \A r \in RM : /\ WF_vars(RMPrepare(r) \/ RMChooseToAbort(r))
                   /\ WF_vars(RMRcvCommitMsg(r))
                   /\ WF_vars(RMRcvAbortMsg(r))
  /\ \A bal \in Ballot \ {0}, r \in RM : WF_vars(Phase2a(bal, r))
  /\ \A acc \in Acceptor : WF_vars(Phase1b(acc)) /\ WF_vars(Phase2b(acc))

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ Fairness

(* Failure-free execution: no recovery leaders start higher ballots. *)
NextNoFailure ==
  \/ Decide
  \/ \E r \in RM :
       \/ RMPrepare(r)
       \/ RMChooseToAbort(r)
       \/ RMRcvCommitMsg(r)
       \/ RMRcvAbortMsg(r)
  \/ \E acc \in Acceptor : Phase2b(acc)

NoFailureSpec ==
  /\ Init
  /\ [][NextNoFailure]_vars
  /\ WF_vars(Decide)
  /\ \A r \in RM : WF_vars(RMRcvCommitMsg(r)) /\ WF_vars(RMRcvAbortMsg(r))
  /\ \A acc \in Acceptor : WF_vars(Phase2b(acc))

-----------------------------------------------------------------------------
(* Safety invariants *)

\* Consistency: no RM commits while another aborts.
TCConsistent ==
  \A r1, r2 \in RM : ~ /\ rmState[r1] = "aborted"
                       /\ rmState[r2] = "committed"

\* Commit validity: commit only if every RM voted to prepare.
CommitValidity ==
  /\ (\E r \in RM : rmState[r] = "committed") =>
        \A r2 \in RM : rmState[r2] \in {"prepared", "committed"}
  /\ ([type |-> "Commit"] \in msgs) =>
        \A r \in RM : [type |-> "phase2a", ins |-> r, bal |-> 0,
                       val |-> "prepared"] \in msgs

\* Abort validity: if any RM chose to abort, the transaction cannot commit.
AbortValidity ==
  (\E r \in RM : [type |-> "phase2a", ins |-> r, bal |-> 0,
                  val |-> "aborted"] \in msgs)
     => /\ [type |-> "Commit"] \notin msgs
        /\ \A r \in RM : rmState[r] # "committed"

\* The global decision is unique.
DecisionUnique ==
  ~ ([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)

Invariant == TypeOK /\ TCConsistent /\ CommitValidity
             /\ AbortValidity /\ DecisionUnique

\* Stability: once committed or aborted, an RM's decision never changes.
Stability ==
  [][\A r \in RM :
       /\ (rmState[r] = "committed") => (rmState'[r] = "committed")
       /\ (rmState[r] = "aborted")   => (rmState'[r] = "aborted")
       /\ ([type |-> "Commit"] \in msgs) => ([type |-> "Commit"] \in msgs')
       /\ ([type |-> "Abort"] \in msgs)  => ([type |-> "Abort"] \in msgs')
    ]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Under fairness, every RM eventually reaches a decision.
Termination ==
  <>(\A r \in RM : rmState[r] \in {"committed", "aborted"})

\* Non-triviality: if all RMs prepare and there are no failures,
\* the transaction commits (checked against NoFailureSpec).
NonTriviality ==
  (\A r \in RM : rmState[r] = "prepared")
     ~> (\A r \in RM : rmState[r] = "committed")

-----------------------------------------------------------------------------
(* Refinement of the simple transaction commit specification (TCommit). *)

TCInit == rmState = [r \in RM |-> "working"]

canCommit == \A r \in RM : rmState[r] \in {"prepared", "committed"}

notCommitted == \A r \in RM : rmState[r] # "committed"

TCPrepare(r) ==
  /\ rmState[r] = "working"
  /\ rmState' = [rmState EXCEPT ![r] = "prepared"]

TCDecide(r) ==
  \/ /\ rmState[r] = "prepared"
     /\ canCommit
     /\ rmState' = [rmState EXCEPT ![r] = "committed"]
  \/ /\ rmState[r] \in {"working", "prepared"}
     /\ notCommitted
     /\ rmState' = [rmState EXCEPT ![r] = "aborted"]

TCNext == \E r \in RM : TCPrepare(r) \/ TCDecide(r)

TCSpec == TCInit /\ [][TCNext]_rmState

\* PaxosCommit implements TCommit: Spec => TCSpec
RefinesTCommit == TCSpec

THEOREM Spec => []Invariant
THEOREM Spec => Stability
THEOREM Spec => TCSpec
THEOREM FairSpec => Termination
THEOREM NoFailureSpec => NonTriviality
=============================================================================