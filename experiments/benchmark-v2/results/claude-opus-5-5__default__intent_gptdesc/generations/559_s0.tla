---------------------------- MODULE PaxosTransactionCommit ----------------------------
(***************************************************************************)
(* A transaction commit service built on a consensus protocol (Paxos).     *)
(* Each transaction has its own consensus instance that decides "commit"   *)
(* or "abort". Many transactions may be decided concurrently.              *)
(*                                                                         *)
(* Roles:                                                                  *)
(*   - Clients submit transactions (Submit).                               *)
(*   - Participants (RMs) vote "yes" (prepared) or "no" per transaction.   *)
(*   - Coordinators (proposers) own ballots and run Phase1a / Phase2a.     *)
(*   - Acceptors run Phase1b / Phase2b. A minority of them may crash.      *)
(*   - Learners learn a value once a quorum accepted it in one ballot.     *)
(*                                                                         *)
(* Messages are never removed from msgs. A message can therefore be        *)
(* received any number of times and in any order. This models reordering  *)
(* and duplication. Loss is modeled by a message never being received.    *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Tx,        \* set of transaction identifiers
          RM,        \* set of participants (resource managers) of each transaction
          Acceptor,  \* set of acceptors / replicas
          Learner,   \* set of learners
          Ballot,    \* finite set of ballot numbers (each owned by one coordinator)
          Quorum     \* set of majority quorums of acceptors

ASSUME QuorumAssumption ==
          /\ Quorum # {}
          /\ Quorum \subseteq SUBSET Acceptor
          /\ \A Q1, Q2 \in Quorum : Q1 \cap Q2 # {}

ASSUME BallotAssumption ==
          /\ Ballot \subseteq Nat
          /\ Ballot # {}
          /\ IsFiniteSet(Ballot)

None     == "none"
Decision == {"commit", "abort"}
VoteVal  == {"yes", "no"}

\* The ballot of the eventually-stable, correct coordinator, used for liveness.
LeaderBal == CHOOSE b \in Ballot : \A c \in Ballot : c <= b

Messages ==
       [type : {"1a"}, tx : Tx, bal : Ballot]
  \cup [type : {"1b"}, tx : Tx, acc : Acceptor, bal : Ballot,
        mbal : Ballot \cup {-1}, mval : Decision \cup {None}]
  \cup [type : {"2a"}, tx : Tx, bal : Ballot, val : Decision]
  \cup [type : {"2b"}, tx : Tx, acc : Acceptor, bal : Ballot, val : Decision]

VARIABLES txStatus,  \* txStatus[t] \in {"idle","active"}: submitted by a client?
          vote,      \* vote[t][r] \in {"none","yes","no"}: participant votes
          msgs,      \* set of all messages sent so far
          maxBal,    \* maxBal[t][a]: highest ballot acceptor a joined for t
          maxVBal,   \* maxVBal[t][a]: highest ballot in which a accepted for t
          maxVal,    \* maxVal[t][a]: value a accepted in maxVBal[t][a]
          learned,   \* learned[t][l] \in Decision \cup {None}
          crashed    \* set of crashed (non-responsive) acceptors

vars == <<txStatus, vote, msgs, maxBal, maxVBal, maxVal, learned, crashed>>

TypeOK ==
  /\ txStatus \in [Tx -> {"idle", "active"}]
  /\ vote     \in [Tx -> [RM -> VoteVal \cup {None}]]
  /\ msgs     \subseteq Messages
  /\ maxBal   \in [Tx -> [Acceptor -> Ballot \cup {-1}]]
  /\ maxVBal  \in [Tx -> [Acceptor -> Ballot \cup {-1}]]
  /\ maxVal   \in [Tx -> [Acceptor -> Decision \cup {None}]]
  /\ learned  \in [Tx -> [Learner -> Decision \cup {None}]]
  /\ crashed  \subseteq Acceptor

Init ==
  /\ txStatus = [t \in Tx |-> "idle"]
  /\ vote     = [t \in Tx |-> [r \in RM |-> None]]
  /\ msgs     = {}
  /\ maxBal   = [t \in Tx |-> [a \in Acceptor |-> -1]]
  /\ maxVBal  = [t \in Tx |-> [a \in Acceptor |-> -1]]
  /\ maxVal   = [t \in Tx |-> [a \in Acceptor |-> None]]
  /\ learned  = [t \in Tx |-> [l \in Learner |-> None]]
  /\ crashed  = {}

Send(m) == msgs' = msgs \cup {m}

(***************************************************************************)
(* Validity of an initial proposal:                                        *)
(*   - commit only if every participant voted "yes";                      *)
(*   - abort only if some participant voted "no".                         *)
(***************************************************************************)
ValidValue(t, v) ==
  /\ v = "commit" => \A r \in RM : vote[t][r] = "yes"
  /\ v = "abort"  => \E r \in RM : vote[t][r] = "no"

---------------------------------------------------------------------------------------
(* Client: submit a transaction for commitment. *)
Submit(t) ==
  /\ txStatus[t] = "idle"
  /\ txStatus' = [txStatus EXCEPT ![t] = "active"]
  /\ UNCHANGED <<vote, msgs, maxBal, maxVBal, maxVal, learned, crashed>>

(* Participant r votes on transaction t. A vote is cast once and never changes. *)
RMVote(t, r, v) ==
  /\ txStatus[t] = "active"
  /\ vote[t][r] = None
  /\ vote' = [vote EXCEPT ![t][r] = v]
  /\ UNCHANGED <<txStatus, msgs, maxBal, maxVBal, maxVal, learned, crashed>>

(* Coordinator owning ballot b starts the consensus instance for t. *)
Phase1a(t, b) ==
  /\ txStatus[t] = "active"
  /\ [type |-> "1a", tx |-> t, bal |-> b] \notin msgs
  /\ Send([type |-> "1a", tx |-> t, bal |-> b])
  /\ UNCHANGED <<txStatus, vote, maxBal, maxVBal, maxVal, learned, crashed>>

(* Acceptor a promises ballot b for t and reports its last accepted value. *)
Phase1b(t, a, b) ==
  /\ a \notin crashed
  /\ [type |-> "1a", tx |-> t, bal |-> b] \in msgs
  /\ b > maxBal[t][a]
  /\ maxBal' = [maxBal EXCEPT ![t][a] = b]
  /\ Send([type |-> "1b", tx |-> t, acc |-> a, bal |-> b,
           mbal |-> maxVBal[t][a], mval |-> maxVal[t][a]])
  /\ UNCHANGED <<txStatus, vote, maxVBal, maxVal, learned, crashed>>

(* Coordinator of ballot b proposes a value for t after it receives a quorum of 1b messages. *)
Phase2a(t, b) ==
  /\ txStatus[t] = "active"
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.tx = t /\ m.bal = b
  /\ \E Q \in Quorum, v \in Decision :
       LET Q1b  == {m \in msgs : m.type = "1b" /\ m.tx = t
                                  /\ m.bal = b /\ m.acc \in Q}
           Q1bv == {m \in Q1b : m.mbal >= 0}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ /\ Q1bv = {}
                 /\ ValidValue(t, v)
              \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal >= mm.mbal
           /\ Send([type |-> "2a", tx |-> t, bal |-> b, val |-> v])
  /\ UNCHANGED <<txStatus, vote, maxBal, maxVBal, maxVal, learned, crashed>>

(* Acceptor a accepts the proposal of ballot b for t. *)
Phase2b(t, a, b) ==
  /\ a \notin crashed
  /\ b >= maxBal[t][a]
  /\ \E m \in msgs :
       /\ m.type = "2a" /\ m.tx = t /\ m.bal = b
       /\ maxBal'  = [maxBal  EXCEPT ![t][a] = b]
       /\ maxVBal' = [maxVBal EXCEPT ![t][a] = b]
       /\ maxVal'  = [maxVal  EXCEPT ![t][a] = m.val]
       /\ Send([type |-> "2b", tx |-> t, acc |-> a, bal |-> b, val |-> m.val])
  /\ UNCHANGED <<txStatus, vote, learned, crashed>>

(* A value is chosen for t if a quorum accepted it in the same ballot. *)
ChosenIn(t, b, v) ==
  \E Q \in Quorum : \A a \in Q :
     [type |-> "2b", tx |-> t, acc |-> a, bal |-> b, val |-> v] \in msgs

Chosen(t, v) == \E b \in Ballot : ChosenIn(t, b, v)

(* Learner l learns the decision for t. *)
Learn(t, l, v) ==
  /\ learned[t][l] = None
  /\ Chosen(t, v)
  /\ learned' = [learned EXCEPT ![t][l] = v]
  /\ UNCHANGED <<txStatus, vote, msgs, maxBal, maxVBal, maxVal, crashed>>

(* An acceptor crashes. A majority quorum always stays responsive. *)
Crash(a) ==
  /\ a \notin crashed
  /\ \E Q \in Quorum : Q \cap (crashed \cup {a}) = {}
  /\ crashed' = crashed \cup {a}
  /\ UNCHANGED <<txStatus, vote, msgs, maxBal, maxVBal, maxVal, learned>>

Next ==
  \/ \E t \in Tx : Submit(t)
  \/ \E t \in Tx, r \in RM, v \in VoteVal : RMVote(t, r, v)
  \/ \E t \in Tx, b \in Ballot : Phase1a(t, b) \/ Phase2a(t, b)
  \/ \E t \in Tx, a \in Acceptor, b \in Ballot : Phase1b(t, a, b) \/ Phase2b(t, a, b)
  \/ \E t \in Tx, l \in Learner, v \in Decision : Learn(t, l, v)
  \/ \E a \in Acceptor : Crash(a)

---------------------------------------------------------------------------------------
(***************************************************************************)
(* Fairness assumptions:                                                   *)
(*   - Participants eventually vote.                                       *)
(*   - A correct coordinator owns the highest ballot LeaderBal and acts.  *)
(*     No higher ballot interferes with it.                               *)
(*   - Responsive acceptors eventually receive messages and reply.         *)
(*   - Learners eventually learn chosen values.                            *)
(***************************************************************************)
Fairness ==
  /\ \A t \in Tx, r \in RM : WF_vars(\E v \in VoteVal : RMVote(t, r, v))
  /\ \A t \in Tx : WF_vars(Phase1a(t, LeaderBal))
  /\ \A t \in Tx : SF_vars(Phase2a(t, LeaderBal))
  /\ \A t \in Tx, a \in Acceptor : WF_vars(Phase1b(t, a, LeaderBal))
  /\ \A t \in Tx, a \in Acceptor : WF_vars(Phase2b(t, a, LeaderBal))
  /\ \A t \in Tx, l \in Learner : WF_vars(\E v \in Decision : Learn(t, l, v))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------------
(*************************** Safety properties ****************************)

(* (4) Nontriviality: the only decisions are commit or abort. *)
Nontriviality ==
  \A t \in Tx, l \in Learner : learned[t][l] \in Decision \cup {None}

(* (1) Agreement: no two learners decide differently for the same transaction. *)
Agreement ==
  \A t \in Tx, l1, l2 \in Learner :
     (learned[t][l1] # None /\ learned[t][l2] # None)
        => learned[t][l1] = learned[t][l2]

(* Consensus-level agreement: at most one value is chosen per instance. *)
ChosenAgreement ==
  \A t \in Tx, v1, v2 \in Decision :
     (Chosen(t, v1) /\ Chosen(t, v2)) => v1 = v2

(* (2) Validity: commit requires unanimous "yes" votes. Abort requires a "no" vote. *)
Validity ==
  \A t \in Tx, l \in Learner :
     /\ learned[t][l] = "commit" => \A r \in RM : vote[t][r] = "yes"
     /\ learned[t][l] = "abort"  => \E r \in RM : vote[t][r] = "no"

(* (3) Integrity: a learned decision is final. *)
Integrity ==
  [][\A t \in Tx, l \in Learner :
        learned[t][l] # None => learned'[t][l] = learned[t][l]]_vars

(* Votes are immutable once cast (used by Validity). *)
VoteStability ==
  [][\A t \in Tx, r \in RM : vote[t][r] # None => vote'[t][r] = vote[t][r]]_vars

(***************************************************************************)
(* Refinement of the abstract transaction-commit specification. Each      *)
(* transaction has an abstract decision. It moves at most once from none  *)
(* to commit or abort. It is consistent with the votes, and it is never   *)
(* revoked.                                                               *)
(***************************************************************************)
AbsDecision(t) ==
  IF \E l \in Learner : learned[t][l] = "commit" THEN "commit"
  ELSE IF \E l \in Learner : learned[t][l] = "abort" THEN "abort"
  ELSE None

AbsTCInvariant ==
  \A t \in Tx :
     /\ AbsDecision(t) \in Decision \cup {None}
     /\ AbsDecision(t) = "commit" => \A r \in RM : vote[t][r] = "yes"
     /\ AbsDecision(t) = "abort"  => \E r \in RM : vote[t][r] = "no"
     /\ \A l \in Learner : learned[t][l] \in {None, AbsDecision(t)}

RefinesAbstractCommit ==
  [][\A t \in Tx : AbsDecision(t) # None => AbsDecision(t)' = AbsDecision(t)]_vars

SafetyInvariant ==
  /\ TypeOK
  /\ Nontriviality
  /\ Agreement
  /\ ChosenAgreement
  /\ Validity
  /\ AbsTCInvariant

(*************************** Liveness properties **************************)

(* Every transaction submitted to the correct coordinator is eventually decided by every learner. *)
Termination ==
  \A t \in Tx :
     (txStatus[t] = "active") ~> (\A l \in Learner : learned[t][l] # None)

(* A decided transaction eventually has a chosen value at the consensus level. *)
EventuallyChosen ==
  \A t \in Tx :
     (txStatus[t] = "active") ~> (\E v \in Decision : Chosen(t, v))

---------------------------------------------------------------------------------------
THEOREM Spec => []SafetyInvariant
THEOREM Spec => Integrity /\ VoteStability /\ RefinesAbstractCommit
THEOREM Spec => Termination /\ EventuallyChosen
=======================================================================================