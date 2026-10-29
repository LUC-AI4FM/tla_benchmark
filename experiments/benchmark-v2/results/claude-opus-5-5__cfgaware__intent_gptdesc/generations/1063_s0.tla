---------------------------- MODULE AsyncCommit ----------------------------
(***************************************************************************)
(* Asynchronous distributed system: a fixed set of processes Procs = 1..N  *)
(* run a simple majority-acknowledged commit task.                         *)
(*                                                                         *)
(*  - Process Leader (=1) broadcasts PREPARE, collects ACKs, and commits   *)
(*    once a majority (counting itself) has acknowledged. It then          *)
(*    broadcasts COMMIT and decides.                                       *)
(*  - Followers ACK a PREPARE, adopt COMMIT, and then decide.              *)
(*                                                                         *)
(* Network: an unordered set of in-flight messages.                        *)
(*  - Unordered: any message in the set may be received at any time.       *)
(*  - Duplicated: receiving a message does not remove it, so it may be     *)
(*    received any number of times.                                        *)
(*  - Delayed: receive steps are scheduled nondeterministically.           *)
(*  - Lost: Lose(m) drops a message. At most MaxLoss losses occur.         *)
(*  - Never corrupted: payloads are drawn from the fixed set Message and   *)
(*    are never rewritten.                                                 *)
(* Retransmission on timeouts gives liveness despite the bounded losses.   *)
(*                                                                         *)
(* Faults: followers may crash (stop forever). There are no Byzantine      *)
(* faults. At most MaxCrash followers crash, so a correct majority         *)
(* always remains.                                                         *)
(*                                                                         *)
(* Alternative delivery guarantee: set DeliveryMode to "reliable". This    *)
(* disables loss, which models reliable channels. FIFO ordering only       *)
(* strengthens that guarantee and preserves every property stated below,   *)
(* because each channel carries at most one distinct message type in       *)
(* each direction.                                                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N
ASSUME NAssump == N \in Nat /\ N >= 1

VARIABLES phase,    \* local phase of each process
          acks,     \* set of followers whose ACK the leader has received
          msgs,     \* network: set of in-flight messages
          crashed,  \* crashed[p] = TRUE iff p has stopped forever
          lost      \* number of messages lost so far

vars == <<phase, acks, msgs, crashed, lost>>

Procs     == 1..N
Leader    == 1
Followers == Procs \ {Leader}

\* Delivery scenario: "lossy" (default) or "reliable".
DeliveryMode == "lossy"
Reliable     == DeliveryMode = "reliable"
MaxLoss      == IF Reliable THEN 0 ELSE 2
MaxCrash     == (N - 1) \div 2

Phases == {"idle", "waiting", "prepared", "committed", "decided"}
Rank   == [ph \in Phases |->
            CASE ph = "idle"      -> 0
              [] ph = "waiting"   -> 1
              [] ph = "prepared"  -> 1
              [] ph = "committed" -> 2
              [] ph = "decided"   -> 3]

Message == [type : {"prepare", "ack", "commit"}, src : Procs, dst : Procs]

PrepareMsg(q) == [type |-> "prepare", src |-> Leader, dst |-> q]
AckMsg(q)     == [type |-> "ack",     src |-> q,      dst |-> Leader]
CommitMsg(q)  == [type |-> "commit",  src |-> Leader, dst |-> q]

Majority(S) == 2 * Cardinality(S) > N
Committed(p) == phase[p] \in {"committed", "decided"}
NumCrashed  == Cardinality({p \in Procs : crashed[p]})

-----------------------------------------------------------------------------
Init ==
    /\ phase   = [p \in Procs |-> "idle"]
    /\ acks    = {}
    /\ msgs    = {}
    /\ crashed = [p \in Procs |-> FALSE]
    /\ lost    = 0

\* ---------------- Leader steps ----------------
StartPrepare ==
    /\ ~crashed[Leader]
    /\ phase[Leader] = "idle"
    /\ phase' = [phase EXCEPT ![Leader] = "waiting"]
    /\ msgs'  = msgs \cup {PrepareMsg(q) : q \in Followers}
    /\ UNCHANGED <<acks, crashed, lost>>

\* Timeout-driven retransmission of PREPARE.
RetransmitPrepare(q) ==
    /\ ~crashed[Leader]
    /\ phase[Leader] = "waiting"
    /\ q \notin acks
    /\ PrepareMsg(q) \notin msgs
    /\ msgs' = msgs \cup {PrepareMsg(q)}
    /\ UNCHANGED <<phase, acks, crashed, lost>>

RcvAck(q) ==
    /\ ~crashed[Leader]
    /\ phase[Leader] = "waiting"
    /\ AckMsg(q) \in msgs
    /\ q \notin acks
    /\ acks' = acks \cup {q}
    /\ UNCHANGED <<phase, msgs, crashed, lost>>

LeaderCommit ==
    /\ ~crashed[Leader]
    /\ phase[Leader] = "waiting"
    /\ Majority(acks \cup {Leader})
    /\ phase' = [phase EXCEPT ![Leader] = "committed"]
    /\ msgs'  = msgs \cup {CommitMsg(q) : q \in Followers}
    /\ UNCHANGED <<acks, crashed, lost>>

\* Timeout-driven retransmission of COMMIT. This step leaves the local
\* phase unchanged, and it is disabled once no message is missing.
RetransmitCommit(q) ==
    /\ ~crashed[Leader]
    /\ Committed(Leader)
    /\ CommitMsg(q) \notin msgs
    /\ msgs' = msgs \cup {CommitMsg(q)}
    /\ UNCHANGED <<phase, acks, crashed, lost>>

\* ---------------- Follower steps ----------------
RcvPrepare(q) ==
    /\ ~crashed[q]
    /\ phase[q] = "idle"
    /\ PrepareMsg(q) \in msgs
    /\ phase' = [phase EXCEPT ![q] = "prepared"]
    /\ msgs'  = msgs \cup {AckMsg(q)}
    /\ UNCHANGED <<acks, crashed, lost>>

\* Timeout-driven retransmission of ACK.
RetransmitAck(q) ==
    /\ ~crashed[q]
    /\ phase[q] = "prepared"
    /\ AckMsg(q) \notin msgs
    /\ msgs' = msgs \cup {AckMsg(q)}
    /\ UNCHANGED <<phase, acks, crashed, lost>>

RcvCommit(q) ==
    /\ ~crashed[q]
    /\ phase[q] \in {"idle", "prepared"}
    /\ CommitMsg(q) \in msgs
    /\ phase' = [phase EXCEPT ![q] = "committed"]
    /\ UNCHANGED <<acks, msgs, crashed, lost>>

\* ---------------- Local computation: decide ----------------
Decide(p) ==
    /\ ~crashed[p]
    /\ phase[p] = "committed"
    /\ phase' = [phase EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<acks, msgs, crashed, lost>>

\* ---------------- Environment / faults ----------------
Crash(p) ==
    /\ p \in Followers
    /\ ~crashed[p]
    /\ NumCrashed < MaxCrash
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<phase, acks, msgs, lost>>

Lose(m) ==
    /\ ~Reliable
    /\ lost < MaxLoss
    /\ m \in msgs
    /\ msgs' = msgs \ {m}
    /\ lost' = lost + 1
    /\ UNCHANGED <<phase, acks, crashed>>

\* Every live process has stopped in the decided state.
Done == \A p \in Procs : crashed[p] \/ phase[p] = "decided"

\* Explicit stuttering after termination, which avoids spurious deadlock.
Terminated == Done /\ UNCHANGED vars

-----------------------------------------------------------------------------
LeaderActions ==
    \/ StartPrepare
    \/ LeaderCommit
    \/ Decide(Leader)
    \/ \E q \in Followers : RetransmitPrepare(q) \/ RcvAck(q) \/ RetransmitCommit(q)

FollowerActions(q) ==
    RcvPrepare(q) \/ RetransmitAck(q) \/ RcvCommit(q) \/ Decide(q)

Next ==
    \/ LeaderActions
    \/ \E q \in Followers : FollowerActions(q)
    \/ \E p \in Procs : Crash(p)
    \/ \E m \in msgs : Lose(m)
    \/ Terminated

\* Fair scheduling: weak fairness on every step of a non-crashed process.
\* Crash and Lose get no fairness, and both are bounded.
Fairness ==
    /\ WF_vars(StartPrepare)
    /\ WF_vars(LeaderCommit)
    /\ \A p \in Procs : WF_vars(Decide(p))
    /\ \A q \in Followers :
          /\ WF_vars(RetransmitPrepare(q))
          /\ WF_vars(RcvAck(q))
          /\ WF_vars(RetransmitCommit(q))
          /\ WF_vars(RcvPrepare(q))
          /\ WF_vars(RetransmitAck(q))
          /\ WF_vars(RcvCommit(q))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety-only specification, with no fairness.
SafetySpec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(*************************** SAFETY: INVARIANTS ****************************)
TypeOK ==
    /\ phase \in [Procs -> Phases]
    /\ acks \subseteq Followers
    /\ msgs \subseteq Message
    /\ crashed \in [Procs -> BOOLEAN]
    /\ lost \in 0..MaxLoss

RoleOK ==
    /\ phase[Leader] \in {"idle", "waiting", "committed", "decided"}
    /\ \A q \in Followers : phase[q] \in {"idle", "prepared", "committed", "decided"}

\* (1) Local states are consistent with the messages that were sent and
\*     received.
Consistency ==
    /\ Committed(Leader) => Majority(acks \cup {Leader})
    /\ \A q \in acks : phase[q] # "idle"
    /\ \A m \in msgs :
          /\ m.type = "prepare" => phase[Leader] # "idle"
          /\ m.type = "ack"     => phase[m.src] # "idle"
          /\ m.type = "commit"  => Committed(Leader)
    /\ \A q \in Followers : Committed(q) => Committed(Leader)

\* Fault assumptions: the number of crashes and losses stays bounded, and
\* the leader never crashes.
FaultBounds ==
    /\ NumCrashed <= MaxCrash
    /\ ~crashed[Leader]
    /\ (Reliable => lost = 0)

\* Combined state invariant, checked as INVARIANT.
JsonInv == TypeOK /\ RoleOK /\ Consistency /\ FaultBounds

(******************* SAFETY: ACTION (TEMPORAL) PROPERTIES ******************)
\* (2) No process regresses to an earlier phase, and a decision is stable.
NoRegress ==
    [][\A p \in Procs : Rank[phase'[p]] >= Rank[phase[p]]]_vars

DecisionStable ==
    [][\A p \in Procs : phase[p] = "decided" => phase'[p] = "decided"]_vars

(************* LIVENESS: checked under Spec, which includes fairness ******)
\* (3) Eventual progress: the leader eventually reaches a stable commit.
Progress == <>[](Committed(Leader))

\* (4) Termination: every process that has not crashed eventually stops
\*     in the decided state.
Termination == <>[](Done)

\* A non-crashed process eventually decides.
EventualDecision ==
    \A p \in Procs : (phase[p] # "decided") ~> (phase[p] = "decided" \/ crashed[p])

\* Check as INVARIANTS:  JsonInv (TypeOK, RoleOK, Consistency, FaultBounds)
\* Check as PROPERTIES:  NoRegress, DecisionStable          (safety, any spec)
\*                       Progress, Termination, EventualDecision
\*                       (liveness, require Spec with fairness)
=============================================================================