---------------------------- MODULE AsyncQuorumCommit ----------------------------
(***************************************************************************)
(* Asynchronous message-passing system with crash faults.                  *)
(*                                                                         *)
(* A fixed set of processes runs a leader-driven quorum-commit protocol.   *)
(*   1. The Leader proposes a value and broadcasts Prepare.                *)
(*   2. Participants adopt the value and reply with Ack.                   *)
(*   3. The Leader commits once it holds a majority of Acks, then          *)
(*      broadcasts Decide.                                                 *)
(*   4. Participants decide and reply with DecAck.                         *)
(*   5. The Leader retransmits Prepare and Decide to cover lost messages.  *)
(*                                                                         *)
(* Channels                                                                *)
(*   chan[s][d] holds the messages in transit from s to d.                 *)
(*   DeliveryMode = "Unreliable":                                          *)
(*     - delivery is unordered (any pending message may be received);      *)
(*     - a message may be lost (at most MaxLoss losses in total);          *)
(*     - a message may be duplicated (at most MaxDup in total).            *)
(*   DeliveryMode = "FIFO": the optional stronger scenario, with reliable  *)
(*     FIFO channels. Only the head of a channel may be received, and no   *)
(*     loss or duplication occurs.                                         *)
(*   In both modes, channels never corrupt payloads. Every in-transit      *)
(*   message is a message that was actually sent.                         *)
(*                                                                         *)
(* Faults                                                                  *)
(*   - Processes may crash (stop forever), at most MaxCrash of them.       *)
(*   - There is no Byzantine behaviour: processes only take the protocol   *)
(*     actions defined below.                                              *)
(*                                                                         *)
(* Scheduling                                                              *)
(*   Step interleaving is nondeterministic, as given by the disjunction    *)
(*   in Next.                                                              *)
(*                                                                         *)
(* What to check                                                           *)
(*   Check as INVARIANTS (no fairness needed):                             *)
(*     TypeOK, NoCorruption, PhaseWellFormed, QuorumBeforeCommit,          *)
(*     AcksJustified, AckConsistency, DecideJustified, DecidedConsistent,  *)
(*     Agreement.                                                          *)
(*   Check as an action PROPERTY (safety, no fairness needed):             *)
(*     NoRegression.                                                       *)
(*   Check as PROPERTIES under Spec, which includes Fairness (liveness):   *)
(*     EventualDecision, Termination.                                      *)
(*     These rely on: weak fairness of the steps of non-crashed processes  *)
(*     and of channel delivery; bounded loss (MaxLoss) and bounded         *)
(*     duplication (MaxDup); a correct Leader; and a correct majority      *)
(*     (2 * MaxCrash < |Procs|).                                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Procs,          \* fixed set of processes
    Leader,         \* distinguished coordinator
    Values,         \* values that may be proposed
    NoVal,          \* placeholder for "no value yet"
    MaxLoss,        \* bound on total message losses
    MaxDup,         \* bound on total message duplications
    MaxCrash,       \* bound on number of crashed processes
    DeliveryMode    \* "Unreliable" or "FIFO"

ASSUME
    /\ Leader \in Procs
    /\ Values # {}
    /\ NoVal \notin Values
    /\ MaxLoss \in Nat
    /\ MaxDup \in Nat
    /\ MaxCrash \in Nat
    /\ 2 * MaxCrash < Cardinality(Procs)   \* a correct majority always exists
    /\ DeliveryMode \in {"Unreliable", "FIFO"}

VARIABLES
    phase,      \* phase[p] \in Phases : local protocol phase
    val,        \* val[p] : value adopted / decided by p
    acks,       \* Leader-local: set of processes whose Ack was received
    decAcks,    \* Leader-local: set of processes whose DecAck was received
    alive,      \* alive[p] = FALSE iff p has crashed
    chan,       \* chan[s][d] : sequence of messages in transit s -> d
    sent,       \* ghost: set of every message ever sent
    lossCount,  \* number of message losses so far
    dupCount    \* number of message duplications so far

vars == <<phase, val, acks, decAcks, alive, chan, sent, lossCount, dupCount>>

-----------------------------------------------------------------------------
Phases   == {"init", "waiting", "committed", "decided"}
MsgTypes == {"Prepare", "Ack", "Decide", "DecAck"}
Messages == [type : MsgTypes, src : Procs, dst : Procs, val : Values]
Others   == Procs \ {Leader}

Msg(t, s, d, v) == [type |-> t, src |-> s, dst |-> d, val |-> v]

IsMajority(S) == 2 * Cardinality(S) > Cardinality(Procs)

Rank(ph) == CASE ph = "init"      -> 0
              [] ph = "waiting"   -> 1
              [] ph = "committed" -> 2
              [] ph = "decided"   -> 3

Crashed == {p \in Procs : ~alive[p]}

InChan(t, s, d) == \E i \in 1..Len(chan[s][d]) : chan[s][d][i].type = t

RemoveAt(sq, i) == SubSeq(sq, 1, i - 1) \o SubSeq(sq, i + 1, Len(sq))

\* Indices of messages that may be delivered next on channel s -> d.
DeliverableIdx(s, d) ==
    IF DeliveryMode = "FIFO" THEN {1} ELSE 1..Len(chan[s][d])

\* Leader sends message type t carrying v to every process in dsts.
LeaderSend(t, v, dsts) ==
    /\ chan' = [p \in Procs |-> [q \in Procs |->
                  IF p = Leader /\ q \in dsts
                     THEN Append(chan[p][q], Msg(t, Leader, q, v))
                     ELSE chan[p][q]]]
    /\ sent' = sent \cup {Msg(t, Leader, q, v) : q \in dsts}

\* Starting from channel state c, process "from" sends (t, v) to "to".
ReplyWith(c, from, to, t, v) ==
    /\ chan' = [c EXCEPT ![from][to] = Append(c[from][to], Msg(t, from, to, v))]
    /\ sent' = sent \cup {Msg(t, from, to, v)}

-----------------------------------------------------------------------------
Init ==
    /\ phase     = [p \in Procs |-> "init"]
    /\ val       = [p \in Procs |-> NoVal]
    /\ acks      = {}
    /\ decAcks   = {}
    /\ alive     = [p \in Procs |-> TRUE]
    /\ chan      = [s \in Procs |-> [d \in Procs |-> << >>]]
    /\ sent      = {}
    /\ lossCount = 0
    /\ dupCount  = 0

-----------------------------------------------------------------------------
(* Leader actions: local computation and sending                          *)

Propose(v) ==
    /\ alive[Leader]
    /\ phase[Leader] = "init"
    /\ phase' = [phase EXCEPT ![Leader] = "waiting"]
    /\ val'   = [val EXCEPT ![Leader] = v]
    /\ acks'  = {Leader}
    /\ LeaderSend("Prepare", v, Others)
    /\ UNCHANGED <<decAcks, alive, lossCount, dupCount>>

ResendPrepare(q) ==
    /\ alive[Leader]
    /\ phase[Leader] = "waiting"
    /\ q \in Others \ acks
    /\ ~InChan("Prepare", Leader, q)
    /\ ~InChan("Ack", q, Leader)
    /\ LeaderSend("Prepare", val[Leader], {q})
    /\ UNCHANGED <<phase, val, acks, decAcks, alive, lossCount, dupCount>>

Commit ==
    /\ alive[Leader]
    /\ phase[Leader] = "waiting"
    /\ IsMajority(acks)
    /\ phase' = [phase EXCEPT ![Leader] = "committed"]
    /\ LeaderSend("Decide", val[Leader], Others)
    /\ UNCHANGED <<val, acks, decAcks, alive, lossCount, dupCount>>

LeaderDecide ==
    /\ alive[Leader]
    /\ phase[Leader] = "committed"
    /\ phase' = [phase EXCEPT ![Leader] = "decided"]
    /\ UNCHANGED <<val, acks, decAcks, alive, chan, sent, lossCount, dupCount>>

ResendDecide(q) ==
    /\ alive[Leader]
    /\ phase[Leader] \in {"committed", "decided"}
    /\ q \in Others \ decAcks
    /\ ~InChan("Decide", Leader, q)
    /\ ~InChan("DecAck", q, Leader)
    /\ LeaderSend("Decide", val[Leader], {q})
    /\ UNCHANGED <<phase, val, acks, decAcks, alive, lossCount, dupCount>>

-----------------------------------------------------------------------------
(* Receiving a message (if one is available)                              *)

Receive(s, d) ==
    /\ alive[d]
    /\ Len(chan[s][d]) > 0
    /\ \E i \in DeliverableIdx(s, d) :
         LET m == chan[s][d][i]
             c == [chan EXCEPT ![s][d] = RemoveAt(chan[s][d], i)]
         IN
         \/ /\ m.type = "Prepare"
            /\ IF phase[d] \in {"init", "waiting"}
                 THEN /\ phase' = [phase EXCEPT ![d] = "waiting"]
                      /\ val'   = [val EXCEPT ![d] = m.val]
                      /\ ReplyWith(c, d, s, "Ack", m.val)
                 ELSE /\ chan' = c
                      /\ UNCHANGED <<phase, val, sent>>
            /\ UNCHANGED <<acks, decAcks>>
         \/ /\ m.type = "Ack"
            /\ acks' = acks \cup {m.src}
            /\ chan' = c
            /\ UNCHANGED <<phase, val, decAcks, sent>>
         \/ /\ m.type = "Decide"
            /\ phase' = [phase EXCEPT ![d] = "decided"]
            /\ val'   = [val EXCEPT ![d] = m.val]
            /\ ReplyWith(c, d, s, "DecAck", m.val)
            /\ UNCHANGED <<acks, decAcks>>
         \/ /\ m.type = "DecAck"
            /\ decAcks' = decAcks \cup {m.src}
            /\ chan' = c
            /\ UNCHANGED <<phase, val, acks, sent>>
    /\ UNCHANGED <<alive, lossCount, dupCount>>

-----------------------------------------------------------------------------
(* Environment: channel faults and process crashes                        *)

Lose(s, d) ==
    /\ DeliveryMode = "Unreliable"
    /\ lossCount < MaxLoss
    /\ Len(chan[s][d]) > 0
    /\ \E i \in 1..Len(chan[s][d]) :
         chan' = [chan EXCEPT ![s][d] = RemoveAt(chan[s][d], i)]
    /\ lossCount' = lossCount + 1
    /\ UNCHANGED <<phase, val, acks, decAcks, alive, sent, dupCount>>

Duplicate(s, d) ==
    /\ DeliveryMode = "Unreliable"
    /\ dupCount < MaxDup
    /\ Len(chan[s][d]) > 0
    /\ \E i \in 1..Len(chan[s][d]) :
         chan' = [chan EXCEPT ![s][d] = Append(chan[s][d], chan[s][d][i])]
    /\ dupCount' = dupCount + 1
    /\ UNCHANGED <<phase, val, acks, decAcks, alive, sent, lossCount>>

Crash(p) ==
    /\ alive[p]
    /\ Cardinality(Crashed) < MaxCrash
    /\ alive' = [alive EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<phase, val, acks, decAcks, chan, sent, lossCount, dupCount>>

\* Termination: every live process has decided. This stuttering step
\* prevents TLC from reporting spurious deadlock.
Terminated ==
    /\ \A p \in Procs : alive[p] => phase[p] = "decided"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
Next ==
    \/ \E v \in Values : Propose(v)
    \/ Commit
    \/ LeaderDecide
    \/ \E q \in Others : ResendPrepare(q) \/ ResendDecide(q)
    \/ \E s, d \in Procs : Receive(s, d) \/ Lose(s, d) \/ Duplicate(s, d)
    \/ \E p \in Procs : Crash(p)
    \/ Terminated

\* Fair scheduling of correct processes and eventual delivery. Every
\* action requires its executing process to be alive, so crashed
\* processes are never forced to act.
Fairness ==
    /\ WF_vars(\E v \in Values : Propose(v))
    /\ WF_vars(Commit)
    /\ WF_vars(LeaderDecide)
    /\ \A q \in Others : WF_vars(ResendPrepare(q)) /\ WF_vars(ResendDecide(q))
    /\ \A s, d \in Procs : WF_vars(Receive(s, d))

SafetySpec == Init /\ [][Next]_vars

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* SAFETY: state invariants                                               *)

TypeOK ==
    /\ phase \in [Procs -> Phases]
    /\ val \in [Procs -> Values \cup {NoVal}]
    /\ acks \subseteq Procs
    /\ decAcks \subseteq Procs
    /\ alive \in [Procs -> BOOLEAN]
    /\ chan \in [Procs -> [Procs -> Seq(Messages)]]
    /\ sent \subseteq Messages
    /\ lossCount \in 0..MaxLoss
    /\ dupCount \in 0..MaxDup

\* Channels never corrupt or invent payloads.
NoCorruption ==
    \A s, d \in Procs : \A i \in 1..Len(chan[s][d]) :
        /\ chan[s][d][i] \in sent
        /\ chan[s][d][i].src = s
        /\ chan[s][d][i].dst = d

\* Application-level constraint: only the Leader can be in "committed".
PhaseWellFormed ==
    /\ \A p \in Others : phase[p] # "committed"
    /\ \A p \in Procs : phase[p] # "init" <=> val[p] # NoVal

\* (1) Consistency between local state and messages: no commit without
\*     a quorum of acknowledgements ...
QuorumBeforeCommit ==
    phase[Leader] \in {"committed", "decided"} => IsMajority(acks)

\* ... and every acknowledgement counted was actually sent.
AcksJustified ==
    \A q \in acks \ {Leader} : Msg("Ack", q, Leader, val[Leader]) \in sent

\* Every Ack ever sent reflects the sender's local state.
AckConsistency ==
    \A m \in sent :
        m.type = "Ack" =>
            /\ phase[m.src] \in {"waiting", "decided"}
            /\ val[m.src] = m.val

\* Decide messages are sent only after a commit, and carry the committed value.
DecideJustified ==
    \A m \in sent :
        m.type = "Decide" =>
            /\ phase[Leader] \in {"committed", "decided"}
            /\ m.val = val[Leader]

\* No process is decided unless the Leader has committed its value.
DecidedConsistent ==
    \A p \in Procs :
        phase[p] = "decided" =>
            /\ phase[Leader] \in {"committed", "decided"}
            /\ val[p] = val[Leader]

\* All decided processes decide the same value.
Agreement ==
    \A p, q \in Procs :
        (phase[p] = "decided" /\ phase[q] = "decided") => val[p] = val[q]

Invariants ==
    /\ TypeOK
    /\ NoCorruption
    /\ PhaseWellFormed
    /\ QuorumBeforeCommit
    /\ AcksJustified
    /\ AckConsistency
    /\ DecideJustified
    /\ DecidedConsistent
    /\ Agreement

-----------------------------------------------------------------------------
(* SAFETY: (2) no invalid transitions (checked as an action property)     *)

NoRegressionStep ==
    \A p \in Procs :
        /\ Rank(phase'[p]) >= Rank(phase[p])
        /\ phase[p] = "decided" => (phase'[p] = "decided" /\ val'[p] = val[p])
        /\ phase[p] = "committed" => val'[p] = val[p]
        /\ ~alive[p] => ~alive'[p]          \* crashes are permanent
        /\ ~alive[p] => (phase'[p] = phase[p] /\ val'[p] = val[p])

NoRegression == [][NoRegressionStep]_vars

-----------------------------------------------------------------------------
(* LIVENESS: checked under Spec (fairness + bounded losses/duplications)  *)

\* (3) Eventual progress: if the Leader is correct (and, by assumption,
\*     a majority is correct and losses are bounded), the protocol
\*     reaches a stable decision.
EventualDecision ==
    []alive[Leader] => <>[](phase[Leader] = "decided")

\* (4) Termination: every process that never crashes eventually stops
\*     in a decided state (decided is absorbing, by NoRegression).
Termination ==
    []alive[Leader] =>
        \A p \in Procs : []alive[p] => <>[](phase[p] = "decided")

\* Leads-to form of progress: once the Leader commits, every
\* participant that stays alive eventually decides.
CommitLeadsToDecision ==
    \A p \in Procs :
        (phase[Leader] = "committed" /\ alive[p]) ~>
            (phase[p] = "decided" \/ ~alive[p])

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => NoRegression
THEOREM Spec => EventualDecision /\ Termination /\ CommitLeadsToDecision
=============================================================================