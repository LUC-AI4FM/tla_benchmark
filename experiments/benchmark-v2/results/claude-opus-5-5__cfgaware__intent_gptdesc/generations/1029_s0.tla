------------------------------ MODULE RingLeaderElection ------------------------------
(***************************************************************************)
(* Chang-Roberts style leader election on a unidirectional ring.           *)
(*                                                                         *)
(* N processes, numbered 1..N, sit on a logical ring.  Process p sends     *)
(* only to its clockwise successor Succ(p).  Each link is a reliable FIFO  *)
(* channel with arbitrary delay.  chan[p] holds the messages in flight on  *)
(* the link that ends at p.                                                *)
(*                                                                         *)
(* A nonempty set of initiators is chosen nondeterministically, so any     *)
(* subset of processes may start an election concurrently.                *)
(*                                                                         *)
(* Election rules, when process p receives <<"elect", j>>:                 *)
(*   - j > Id[p]: forward j. If p was idle, p becomes a participant.       *)
(*   - j < Id[p]: if p is idle, p becomes a participant and sends its own  *)
(*                id. Otherwise p drops the message.                       *)
(*   - j = Id[p]: p declares itself leader and sends <<"leader", j>>.      *)
(*                                                                         *)
(* When a non-leader receives <<"leader", v>>, it records v, becomes       *)
(* decided, and forwards the message.  When the leader gets its own        *)
(* announcement back, it consumes the message and the protocol is over.    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

VARIABLES
    state,       \* state[p] \in {"idle","participant","leader","decided"}
    leaderId,    \* leaderId[p] is the leader id known to p (0 = unknown)
    chan,        \* chan[p] is the FIFO queue on the link Pred(p) -> p
    initiators,  \* nonempty set of processes allowed to start an election
    initiated    \* set of processes that actually started an election

vars == <<state, leaderId, chan, initiators, initiated>>

Procs == 1..N

\* Distinct integer identifiers, given as a permutation of 1..N.
Id == [p \in Procs |-> N + 1 - p]

IdSet == {Id[p] : p \in Procs}

MaxId == CHOOSE v \in IdSet : \A w \in IdSet : v >= w

Succ(p) == IF p = N THEN 1 ELSE p + 1

States == {"idle", "participant", "leader", "decided"}

Msg == [type : {"elect", "leader"}, id : IdSet]

ElectMsg(v)  == [type |-> "elect",  id |-> v]
LeaderMsg(v) == [type |-> "leader", id |-> v]

\* Send message m from p to Succ(p), using channel function c.
SendOn(c, p, m) == [c EXCEPT ![Succ(p)] = Append(@, m)]

-----------------------------------------------------------------------------
TypeOK ==
    /\ state \in [Procs -> States]
    /\ leaderId \in [Procs -> 0..N]
    /\ chan \in [Procs -> Seq(Msg)]
    /\ initiators \subseteq Procs
    /\ initiators # {}
    /\ initiated \subseteq Procs

Init ==
    /\ state = [p \in Procs |-> "idle"]
    /\ leaderId = [p \in Procs |-> 0]
    /\ chan = [p \in Procs |-> << >>]
    /\ initiators \in SUBSET Procs \ {{}}
    /\ initiated = {}

-----------------------------------------------------------------------------
(* An idle initiator starts an election by sending its own identifier.    *)
Start(p) ==
    /\ p \in initiators
    /\ state[p] = "idle"
    /\ state' = [state EXCEPT ![p] = "participant"]
    /\ initiated' = initiated \cup {p}
    /\ chan' = SendOn(chan, p, ElectMsg(Id[p]))
    /\ UNCHANGED <<leaderId, initiators>>

(* Process p handles the message at the head of its incoming channel.     *)
Receive(p) ==
    /\ chan[p] # << >>
    /\ LET m    == Head(chan[p])
           rest == [chan EXCEPT ![p] = Tail(@)]
       IN
       IF m.type = "elect" THEN
          CASE m.id > Id[p] ->
                 /\ chan' = SendOn(rest, p, m)
                 /\ state' = IF state[p] = "idle"
                               THEN [state EXCEPT ![p] = "participant"]
                               ELSE state
                 /\ UNCHANGED leaderId
            [] m.id < Id[p] /\ state[p] = "idle" ->
                 /\ chan' = SendOn(rest, p, ElectMsg(Id[p]))
                 /\ state' = [state EXCEPT ![p] = "participant"]
                 /\ UNCHANGED leaderId
            [] m.id < Id[p] /\ state[p] # "idle" ->
                 /\ chan' = rest
                 /\ UNCHANGED <<state, leaderId>>
            [] m.id = Id[p] ->
                 /\ chan' = SendOn(rest, p, LeaderMsg(Id[p]))
                 /\ state' = [state EXCEPT ![p] = "leader"]
                 /\ leaderId' = [leaderId EXCEPT ![p] = Id[p]]
       ELSE \* m.type = "leader"
          IF m.id = Id[p]
            THEN /\ chan' = rest     \* announcement completed the ring
                 /\ UNCHANGED <<state, leaderId>>
            ELSE /\ chan' = SendOn(rest, p, m)
                 /\ state' = [state EXCEPT ![p] = "decided"]
                 /\ leaderId' = [leaderId EXCEPT ![p] = m.id]
    /\ UNCHANGED <<initiators, initiated>>

(* The protocol has finished. Stuttering is allowed so that the final     *)
(* state is not reported as a deadlock.                                   *)
Terminated ==
    /\ \A p \in Procs : chan[p] = << >>
    /\ \A p \in Procs : state[p] \in {"leader", "decided"}
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Start(p) \/ Receive(p)
    \/ Terminated

Fairness ==
    \A p \in Procs : WF_vars(Start(p)) /\ WF_vars(Receive(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(*************************** Safety / Invariants ***************************)

\* Safety: at most one process is ever declared leader.
AtMostOneLeader ==
    \A p, q \in Procs : (state[p] = "leader" /\ state[q] = "leader") => p = q

\* Validity: every declared or known leader id belongs to some process.
Validity ==
    \A p \in Procs :
        /\ state[p] = "leader" => leaderId[p] = Id[p]
        /\ state[p] \in {"leader", "decided"} => leaderId[p] \in IdSet

\* The elected leader is always the process with the maximum identifier.
LeaderIsMax ==
    \A p \in Procs : state[p] = "leader" => Id[p] = MaxId

\* All decided processes agree on the leader.
Agreement ==
    \A p \in Procs : state[p] = "decided" => leaderId[p] = MaxId

\* Progress invariants.

\* Only initiators start elections, and an initiator is never idle again.
InitiatedOK ==
    /\ initiated \subseteq initiators
    /\ \A p \in initiated : state[p] # "idle"

\* An elect message carries the id of a process that has joined the election.
ElectMsgsFromParticipants ==
    \A p \in Procs : \A i \in 1..Len(chan[p]) :
        chan[p][i].type = "elect" =>
            \E q \in Procs : Id[q] = chan[p][i].id /\ state[q] # "idle"

\* A leader announcement exists only after its originator became leader.
LeaderMsgsJustified ==
    \A p \in Procs : \A i \in 1..Len(chan[p]) :
        chan[p][i].type = "leader" =>
            \E q \in Procs : Id[q] = chan[p][i].id /\ state[q] = "leader"

\* A decided process implies a leader exists.
DecidedImpliesLeader ==
    (\E p \in Procs : state[p] = "decided") =>
        (\E q \in Procs : state[q] = "leader")

\* Some election activity has begun whenever a message is in flight.
MessagesImplyInitiation ==
    (\E p \in Procs : chan[p] # << >>) => initiated # {}

Correctness ==
    /\ AtMostOneLeader
    /\ Validity
    /\ LeaderIsMax
    /\ Agreement
    /\ InitiatedOK
    /\ ElectMsgsFromParticipants
    /\ LeaderMsgsJustified
    /\ DecidedImpliesLeader
    /\ MessagesImplyInitiation

-----------------------------------------------------------------------------
(********************** Monotonic progress (actions) ***********************)

Rank(s) == CASE s = "idle"        -> 0
             [] s = "participant" -> 1
             [] s = "decided"     -> 2
             [] s = "leader"      -> 2

\* No process ever moves back to an earlier phase, the set of initiated
\* processes only grows, and a known leader id never changes.
MonotonicProgress ==
    [][ /\ \A p \in Procs : Rank(state'[p]) >= Rank(state[p])
        /\ \A p \in Procs : state[p] = "leader" => state'[p] = "leader"
        /\ initiated \subseteq initiated'
        /\ \A p \in Procs : leaderId[p] # 0 => leaderId'[p] = leaderId[p]
      ]_vars

-----------------------------------------------------------------------------
(******************************* Liveness **********************************)

StableElected ==
    \E p \in Procs :
        /\ state[p] = "leader"
        /\ \A q \in Procs :
             /\ state[q] \in {"leader", "decided"}
             /\ leaderId[q] = Id[p]
             /\ (q # p => state[q] = "decided")

AllMessagesProcessed == \A p \in Procs : chan[p] = << >>

\* Eventually there is exactly one leader, every process knows it, and
\* every message injected for the election has been processed.
EventualLeader == <>[]StableElected

ElectionTerminates == <>[]AllMessagesProcessed

\* Each message at the head of a channel is eventually consumed.
EachMessageProcessed ==
    \A p \in Procs : [](chan[p] # << >> => <>(chan[p] = << >>))

Liveness ==
    /\ EventualLeader
    /\ ElectionTerminates
    /\ EachMessageProcessed

THEOREM Spec => []TypeOK /\ []Correctness /\ MonotonicProgress /\ Liveness
=============================================================================