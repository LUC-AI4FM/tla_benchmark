------------------------------ MODULE RingLeaderElection ------------------------------
(***************************************************************************)
(* Asynchronous unidirectional ring leader election (LCR / Chang-Roberts). *)
(*                                                                         *)
(* Processes 0..N-1 are arranged in a ring. Process p sends only to its    *)
(* clockwise neighbour Succ(p). Each channel is a reliable FIFO queue:     *)
(* messages may be delayed arbitrarily but are never lost, duplicated or   *)
(* reordered. Any subset of the processes in Initiators may wake up and    *)
(* start an election, at any time, including concurrently. A process that  *)
(* receives an election message before waking up becomes a passive relay.  *)
(*                                                                         *)
(* Protocol:                                                               *)
(*  - An initiator sends <<elect, own id>> and becomes a candidate.        *)
(*  - On receiving <<elect, v>>:                                           *)
(*      v = own id (candidate) -> becomes leader, sends <<leader, v>>.     *)
(*      v > own id, or idle/relay -> forwards v and becomes a relay.       *)
(*      v < own id and candidate  -> discards the message.                 *)
(*  - On receiving <<leader, v>>: records v as the leader and forwards     *)
(*    it, unless v is its own id, in which case the message is absorbed.   *)
(*                                                                         *)
(* This model is crash-free, so every process is non-faulty.               *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    N,           \* number of processes in the ring
    Id,          \* Id[p] : unique numeric identifier of process p
    Initiators   \* the processes that may spontaneously start an election

Proc == 0 .. (N - 1)

ASSUME NAssump        == N \in Nat /\ N >= 1
ASSUME IdAssump       == /\ Id \in [Proc -> Nat]
                         /\ \A p, q \in Proc : p # q => Id[p] # Id[q]
ASSUME InitiatorsAssump == Initiators \subseteq Proc /\ Initiators # {}

None == -1                       \* "no leader known yet"

Succ(p) == (p + 1) % N           \* clockwise neighbour

NonFaulty == Proc                \* crash-free model: every process is non-faulty

States == {"idle", "candidate", "relay", "leader"}

Msgs == [type : {"elect", "leader"}, id : {Id[p] : p \in Proc}]

ElectMsg(v)  == [type |-> "elect",  id |-> v]
LeaderMsg(v) == [type |-> "leader", id |-> v]

MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

VARIABLES
    state,       \* state[p] \in States
    known,       \* known[p] : the leader id known by p, or None
    initiated,   \* initiated[p] : TRUE iff p started an election
    chan         \* chan[p] : FIFO queue of messages in transit to p

vars == << state, known, initiated, chan >>

(* Identifiers of the processes that participate as initiators *)
Participants == {q \in Proc : initiated[q]}
ParticipantIds == {Id[q] : q \in Participants}
MaxParticipant == MaxOf(ParticipantIds)

---------------------------------------------------------------------------------------
TypeOK ==
    /\ state     \in [Proc -> States]
    /\ known     \in [Proc -> {Id[p] : p \in Proc} \cup {None}]
    /\ initiated \in [Proc -> BOOLEAN]
    /\ chan      \in [Proc -> Seq(Msgs)]

Init ==
    /\ state     = [p \in Proc |-> "idle"]
    /\ known     = [p \in Proc |-> None]
    /\ initiated = [p \in Proc |-> FALSE]
    /\ chan      = [p \in Proc |-> << >>]

---------------------------------------------------------------------------------------
(* Process p spontaneously starts an election. Several may do so concurrently. *)
Initiate(p) ==
    /\ p \in Initiators
    /\ state[p] = "idle"
    /\ state'     = [state EXCEPT ![p] = "candidate"]
    /\ initiated' = [initiated EXCEPT ![p] = TRUE]
    /\ chan'      = [chan EXCEPT ![Succ(p)] = Append(@, ElectMsg(Id[p]))]
    /\ UNCHANGED known

(* Process p consumes the head of its incoming FIFO channel. *)
ReceiveElect(p) ==
    /\ chan[p] # << >>
    /\ Head(chan[p]).type = "elect"
    /\ LET v == Head(chan[p]).id IN
       IF v = Id[p]
       THEN \* own identifier returned: p wins
            /\ state' = [state EXCEPT ![p] = "leader"]
            /\ known' = [known EXCEPT ![p] = Id[p]]
            /\ chan'  = [chan EXCEPT ![p]       = Tail(@),
                                     ![Succ(p)] = Append(@, LeaderMsg(Id[p]))]
       ELSE IF v > Id[p] \/ state[p] \in {"idle", "relay"}
       THEN \* forward unchanged; p becomes (or stays) a relay
            /\ state' = [state EXCEPT ![p] = "relay"]
            /\ chan'  = [chan EXCEPT ![p]       = Tail(@),
                                     ![Succ(p)] = Append(@, ElectMsg(v))]
            /\ UNCHANGED known
       ELSE \* candidate with a larger id swallows the message
            /\ chan'  = [chan EXCEPT ![p] = Tail(@)]
            /\ UNCHANGED << state, known >>
    /\ UNCHANGED initiated

ReceiveLeader(p) ==
    /\ chan[p] # << >>
    /\ Head(chan[p]).type = "leader"
    /\ LET v == Head(chan[p]).id IN
       /\ known' = [known EXCEPT ![p] = v]
       /\ IF v = Id[p]
          THEN chan' = [chan EXCEPT ![p] = Tail(@)]       \* announcement completed the ring
          ELSE chan' = [chan EXCEPT ![p]       = Tail(@),
                                    ![Succ(p)] = Append(@, LeaderMsg(v))]
    /\ UNCHANGED << state, initiated >>

Receive(p) == ReceiveElect(p) \/ ReceiveLeader(p)

(* Explicit terminal stuttering, so that a finished run is not a deadlock. *)
Terminated ==
    /\ \A p \in Proc : chan[p] = << >>
    /\ \A p \in Initiators : state[p] # "idle"

Done == Terminated /\ UNCHANGED vars

Next ==
    \/ \E p \in Proc : Initiate(p) \/ Receive(p)
    \/ Done

(* Fairness: every process takes steps fairly. Each sent message is eventually *)
(* delivered: WF on Receive(p) together with FIFO channels guarantees this.     *)
Fairness ==
    /\ \A p \in Proc       : WF_vars(Receive(p))
    /\ \A p \in Initiators : WF_vars(Initiate(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------------
(*************************** SAFETY INVARIANTS ****************************)

(* At most one process ever decides that it is the leader. *)
AtMostOneLeader ==
    \A p, q \in Proc : (state[p] = "leader" /\ state[q] = "leader") => p = q

(* No two processes ever hold different leaders. *)
Agreement ==
    \A p, q \in Proc : (known[p] # None /\ known[q] # None) => known[p] = known[q]

(* The leader is the participant with the maximum identifier. *)
LeaderIsMax ==
    \A p \in Proc : state[p] = "leader" => /\ initiated[p]
                                           /\ Id[p] = MaxParticipant

(* Any known leader is the elected process with the maximum participating id. *)
KnownLeaderCorrect ==
    \A p \in Proc : known[p] # None =>
        /\ known[p] = MaxParticipant
        /\ \E l \in Proc : state[l] = "leader" /\ Id[l] = known[p]

(* Message integrity: identifiers are preserved and never invented. Every *)
(* election message carries the id of a real initiator, and every leader  *)
(* announcement carries the id of the actual leader.                      *)
MessageIntegrity ==
    \A p \in Proc : \A i \in 1 .. Len(chan[p]) :
        LET m == chan[p][i] IN
        /\ m \in Msgs
        /\ m.type = "elect"  => m.id \in ParticipantIds
        /\ m.type = "leader" => \E l \in Proc : state[l] = "leader" /\ Id[l] = m.id

(* Redundant/concurrent elections never produce conflicting announcements. *)
LeaderMsgsConsistent ==
    \A p, q \in Proc :
      \A i \in 1 .. Len(chan[p]) : \A j \in 1 .. Len(chan[q]) :
        (chan[p][i].type = "leader" /\ chan[q][j].type = "leader")
            => chan[p][i].id = chan[q][j].id

(* Only a candidate that started an election can become leader, and no process *)
(* that has relayed a larger id ever wins.                                     *)
RelayNeverWins ==
    \A p \in Proc : state[p] = "leader" =>
        \A q \in Participants : Id[q] <= Id[p]

(* Termination condition: once quiescent after some election started, every *)
(* non-faulty process knows the unique, maximal leader.                     *)
TerminationCorrect ==
    ((\A p \in Proc : chan[p] = << >>) /\ Participants # {})
        => /\ \E l \in Proc : state[l] = "leader"
           /\ \A p \in NonFaulty : known[p] = MaxParticipant

SafetyInv ==
    /\ TypeOK
    /\ AtMostOneLeader
    /\ Agreement
    /\ LeaderIsMax
    /\ KnownLeaderCorrect
    /\ MessageIntegrity
    /\ LeaderMsgsConsistent
    /\ RelayNeverWins
    /\ TerminationCorrect

(* Stability: decisions are never revoked. *)
LeaderStable ==
    [][\A p \in Proc : state[p] = "leader" => state'[p] = "leader"]_vars

KnownStable ==
    [][\A p \in Proc : known[p] # None => known'[p] = known[p]]_vars

(************************** LIVENESS PROPERTIES ***************************)

(* Eventually exactly one process decides it is the leader. *)
EventuallyLeader ==
    <>[](\E l \in Proc : /\ state[l] = "leader"
                         /\ \A q \in Proc : state[q] = "leader" => q = l)

(* Eventually the leader is known to every non-faulty process. *)
EventuallyAllKnow ==
    <>[](\E l \in Proc : /\ state[l] = "leader"
                         /\ \A p \in NonFaulty : known[p] = Id[l])

(* The protocol eventually terminates (quiescence). *)
EventuallyTerminates == <>Terminated

(* Every message sent is eventually delivered: each channel eventually empties. *)
MessagesDelivered ==
    \A p \in Proc : []<>(chan[p] = << >>)

THEOREM Spec => []SafetyInv
THEOREM Spec => LeaderStable /\ KnownStable
THEOREM Spec => EventuallyLeader /\ EventuallyAllKnow /\ EventuallyTerminates
=======================================================================================