------------------------------ MODULE RingLeaderElection ------------------------------
(***************************************************************************)
(* Chang-Roberts style leader election on a unidirectional ring.           *)
(*                                                                         *)
(* N processes 1..N are arranged in a logical ring. Process p sends only   *)
(* clockwise, to Succ(p). chan[p] is the FIFO link from Pred(p) to p, so   *)
(* it is the inbox of p. Links are reliable and FIFO, but delivery is      *)
(* asynchronous: a message stays in a link for an arbitrary number of      *)
(* steps until the Receive action fires.                                   *)
(*                                                                         *)
(* Any subset of processes may start an election concurrently (Initiate).  *)
(* Elect messages carry identifiers. On receipt a process does one of:     *)
(*   - forward the message, when the identifier is larger than its own;    *)
(*   - replace it with its own identifier, when the identifier is smaller  *)
(*     and the process is still idle;                                      *)
(*   - drop it, when the identifier is smaller and the process is already  *)
(*     participating, or when the process has already decided;             *)
(*   - declare itself leader, when its own identifier comes back.          *)
(* The leader then circulates a "leader" announcement, so that every       *)
(* process learns the leader. The announcement stops when it returns to    *)
(* the leader.                                                             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS N,     \* number of processes in the ring
          Id     \* Id[p] is the integer identifier of process p

ASSUME NAssumption  == N \in Nat /\ N >= 1

Proc == 1..N

ASSUME IdAssumption ==
    /\ Id \in [Proc -> Nat \ {0}]
    /\ \A p, q \in Proc : p # q => Id[p] # Id[q]   \* identifiers are unique

Ids   == {Id[p] : p \in Proc}
MaxId == CHOOSE m \in Ids : \A x \in Ids : m >= x

Succ(p) == IF p = N THEN 1 ELSE p + 1

Origin(v) == CHOOSE q \in Proc : Id[q] = v

States == {"idle", "participant", "leader", "decided"}

Msg == [type : {"elect", "leader"}, id : Ids]

VARIABLES state,      \* local state of each process
          leaderId,   \* identifier of the leader known to each process; 0 = unknown
          chan,       \* chan[p]: FIFO queue of messages in flight from Pred(p) to p
          initiated,  \* set of processes that spontaneously started an election
          declared    \* history: identifiers that have ever been declared leader

vars == <<state, leaderId, chan, initiated, declared>>

---------------------------------------------------------------------------------------
TypeOK ==
    /\ state     \in [Proc -> States]
    /\ leaderId  \in [Proc -> Ids \cup {0}]
    /\ chan      \in [Proc -> Seq(Msg)]
    /\ initiated \subseteq Proc
    /\ declared  \subseteq Ids

Init ==
    /\ state     = [p \in Proc |-> "idle"]
    /\ leaderId  = [p \in Proc |-> 0]
    /\ chan      = [p \in Proc |-> <<>>]
    /\ initiated = {}
    /\ declared  = {}

\* Remove the head of p's inbox, then append m to the outgoing link of p.
\* Writing it in two steps keeps the update correct when N = 1 (Succ(p) = p).
PopAndSend(p, m) ==
    LET c1 == [chan EXCEPT ![p] = Tail(@)]
    IN  [c1 EXCEPT ![Succ(p)] = Append(@, m)]

Pop(p) == [chan EXCEPT ![p] = Tail(@)]

---------------------------------------------------------------------------------------
(* A process starts an election spontaneously. *)
Initiate(p) ==
    /\ state[p] = "idle"
    /\ state'     = [state EXCEPT ![p] = "participant"]
    /\ chan'      = [chan EXCEPT ![Succ(p)] = Append(@, [type |-> "elect", id |-> Id[p]])]
    /\ initiated' = initiated \cup {p}
    /\ UNCHANGED <<leaderId, declared>>

(* Processing an elect message carrying identifier v at process p. *)
RecvElect(p, v) ==
    CASE state[p] \in {"leader", "decided"} ->           \* stale message: drop
            /\ chan' = Pop(p)
            /\ UNCHANGED <<state, leaderId, initiated, declared>>
      [] v > Id[p] ->                                    \* forward
            /\ state' = [state EXCEPT ![p] = "participant"]
            /\ chan'  = PopAndSend(p, [type |-> "elect", id |-> v])
            /\ UNCHANGED <<leaderId, initiated, declared>>
      [] v < Id[p] /\ state[p] = "idle" ->               \* replace with own identifier
            /\ state' = [state EXCEPT ![p] = "participant"]
            /\ chan'  = PopAndSend(p, [type |-> "elect", id |-> Id[p]])
            /\ UNCHANGED <<leaderId, initiated, declared>>
      [] v < Id[p] ->                                    \* participant: drop (swallow)
            /\ chan' = Pop(p)
            /\ UNCHANGED <<state, leaderId, initiated, declared>>
      [] OTHER ->                                        \* v = Id[p]: become leader
            /\ state'    = [state EXCEPT ![p] = "leader"]
            /\ leaderId' = [leaderId EXCEPT ![p] = Id[p]]
            /\ declared' = declared \cup {Id[p]}
            /\ chan'     = PopAndSend(p, [type |-> "leader", id |-> Id[p]])
            /\ UNCHANGED initiated

(* Processing a leader announcement carrying identifier v at process p. *)
RecvLeader(p, v) ==
    IF v = Id[p]
    THEN /\ chan' = Pop(p)                               \* announcement completed the ring
         /\ UNCHANGED <<state, leaderId, initiated, declared>>
    ELSE /\ state'    = [state EXCEPT ![p] = "decided"]
         /\ leaderId' = [leaderId EXCEPT ![p] = v]
         /\ chan'     = PopAndSend(p, [type |-> "leader", id |-> v])
         /\ UNCHANGED <<initiated, declared>>

(* Asynchronous, FIFO delivery of the head of p's inbox. *)
Receive(p) ==
    /\ chan[p] # <<>>
    /\ LET m == Head(chan[p])
       IN  IF m.type = "elect" THEN RecvElect(p, m.id) ELSE RecvLeader(p, m.id)

Next == \E p \in Proc : Initiate(p) \/ Receive(p)

(* Message delivery is weakly fair. Initiation is not forced: any subset of *)
(* processes, possibly empty, may initiate.                                 *)
Fairness == \A p \in Proc : WF_vars(Receive(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------------
(*************************** Safety invariants ****************************)

\* At most one process is ever declared leader (declared is a history variable).
AtMostOneLeader ==
    /\ Cardinality(declared) <= 1
    /\ \A p, q \in Proc : state[p] = "leader" /\ state[q] = "leader" => p = q

\* Validity: every declared or known leader identifier belongs to some process.
Validity ==
    /\ declared \subseteq Ids
    /\ \A p \in Proc : leaderId[p] # 0 => \E q \in Proc : Id[q] = leaderId[p]

\* The elected leader is the process with the maximum identifier.
LeaderIsMax ==
    /\ declared \subseteq {MaxId}
    /\ \A p \in Proc : state[p] = "leader" => Id[p] = MaxId

\* A process knows a leader only after it has decided or become leader,
\* and the leader it knows is the maximum.
DecidedConsistent ==
    \A p \in Proc :
        /\ (state[p] \in {"leader", "decided"}) <=> (leaderId[p] # 0)
        /\ leaderId[p] # 0 => leaderId[p] = MaxId

\* Leader announcements in flight always carry the maximum identifier.
AnnouncementsCarryMax ==
    \A p \in Proc : \A i \in 1..Len(chan[p]) :
        chan[p][i].type = "leader" => chan[p][i].id = MaxId /\ MaxId \in declared

(* Progress invariant: an elect message carrying v that is in flight to p has   *)
(* been forwarded only by processes with smaller identifiers. These are the     *)
(* processes strictly between Origin(v) and p, going clockwise. Each hop        *)
(* therefore makes strict progress around the ring toward Origin(v).            *)
Dist(a, b)  == IF a = b THEN N ELSE (b - a) % N
Between(a, b) == {q \in Proc : (q - a) % N > 0 /\ (q - a) % N < Dist(a, b)}

ElectProgress ==
    \A p \in Proc : \A i \in 1..Len(chan[p]) :
        chan[p][i].type = "elect" =>
            \A q \in Between(Origin(chan[p][i].id), p) : Id[q] < chan[p][i].id

\* At most one copy of each message exists in the whole system, so the number
\* of in-flight messages is bounded by 2 * N.
InFlightCount(m) ==
    LET Cnt(p) == Cardinality({i \in 1..Len(chan[p]) : chan[p][i] = m})
        RECURSIVE SumOver(_)
        SumOver(S) == IF S = {} THEN 0
                      ELSE LET x == CHOOSE x \in S : TRUE IN Cnt(x) + SumOver(S \ {x})
    IN SumOver(Proc)

UniqueMessages == \A m \in Msg : InFlightCount(m) <= 1

\* Only processes that initiated, or were woken by a message, are non-idle.
InitiatorsParticipate == \A p \in initiated : state[p] # "idle"

Invariants ==
    /\ TypeOK
    /\ AtMostOneLeader
    /\ Validity
    /\ LeaderIsMax
    /\ DecidedConsistent
    /\ AnnouncementsCarryMax
    /\ ElectProgress
    /\ UniqueMessages
    /\ InitiatorsParticipate

(************** Monotonic progress (action / temporal safety) **************)
Rank(s) == CASE s = "idle" -> 0 [] s = "participant" -> 1 [] OTHER -> 2

StateMonotone     == [][\A p \in Proc : Rank(state'[p]) >= Rank(state[p])]_vars
LeaderIdStable    == [][\A p \in Proc : leaderId[p] # 0 => leaderId'[p] = leaderId[p]]_vars
InitiatedMonotone == [][initiated \subseteq initiated']_vars
DeclaredMonotone  == [][declared \subseteq declared']_vars
\* Once some process has decided, no process ever becomes leader again.
NoSecondLeader    == [][(declared # {}) => (declared' = declared)]_vars

---------------------------------------------------------------------------------------
(*************************** Liveness properties ***************************)

\* Stable final configuration: exactly one leader, all others decided and
\* aware of it, and no messages in flight.
Elected ==
    /\ \E l \in Proc :
         /\ state[l] = "leader"
         /\ \A q \in Proc : leaderId[q] = Id[l]
         /\ \A q \in Proc \ {l} : state[q] = "decided"
    /\ \A p \in Proc : chan[p] = <<>>

\* Eventual leader election once at least one process has initiated.
EventualLeaderElection == (initiated # {}) ~> Elected

\* The elected configuration is reached and then remains forever.
StableElection == (initiated # {}) ~> []Elected

\* Termination of each election instance: every injected message is
\* eventually processed and no longer in flight.
InFlight(m) == \E p \in Proc : \E i \in 1..Len(chan[p]) : chan[p][i] = m

MessageTermination ==
    \A t \in {"elect", "leader"} : \A v \in Ids :
        InFlight([type |-> t, id |-> v]) ~> ~InFlight([type |-> t, id |-> v])

\* Every initiator eventually learns the leader.
InitiatorsLearnLeader ==
    \A p \in Proc : (p \in initiated) ~> (leaderId[p] = MaxId)

---------------------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => StateMonotone /\ LeaderIdStable /\ InitiatedMonotone
                /\ DeclaredMonotone /\ NoSecondLeader
THEOREM Spec => EventualLeaderElection /\ StableElection
                /\ MessageTermination /\ InitiatorsLearnLeader
=======================================================================================