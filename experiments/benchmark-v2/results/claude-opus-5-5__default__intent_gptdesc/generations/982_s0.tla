---------------------------- MODULE PhasedGraphBFS ----------------------------
(***************************************************************************)
(* A fixed set of processes sits on the vertices of a finite undirected   *)
(* graph. They communicate only with neighbours, over reliable channels   *)
(* with arbitrary delay. Delivered messages are buffered in per-process    *)
(* mailboxes.                                                              *)
(*                                                                         *)
(* A synchronous, phase-based (round-based) computation is simulated on    *)
(* top of the asynchronous network. In phase k, every process:             *)
(*   1. sends one phase-k message to each neighbour, in any order and      *)
(*      concurrently with the other processes;                             *)
(*   2. waits until its mailbox holds a phase-k message from every         *)
(*      neighbour;                                                         *)
(*   3. performs a local update and moves to phase k+1.                    *)
(*                                                                         *)
(* The local rule is a self-stabilising BFS spanning-forest computation:   *)
(*   - the root sets dist = 0;                                             *)
(*   - every other node sets dist = min(Cap, min over neighbours of d+1);  *)
(*   - every other node picks as parent a neighbour that reported          *)
(*     d = dist-1, or None when dist = Cap (unreachable).                  *)
(* Local states (dist, parent) may start out arbitrary.                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,       \* finite set of processes (graph vertices)
    Adj,        \* edge relation: a set of ordered pairs, symmetric
    Root,       \* source process
    MaxPhase,   \* bound on the number of simulated phases
    None        \* "no parent" marker

ASSUME /\ IsFiniteSet(Proc)
       /\ Proc # {}
       /\ Root \in Proc
       /\ Adj \subseteq Proc \X Proc
       /\ \A e \in Adj : e[1] # e[2]                  \* no self loops
       /\ \A e \in Adj : <<e[2], e[1]>> \in Adj       \* undirected
       /\ MaxPhase \in Nat
       /\ None \notin Proc

Nbrs(p) == {q \in Proc : <<p, q>> \in Adj}
Cap     == Cardinality(Proc)          \* "infinity" for distances
Min(S)  == CHOOSE x \in S : \A y \in S : x <= y

Msg == [src : Proc, dst : Proc, ph : 0..MaxPhase, d : 0..Cap]

VARIABLES
    phase,    \* phase[p]   : current logical phase of p
    sentTo,   \* sentTo[p]  : neighbours already sent the phase[p] message
    dist,     \* dist[p]    : local distance estimate
    parent,   \* parent[p]  : chosen parent, or None
    chan,     \* set of messages in transit
    mbox,     \* mbox[p]    : delivered but not yet consumed messages
    rcvd,     \* ghost: rcvd[p] = messages consumed by p
    sentLog,  \* ghost: every message ever sent
    hist      \* ghost: hist[p][k] = dist[p] held during phase k

vars == <<phase, sentTo, dist, parent, chan, mbox, rcvd, sentLog, hist>>

-----------------------------------------------------------------------------
(* Graph-level reference outcome: BFS distances from Root *)

Layer[k \in 0..Cap] ==
    IF k = 0 THEN {Root}
    ELSE Layer[k-1] \cup {q \in Proc : \E r \in Layer[k-1] : q \in Nbrs(r)}

BFSDist(p) ==
    IF \E k \in 0..Cap : p \in Layer[k]
    THEN Min({k \in 0..Cap : p \in Layer[k]})
    ELSE Cap

-----------------------------------------------------------------------------
(* Initial state: arbitrary local states, empty network *)

Init ==
    /\ phase   = [p \in Proc |-> 0]
    /\ sentTo  = [p \in Proc |-> {}]
    /\ dist    \in [Proc -> 0..Cap]
    /\ parent  \in [Proc -> Proc \cup {None}]
    /\ chan    = {}
    /\ mbox    = [p \in Proc |-> {}]
    /\ rcvd    = [p \in Proc |-> {}]
    /\ sentLog = {}
    /\ hist    = [p \in Proc |-> [k \in 0..MaxPhase |->
                                    IF k = 0 THEN dist[p] ELSE 0]]

-----------------------------------------------------------------------------
(* Actions *)

\* p sends its phase message to one neighbour q.
CanSend(p, q) == /\ phase[p] < MaxPhase
                 /\ q \in Nbrs(p) \ sentTo[p]

SendTo(p, q) ==
    /\ CanSend(p, q)
    /\ LET m == [src |-> p, dst |-> q, ph |-> phase[p], d |-> dist[p]]
       IN /\ chan'    = chan \cup {m}
          /\ sentLog' = sentLog \cup {m}
    /\ sentTo' = [sentTo EXCEPT ![p] = @ \cup {q}]
    /\ UNCHANGED <<phase, dist, parent, mbox, rcvd, hist>>

\* Reliable, arbitrarily delayed delivery into the destination mailbox.
Deliver(m) ==
    /\ m \in chan
    /\ chan' = chan \ {m}
    /\ mbox' = [mbox EXCEPT ![m.dst] = @ \cup {m}]
    /\ UNCHANGED <<phase, sentTo, dist, parent, rcvd, sentLog, hist>>

\* Inbound messages for p's current phase.
PhaseMsgs(p) == {m \in mbox[p] : m.ph = phase[p]}

CanComplete(p) ==
    /\ phase[p] < MaxPhase
    /\ sentTo[p] = Nbrs(p)
    /\ {m.src : m \in PhaseMsgs(p)} = Nbrs(p)

\* Local computation that ends the phase.
Complete(p) ==
    /\ CanComplete(p)
    /\ LET M     == PhaseMsgs(p)
           nd    == IF p = Root THEN 0
                    ELSE Min({m.d + 1 : m \in M} \cup {Cap})
           cands == {m \in M : m.d + 1 = nd}
           np    == IF p = Root \/ nd = Cap \/ cands = {}
                    THEN None
                    ELSE (CHOOSE m \in cands : TRUE).src
       IN /\ dist'   = [dist   EXCEPT ![p] = nd]
          /\ parent' = [parent EXCEPT ![p] = np]
          /\ mbox'   = [mbox   EXCEPT ![p] = @ \ M]
          /\ rcvd'   = [rcvd   EXCEPT ![p] = @ \cup M]
          /\ hist'   = [hist   EXCEPT ![p][phase[p] + 1] = nd]
    /\ phase'  = [phase  EXCEPT ![p] = @ + 1]
    /\ sentTo' = [sentTo EXCEPT ![p] = {}]
    /\ UNCHANGED <<chan, sentLog>>

\* Explicit stuttering once the bounded run has finished.
Done == /\ \A p \in Proc : phase[p] = MaxPhase
        /\ chan = {}
        /\ UNCHANGED vars

Next ==
    \/ \E p \in Proc : \E q \in Nbrs(p) : SendTo(p, q)
    \/ \E m \in chan : Deliver(m)
    \/ \E p \in Proc : Complete(p)
    \/ Done

Fairness ==
    /\ \A p \in Proc : \A q \in Nbrs(p) : WF_vars(SendTo(p, q))
    /\ \A m \in Msg : WF_vars(Deliver(m))
    /\ \A p \in Proc : WF_vars(Complete(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ phase   \in [Proc -> 0..MaxPhase]
    /\ \A p \in Proc : sentTo[p] \subseteq Nbrs(p)
    /\ dist    \in [Proc -> 0..Cap]
    /\ parent  \in [Proc -> Proc \cup {None}]
    /\ chan    \subseteq Msg
    /\ mbox    \in [Proc -> SUBSET Msg]
    /\ rcvd    \in [Proc -> SUBSET Msg]
    /\ sentLog \subseteq Msg
    /\ hist    \in [Proc -> [0..MaxPhase -> 0..Cap]]

InMbox == UNION {mbox[p] : p \in Proc}
InRcvd == UNION {rcvd[p] : p \in Proc}

\* Messages travel only along edges; mailboxes hold only neighbour messages.
MailboxFromNeighbours ==
    /\ \A p \in Proc : \A m \in mbox[p] : m.dst = p /\ m.src \in Nbrs(p)
    /\ \A m \in chan : m.src \in Nbrs(m.dst)

\* Message contents agree with the sender's state in the phase it was sent.
MsgConsistent ==
    \A m \in chan \cup InMbox :
        /\ m.d = hist[m.src][m.ph]
        /\ m.ph \in {phase[m.src] - 1, phase[m.src]}
        /\ (m.ph = phase[m.src]) => (m.d = dist[m.src] /\ m.dst \in sentTo[m.src])
        /\ m.ph \in {phase[m.dst], phase[m.dst] + 1}

\* No duplication: each (src, dst, phase) is sent once and sits in exactly
\* one place: in transit, in a mailbox, or consumed.
NoDuplication ==
    /\ \A m1, m2 \in sentLog :
         (m1.src = m2.src /\ m1.dst = m2.dst /\ m1.ph = m2.ph) => m1 = m2
    /\ chan \cap InMbox = {}
    /\ chan \cap InRcvd = {}
    /\ InMbox \cap InRcvd = {}
    /\ chan \cup InMbox \cup InRcvd = sentLog

\* Local and edge states never contradict: a process that adopted a parent
\* in a phase must have received that parent's corresponding message.
ParentJustified ==
    \A p \in Proc :
        (phase[p] > 0 /\ parent[p] # None) =>
            /\ parent[p] \in Nbrs(p)
            /\ \E m \in rcvd[p] : /\ m.src = parent[p]
                                  /\ m.ph = phase[p] - 1
                                  /\ m.d + 1 = dist[p]

\* The synchronizer keeps neighbouring phases within one of each other.
PhaseSynchrony ==
    \A p \in Proc : \A q \in Nbrs(p) :
        phase[p] <= phase[q] + 1 /\ phase[q] <= phase[p] + 1

\* No global deadlock: until the run is finished, some step can be taken.
NoDeadlock ==
    (\E p \in Proc : phase[p] < MaxPhase) =>
        \/ \E p \in Proc : \E q \in Nbrs(p) : CanSend(p, q)
        \/ chan # {}
        \/ \E p \in Proc : CanComplete(p)

\* After Cap phases, every local estimate equals the true BFS distance,
\* even when the initial state was arbitrary.
StabilisedDist ==
    \A p \in Proc : phase[p] >= Cap => dist[p] = BFSDist(p)

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Every sent message is eventually delivered.
EventualDelivery ==
    \A m \in Msg : (m \in chan) ~> (m \in mbox[m.dst] \/ m \in rcvd[m.dst])

\* Every process eventually advances beyond any given phase.
PhaseProgress ==
    \A p \in Proc : \A k \in 0..(MaxPhase - 1) : <>(phase[p] > k)

AllFinish == <>[](\A p \in Proc : phase[p] = MaxPhase)

\* The intended outcome: a BFS spanning forest rooted at Root, with
\* unreachable vertices marked Cap and parentless.
StableBFS ==
    \A p \in Proc :
        /\ dist[p] = BFSDist(p)
        /\ (p = Root \/ dist[p] = Cap) => parent[p] = None
        /\ (p # Root /\ dist[p] < Cap) =>
              /\ parent[p] \in Nbrs(p)
              /\ BFSDist(parent[p]) = dist[p] - 1

EventuallyStable ==
    (MaxPhase > Cap) => <>[](StableBFS)

=============================================================================