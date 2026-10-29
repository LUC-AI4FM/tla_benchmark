---------------------------- MODULE PhasedGraphBFS ----------------------------
(***************************************************************************)
(* A phase-based (synchronizer-style) distributed BFS / spanning-forest   *)
(* construction over an asynchronous, reliable, arbitrarily delaying       *)
(* network. Processes occupy the vertices of a fixed undirected graph and *)
(* communicate only with neighbors. In every logical phase, a process     *)
(* sends its current distance estimate to every neighbor, waits until it  *)
(* has a phase-tagged message from each neighbor in its mailbox, updates  *)
(* its distance and parent, and advances to the next phase. Sources begin *)
(* at distance 0. The result is a BFS spanning forest rooted at sources.  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

\* ---------------- Fixed finite graph (no external constants) -------------
Procs   == 1..4
Edges   == { {1,2}, {2,3}, {3,4}, {1,3} }
Sources == {1}

Nbr(p)   == { q \in Procs : {p, q} \in Edges }
MaxPhase == Cardinality(Procs)          \* >= diameter, enough phases
Inf      == MaxPhase + 1                \* "unreached" distance
None     == 0                           \* no parent

Dist     == 0..Inf
Phases   == 0..MaxPhase

Msgs == [from : Procs, to : Procs, ph : 0..(MaxPhase - 1), d : Dist]

Min(a, b)  == IF a <= b THEN a ELSE b
MinSet(S)  == CHOOSE x \in S : \A y \in S : x <= y

VARIABLES
    phase,   \* phase[p] : current logical phase of p
    sent,    \* sent[p]  : has p sent its messages for the current phase
    dist,    \* dist[p]  : current distance estimate
    parent,  \* parent[p]: chosen parent in the spanning forest
    net,     \* set of in-flight messages (reliable, arbitrary delay)
    mbox     \* mbox[p]  : delivered but not yet consumed messages

vars == << phase, sent, dist, parent, net, mbox >>

-----------------------------------------------------------------------------
Init ==
    /\ phase  = [p \in Procs |-> 0]
    /\ sent   = [p \in Procs |-> FALSE]
    /\ dist   = [p \in Procs |-> IF p \in Sources THEN 0 ELSE Inf]
    /\ parent = [p \in Procs |-> IF p \in Sources THEN p ELSE None]
    /\ net    = {}
    /\ mbox   = [p \in Procs |-> {}]

\* p sends its phase-tagged state to all neighbors (once per phase)
Send(p) ==
    /\ phase[p] < MaxPhase
    /\ ~sent[p]
    /\ net' = net \cup
              { [from |-> p, to |-> q, ph |-> phase[p], d |-> dist[p]] : q \in Nbr(p) }
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ UNCHANGED << phase, dist, parent, mbox >>

\* the network delivers an in-flight message into the receiver's mailbox
Deliver(m) ==
    /\ m \in net
    /\ net'  = net \ {m}
    /\ mbox' = [mbox EXCEPT ![m.to] = @ \cup {m}]
    /\ UNCHANGED << phase, sent, dist, parent >>

Recv(p) == { m \in mbox[p] : m.ph = phase[p] }

Ready(p) ==
    /\ phase[p] < MaxPhase
    /\ sent[p]
    /\ \A q \in Nbr(p) : \E m \in Recv(p) : m.from = q

\* p consumes all phase messages, updates its state and advances
Advance(p) ==
    /\ Ready(p)
    /\ LET R    == Recv(p)
           best == MinSet({ Min(m.d + 1, Inf) : m \in R } \cup {dist[p]})
       IN  /\ dist' = [dist EXCEPT ![p] = best]
           /\ parent' = IF best < dist[p]
                          THEN [parent EXCEPT ![p] =
                                  CHOOSE q \in Nbr(p) :
                                    \E m \in R : m.from = q /\ m.d + 1 = best]
                          ELSE parent
           /\ mbox' = [mbox EXCEPT ![p] = @ \ R]
    /\ phase' = [phase EXCEPT ![p] = @ + 1]
    /\ sent'  = [sent EXCEPT ![p] = FALSE]
    /\ UNCHANGED net

Terminated ==
    /\ \A p \in Procs : phase[p] = MaxPhase
    /\ net = {}

\* explicit stuttering once the protocol has terminated (not a deadlock)
Done == Terminated /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Send(p) \/ Advance(p)
    \/ \E m \in net : Deliver(m)
    \/ Done

Fairness ==
    /\ \A p \in Procs : WF_vars(Send(p)) /\ WF_vars(Advance(p))
    /\ \A m \in Msgs  : WF_vars(Deliver(m))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* ------------------------------ Invariants --------------------------------
TypeOK ==
    /\ phase  \in [Procs -> Phases]
    /\ sent   \in [Procs -> BOOLEAN]
    /\ dist   \in [Procs -> Dist]
    /\ parent \in [Procs -> Procs \cup {None}]
    /\ net    \subseteq Msgs
    /\ mbox   \in [Procs -> SUBSET Msgs]

\* mailboxes and channels only carry messages along edges; parents are neighbors;
\* message contents are consistent with the sender's state; no duplication
NeighborInv ==
    /\ \A p \in Procs : \A m \in mbox[p] : m.to = p /\ m.from \in Nbr(p)
    /\ \A m \in net : m.from \in Nbr(m.to)
    /\ \A m \in net : \A p \in Procs : m \notin mbox[p]
    /\ \A m \in net \cup UNION { mbox[p] : p \in Procs } :
          /\ m.ph <= phase[m.from]
          /\ (m.ph = phase[m.from]) => sent[m.from]
          /\ dist[m.from] <= m.d
          /\ m.ph >= phase[m.to]
    /\ \A p \in Procs \ Sources :
          parent[p] # None =>
             /\ parent[p] \in Nbr(p)
             /\ dist[parent[p]] + 1 <= dist[p]
             /\ dist[p] < Inf
    /\ \A p \in Procs \ Sources : (parent[p] = None) <=> (dist[p] = Inf)

\* only initial sources are ever roots / at distance 0
NoNewSource ==
    \A p \in Procs \ Sources : dist[p] # 0 /\ parent[p] # p

\* no global deadlock: some process or the network can always act, or done
NoDeadlock ==
    \/ Terminated
    \/ \E p \in Procs : (phase[p] < MaxPhase /\ ~sent[p]) \/ Ready(p)
    \/ net # {}

\* intended graph-level outcome: a BFS spanning forest rooted at sources
StableOutcome ==
    /\ Terminated
    /\ \A p \in Sources : dist[p] = 0 /\ parent[p] = p
    /\ \A p \in Procs \ Sources :
          /\ dist[p] < Inf
          /\ parent[p] \in Nbr(p)
          /\ dist[p] = dist[parent[p]] + 1
          /\ \A q \in Nbr(p) : dist[p] <= dist[q] + 1

\* ------------------------------ Liveness ----------------------------------
EventualDelivery ==
    \A m \in Msgs : (m \in net) ~> (m \notin net)

PhaseProgress ==
    \A p \in Procs : \A k \in 0..(MaxPhase - 1) :
        (phase[p] = k) ~> (phase[p] > k)

Liveness ==
    /\ EventualDelivery
    /\ PhaseProgress
    /\ <>[]StableOutcome

=============================================================================