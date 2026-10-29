------------------------------ MODULE GraphPruning ------------------------------
(***************************************************************************)
(* Distributed pruning of redundant vertices while preserving the         *)
(* connectivity of the active (spanning) subgraph and of the designated    *)
(* terminals.                                                              *)
(*                                                                         *)
(* Protocol overview (one "phase" = one pruning attempt of a node):        *)
(*  1. An active, idle, non-terminal node n becomes a CANDIDATE and sends  *)
(*     "request" to every neighbor it believes active (view[n]).           *)
(*  2. A neighbor q answers:                                               *)
(*       "gone"  if q is no longer active,                                 *)
(*       "grant" if q is active and idle. q then becomes LOCKED by n and   *)
(*               may not deactivate or grant to others until released,    *)
(*       "deny"  if q is active but is a candidate or already locked.      *)
(*  3. When all replies have arrived, n decides:                           *)
(*       - if any deny: abort, release grants, increment retry counter;    *)
(*       - else if the granting neighbors (all of n's active neighbors)    *)
(*         are nonempty and induce a connected subgraph, n deactivates     *)
(*         and sends "pruned" to them, which unlocks them;                 *)
(*       - otherwise abort, release grants, and mark itself done until    *)
(*         the neighborhood changes (a "pruned" notification).             *)
(* Channels are reliable FIFO queues per directed edge.                    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes,        \* set of processors
          Edges,        \* set of undirected edges, each a 2-element set
          Terminals,    \* designated terminals that must stay connected
          MaxRetries    \* bound on retries after contention (denials)

None == CHOOSE x : x \notin Nodes

Nbrs(n) == {m \in Nodes : {n, m} \in Edges}

RECURSIVE ReachFrom(_, _)
ReachFrom(S, R) ==
  LET R2 == R \cup {y \in S : \E x \in R : {x, y} \in Edges}
  IN  IF R2 = R THEN R ELSE ReachFrom(S, R2)

\* S induces a connected subgraph of the graph
Connected(S) == S = {} \/ \E x \in S : ReachFrom(S, {x}) = S

ASSUME /\ Edges \subseteq {{a, b} : a \in Nodes, b \in Nodes}
       /\ \A e \in Edges : Cardinality(e) = 2
       /\ Terminals \subseteq Nodes
       /\ Terminals # {}
       /\ MaxRetries \in Nat
       /\ Connected(Nodes)

Dir  == {<<p, q>> \in Nodes \X Nodes : {p, q} \in Edges}
Msgs == {"request", "grant", "deny", "gone", "release", "pruned"}

VARIABLES active,    \* active[n]: n has not been pruned
          status,    \* "idle" | "candidate" | "locked" | "pruned"
          lockedBy,  \* candidate that n granted to, or None
          view,      \* neighbors n believes to be active
          pending,   \* neighbors whose reply n still awaits
          grants,    \* neighbors that granted n's current request
          denied,    \* some neighbor denied n's current request
          done,      \* n found itself not prunable; waits for change
          retries,   \* number of contention-aborts of n
          chan       \* chan[<<p,q>>]: FIFO queue from p to q

vars == <<active, status, lockedBy, view, pending, grants, denied, done,
          retries, chan>>

ActiveSet == {n \in Nodes : active[n]}

Send(c, from, to, m) == [c EXCEPT ![<<from, to>>] = Append(@, m)]

SendAll(c, from, S, m) ==
  [e \in DOMAIN c |-> IF e[1] = from /\ e[2] \in S
                        THEN Append(c[e], m) ELSE c[e]]

TypeOK ==
  /\ active   \in [Nodes -> BOOLEAN]
  /\ status   \in [Nodes -> {"idle", "candidate", "locked", "pruned"}]
  /\ lockedBy \in [Nodes -> Nodes \cup {None}]
  /\ view     \in [Nodes -> SUBSET Nodes]
  /\ pending  \in [Nodes -> SUBSET Nodes]
  /\ grants   \in [Nodes -> SUBSET Nodes]
  /\ denied   \in [Nodes -> BOOLEAN]
  /\ done     \in [Nodes -> BOOLEAN]
  /\ retries  \in [Nodes -> Nat]
  /\ chan     \in [Dir -> Seq(Msgs)]

Init ==
  /\ active   = [n \in Nodes |-> TRUE]
  /\ status   = [n \in Nodes |-> "idle"]
  /\ lockedBy = [n \in Nodes |-> None]
  /\ view     = [n \in Nodes |-> Nbrs(n)]
  /\ pending  = [n \in Nodes |-> {}]
  /\ grants   = [n \in Nodes |-> {}]
  /\ denied   = [n \in Nodes |-> FALSE]
  /\ done     = [n \in Nodes |-> FALSE]
  /\ retries  = [n \in Nodes |-> 0]
  /\ chan     = [e \in Dir |-> <<>>]

-----------------------------------------------------------------------------
(* Precise condition under which a node may start a pruning phase. *)
CanStart(n) ==
  /\ active[n]
  /\ status[n] = "idle"
  /\ ~done[n]
  /\ n \notin Terminals
  /\ view[n] # {}
  /\ retries[n] <= MaxRetries

Start(n) ==
  /\ CanStart(n)
  /\ status'  = [status  EXCEPT ![n] = "candidate"]
  /\ pending' = [pending EXCEPT ![n] = view[n]]
  /\ grants'  = [grants  EXCEPT ![n] = {}]
  /\ denied'  = [denied  EXCEPT ![n] = FALSE]
  /\ chan'    = SendAll(chan, n, view[n], "request")
  /\ UNCHANGED <<active, lockedBy, view, done, retries>>

Decide(n) ==
  /\ status[n] = "candidate"
  /\ pending[n] = {}
  /\ IF denied[n]
       THEN \* contention: abort and possibly retry later
            /\ status'  = [status  EXCEPT ![n] = "idle"]
            /\ retries' = [retries EXCEPT ![n] = @ + 1]
            /\ chan'    = SendAll(chan, n, grants[n], "release")
            /\ UNCHANGED <<active, done>>
       ELSE IF grants[n] # {} /\ Connected(grants[n])
         THEN \* safe to deactivate: active neighbors stay connected
              /\ active' = [active EXCEPT ![n] = FALSE]
              /\ status' = [status EXCEPT ![n] = "pruned"]
              /\ done'   = [done   EXCEPT ![n] = TRUE]
              /\ chan'   = SendAll(chan, n, grants[n], "pruned")
              /\ UNCHANGED retries
         ELSE \* not redundant: abort until neighborhood changes
              /\ status' = [status EXCEPT ![n] = "idle"]
              /\ done'   = [done   EXCEPT ![n] = TRUE]
              /\ chan'   = SendAll(chan, n, grants[n], "release")
              /\ UNCHANGED <<active, retries>>
  /\ grants' = [grants EXCEPT ![n] = {}]
  /\ denied' = [denied EXCEPT ![n] = FALSE]
  /\ UNCHANGED <<lockedBy, view, pending>>

-----------------------------------------------------------------------------
(* Message reception: q receives the head of channel p -> q. *)
Rest(p, q) == [chan EXCEPT ![<<p, q>>] = Tail(@)]

HasMsg(p, q, m) == chan[<<p, q>>] # <<>> /\ Head(chan[<<p, q>>]) = m

RcvRequest(p, q) ==
  /\ HasMsg(p, q, "request")
  /\ IF ~active[q]
       THEN /\ chan' = Send(Rest(p, q), q, p, "gone")
            /\ UNCHANGED <<status, lockedBy>>
       ELSE IF status[q] = "idle"
         THEN /\ status'   = [status   EXCEPT ![q] = "locked"]
              /\ lockedBy' = [lockedBy EXCEPT ![q] = p]
              /\ chan'     = Send(Rest(p, q), q, p, "grant")
         ELSE /\ chan' = Send(Rest(p, q), q, p, "deny")
              /\ UNCHANGED <<status, lockedBy>>
  /\ UNCHANGED <<active, view, pending, grants, denied, done, retries>>

RcvGrant(p, q) ==
  /\ HasMsg(p, q, "grant")
  /\ chan'    = Rest(p, q)
  /\ grants'  = [grants  EXCEPT ![q] = @ \cup {p}]
  /\ pending' = [pending EXCEPT ![q] = @ \ {p}]
  /\ UNCHANGED <<active, status, lockedBy, view, denied, done, retries>>

RcvDeny(p, q) ==
  /\ HasMsg(p, q, "deny")
  /\ chan'    = Rest(p, q)
  /\ denied'  = [denied  EXCEPT ![q] = TRUE]
  /\ pending' = [pending EXCEPT ![q] = @ \ {p}]
  /\ UNCHANGED <<active, status, lockedBy, view, grants, done, retries>>

RcvGone(p, q) ==
  /\ HasMsg(p, q, "gone")
  /\ chan'    = Rest(p, q)
  /\ view'    = [view    EXCEPT ![q] = @ \ {p}]
  /\ pending' = [pending EXCEPT ![q] = @ \ {p}]
  /\ UNCHANGED <<active, status, lockedBy, grants, denied, done, retries>>

RcvRelease(p, q) ==
  /\ HasMsg(p, q, "release")
  /\ chan' = Rest(p, q)
  /\ IF lockedBy[q] = p
       THEN /\ status'   = [status   EXCEPT ![q] = "idle"]
            /\ lockedBy' = [lockedBy EXCEPT ![q] = None]
       ELSE UNCHANGED <<status, lockedBy>>
  /\ UNCHANGED <<active, view, pending, grants, denied, done, retries>>

RcvPruned(p, q) ==
  /\ HasMsg(p, q, "pruned")
  /\ chan' = Rest(p, q)
  /\ view' = [view EXCEPT ![q] = @ \ {p}]
  /\ done' = [done EXCEPT ![q] = FALSE]   \* neighborhood changed: re-evaluate
  /\ IF lockedBy[q] = p
       THEN /\ status'   = [status   EXCEPT ![q] = "idle"]
            /\ lockedBy' = [lockedBy EXCEPT ![q] = None]
       ELSE UNCHANGED <<status, lockedBy>>
  /\ UNCHANGED <<active, pending, grants, denied, retries>>

Receive(p, q) ==
  \/ RcvRequest(p, q)
  \/ RcvGrant(p, q)
  \/ RcvDeny(p, q)
  \/ RcvGone(p, q)
  \/ RcvRelease(p, q)
  \/ RcvPruned(p, q)

Next ==
  \/ \E n \in Nodes : Start(n) \/ Decide(n)
  \/ \E e \in Dir : Receive(e[1], e[2])

(* Fairness: every message is eventually delivered; every enabled         *)
(* decision is eventually taken; enabled pruning attempts eventually run. *)
Fairness ==
  /\ \A e \in Dir : WF_vars(Receive(e[1], e[2]))
  /\ \A n \in Nodes : WF_vars(Decide(n))
  /\ \A n \in Nodes : WF_vars(Start(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

\* The active processors always induce a connected subgraph
ActiveConnected == Connected(ActiveSet)

\* All designated terminals remain active (hence mutually connected)
TerminalsPreserved == Terminals \subseteq ActiveSet

\* Locks are only held by active nodes on behalf of a neighbor
LockSound ==
  \A q \in Nodes :
    lockedBy[q] # None =>
      /\ active[q]
      /\ status[q] = "locked"
      /\ {q, lockedBy[q]} \in Edges

\* Every grant held by a candidate is backed by a lock at the granter
GrantsHeld ==
  \A p \in Nodes :
    status[p] = "candidate" => \A q \in grants[p] : lockedBy[q] = p

\* Views never omit an active neighbor
ViewSound ==
  \A n \in Nodes :
    active[n] => {m \in Nbrs(n) : active[m]} \subseteq view[n]

\* Absence of conflicting deactivations: two adjacent nodes can never both
\* be in a position to prune with each other's consent
NoConflictingGrants ==
  \A p, q \in Nodes :
    ({p, q} \in Edges /\ status[p] = "candidate" /\ q \in grants[p])
      => status[q] = "locked"

Safety ==
  /\ TypeOK
  /\ ActiveConnected
  /\ TerminalsPreserved
  /\ LockSound
  /\ GrantsHeld
  /\ ViewSound
  /\ NoConflictingGrants

\* Action property: a deactivation happens only when all active neighbors
\* are locked by the deactivating node and remain active in that step
NoConflictingDeactivation ==
  [][\A n \in Nodes :
       (active[n] /\ ~active'[n]) =>
         \A m \in Nbrs(n) : active[m] => (lockedBy[m] = n /\ active'[m])]_vars

\* Active set only shrinks
MonotonicPruning ==
  [][\A n \in Nodes : ~active[n] => ~active'[n]]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

Quiescent ==
  /\ \A e \in Dir : chan[e] = <<>>
  /\ \A n \in Nodes : status[n] \in {"idle", "pruned"}
  /\ \A n \in Nodes : ~CanStart(n)

\* Eventual termination in a stable, message-free configuration
Termination == <>[]Quiescent

\* Eventually no further deactivations occur
StableActiveSet == <>[][active' = active]_vars

\* Every pruning phase eventually completes
PhaseCompletes ==
  \A n \in Nodes : (status[n] = "candidate") ~> (status[n] # "candidate")

\* Every lock is eventually released
LocksReleased ==
  \A n \in Nodes : (status[n] = "locked") ~> (status[n] = "idle")

=============================================================================