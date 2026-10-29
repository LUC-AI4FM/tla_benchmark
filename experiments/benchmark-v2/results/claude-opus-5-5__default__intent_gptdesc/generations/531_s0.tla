------------------------------ MODULE SessionManager ------------------------------
(***************************************************************************)
(* A distributed session-management system. A finite set of clients       *)
(* request, acquire, use, and release sessions drawn from a fixed universe *)
(* of session identifiers. Each session is held by at most one client at a *)
(* time. Released sessions go through a reclamation step before returning  *)
(* to the free pool, where other clients can reuse them.                   *)
(*                                                                         *)
(* Client lifecycle:                                                       *)
(*   Idle -> Waiting -> Holding -> Using -> Done -> Idle                   *)
(*   (Request, Grant, Use, Finish, Release)                                *)
(* Session lifecycle:                                                      *)
(*   free -> held -> returning -> free                                     *)
(*   (Grant, Release, Reclaim)                                             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    Clients,      \* finite set of clients
    Sessions,     \* fixed universe of session identifiers
    NoSession     \* sentinel value meaning "no session held"

ASSUME /\ IsFiniteSet(Clients)
       /\ IsFiniteSet(Sessions)
       /\ Clients # {}
       /\ Sessions # {}
       /\ NoSession \notin Sessions

VARIABLES
    cstate,     \* cstate[c] : lifecycle phase of client c
    holds,      \* holds[c]  : session held by client c, or NoSession
    free,       \* sessions currently available in the pool
    returning   \* sessions released by clients, pending return to the pool

vars == <<cstate, holds, free, returning>>

ClientStates == {"Idle", "Waiting", "Holding", "Using", "Done"}

\* Sessions currently held by some client
Holders     == {c \in Clients : holds[c] # NoSession}
HeldSessions == {holds[c] : c \in Holders}

-----------------------------------------------------------------------------
(* Initial state: all clients idle, all sessions free. *)

Init ==
    /\ cstate    = [c \in Clients |-> "Idle"]
    /\ holds     = [c \in Clients |-> NoSession]
    /\ free      = Sessions
    /\ returning = {}

-----------------------------------------------------------------------------
(* Actions *)

\* A client nondeterministically issues a request for a session.
Request(c) ==
    /\ cstate[c] = "Idle"
    /\ cstate' = [cstate EXCEPT ![c] = "Waiting"]
    /\ UNCHANGED <<holds, free, returning>>

\* The allocator grants a free session s to a waiting client c.
Grant(c, s) ==
    /\ cstate[c] = "Waiting"
    /\ s \in free
    /\ holds[c] = NoSession
    /\ cstate' = [cstate EXCEPT ![c] = "Holding"]
    /\ holds'  = [holds  EXCEPT ![c] = s]
    /\ free'   = free \ {s}
    /\ UNCHANGED returning

\* A client begins using its granted session.
Use(c) ==
    /\ cstate[c] = "Holding"
    /\ cstate' = [cstate EXCEPT ![c] = "Using"]
    /\ UNCHANGED <<holds, free, returning>>

\* A client signals completion of its work on the session.
Finish(c) ==
    /\ cstate[c] = "Using"
    /\ cstate' = [cstate EXCEPT ![c] = "Done"]
    /\ UNCHANGED <<holds, free, returning>>

\* A client releases its session; the session enters reclamation.
Release(c) ==
    /\ cstate[c] = "Done"
    /\ holds[c] \in Sessions
    /\ returning' = returning \cup {holds[c]}
    /\ holds'     = [holds  EXCEPT ![c] = NoSession]
    /\ cstate'    = [cstate EXCEPT ![c] = "Idle"]
    /\ UNCHANGED free

\* A released session is returned to the free pool for reuse.
Reclaim(s) ==
    /\ s \in returning
    /\ returning' = returning \ {s}
    /\ free'      = free \cup {s}
    /\ UNCHANGED <<cstate, holds>>

\* Grant enabled for client c with some free session
GrantAny(c) == \E s \in free : Grant(c, s)

Next ==
    \/ \E c \in Clients :
          \/ Request(c)
          \/ GrantAny(c)
          \/ Use(c)
          \/ Finish(c)
          \/ Release(c)
    \/ \E s \in Sessions : Reclaim(s)

-----------------------------------------------------------------------------
(* Fairness                                                                *)
(* Request arrival is not subject to fairness, so clients may stay idle    *)
(* forever. Use, Finish, Release, and Reclaim are weakly fair. Grant is     *)
(* strongly fair per client. With several clients competing, the free pool *)
(* may be repeatedly emptied by others, so weak fairness alone cannot      *)
(* guarantee that each individual waiting client makes progress.           *)

Fairness ==
    /\ \A c \in Clients :
          /\ SF_vars(GrantAny(c))
          /\ WF_vars(Use(c))
          /\ WF_vars(Finish(c))
          /\ WF_vars(Release(c))
    /\ \A s \in Sessions : WF_vars(Reclaim(s))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ cstate    \in [Clients -> ClientStates]
    /\ holds     \in [Clients -> Sessions \cup {NoSession}]
    /\ free      \subseteq Sessions
    /\ returning \subseteq Sessions

\* No two clients hold the same session simultaneously.
MutualExclusion ==
    \A c1, c2 \in Clients :
        (c1 # c2 /\ holds[c1] # NoSession) => holds[c1] # holds[c2]

\* Only session identifiers from the fixed universe are ever allocated.
Validity ==
    /\ \A c \in Clients : holds[c] \in Sessions \cup {NoSession}
    /\ HeldSessions \subseteq Sessions

\* Held sessions form a subset of the universe with unique ownership.
\* Every session is in exactly one of: free, held, or returning.
NoDuplication ==
    /\ HeldSessions \subseteq Sessions
    /\ \A s \in HeldSessions : \E! c \in Clients : holds[c] = s
    /\ free \cap HeldSessions = {}
    /\ free \cap returning    = {}
    /\ returning \cap HeldSessions = {}
    /\ free \cup returning \cup HeldSessions = Sessions

\* A client holds a session exactly when it is in a holding phase.
HoldingConsistent ==
    \A c \in Clients :
        (holds[c] # NoSession) <=> (cstate[c] \in {"Holding", "Using", "Done"})

\* Cardinality bounds: allocations never exceed the universe size.
CardinalityBound ==
    /\ Cardinality(HeldSessions) <= Cardinality(Sessions)
    /\ Cardinality(Holders) = Cardinality(HeldSessions)
    /\ Cardinality(free) + Cardinality(returning) + Cardinality(HeldSessions)
           = Cardinality(Sessions)

\* Deadlock freedom: some step of the system is always enabled.
DeadlockFree == ENABLED Next

Invariants ==
    /\ TypeOK
    /\ MutualExclusion
    /\ Validity
    /\ NoDuplication
    /\ HoldingConsistent
    /\ CardinalityBound

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Progress: every waiting client eventually acquires a session.
Progress ==
    \A c \in Clients : (cstate[c] = "Waiting") ~> (holds[c] # NoSession)

\* Every client that acquires a session eventually releases it.
EventualRelease ==
    \A c \in Clients : (holds[c] # NoSession) ~> (cstate[c] = "Idle")

\* Reusability: released sessions eventually return to the free pool.
Reusability ==
    \A s \in Sessions : (s \in returning) ~> (s \in free)

\* Every held session eventually becomes available again.
HeldEventuallyFree ==
    \A s \in Sessions : (s \in HeldSessions) ~> (s \in free)

\* The system never stops while there is outstanding work.
NoStarvation ==
    \A c \in Clients : []<>(cstate[c] \in {"Idle"})

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => []DeadlockFree
THEOREM Spec => Progress /\ EventualRelease /\ Reusability /\ HeldEventuallyFree
=============================================================================