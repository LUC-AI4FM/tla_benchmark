------------------------------ MODULE ResourceAllocator ------------------------------

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
  Clients,       \* finite set of clients
  Resources      \* finite set of distinct resources

(*
State variables:
  req[c]   = the set of resources currently requested by client c (may be empty)
  held[c]  = the set of resources currently held by client c (subset of req[c])
  sched    = a permutation (sequence) of Clients that constrains serving order
*)
VARIABLES
  req, held, sched

vars == << req, held, sched >>

\* Basic sequence/set helpers
ToSet(s) == { s[i] : i \in 1..Len(s) }
NoDup(s) == \A i, j \in 1..Len(s) : i # j => s[i] # s[j]
IsPerm(s) == /\ Len(s) = Cardinality(Clients)
             /\ ToSet(s) = Clients
             /\ NoDup(s)

\* Clients that appear before c in the schedule sequence s
Before(s, c) ==
  { s[i] : i \in 1..Len(s) /\ \E j \in 1..Len(s) : s[j] = c /\ i < j }

\* Aggregate of all held resources
AllHeld == UNION { held[c] : c \in Clients }

\* Predicates about client state
Outstanding(c) == req[c] # {} /\ (req[c] \ held[c]) # {}
FullySat(c)    == req[c] # {} /\ held[c] = req[c]
Idle(c)        == req[c] = {} /\ held[c] = {}

\* Schedule constraint: c can be served only if no earlier client in sched has an outstanding unsatisfied request
SchedAllows(c) == \A d \in Before(sched, c) : ~Outstanding(d)

TypeOK ==
  /\ req \in [Clients -> SUBSET Resources]
  /\ held \in [Clients -> SUBSET Resources]
  /\ IsPerm(sched)

\* Safety invariants
MutualExclusion ==
  \A c1, c2 \in Clients : c1 # c2 => held[c1] \cap held[c2] = {}

AllocatorInv ==
  \A c \in Clients : held[c] \subseteq req[c]

Inv == TypeOK /\ MutualExclusion /\ AllocatorInv

\* Initial conditions: no requests, nothing held, arbitrary permutation schedule
Init ==
  /\ req  = [c \in Clients |-> {}]
  /\ held = [c \in Clients |-> {}]
  /\ \E s \in Seq(Clients) :
       /\ IsPerm(s)
       /\ sched = s

\* Actions

\* Clients issue a new request only when they have no unsatisfied request and hold no resources
IssueReq(c) ==
  /\ c \in Clients
  /\ req[c] = {}
  /\ held[c] = {}
  /\ \E S \in SUBSET Resources :
       /\ S # {}
       /\ req'  = [req EXCEPT ![c] = S]
       /\ held' = held
       /\ sched' = sched

\* Allocate a single resource r to client c, respecting mutual exclusion and schedule constraints
Allocate(c, r) ==
  /\ c \in Clients /\ r \in Resources
  /\ r \in (req[c] \ held[c])
  /\ \A d \in Clients \ {c} : ~(r \in held[d])
  /\ SchedAllows(c)
  /\ req'  = req
  /\ held' = [held EXCEPT ![c] = held[c] \cup {r}]
  /\ sched' = sched

\* Client returns some resources early (but not when fully satisfied; see ReturnAll)
ReturnSome(c) ==
  /\ c \in Clients
  /\ held[c] # {}
  /\ ~(held[c] = req[c])
  /\ \E X \in SUBSET held[c] :
       /\ X # {}
       /\ held' = [held EXCEPT ![c] = held[c] \ X]
       /\ req'  = req
       /\ sched' = sched

\* Once fully satisfied, client returns all and clears the request
ReturnAll(c) ==
  /\ c \in Clients
  /\ req[c] # {}
  /\ held[c] = req[c]
  /\ held' = [held EXCEPT ![c] = {}]
  /\ req'  = [req  EXCEPT ![c] = {}]
  /\ sched' = sched

\* Scheduler advances (rotates) the schedule sequence
Schedule ==
  /\ Len(sched) > 0
  /\ sched' = Append(SubSeq(sched, 2, Len(sched)), sched[1])
  /\ req' = req
  /\ held' = held

\* Any allocation occurs (for fairness)
AllocateAny == \E c \in Clients : \E r \in Resources : Allocate(c, r)

Next ==
  \/ \E c \in Clients : IssueReq(c)
  \/ \E c \in Clients : \E r \in Resources : Allocate(c, r)
  \/ \E c \in Clients : ReturnSome(c)
  \/ \E c \in Clients : ReturnAll(c)
  \/ Schedule

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(ReturnAll(c))
  /\ WF_vars(AllocateAny)
  /\ WF_vars(Schedule)

\* Liveness properties

\* Eventual return: once fully satisfied, client eventually returns all resources and clears the request
LivenessReturn ==
  \A c \in Clients : []( FullySat(c) => <> Idle(c) )

\* Eventual obtainment: whenever client has an outstanding unsatisfied request, it is eventually fully satisfied
LivenessObtainment ==
  \A c \in Clients : []( Outstanding(c) => <> FullySat(c) )

\* Infinitely often satisfied/idle (requests are satisfied and cleared infinitely often)
LivenessInfOftenIdle ==
  \A c \in Clients : []<>( Idle(c) )

=============================================================================