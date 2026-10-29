------------------------ MODULE SchedulingAllocator ------------------------
EXTENDS FiniteSets, Sequences, Naturals, TLC

CONSTANTS
  Clients,     \* set of clients
  Resources    \* set of resources

ASSUME IsFiniteSet(Resources)

VARIABLES
  unsat,   \* unsat[c]: resources requested by client c but not yet granted
  alloc,   \* alloc[c]: resources currently held by client c
  pool,    \* set of clients with pending requests that are not yet scheduled
  sched    \* schedule: sequence of clients whose requests will be served in order

vars == <<unsat, alloc, pool, sched>>

-----------------------------------------------------------------------------
(* Auxiliary definitions *)

Range(f) == { f[x] : x \in DOMAIN f }

\* Set of resources currently not allocated to any client
available == Resources \ (UNION {alloc[c] : c \in Clients})

\* Set of all permutations (as sequences) of the elements of a finite set S
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                           { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

\* Remove the i-th element from a sequence
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ pool \in SUBSET Clients
  /\ sched \in Seq(Clients)

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ pool  = {}
  /\ sched = << >>

(* A client c may request a set S of resources only if it has no
   outstanding unsatisfied request and holds no resources. *)
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ pool'  = pool \cup {c}
  /\ UNCHANGED <<alloc, sched>>

(* Allocate a (possibly partial) set S of available resources to a scheduled
   client c, provided no client scheduled before c requests any of them.
   When the request is fully satisfied, c is removed from the schedule. *)
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<pool>>

(* Client c returns a set S of resources it holds (possibly early). *)
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, pool, sched>>

(* Append the clients in the pool, in some order, to the schedule. *)
Schedule ==
  /\ pool # {}
  /\ pool' = {}
  /\ \E sq \in PermSeqs(pool) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        \/ Request(c, S)
        \/ Allocate(c, S)
        \/ Return(c, S)
  \/ Schedule

Liveness ==
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

Spec == Init /\ [][Next]_vars /\ Liveness

-----------------------------------------------------------------------------
(* Safety properties *)

ResourceMutex ==
  \A c1, c2 \in Clients :
     c1 # c2 => alloc[c1] \cap alloc[c2] = {}

AllocatorInvariant ==
  \* clients in the pool have unsatisfied requests and hold no resources
  /\ \A c \in pool : unsat[c] # {} /\ alloc[c] = {}
  \* scheduled clients have unsatisfied requests, and no client holds
  \* resources still needed by a client scheduled earlier
  /\ \A i \in DOMAIN sched :
        /\ unsat[sched[i]] # {}
        /\ \A j \in 1..(i-1) : alloc[sched[i]] \cap unsat[sched[j]] = {}
  \* every client with an unsatisfied request is either pooled or scheduled
  /\ \A c \in Clients :
        unsat[c] # {} => (c \in pool \/ c \in Range(sched))
  \* pooled clients are not yet scheduled
  /\ pool \cap Range(sched) = {}

-----------------------------------------------------------------------------
(* Liveness properties *)

ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ ResourceMutex /\ AllocatorInvariant)
THEOREM Spec => ClientsWillReturn /\ ClientsWillObtain /\ InfOftenSatisfied
=============================================================================