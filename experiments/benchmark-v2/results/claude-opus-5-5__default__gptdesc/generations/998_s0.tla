------------------------ MODULE SchedulingAllocator ------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS Clients, Resources

ASSUME IsFiniteSet(Clients) /\ IsFiniteSet(Resources)

VARIABLES
  unsat,  \* unsat[c]: resources requested by client c and not yet allocated
  alloc,  \* alloc[c]: resources currently held by client c
  pool,   \* clients with requests that have not yet been scheduled
  sched   \* schedule: sequence of clients whose requests may be served

vars == <<unsat, alloc, pool, sched>>

-----------------------------------------------------------------------------
(* Auxiliary definitions *)

Range(f) == { f[x] : x \in DOMAIN f }

available == Resources \ (UNION { alloc[c] : c \in Clients })

\* Remove the i-th element of a sequence
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

\* The set of all sequences that enumerate the elements of S exactly once
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                          { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ pool \in SUBSET Clients
  /\ sched \in Seq(Clients)

-----------------------------------------------------------------------------
Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ pool  = {}
  /\ sched = << >>

(* A client may request resources only when it has no outstanding         *)
(* unsatisfied request and holds no resources.                             *)
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ pool'  = pool \cup {c}
  /\ UNCHANGED <<alloc, sched>>

(* Allocation of a (possibly partial) set of available requested           *)
(* resources to a scheduled client, provided no client scheduled earlier  *)
(* is still waiting for any of these resources.                            *)
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
  /\ UNCHANGED pool

(* A client may return resources at any time (possibly early).            *)
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, pool, sched>>

(* Clients in the pool are appended to the schedule in some order.        *)
Schedule ==
  /\ pool # {}
  /\ \E sq \in PermSeqs(pool) : sched' = sched \o sq
  /\ pool' = {}
  /\ UNCHANGED <<unsat, alloc>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ Schedule

-----------------------------------------------------------------------------
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
  /\ \A c \in pool : unsat[c] # {} /\ alloc[c] = {}
  /\ pool \cap Range(sched) = {}
  /\ \A c \in Clients : unsat[c] # {} => c \in pool \cup Range(sched)
  /\ \A i \in DOMAIN sched :
        /\ unsat[sched[i]] # {}
        /\ \A j \in 1..(i-1) :
              /\ sched[i] # sched[j]
              /\ alloc[sched[i]] \cap unsat[sched[j]] = {}

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