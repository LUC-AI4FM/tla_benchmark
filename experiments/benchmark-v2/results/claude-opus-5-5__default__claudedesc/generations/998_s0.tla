------------------------ MODULE SchedulingAllocator ---------------------
(***************************************************************************)
(* A scheduling-based resource allocator managing a shared pool of         *)
(* resources among a set of competing clients.                             *)
(***************************************************************************)
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS
  Clients,     \* set of all clients
  Resources    \* set of all resources

ASSUME
  IsFiniteSet(Resources)

VARIABLES
  unsat,       \* unsat[c] is the set of resources requested by c but not yet allocated
  alloc,       \* alloc[c] is the set of resources currently allocated to c
  sched        \* sequence of clients representing the allocation schedule

vars == <<unsat, alloc, sched>>

-------------------------------------------------------------------------

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

(* Resources that are not currently allocated to any client. *)
available == Resources \ (UNION {alloc[c] : c \in Clients})

(* The set of elements appearing in a sequence/function. *)
Range(f) == { f[x] : x \in DOMAIN f }

(* The set of all permutations of a finite set S, as sequences. *)
PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                           { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

(* Remove the i-th element of a sequence. *)
Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

(* Clients with pending requests that are not yet scheduled. *)
toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

(* Clients that do not appear in the schedule. *)
UnscheduledClients == Clients \ Range(sched)

-------------------------------------------------------------------------

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

(* A client with no pending requests and no held resources may issue a   *)
(* new non-empty request.                                                 *)
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

(* Allocate a subset of available, requested resources to a scheduled    *)
(* client, provided no client earlier in the schedule requested any of   *)
(* them. A fully satisfied client is dropped from the schedule.          *)
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq (available \cap unsat[c])
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* A client may return any subset of its held resources at any time. *)
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, sched>>

(* Append a permutation of all unscheduled clients with pending requests. *)
Schedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
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

-------------------------------------------------------------------------
(* Safety properties *)

ResourceMutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* Resources held by unscheduled clients or by clients scheduled before   *)
(* position i, together with resources requested by those earlier ones.  *)
PrevResources(i) ==
     alloc[sched[i]]
  \cup UNION { unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..(i-1) }
  \cup UNION { alloc[c] : c \in UnscheduledClients }

AllocatorInvariant ==
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \A i \in DOMAIN sched : \A j \in 1..(i-1) : sched[i] # sched[j]
  /\ \A c \in toSchedule : alloc[c] = {}
  /\ \A i \in DOMAIN sched :
        \A r \in unsat[sched[i]] : r \in available \/ r \in PrevResources(i)

-------------------------------------------------------------------------
(* Liveness properties *)

ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {} ~> alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c] ~> r \in alloc[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

-------------------------------------------------------------------------

THEOREM Spec => []TypeInvariant
THEOREM Spec => []ResourceMutex
THEOREM Spec => []AllocatorInvariant
THEOREM Spec => ClientsWillReturn
THEOREM Spec => ClientsWillObtain
THEOREM Spec => InfOftenSatisfied

=========================================================================