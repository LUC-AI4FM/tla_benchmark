------------------------ MODULE SchedulingAllocator ------------------------
EXTENDS FiniteSets, Sequences, Naturals, TLC

CONSTANTS Clients, Resources

ASSUME IsFiniteSet(Resources)

VARIABLES unsat, alloc, sched

vars == <<unsat, alloc, sched>>

-----------------------------------------------------------------------------
(* Auxiliary operators *)

Range(f) == { f[x] : x \in DOMAIN f }

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                          { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

available == Resources \ (UNION { alloc[c] : c \in Clients })

toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

(* A client may request resources only when it has no outstanding
   request and holds no resources. *)
Request(c, S) ==
  /\ unsat[c] = {}
  /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

(* Allocate a (possibly partial) set of available requested resources to a
   scheduled client, provided no earlier client in the schedule still
   requests any of these resources. *)
Allocate(c, S) ==
  /\ S # {}
  /\ S \subseteq (available \cap unsat[c])
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

(* A client returns some of its held resources. *)
Return(c, S) ==
  /\ S # {}
  /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, sched>>

(* Extend the schedule with all currently requesting, unscheduled clients
   in an arbitrary order. *)
Schedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ Schedule

Liveness ==
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

Allocator == Init /\ [][Next]_vars /\ Liveness

-----------------------------------------------------------------------------
(* Correctness properties *)

ResourceMutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

UnscheduledClients == Clients \ Range(sched)

PrevResources(i) ==
  alloc[sched[i]]
    \cup (UNION { unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..(i-1) })
    \cup (UNION { alloc[c] : c \in UnscheduledClients })

AllocatorInvariant ==
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \A i \in DOMAIN sched : \A j \in 1..(i-1) :
        alloc[sched[i]] \cap unsat[sched[j]] = {}
  /\ \A i \in DOMAIN sched : unsat[sched[i]] \subseteq PrevResources(i)

ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {} ~> alloc[c] = {})

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

=============================================================================