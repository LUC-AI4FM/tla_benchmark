------------------------ MODULE SchedulingAllocator ------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS Clients, Resources

ASSUME IsFiniteSet(Resources)

VARIABLES unsat, alloc, sched

vars == <<unsat, alloc, sched>>

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

available == Resources \ (UNION {alloc[c] : c \in Clients})

Range(f) == { f[x] : x \in DOMAIN f }

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN { << >> }
        ELSE LET ps == [ x \in ss |->
                           { Append(sq, x) : sq \in perms[ss \ {x}] } ]
             IN  UNION { ps[x] : x \in ss }
  IN  perms[S]

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

Request(c, S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

Allocate(c, S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..i-1 : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

Return(c, S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, sched>>

toSchedule == { c \in Clients : unsat[c] # {} /\ c \notin Range(sched) }

Schedule ==
  /\ toSchedule # {}
  /\ \E sq \in PermSeqs(toSchedule) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

Next ==
  \/ Schedule
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)

Allocator ==
  /\ Init /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : SF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

ResourceMutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

UnscheduledClients == Clients \ Range(sched)

PrevResources(i) ==
     available
  \cup (UNION { unsat[sched[j]] \cup alloc[sched[j]] : j \in 1..i-1 })
  \cup (UNION { alloc[c] : c \in UnscheduledClients })

AllocatorInvariant ==
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \A i \in DOMAIN sched : \A j \in 1..i-1 :
        alloc[sched[i]] \cap unsat[sched[j]] = {}
  /\ \A i \in DOMAIN sched : unsat[sched[i]] \subseteq PrevResources(i)

ClientsWillReturn ==
  \A c \in Clients : unsat[c] = {} ~> alloc[c] = {}

ClientsWillObtain ==
  \A c \in Clients, r \in Resources : r \in unsat[c] ~> r \in alloc[c]

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

=============================================================================