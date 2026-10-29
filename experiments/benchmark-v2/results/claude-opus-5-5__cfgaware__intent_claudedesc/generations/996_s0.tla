------------------------ MODULE AllocatorRefinement ------------------------
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS Clients, Resources

ASSUME IsFiniteSet(Resources)

VARIABLES unsat, alloc, pool, sched

vars == <<unsat, alloc, pool, sched>>
svars == <<unsat, alloc>>

available == Resources \ (UNION {alloc[c] : c \in Clients})

-----------------------------------------------------------------------------
(* Simple (abstract) allocator over unsat and alloc                         *)
-----------------------------------------------------------------------------

SimpleTypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]

SimpleMutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

SInit ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

SRequest(c, S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

SAllocate(c, S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

SReturn(c, S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

SNext ==
  \E c \in Clients, S \in SUBSET Resources :
     SRequest(c, S) \/ SAllocate(c, S) \/ SReturn(c, S)

SimpleAllocator ==
  /\ SInit
  /\ [][SNext]_svars
  /\ \A c \in Clients : WF_svars(unsat[c] = {} /\ SReturn(c, alloc[c]))
  /\ \A c \in Clients : SF_svars(\E S \in SUBSET Resources : SAllocate(c, S))

-----------------------------------------------------------------------------
(* Scheduling allocator                                                     *)
-----------------------------------------------------------------------------

Range(f) == {f[x] : x \in DOMAIN f}

PermSeqs(S) ==
  {f \in [1..Cardinality(S) -> S] :
      \A i, j \in 1..Cardinality(S) : i # j => f[i] # f[j]}

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ pool \in SUBSET Clients
  /\ sched \in Seq(Clients)

Mutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ pool = {}
  /\ sched = << >>

Request(c, S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ pool' = pool \cup {c}
  /\ UNCHANGED <<alloc, sched>>

Allocate(c, S) ==
  /\ S # {} /\ S \subseteq available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
  /\ UNCHANGED pool

Return(c, S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, pool, sched>>

Schedule ==
  /\ pool # {}
  /\ pool' = {}
  /\ \E sq \in PermSeqs(pool) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ Schedule

Allocator ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

-----------------------------------------------------------------------------
(* Refinement: the scheduling allocator implements the simple allocator     *)
(* under the identity mapping on unsat and alloc.                           *)
-----------------------------------------------------------------------------

THEOREM Allocator => SimpleAllocator

=============================================================================