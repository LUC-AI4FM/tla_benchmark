------------------------- MODULE AllocatorRefinement -------------------------
(***************************************************************************)
(* Refinement of a high-level SimpleAllocator by a lower-level             *)
(* scheduling allocator (Allocator).                                       *)
(*                                                                         *)
(* Observable interface: unsat[c] is the set of resources client c has     *)
(* requested and not yet received. alloc[c] is the set of resources c      *)
(* currently holds. Request, grant (Allocate) and release (Return) change  *)
(* only these variables.                                                   *)
(*                                                                         *)
(* The implementation adds the internal variables pool, sched and          *)
(* requested. Its internal Schedule step is a stuttering step of the       *)
(* abstract allocator.                                                     *)
(*                                                                         *)
(* The refinement mapping is the projection onto <<unsat, alloc>>. Under   *)
(* that mapping every behaviour of Allocator is a behaviour of             *)
(* SimpleAllocator: THEOREM Allocator => SimpleAllocator.                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Clients, Resources

ASSUME IsFiniteSet(Resources)

VARIABLES unsat, alloc, pool, sched, requested

absVars == <<unsat, alloc>>
vars    == <<unsat, alloc, pool, sched, requested>>

-----------------------------------------------------------------------------
(* Shared helper operators *)

Available == Resources \ (UNION {alloc[c] : c \in Clients})

Range(f) == {f[i] : i \in DOMAIN f}

Drop(seq, i) == SubSeq(seq, 1, i-1) \o SubSeq(seq, i+1, Len(seq))

PermSeqs(S) ==
  LET perms[ss \in SUBSET S] ==
        IF ss = {} THEN {<<>>}
        ELSE LET ps == [x \in ss |-> {Append(sq, x) : sq \in perms[ss \ {x}]}]
             IN  UNION {ps[x] : x \in ss}
  IN  perms[S]

-----------------------------------------------------------------------------
(***************************************************************************)
(* High-level specification: the simple allocator.                         *)
(* It refers only to the observable variables unsat and alloc.             *)
(***************************************************************************)

SInit ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]

SRequest(c, S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ UNCHANGED alloc

SAllocate(c, S) ==
  /\ S # {} /\ S \subseteq Available \cap unsat[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]

SReturn(c, S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED unsat

SNext ==
  \E c \in Clients, S \in SUBSET Resources :
     SRequest(c, S) \/ SAllocate(c, S) \/ SReturn(c, S)

SLiveness ==
  /\ \A c \in Clients : WF_absVars(unsat[c] = {} /\ SReturn(c, alloc[c]))
  /\ \A c \in Clients : SF_absVars(\E S \in SUBSET Resources : SAllocate(c, S))

SimpleAllocator == SInit /\ [][SNext]_absVars /\ SLiveness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Low-level implementation: the scheduling allocator.                     *)
(* pool  : clients with pending requests that are not yet scheduled.       *)
(* sched : the scheduling queue, which fixes the priority order.           *)
(* requested : ghost history of the most recent request of each client.    *)
(***************************************************************************)

TypeInvariant ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ pool \in SUBSET Clients
  /\ sched \in Seq(Clients)
  /\ requested \in [Clients -> SUBSET Resources]

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ pool = {}
  /\ sched = <<>>
  /\ requested = [c \in Clients |-> {}]

(* Observable: a client issues a request. The request enters the pool. *)
Request(c, S) ==
  /\ unsat[c] = {} /\ alloc[c] = {}
  /\ S # {}
  /\ unsat' = [unsat EXCEPT ![c] = S]
  /\ pool' = pool \cup {c}
  /\ requested' = [requested EXCEPT ![c] = S]
  /\ UNCHANGED <<alloc, sched>>

(* Observable: a grant, made according to the queue order. *)
Allocate(c, S) ==
  /\ S # {} /\ S \subseteq Available \cap unsat[c]
  /\ \E i \in DOMAIN sched :
        /\ sched[i] = c
        /\ \A j \in 1..(i-1) : unsat[sched[j]] \cap S = {}
        /\ sched' = IF S = unsat[c] THEN Drop(sched, i) ELSE sched
  /\ alloc' = [alloc EXCEPT ![c] = @ \cup S]
  /\ unsat' = [unsat EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<pool, requested>>

(* Observable: a release. *)
Return(c, S) ==
  /\ S # {} /\ S \subseteq alloc[c]
  /\ alloc' = [alloc EXCEPT ![c] = @ \ S]
  /\ UNCHANGED <<unsat, pool, sched, requested>>

(* Internal: move the pooled requests into the queue in some order. *)
Schedule ==
  /\ pool # {}
  /\ pool' = {}
  /\ \E sq \in PermSeqs(pool) : sched' = sched \o sq
  /\ UNCHANGED <<unsat, alloc, requested>>

Next ==
  \/ \E c \in Clients, S \in SUBSET Resources :
        Request(c, S) \/ Allocate(c, S) \/ Return(c, S)
  \/ Schedule

Liveness ==
  /\ \A c \in Clients : WF_vars(unsat[c] = {} /\ Return(c, alloc[c]))
  /\ \A c \in Clients : WF_vars(\E S \in SUBSET Resources : Allocate(c, S))
  /\ WF_vars(Schedule)

Allocator == Init /\ [][Next]_vars /\ Liveness

SchedulingAllocator == Allocator

-----------------------------------------------------------------------------
(* Safety properties *)

(* No resource is held by two different clients. *)
Mutex ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

(* Every held or pending resource belongs to a previously issued request. *)
NoAllocWithoutRequest ==
  \A c \in Clients : (alloc[c] \cup unsat[c]) \subseteq requested[c]

(* Resource counts are preserved. *)
ResourceCount ==
  /\ Available \cup UNION {alloc[c] : c \in Clients} = Resources
  /\ Available \cap UNION {alloc[c] : c \in Clients} = {}

(* Queue invariant of the implementation. *)
SchedInv ==
  /\ \A c \in Clients : unsat[c] # {} <=> (c \in pool \/ c \in Range(sched))
  /\ pool \cap Range(sched) = {}
  /\ \A i, j \in DOMAIN sched : i # j => sched[i] # sched[j]

Safety == TypeInvariant /\ Mutex /\ NoAllocWithoutRequest /\ ResourceCount /\ SchedInv

-----------------------------------------------------------------------------
(* Liveness properties *)

(* Every pending request is eventually granted. *)
ClientsWillObtain ==
  \A c \in Clients, r \in Resources : (r \in unsat[c]) ~> (r \in alloc[c])

(* Clients that complete eventually release their resources. *)
ClientsWillReturn ==
  \A c \in Clients : (unsat[c] = {}) ~> (alloc[c] = {})

-----------------------------------------------------------------------------
(* Refinement proof obligations *)

THEOREM ImplSafety == Allocator => []Safety
THEOREM ImplLiveness == Allocator => (ClientsWillObtain /\ ClientsWillReturn)
THEOREM Refinement == Allocator => SimpleAllocator
=============================================================================