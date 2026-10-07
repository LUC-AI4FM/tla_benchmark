---- MODULE Allocator ----
EXTENDS Sequences, FiniteSets, TLC

CONSTANTS Clients, Resources

VARIABLES unsat, alloc, sched

vars == << unsat, alloc, sched >>

ElemSet(s) == { s[i] : i \in DOMAIN s }

NoDup(s) == \A i, j \in DOMAIN s : i # j => s[i] # s[j]

IsPerm(S, s) == s \in Seq(Clients) /\ NoDup(s) /\ ElemSet(s) = S

InSeq(s, x) == \E i \in DOMAIN s : s[i] = x

Earlier(s, i) == { s[j] : j \in DOMAIN s /\ j < i }

Allocated == UNION { alloc[c] : c \in Clients }

Available == Resources \ Allocated

Grantable(c, i) ==
  LET er == Earlier(sched, i) IN
    Available \cap unsat[c] \cap (Resources \ UNION { unsat[e] : e \in er })

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = << >>

Request ==
  \E c \in Clients :
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ \E req \in SUBSET Resources :
         /\ req # {}
         /\ unsat' = [unsat EXCEPT ![c] = req]
         /\ UNCHANGED << alloc, sched >>

Schedule ==
  LET P == { c \in Clients : unsat[c] # {} /\ ~InSeq(sched, c) }
  IN /\ P # {}
     /\ \E s \in Seq(Clients) :
          /\ IsPerm(P, s)
          /\ sched' = sched \o s
          /\ UNCHANGED << unsat, alloc >>

AllocateSome(c) ==
  \E i \in DOMAIN sched :
    /\ sched[i] = c
    /\ \E g \in SUBSET Grantable(c, i) :
         /\ g # {}
         /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup g]
         /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ g]
         /\ sched' =
              IF (unsat[c] \ g) = {}
              THEN SubSeq(sched, 1, i - 1) \o SubSeq(sched, i + 1, Len(sched))
              ELSE sched

Allocate ==
  \E c \in Clients : AllocateSome(c)

ReturnSome ==
  \E c \in Clients :
    \E rel \in SUBSET alloc[c] :
      /\ rel # {}
      /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ rel]
      /\ UNCHANGED << unsat, sched >>

ReturnAll(c) ==
  /\ unsat[c] = {}
  /\ alloc[c] # {}
  /\ alloc' = [alloc EXCEPT ![c] = {}]
  /\ UNCHANGED << unsat, sched >>

Return ==
  ReturnSome \/ (\E c \in Clients : ReturnAll(c))

Next ==
  Request \/ Schedule \/ Allocate \/ Return

Spec ==
  Init
  /\ [][Next]_vars
  /\ WF_vars(Schedule)
  /\ \A c \in Clients : WF_vars(AllocateSome(c))
  /\ \A c \in Clients : WF_vars(ReturnAll(c))

TypeOK ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

MutEx ==
  \A c1, c2 \in Clients : c1 # c2 => alloc[c1] \cap alloc[c2] = {}

SchedOK ==
  /\ NoDup(sched)
  /\ \A i \in DOMAIN sched : unsat[sched[i]] # {}
  /\ \A i, j \in DOMAIN sched : i < j => (alloc[sched[j]] \cap unsat[sched[i]] = {})

ReturnAllEventually ==
  \A c \in Clients : [](unsat[c] = {} => <> (alloc[c] = {}))

EvAllocEachRequested ==
  \A c \in Clients : \A r \in Resources : [] (r \in unsat[c] => <> (r \in alloc[c]))

InfOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

THEOREM TypeCorrectness == Spec => []TypeOK
THEOREM MutualExclusionOfAllocations == Spec => []MutEx
THEOREM StructuralAllocatorInvariant == Spec => []SchedOK
THEOREM EventualFullReturns == Spec => ReturnAllEventually
THEOREM EveryRequestedResourceEventuallyAllocated == Spec => EvAllocEachRequested
THEOREM ClientsInfinitelyOftenSatisfied == Spec => InfOftenSatisfied
====