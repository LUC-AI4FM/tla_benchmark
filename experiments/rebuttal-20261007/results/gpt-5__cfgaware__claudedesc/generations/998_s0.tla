---- MODULE AllocScheduler ----
EXTENDS Naturals, Sequences

CONSTANTS Clients, Resources

VARIABLES unsat, alloc, sched

vars == << unsat, alloc, sched >>

SeqSet(s) == { s[i] : i \in 1..Len(s) }

NoDuplicates(s) ==
  \A i, j \in 1..Len(s) : (i # j) => s[i] # s[j]

RemoveFirst(s, x) ==
  LET pos == CHOOSE i \in 1..Len(s) : s[i] = x
  IN SubSeq(s, 1, pos - 1) \o SubSeq(s, pos + 1, Len(s))

IsPermutationOf(t, S) == /\ NoDuplicates(t) /\ SeqSet(t) = S

AllAllocated == UNION { alloc[c] : c \in Clients }
Avail == Resources \ AllAllocated

TypeOK ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ \A c \in Clients : unsat[c] \cap alloc[c] = {}
  /\ sched \in Seq(Clients)
  /\ NoDuplicates(sched)

MutualExclusion ==
  \A c1, c2 \in Clients : (c1 # c2) => alloc[c1] \cap alloc[c2] = {}

SchedOK ==
  \A i \in 1..Len(sched) : unsat[sched[i]] # {}

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = <<>>

Request ==
  \E c \in Clients :
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ \E req \in SUBSET Resources :
         /\ req # {}
         /\ unsat' = [unsat EXCEPT ![c] = req]
    /\ alloc' = alloc
    /\ sched' = sched

Schedule ==
  LET P == { c \in Clients : /\ unsat[c] # {} /\ ~(c \in SeqSet(sched)) }
  IN \E t \in Seq(Clients) :
       /\ P # {}
       /\ IsPermutationOf(t, P)
       /\ unsat' = unsat
       /\ alloc' = alloc
       /\ sched' = sched \o t

AllocateC(c) ==
  /\ c \in Clients
  /\ c \in SeqSet(sched)
  /\ LET pos == CHOOSE i \in 1..Len(sched) : sched[i] = c IN
     LET earlier == { sched[j] : j \in 1..(pos - 1) } IN
     LET blocked == UNION { unsat[e] : e \in earlier } IN
     LET cand == (Avail \cap unsat[c]) \ blocked IN
     \E grant \in SUBSET cand :
       /\ grant # {}
       /\ LET newUnsat == unsat[c] \ grant IN
          /\ unsat' = [unsat EXCEPT ![c] = newUnsat]
          /\ alloc' = [alloc EXCEPT ![c] = @ \cup grant]
          /\ sched' = IF newUnsat = {} THEN RemoveFirst(sched, c) ELSE sched

Allocate ==
  \E c \in Clients : AllocateC(c)

Return ==
  \E c \in Clients :
    \E ret \in SUBSET alloc[c] :
      /\ ret # {}
      /\ unsat' = unsat
      /\ alloc' = [alloc EXCEPT ![c] = @ \ ret]
      /\ sched' = sched

FullReturn(c) ==
  /\ c \in Clients
  /\ unsat[c] = {}
  /\ alloc[c] # {}
  /\ unsat' = unsat
  /\ alloc' = [alloc EXCEPT ![c] = {}]
  /\ sched' = sched

Next == Request \/ Schedule \/ Allocate \/ Return

Fairness ==
  /\ WF_vars(Schedule)
  /\ \A c \in Clients : WF_vars(AllocateC(c))
  /\ \A c \in Clients : WF_vars(FullReturn(c))

Spec == Init /\ [][Next]_vars /\ Fairness

EventuallyReturnAll ==
  \A c \in Clients : [](unsat[c] = {} => <> alloc[c] = {})

EventuallyAllocateAllRequested ==
  \A c \in Clients : \A r \in Resources : [] (r \in unsat[c] => <> r \in alloc[c])

InfinitelyOftenSatisfied ==
  \A c \in Clients : []<>(unsat[c] = {})

THEOREM TypeCorrectness == Spec => []TypeOK
THEOREM MutualExclusionThm == Spec => []MutualExclusion
THEOREM SchedInvariantThm == Spec => []SchedOK

THEOREM ReturnLiveness == Spec => EventuallyReturnAll
THEOREM AllocateLiveness == Spec => EventuallyAllocateAllRequested
THEOREM SatisfactionLiveness == Spec => InfinitelyOftenSatisfied

====