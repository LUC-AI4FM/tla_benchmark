------------------------------- MODULE ResourceAllocator -------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Clients, Resources
VARIABLES unsat, alloc, sched

Init == /\ unsat = [c \in Clients |-> {}]
        /\ alloc = [c \in Clients |-> {}]
        /\ sched = <<>>

Request ==
  \/ \E c \in Clients : 
     (unsat[c] = {} /\ alloc[c] = {}) /\ 
     (\E r \in Resources : {r} \subseteq unsat'[\cup (DOMAIN unsat)] /\
      unsat'[c] = unsat[c] \cup {r} /\ alloc'[c] = alloc[c])

Schedule ==
  \/ sched' = Append(sched, Permutations({c \in Clients | unsat[c] # {} \notin sched}))

Allocate ==
  \/ \E c \in Clients : 
     (c \in Head(sched) /\ \E r \in Resources :
      (r \in unsat[c] /\ r \notin (\cup {alloc[c'] | c' \in TL(Head(sched))}) /\
       alloc'[c] = alloc[c] \cup {r} /\ 
       IF alloc'[c] = unsat[c] THEN
         unsat'[c] = {} /\ sched' = Tail(sched)
       ELSE
         unsat'[c] = unsat[c] \ {r} /\ sched' = sched))

Return ==
  \/ \E c \in Clients : 
     (alloc[c] # {}) /\
     (\E r \in Resources :
      (r \in alloc[c] /\ alloc'[c] = alloc[c] \ {r}))

Next == Request \/ Schedule \/ Allocate \/ Return

Spec == Init /\ [][Next]_<<unsat, alloc, sched>>

TypeOK ==
  /\ unsat \in [Clients -> SUBSET Resources]
  /\ alloc \in [Clients -> SUBSET Resources]
  /\ sched \in Seq(Clients)

MutualExclusion ==
  \A r \in Resources : Cardinality({c \in Clients | r \in alloc[c]}) <= 1

Schedulability ==
  \A c \in Clients :
    (unsat[c] # {}) => (\E i \in DOMAIN sched : sched[i] = c)

ClientReturnsAllResources ==
  WF_<<unsat, alloc, sched>>(\A c \in Clients : unsat[c] = {} => Return)

EveryResourceAllocated ==
  WF_<<unsat, alloc, sched>>(\A r \in Resources : (\E c \in Clients : r \in alloc[c]))

ClientFullySatisfiedInfinitelyOften ==
  SF_<<unsat, alloc, sched>>(\A c \in Clients : unsat[c] = {})

THEOREMS TypeOK /\ MutualExclusion /\ Schedulability
           /\ ClientReturnsAllResources
           /\ EveryResourceAllocated
           /\ ClientFullySatisfiedInfinitelyOften

=============================================================================