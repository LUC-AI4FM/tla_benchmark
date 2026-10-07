```tla
MODULE ResourceAllocator

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Clients, Resources

VARIABLES unsat, alloc, sched

Init ==
  /\ unsat = [c \in Clients |-> {}]
  /\ alloc = [c \in Clients |-> {}]
  /\ sched = <<>>

Next ==
  \/ Request
  \/ Schedule
  \/ Allocate
  \/ Return

Request ==
  \E c \in Clients :
    /\ unsat[c] = {}
    /\ alloc[c] = {}
    /\ unsat' = [unsat EXCEPT ![c] = {r \in Resources : TRUE}]
    /\ alloc' = alloc
    /\ sched' = sched

Schedule ==
  \E perm \in Permutations({c \in Clients : unsat[c] # {} \land c \notin sched}) :
    /\ sched' = Append(sched, perm)
    /\ unsat' = unsat
    /\ alloc' = alloc

Allocate ==
  \E c \in Clients, subset \subseteq Resources :
    /\ c \in sched
    /\ subset \subseteq unsat[c]
    /\ subset \cap Union({alloc[d] : d \in SubSeq(sched, 1, Index(sched, c))}) = {}
    /\ unsat' = [unsat EXCEPT ![c] = unsat[c] \ subset]
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \cup subset]
    /\ IF subset = unsat[c] THEN sched' = Remove(sched, c) ELSE sched' = sched

Return ==
  \E c \in Clients, subset \subseteq Resources :
    /\ subset \subseteq alloc[c]
    /\ unsat' = unsat
    /\ alloc' = [alloc EXCEPT ![c] = alloc[c] \ subset]
    /\ sched' = sched

Spec == Init /\ [][Next]_unsat,alloc,sched

THEOREM TypeCorrectness ==
  Spec => [](\A c \in Clients : unsat[c] \subseteq Resources) /\ [](\A c \in Clients : alloc[c] \subseteq Resources)

THEOREM MutualExclusion ==
  Spec => [](\A r \in Resources : {c \in Clients : r \in alloc[c]} \subseteq {c})

THEOREM AllocatorInvariant ==
  Spec => [](\A c \in Clients : unsat[c] # {} => c \in sched)

THEOREM LivenessFullReturn ==
  Spec => WF_Return /\ [](\A c \in Clients : []<>(unsat[c] = {}))

THEOREM LivenessPartialAllocation ==
  Spec => WF_Allocate /\ [](\A c \in Clients, r \in Resources : <>((r \in unsat[c]) /\ (r \in alloc[c])))

THEOREM LivenessScheduling ==
  Spec => WF_Schedule /\ [](\A c \in Clients : <><>(c \in sched))

WF_Return == \A c \in Clients : []<><Request \/ Schedule \/ Allocate>_(unsat,alloc,sched)
WF_Allocate == \A c \in Clients : []<><Request \/ Schedule>_(unsat,alloc,sched)
WF_Schedule == []<><Request>_(unsat,alloc,sched)

=============================================================================
Instantiation for model checking
=============================================================================

CONSTANT ModelClients, ModelResources

ASSUME
  /\ ModelClients = {c1, c2, c3}
  /\ ModelResources = {r1, r2}

THEOREM ModelChecking ==
  Spec => THEOREM TypeCorrectness
          /\ THEOREM MutualExclusion
          /\ THEOREM AllocatorInvariant
          /\ THEOREM LivenessFullReturn
          /\ THEOREM LivenessPartialAllocation
          /\ THEOREM LivenessScheduling

=============================================================================
End of module
=============================================================================
```