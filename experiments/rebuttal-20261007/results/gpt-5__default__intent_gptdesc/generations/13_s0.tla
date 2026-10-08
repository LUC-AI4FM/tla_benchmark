------------------------------ MODULE RollingUpdate ------------------------------

EXTENDS TLC

CONSTANTS 
  SERVERS, \* finite, with at least two elements
  OLD,
  NEW,
  UPDATING

ASSUME /\ OLD # NEW
       /\ OLD # UPDATING
       /\ NEW # UPDATING
       /\ SERVERS # {}
       /\ Cardinality(SERVERS) >= 2

VARIABLES 
  Version,   \* [s \in SERVERS -> {OLD, UPDATING, NEW}]
  LB,        \* subset of SERVERS currently behind the load balancer (receiving traffic)
  Removed,   \* subset of SERVERS not in LB, under orchestrator control
  Batch      \* subset of Removed whose return is pending as a unit (must wait until all are NEW)

vars == << Version, LB, Removed, Batch >>

\*----------------------------------------------
\* Initialization
\*----------------------------------------------
Init ==
  /\ Version = [s \in SERVERS |-> OLD]
  /\ LB = SERVERS
  /\ Removed = {}
  /\ Batch = {}

\*----------------------------------------------
\* Helper predicates
\*----------------------------------------------
ServingVersions == {OLD, NEW}

NonEmptyLB == LB # {}

NoUpdatingInLB == \A s \in LB: Version[s] \in ServingVersions

HomoLB == \A s \in LB: \A t \in LB: Version[s] = Version[t]

PartitionInv == /\ LB \subseteq SERVERS
                /\ Removed \subseteq SERVERS
                /\ LB \cap Removed = {}
                /\ LB \cup Removed = SERVERS
                /\ Batch \subseteq Removed

\* Safety: clients only see consistent, runnable state
SafetyInv == /\ NonEmptyLB
             /\ NoUpdatingInLB
             /\ HomoLB
             /\ PartitionInv

\* Orchestrator must wait for removed servers to finish before any return
WaitToReturnSafety ==
  (\E s \in Batch: Version[s] # NEW) => ~ENABLED(PlainReturn \/ CutoverReturn)

\* Progress properties (liveness)
UpdateTerminates ==
  \A s \in SERVERS: [](Version[s] = UPDATING => <> (Version[s] = NEW))

EventualAllUpdated ==
  <> (\A s \in SERVERS: Version[s] = NEW)

\*----------------------------------------------
\* Actions
\*----------------------------------------------

\* Orchestrator removes a nonempty subset R of LB, leaving at least one in LB.
RemoveSome ==
  \E R \in SUBSET LB:
    /\ R # {}
    /\ (LB \ R) # {}
    /\ LB' = LB \ R
    /\ Removed' = Removed \cup R
    /\ Batch' = Batch \cup R
    /\ Version' = Version

\* A removed server starts its update.
StartUpdate(s) ==
  /\ s \in Removed
  /\ Version[s] = OLD
  /\ Version' = [Version EXCEPT ![s] = UPDATING]
  /\ UNCHANGED << LB, Removed, Batch >>

\* An updating server finishes its update.
FinishUpdate(s) ==
  /\ Version[s] = UPDATING
  /\ Version' = [Version EXCEPT ![s] = NEW]
  /\ UNCHANGED << LB, Removed, Batch >>

\* Return the whole current batch when LB is already NEW-homogeneous.
PlainReturn ==
  /\ Batch # {}
  /\ \A s \in Batch: Version[s] = NEW
  /\ LB # {}
  /\ \A s \in LB: Version[s] = NEW
  /\ LB' = LB \cup Batch
  /\ Removed' = Removed \ Batch
  /\ Batch' = {}
  /\ UNCHANGED Version

\* Atomic cutover: swap the entire (OLD) LB with the (NEW) Batch to preserve homogeneity and zero downtime.
CutoverReturn ==
  /\ Batch # {}
  /\ \A s \in Batch: Version[s] = NEW
  /\ LB # {}
  /\ \A s \in LB: Version[s] = OLD
  /\ LB' = Batch
  /\ Removed' = (Removed \ Batch) \cup LB
  /\ Batch' = {}
  /\ UNCHANGED Version

Next ==
  RemoveSome
  \/ (\E s \in SERVERS: StartUpdate(s))
  \/ (\E s \in SERVERS: FinishUpdate(s))
  \/ PlainReturn
  \/ CutoverReturn

\*----------------------------------------------
\* Full specification with fairness
\*----------------------------------------------
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(RemoveSome)
  /\ (\A s \in SERVERS: WF_vars(StartUpdate(s)))
  /\ (\A s \in SERVERS: WF_vars(FinishUpdate(s)))
  /\ WF_vars(PlainReturn)
  /\ WF_vars(CutoverReturn)

===============================================================================