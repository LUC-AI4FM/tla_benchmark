```tla
L

\* 4. A key appears in at most one leaf
KeysInAtMostOneLeaf ==
    \A k \in Keys :
        \A n1, n2 \in LeafNodes :
            (k \in keysOf[n1] /\ k \in keysOf[n2]) => n1 = n2

\* 5. The node pool never runs dry
FreeNodesRemain == free # {}

\* Nodes respect the occupancy limit whenever no operation is in progress
OccupancyBounded ==
    state = "ready" => \A n \in InUse : Cardinality(keysOf[n]) <= MaxOccupancy

\* Refinement of the abstract key-value store: when ready, the tree's
\* key-to-value mapping equals the abstract dictionary, and the last
\* operation returned exactly what the abstract store prescribes.
RefinesKVStore ==
    state = "ready" =>
        /\ Mapping = dict
        /\ op # NONE => ret = expected

\* Get returns exactly the stored value or Missing
GetCorrect ==
    (state = "ready" /\ op = "get") => ret = dict[args.key]

Invariants ==
    /\ TypeOK
    /\ InnerNodesHaveLastChild
    /\ KeyOrderPreserved
    /\ LeavesHaveNoChildren
    /\ KeysInAtMostOneLeaf
    /\ FreeNodesRemain
    /\ OccupancyBounded
    /\ RefinesKVStore
    /\ GetCorrect

-----------------------------------------------------------------------------
\* Liveness (holds under FairSpec): every started operation completes

OperationsComplete == (state # "ready") ~> (state = "ready")

=============================================================================
```