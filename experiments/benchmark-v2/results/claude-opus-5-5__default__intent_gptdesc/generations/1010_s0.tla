```tla
    /\ \A x \in SubKeys(rmost[n]) : \A q \in keys[n] : q <= x

(* Uniqueness: each key appears in at most one leaf *)
UniqueKeys ==
  \A l1, l2 \in Reachable :
    (leaf[l1] /\ leaf[l2] /\ l1 # l2) => keys[l1] \cap keys[l2] = {}

(* Resource safety: free pool and tree are disjoint and account for all nodes *)
FreeAccounting ==
  /\ Reachable \cap free = {}
  /\ Reachable \cup free = Nodes

(* Optional stronger resource invariant (holds only under sufficient pool size) *)
FreeNodeAvailable == phase = "idle" => free # {}

(* Splits allocate only from the free pool; nodes are never returned *)
AllocFromFree ==
  [][ /\ free' \subseteq free
      /\ (Reachable' \ Reachable) \subseteq free
      /\ Cardinality(free) - Cardinality(free') =
           Cardinality(Reachable') - Cardinality(Reachable) ]_vars

Invariants == TypeOK /\ StructInv /\ KeyOrder /\ UniqueKeys /\ FreeAccounting

-------------------------------------------------------------------------
(* Abstract key-value specification, stated over the refinement mapping   *)
(* AbsMap together with the exposed operation state (phase, req, resp).   *)
AbsVars == <<AbsMap, phase, req, resp>>

AbsInit ==
  /\ AbsMap = [k \in Keys |-> Missing]
  /\ phase = "idle"

AbsStart ==
  /\ phase = "idle"
  /\ phase' = "busy"
  /\ req' \in Requests
  /\ UNCHANGED <<AbsMap, resp>>

AbsDo ==
  /\ phase = "busy"
  /\ phase' = "done"
  /\ UNCHANGED req
  /\ LET k == req.key
         v == req.val
         m == AbsMap
     IN \/ /\ req.op = "get"
           /\ resp' = Resp("get", m[k])
           /\ AbsMap' = m
        \/ /\ req.op = "upd" /\ m[k] # Missing
           /\ resp' = Resp("ok", Missing)
           /\ AbsMap' = [m EXCEPT ![k] = v]
        \/ /\ req.op = "upd" /\ m[k] = Missing
           /\ resp' = Resp("err", Missing)
           /\ AbsMap' = m
        \/ /\ req.op = "ins" /\ m[k] = Missing
           /\ resp' = Resp("ok", Missing)
           /\ AbsMap' = [m EXCEPT ![k] = v]
        \/ /\ req.op = "ins" /\ m[k] # Missing
           /\ resp' = Resp("err", Missing)
           /\ AbsMap' = m
        \/ /\ req.op = "ins"
           /\ resp' = Resp("nospace", Missing)
           /\ AbsMap' = m

AbsReturn ==
  /\ phase = "done"
  /\ phase' = "idle"
  /\ UNCHANGED <<AbsMap, req, resp>>

AbsNext == AbsStart \/ AbsDo \/ AbsReturn

(* Functional refinement: the B-tree implements the simple KV map *)
KVRefinement == AbsInit /\ [][AbsNext]_AbsVars

(* Tree-internal steps never change the abstract map while busy *)
InternalPreservesMap ==
  [][(phase = "busy" /\ phase' = "busy") => AbsMap' = AbsMap]_vars

-------------------------------------------------------------------------
(* Progress / liveness *)
EventuallyQuiescent == (phase # "idle") ~> (phase = "idle")
InfinitelyOftenIdle == []<>(phase = "idle")

THEOREM Spec => []Invariants
THEOREM Spec => KVRefinement
THEOREM Spec => EventuallyQuiescent
=============================================================================
```