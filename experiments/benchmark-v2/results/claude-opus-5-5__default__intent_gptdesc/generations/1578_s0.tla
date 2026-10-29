```tla
GED <<rA, absQ>>
          ELSE /\ rA' = [rA EXCEPT ![c] = n]
               /\ pc' = [pc EXCEPT ![c] = "read2"]
               /\ UNCHANGED <<ret, linRet, absQ>>
  /\ UNCHANGED <<heapVars, op, arg, nd, rB>>

\* Read the neighbour of the end node.  The end node is protected by the
\* client's hazard reference rA[c], so it cannot be reclaimed meanwhile.
PopRead2(c) ==
  /\ pc[c] = "read2"
  /\ op[c] \in PopOps
  /\ rB' = [rB EXCEPT ![c] = IF op[c] = "popL" THEN rightP[rA[c]]
                                                ELSE leftP[rA[c]]]
  /\ pc' = [pc EXCEPT ![c] = "cas"]
  /\ UNCHANGED <<heapVars, op, arg, nd, rA, ret, linRet, absQ>>

\* DCAS that unlinks the end node.  It validates the sentinel link and the
\* link of the end node, then writes the sentinel link and the neighbour's
\* back link.  On success this is the linearization point.
PopCAS(c) ==
  /\ pc[c] = "cas"
  /\ op[c] \in PopOps
  /\ LET n == rA[c]
         m == rB[c]
     IN IF op[c] = "popL"
          THEN IF rightP[LS] = n /\ rightP[n] = m
                 THEN /\ rightP' = [rightP EXCEPT ![LS] = m]
                      /\ leftP'  = [leftP EXCEPT ![m] = LS]
                      /\ ret'    = [ret EXCEPT ![c] = val[n]]
                      /\ linRet' = [linRet EXCEPT ![c] = AbsPopL]
                      /\ absQ'   = IF absQ = << >> THEN absQ ELSE Tail(absQ)
                      /\ pc'     = [pc EXCEPT ![c] = "ret"]
                 ELSE /\ pc' = [pc EXCEPT ![c] = "read1"]
                      /\ UNCHANGED <<rightP, leftP, ret, linRet, absQ>>
          ELSE IF leftP[RS] = n /\ leftP[n] = m
                 THEN /\ leftP'  = [leftP EXCEPT ![RS] = m]
                      /\ rightP' = [rightP EXCEPT ![m] = RS]
                      /\ ret'    = [ret EXCEPT ![c] = val[n]]
                      /\ linRet' = [linRet EXCEPT ![c] = AbsPopR]
                      /\ absQ'   = IF absQ = << >> THEN absQ
                                   ELSE SubSeq(absQ, 1, Len(absQ) - 1)
                      /\ pc'     = [pc EXCEPT ![c] = "ret"]
                 ELSE /\ pc' = [pc EXCEPT ![c] = "read1"]
                      /\ UNCHANGED <<rightP, leftP, ret, linRet, absQ>>
  /\ UNCHANGED <<val, free, op, arg, nd, rA, rB>>

(***************************************************************************)
(* Response: the client returns and drops all of its local references.    *)
(***************************************************************************)
Return(c) ==
  /\ pc[c] = "ret"
  /\ pc'     = [pc EXCEPT ![c] = "idle"]
  /\ op'     = [op EXCEPT ![c] = "none"]
  /\ arg'    = [arg EXCEPT ![c] = NoVal]
  /\ nd'     = [nd EXCEPT ![c] = Null]
  /\ rA'     = [rA EXCEPT ![c] = Null]
  /\ rB'     = [rB EXCEPT ![c] = Null]
  /\ ret'    = [ret EXCEPT ![c] = NoRet]
  /\ linRet' = [linRet EXCEPT ![c] = NoRet]
  /\ UNCHANGED <<heapVars, absQ>>

(***************************************************************************)
(* Garbage collector.  It reclaims a node only if the node is unreachable *)
(* from the sentinels and no client holds a reference to it.              *)
(***************************************************************************)
GC(n) ==
  /\ n \in Garbage
  /\ free'   = free \cup {n}
  /\ val'    = [val EXCEPT ![n] = NoVal]
  /\ rightP' = [rightP EXCEPT ![n] = Null]
  /\ leftP'  = [leftP EXCEPT ![n] = Null]
  /\ UNCHANGED <<localVars, absQ>>

ClientStep(c) ==
  \/ Alloc(c) \/ PushRead(c) \/ PushCAS(c)
  \/ PopRead1(c) \/ PopRead2(c) \/ PopCAS(c)
  \/ Return(c)

Next ==
  \/ \E c \in Clients : Invoke(c) \/ ClientStep(c)
  \/ \E n \in Nodes : GC(n)

\* Clients that are inside an operation are scheduled fairly.  Invocation
\* is not forced.  The collector is fair for every node.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A c \in Clients : WF_vars(ClientStep(c))
  /\ \A n \in Nodes : WF_vars(GC(n))

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK ==
  /\ rightP \in [AllNodes -> AllNodes \cup {Null}]
  /\ leftP  \in [AllNodes -> AllNodes \cup {Null}]
  /\ val    \in [Nodes -> Values \cup {NoVal}]
  /\ free   \subseteq Nodes
  /\ pc     \in [Clients -> {"idle", "alloc", "read1", "read2", "cas", "ret"}]
  /\ op     \in [Clients -> Ops \cup {"none"}]
  /\ arg    \in [Clients -> Values \cup {NoVal}]
  /\ nd     \in [Clients -> AllNodes \cup {Null}]
  /\ rA     \in [Clients -> AllNodes \cup {Null}]
  /\ rB     \in [Clients -> AllNodes \cup {Null}]
  /\ ret    \in [Clients -> Values \cup Results \cup {NoRet}]
  /\ linRet \in [Clients -> Values \cup Results \cup {NoRet}]
  /\ absQ   \in Seq(Values)

\* Structural integrity: the sentinels bound the list, the chain is acyclic
\* and duplicate-free, and the forward and backward links agree.
\* Conjuncts are ordered so that later ones are well defined.
StructuralIntegrity ==
  /\ leftP[LS] = Null /\ rightP[RS] = Null
  /\ \A i \in 1..Len(Chain) : Chain[i] \in Nodes
  /\ \A i, j \in 1..Len(Chain) : i # j => Chain[i] # Chain[j]
  /\ \A i \in 1..Len(Chain) :
        leftP[Chain[i]] = IF i = 1 THEN LS ELSE Chain[i - 1]
  /\ leftP[RS] = IF Len(Chain) = 0 THEN LS ELSE Chain[Len(Chain)]
  /\ (rightP[LS] = RS) <=> (leftP[RS] = LS)

\* The concrete list refines the abstract sequential deque.  This rules out
\* value loss and duplication.
AbstractionOK ==
  /\ Len(Chain) = Len(absQ)
  /\ \A i \in 1..Len(Chain) :
        Chain[i] \in Nodes /\ val[Chain[i]] = absQ[i]

\* Linearizability.  Every completed operation took effect exactly once,
\* at its linearization point, and returned exactly what the sequential
\* deque returned at that point.
Linearizable ==
  \A c \in Clients :
     /\ (pc[c] = "ret") => (linRet[c] # NoRet /\ ret[c] = linRet[c])
     /\ (pc[c] # "ret") => (linRet[c] = NoRet /\ ret[c] = NoRet)

\* Memory safety.  Free slots are neither reachable nor held by any client,
\* and they are scrubbed.  Live nodes hold values.
MemorySafety ==
  /\ free \cap Reach = {}
  /\ free \cap Held = {}
  /\ \A n \in free : val[n] = NoVal /\ rightP[n] = Null /\ leftP[n] = Null
  /\ \A n \in Reach : val[n] \in Values
  /\ \A c, d \in Clients :
        (c # d /\ nd[c] \in Nodes) => nd[c] # nd[d]

\* No deadlock: some step is always possible.
DeadlockFree == ENABLED Next

Invariants ==
  /\ TypeOK
  /\ StructuralIntegrity
  /\ AbstractionOK
  /\ Linearizable
  /\ MemorySafety

\* Action property: a node is never reclaimed while reachable or held.
NoPrematureReclaim ==
  [][\A n \in Nodes :
       (n \notin free /\ n \in free') => (n \notin Reach /\ n \notin Held)]_vars

\* Action property: allocation takes slots only from the free pool.
AllocOnlyFree ==
  [][\A n \in Nodes : (n \in free /\ n \notin free') => n \notin Reach]_vars

(***************************************************************************)
(* Liveness properties (under the fairness assumptions in Spec)           *)
(***************************************************************************)
\* Lock-freedom: while some client is inside an operation, some operation
\* eventually completes.
LockFreedom ==
  (\E c \in Clients : pc[c] \notin {"idle", "ret"})
     ~> (\E c \in Clients : pc[c] = "ret")

\* Every completed operation eventually delivers its response.
ResponseDelivered == \A c \in Clients : (pc[c] = "ret") ~> (pc[c] = "idle")

\* Garbage does not stay garbage forever.
GCCompleteness == \A n \in Nodes : (n \in Garbage) ~> (n \notin Garbage)

THEOREM Spec => []Invariants
THEOREM Spec => NoPrematureReclaim /\ AllocOnlyFree
THEOREM Spec => LockFreedom /\ ResponseDelivered /\ GCCompleteness
=============================================================================
```