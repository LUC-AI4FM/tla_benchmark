```tla
          /\ pc[p] = "pl5"
          /\ IF LeftHat = h[p] /\ RightHat = oh[p]
               THEN /\ LeftHat'  = nd[p]
                    /\ RightHat' = nd[p]
                    /\ Ret(p, "okay", NoVal)
                    /\ PushGhost(p, "L")
               ELSE /\ Goto(p, "pl1")
                    /\ UNCHANGED <<LeftHat, RightHat, retVars, ghostVars>>
          /\ UNCHANGED <<Lp, Rp, Val, freeList, locVars>>

\* DCAS(&LeftHat, &lh->L, lh, lhL, nd, nd)
PL6(p) == /\ pc[p] = "pl6"
          /\ IF LeftHat = h[p] /\ Lp[h[p]] = hn[p]
               THEN /\ LeftHat' = nd[p]
                    /\ Lp' = [Lp EXCEPT ![h[p]] = nd[p]]
                    /\ Ret(p, "okay", NoVal)
                    /\ PushGhost(p, "L")
               ELSE /\ Goto(p, "pl1")
                    /\ UNCHANGED <<LeftHat, Lp, retVars, ghostVars>>
          /\ UNCHANGED <<Rp, Val, RightHat, freeList, locVars>>

-----------------------------------------------------------------------------
(* Pop Right *)

QR1(p) == /\ pc[p] = "qr1"
          /\ h' = [h EXCEPT ![p] = RightHat]
          /\ Goto(p, "qr2")
          /\ UNCHANGED <<memVars, op, arg, nd, oh, hn, retVars, ghostVars>>

QR2(p) == /\ pc[p] = "qr2"
          /\ oh' = [oh EXCEPT ![p] = LeftHat]
          /\ Goto(p, "qr3")
          /\ UNCHANGED <<memVars, op, arg, nd, h, hn, retVars, ghostVars>>

\* if (rh->R == rh) return "empty"
QR3(p) == /\ pc[p] = "qr3"
          /\ IF Rp[h[p]] = h[p]
               THEN /\ Ret(p, "empty", NoVal)
                    /\ errs' = IF sawEmpty[p] \/ absQ = <<>>
                                 THEN errs ELSE errs \cup {"empty"}
               ELSE /\ Goto(p, IF h[p] = oh[p] THEN "qr4" ELSE "qr5")
                    /\ UNCHANGED <<retVars, errs>>
          /\ UNCHANGED <<memVars, locVars, absQ, pushed, popped>>

\* DCAS(&RightHat, &LeftHat, rh, lh, Dummy, Dummy)
QR4(p) == /\ pc[p] = "qr4"
          /\ IF RightHat = h[p] /\ LeftHat = oh[p]
               THEN /\ RightHat' = Dummy
                    /\ LeftHat'  = Dummy
                    /\ PopGhost(h[p], "R")
                    /\ Goto(p, "popret")
               ELSE /\ Goto(p, "qr1")
                    /\ UNCHANGED <<LeftHat, RightHat, ghostVars>>
          /\ UNCHANGED <<Lp, Rp, Val, freeList, locVars, retVars>>

QR5(p) == /\ pc[p] = "qr5"
          /\ hn' = [hn EXCEPT ![p] = Lp[h[p]]]
          /\ Goto(p, "qr6")
          /\ UNCHANGED <<memVars, op, arg, nd, h, oh, retVars, ghostVars>>

\* DCAS(&RightHat, &rh->L, rh, rhL, rhL, rh)
QR6(p) == /\ pc[p] = "qr6"
          /\ IF RightHat = h[p] /\ Lp[h[p]] = hn[p]
               THEN /\ RightHat' = hn[p]
                    /\ Lp' = [Lp EXCEPT ![h[p]] = h[p]]
                    /\ PopGhost(h[p], "R")
                    /\ Goto(p, "popret")
               ELSE /\ Goto(p, "qr1")
                    /\ UNCHANGED <<RightHat, Lp, ghostVars>>
          /\ UNCHANGED <<Rp, Val, LeftHat, freeList, locVars, retVars>>

-----------------------------------------------------------------------------
(* Pop Left (mirror image of Pop Right) *)

QL1(p) == /\ pc[p] = "ql1"
          /\ h' = [h EXCEPT ![p] = LeftHat]
          /\ Goto(p, "ql2")
          /\ UNCHANGED <<memVars, op, arg, nd, oh, hn, retVars, ghostVars>>

QL2(p) == /\ pc[p] = "ql2"
          /\ oh' = [oh EXCEPT ![p] = RightHat]
          /\ Goto(p, "ql3")
          /\ UNCHANGED <<memVars, op, arg, nd, h, hn, retVars, ghostVars>>

\* if (lh->L == lh) return "empty"
QL3(p) == /\ pc[p] = "ql3"
          /\ IF Lp[h[p]] = h[p]
               THEN /\ Ret(p, "empty", NoVal)
                    /\ errs' = IF sawEmpty[p] \/ absQ = <<>>
                                 THEN errs ELSE errs \cup {"empty"}
               ELSE /\ Goto(p, IF h[p] = oh[p] THEN "ql4" ELSE "ql5")
                    /\ UNCHANGED <<retVars, errs>>
          /\ UNCHANGED <<memVars, locVars, absQ, pushed, popped>>

\* DCAS(&LeftHat, &RightHat, lh, rh, Dummy, Dummy)
QL4(p) == /\ pc[p] = "ql4"
          /\ IF LeftHat = h[p] /\ RightHat = oh[p]
               THEN /\ LeftHat'  = Dummy
                    /\ RightHat' = Dummy
                    /\ PopGhost(h[p], "L")
                    /\ Goto(p, "popret")
               ELSE /\ Goto(p, "ql1")
                    /\ UNCHANGED <<LeftHat, RightHat, ghostVars>>
          /\ UNCHANGED <<Lp, Rp, Val, freeList, locVars, retVars>>

QL5(p) == /\ pc[p] = "ql5"
          /\ hn' = [hn EXCEPT ![p] = Rp[h[p]]]
          /\ Goto(p, "ql6")
          /\ UNCHANGED <<memVars, op, arg, nd, h, oh, retVars, ghostVars>>

\* DCAS(&LeftHat, &lh->R, lh, lhR, lhR, lh)
QL6(p) == /\ pc[p] = "ql6"
          /\ IF LeftHat = h[p] /\ Rp[h[p]] = hn[p]
               THEN /\ LeftHat' = hn[p]
                    /\ Rp' = [Rp EXCEPT ![h[p]] = h[p]]
                    /\ PopGhost(h[p], "L")
                    /\ Goto(p, "popret")
               ELSE /\ Goto(p, "ql1")
                    /\ UNCHANGED <<LeftHat, Rp, ghostVars>>
          /\ UNCHANGED <<Lp, Val, RightHat, freeList, locVars, retVars>>

\* Read the popped node's value and return it
PopRet(p) == /\ pc[p] = "popret"
             /\ Ret(p, "okay", Val[h[p]])
             /\ UNCHANGED <<memVars, locVars, ghostVars>>

-----------------------------------------------------------------------------
Step(p) ==
    \/ Start(p) \/ Alloc(p)
    \/ PR1(p) \/ PR2(p) \/ PR3(p) \/ PR4(p) \/ PR5(p) \/ PR6(p)
    \/ PL1(p) \/ PL2(p) \/ PL3(p) \/ PL4(p) \/ PL5(p) \/ PL6(p)
    \/ QR1(p) \/ QR2(p) \/ QR3(p) \/ QR4(p) \/ QR5(p) \/ QR6(p)
    \/ QL1(p) \/ QL2(p) \/ QL3(p) \/ QL4(p) \/ QL5(p) \/ QL6(p)
    \/ PopRet(p)

\* sawEmpty[q] records whether the abstract deque was empty at some point
\* during q's current operation. A pop that returns "empty" is
\* linearizable only if this holds.
Next ==
    \E p \in Procs :
        /\ Step(p)
        /\ sawEmpty' = [q \in Procs |->
                          IF q = p /\ pc[p] = "start"
                            THEN absQ' = <<>>
                            ELSE sawEmpty[q] \/ absQ' = <<>>]

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ Lp \in [Nodes -> Nodes]
    /\ Rp \in [Nodes -> Nodes]
    /\ Val \in [Nodes -> Values \cup {NoVal}]
    /\ LeftHat \in Nodes /\ RightHat \in Nodes
    /\ freeList \subseteq Addrs
    /\ pc \in [Procs -> Labels]
    /\ op \in [Procs -> Ops]
    /\ arg \in [Procs -> Values \cup {NoVal}]
    /\ nd \in [Procs -> Nodes]
    /\ h \in [Procs -> Nodes]
    /\ oh \in [Procs -> Nodes]
    /\ hn \in [Procs -> Nodes]
    /\ retStatus \in [Procs -> Statuses]
    /\ retVal \in [Procs -> Values \cup {NoVal}]
    /\ absQ \in Seq(Addrs)
    /\ pushed \subseteq Addrs /\ popped \subseteq Addrs
    /\ sawEmpty \in [Procs -> BOOLEAN]
    /\ errs \subseteq {"order", "dup", "invalid", "empty"}

\* The concrete contents: walk R pointers from LeftHat to RightHat.
RECURSIVE Chain(_, _)
Chain(n, k) == IF n = RightHat \/ k = 0 THEN <<n>>
               ELSE <<n>> \o Chain(Rp[n], k - 1)

ConcreteEmpty == Rp[RightHat] = RightHat \/ Lp[LeftHat] = LeftHat

ConcreteSeq == IF ConcreteEmpty THEN <<>>
               ELSE Chain(LeftHat, Cardinality(Addrs))

\* 1. Linearizability / deque semantics: every successful pop returns the
\*    element at the corresponding end of the abstract deque.
Linearizable == "order" \notin errs

\* Every popped value was previously pushed.
ValidPops == "invalid" \notin errs

\* 2. No lost values: the concrete linked structure holds exactly the
\*    pushed-but-not-popped values, in deque order.
NoLostValues ==
    /\ Range(absQ) = pushed \ popped
    /\ ConcreteSeq = absQ

\* 3. No pushed value instance is returned by more than one pop.
NoDuplicateReturns == "dup" \notin errs

\* 4. A pop returns "empty" only if the deque was empty at some point
\*    during that operation.
ProperEmptyDetection == "empty" \notin errs

\* A pop that succeeded returned the value that was pushed.
ReturnedValuesPushed ==
    \A p \in Procs :
        (retStatus[p] = "okay" /\ op[p] \in {"popL", "popR"} /\ pc[p] = "start")
            => retVal[p] \in Values

Safety ==
    /\ TypeOK
    /\ Linearizable
    /\ ValidPops
    /\ NoLostValues
    /\ NoDuplicateReturns
    /\ ProperEmptyDetection
    /\ ReturnedValuesPushed

-----------------------------------------------------------------------------
(* Liveness: lock-freedom. Some operation always eventually completes. *)

Progress == []<>(\E p \in Procs : pc[p] = "start")

=============================================================================
```