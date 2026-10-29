---------------------------- MODULE InnerSerial ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processes
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          InitMem    \* initial memory contents: a function in [Adr -> Val]

ASSUME InitMem \in [Adr -> Val]

VARIABLES memInt,    \* the memory interface (last communication)
          opQ,       \* opQ[p] : sequence of operations issued by p
          opOrder    \* partial order (set of pairs) over operation ids

vars == <<memInt, opQ, opOrder>>

-----------------------------------------------------------------------------
(* Requests, replies and special values                                     *)
-----------------------------------------------------------------------------
RdReq  == [op : {"Rd"}, adr : Adr]
WrReq  == [op : {"Wr"}, adr : Adr, val : Val]
MReq   == RdReq \cup WrReq

NoVal  == CHOOSE v : v \notin Val
WrAck  == CHOOSE a : a \notin (Val \cup {NoVal})

OpIdUniverse == [proc : Proc, idx : Nat \ {0}]

InitWr   == CHOOSE iw : iw \notin [proc : Proc, idx : Nat]
NoSource == CHOOSE s : s \notin ([proc : Proc, idx : Nat] \cup {InitWr})

-----------------------------------------------------------------------------
(* Operation identifiers                                                    *)
-----------------------------------------------------------------------------
opId == UNION { [proc : {p}, idx : DOMAIN opQ[p]] : p \in Proc }

opIdQ(oi) == opQ[oi.proc][oi.idx]

IsWrite(oi, a) == /\ opIdQ(oi).req.op = "Wr"
                  /\ opIdQ(oi).req.adr = a

IsRead(oi) == opIdQ(oi).req.op = "Rd"

Completed(oi) == opIdQ(oi).reply # NoVal

-----------------------------------------------------------------------------
(* Order relations                                                          *)
-----------------------------------------------------------------------------
Irreflexive(R, S) == \A a \in S : <<a, a>> \notin R

Transitive(R, S) ==
  \A a, b, c \in S : (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R

PartialOrder(R, S) ==
  /\ R \subseteq S \X S
  /\ Irreflexive(R, S)
  /\ Transitive(R, S)

TotalOrder(R, S) ==
  /\ PartialOrder(R, S)
  /\ \A a, b \in S : a # b => (<<a, b>> \in R \/ <<b, a>> \in R)

ProgramOrder(R) ==
  \A oi, oj \in opId :
     (oi.proc = oj.proc /\ oi.idx < oj.idx) => <<oi, oj>> \in R

(* A completed read gets its value from its source write, which is the     *)
(* latest preceding write to the same address in R (or the initial value). *)
GoodRead(R, oi) ==
  LET q == opIdQ(oi)
      a == q.req.adr
  IN  IF q.source = InitWr
        THEN /\ q.reply = InitMem[a]
             /\ \A oj \in opId : IsWrite(oj, a) => <<oi, oj>> \in R
        ELSE /\ q.source \in opId
             /\ IsWrite(q.source, a)
             /\ q.reply = opIdQ(q.source).req.val
             /\ <<q.source, oi>> \in R
             /\ \A oj \in opId :
                  (IsWrite(oj, a) /\ oj # q.source)
                     => ~(<<q.source, oj>> \in R /\ <<oj, oi>> \in R)

Serializable ==
  /\ PartialOrder(opOrder, opId)
  /\ \E R \in SUBSET (opId \X opId) :
        /\ TotalOrder(R, opId)
        /\ opOrder \subseteq R
        /\ ProgramOrder(R)
        /\ \A oi \in opId : (IsRead(oi) /\ Completed(oi)) => GoodRead(R, oi)

-----------------------------------------------------------------------------
(* Type invariant                                                           *)
-----------------------------------------------------------------------------
OpEntry == [req    : MReq,
            reply  : Val \cup {NoVal, WrAck},
            source : [proc : Proc, idx : Nat \ {0}] \cup {InitWr, NoSource}]

TypeInvariant ==
  /\ opQ \in [Proc -> Seq(OpEntry)]
  /\ opOrder \subseteq (opId \X opId)
  /\ memInt \in Proc \X (MReq \cup Val \cup {NoVal, WrAck})

-----------------------------------------------------------------------------
(* Initial state                                                            *)
-----------------------------------------------------------------------------
Init ==
  /\ memInt = <<CHOOSE p \in Proc : TRUE, NoVal>>
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = {}

-----------------------------------------------------------------------------
(* Actions                                                                  *)
-----------------------------------------------------------------------------
(* The new order extends the old one and keeps the history serializable.   *)
ExtendOrder ==
  \E oo \in SUBSET (opId' \X opId') :
     /\ opOrder \subseteq oo
     /\ opOrder' = oo
     /\ Serializable'

IssueRequest(p, req) ==
  /\ \A i \in DOMAIN opQ[p] : opQ[p][i].reply # NoVal
  /\ memInt' = <<p, req>>
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, [req    |-> req,
                                           reply  |-> NoVal,
                                           source |-> NoSource])]
  /\ ExtendOrder

RespondToWr(p, i) ==
  /\ i \in DOMAIN opQ[p]
  /\ opQ[p][i].req.op = "Wr"
  /\ opQ[p][i].reply = NoVal
  /\ memInt' = <<p, WrAck>>
  /\ opQ' = [opQ EXCEPT ![p][i].reply = WrAck]
  /\ ExtendOrder

RespondToRd(p, i) ==
  /\ i \in DOMAIN opQ[p]
  /\ opQ[p][i].req.op = "Rd"
  /\ opQ[p][i].reply = NoVal
  /\ \E src \in ({InitWr} \cup opId), v \in Val :
        /\ memInt' = <<p, v>>
        /\ opQ' = [opQ EXCEPT ![p][i].reply  = v,
                              ![p][i].source = src]
  /\ ExtendOrder

(* Internal step: only extends the order relation, ordering two distinct   *)
(* operations that were previously unordered.                              *)
InternalOrder(oi, oj) ==
  /\ oi \in opId
  /\ oj \in opId
  /\ oi # oj
  /\ <<oi, oj>> \notin opOrder
  /\ <<oj, oi>> \notin opOrder
  /\ \E oo \in SUBSET (opId \X opId) :
        /\ opOrder \subseteq oo
        /\ (<<oi, oj>> \in oo \/ <<oj, oi>> \in oo)
        /\ opOrder' = oo
        /\ Serializable'
  /\ UNCHANGED <<memInt, opQ>>

Internal == \E oi, oj \in opId : InternalOrder(oi, oj)

Next ==
  \/ \E p \in Proc, req \in MReq : IssueRequest(p, req)
  \/ \E p \in Proc, i \in Nat \ {0} : RespondToWr(p, i) \/ RespondToRd(p, i)
  \/ Internal

-----------------------------------------------------------------------------
(* Fairness and specification                                               *)
-----------------------------------------------------------------------------
Fairness ==
  /\ \A p \in Proc, i \in Nat \ {0} :
        /\ WF_vars(RespondToWr(p, i))
        /\ WF_vars(RespondToRd(p, i))
  /\ \A oi, oj \in OpIdUniverse :
        WF_vars(InternalOrder(oi, oj))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties                                                               *)
-----------------------------------------------------------------------------
SafetyInvariant == Serializable

OrderOnlyGrows == [][opOrder \subseteq opOrder']_vars

(* Every issued request eventually receives a response.                    *)
EventuallyResponds ==
  \A p \in Proc, i \in Nat \ {0} :
     (i \in DOMAIN opQ[p] /\ opQ[p][i].reply = NoVal)
        ~> (i \in DOMAIN opQ[p] /\ opQ[p][i].reply # NoVal)

(* Any two distinct operations eventually become ordered.                  *)
EventuallyOrdered ==
  \A oi, oj \in OpIdUniverse :
     (oi \in opId /\ oj \in opId /\ oi # oj)
        ~> (<<oi, oj>> \in opOrder \/ <<oj, oi>> \in opOrder)

THEOREM Spec => [](TypeInvariant /\ SafetyInvariant)
THEOREM Spec => OrderOnlyGrows
THEOREM Spec => EventuallyResponds /\ EventuallyOrdered
=============================================================================