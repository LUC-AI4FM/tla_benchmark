---------------------------- MODULE InnerSerial ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,        \* set of processes
          Adr,         \* set of memory addresses
          Val,         \* set of memory values
          InitMem,     \* initial memory contents
          InitMemInt   \* set of possible initial values of the interface

VARIABLES memInt,      \* the memory interface
          opQ,         \* opQ[p] = sequence of operations issued by p
          opOrder      \* partial order on operation identifiers

ASSUME InitMem \in [Adr -> Val]

vars == <<memInt, opQ, opOrder>>

-----------------------------------------------------------------------------
(* Requests, replies and special values                                    *)
-----------------------------------------------------------------------------
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal    == CHOOSE v : v \notin Val
Busy     == CHOOSE v : v \notin Val \cup {NoVal}

OpIdSet  == [proc : Proc, idx : Nat]
InitWr   == CHOOSE w : w \notin OpIdSet
NoSource == CHOOSE s : s \notin OpIdSet \cup {InitWr}

Send(p, d)  == memInt' = <<p, d>>
Reply(p, d) == memInt' = <<p, d>>

-----------------------------------------------------------------------------
(* Operation identifiers                                                   *)
-----------------------------------------------------------------------------
opId == UNION { [proc : {p}, idx : DOMAIN opQ[p]] : p \in Proc }

opIdQ(oi) == opQ[oi.proc][oi.idx]

IsWrite(oi)     == opIdQ(oi).req.op = "Wr"
IsWriteTo(oi, a) == IsWrite(oi) /\ opIdQ(oi).req.adr = a
IsDoneRead(oi)  == /\ opIdQ(oi).req.op = "Rd"
                   /\ opIdQ(oi).reg # Busy

-----------------------------------------------------------------------------
(* Serializability: opOrder extends to a total order consistent with      *)
(* program order and read-from constraints.                                *)
-----------------------------------------------------------------------------
Serializable ==
  \E R \in SUBSET (opId \X opId) :
    /\ \A oi \in opId : <<oi, oi>> \notin R
    /\ \A oi, oj \in opId :
          (oi # oj) => (<<oi, oj>> \in R \/ <<oj, oi>> \in R)
    /\ \A oi, oj, ok \in opId :
          (<<oi, oj>> \in R /\ <<oj, ok>> \in R) => <<oi, ok>> \in R
    /\ opOrder \subseteq R
    /\ \A oi, oj \in opId :
          (oi.proc = oj.proc /\ oi.idx < oj.idx) => <<oi, oj>> \in R
    /\ \A oi \in opId :
          IsDoneRead(oi) =>
            LET src == opIdQ(oi).source
                a   == opIdQ(oi).req.adr
            IN  IF src = InitWr
                  THEN ~ \E ow \in opId : IsWriteTo(ow, a) /\ <<ow, oi>> \in R
                  ELSE /\ src \in opId
                       /\ <<src, oi>> \in R
                       /\ ~ \E ow \in opId :
                              /\ IsWriteTo(ow, a)
                              /\ <<src, ow>> \in R
                              /\ <<ow, oi>> \in R

-----------------------------------------------------------------------------
TypeOK ==
  /\ opQ \in [Proc -> Seq([req    : MReq,
                           reg    : Val \cup {NoVal, Busy},
                           source : OpIdSet \cup {InitWr, NoSource}])]
  /\ opOrder \subseteq (opId \X opId)

Init ==
  /\ memInt \in InitMemInt
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = {}

UpdateOpOrder ==
  /\ opOrder' \in SUBSET (opId' \X opId')
  /\ opOrder \subseteq opOrder'
  /\ Serializable'

NoPending(p) == \A i \in DOMAIN opQ[p] : opQ[p][i].reg # Busy

IssueRequest(p, req) ==
  /\ NoPending(p)
  /\ Send(p, req)
  /\ opQ' = [opQ EXCEPT ![p] =
               Append(@, [req |-> req, reg |-> Busy, source |-> NoSource])]
  /\ UpdateOpOrder

RespondToWr(p) ==
  /\ Len(opQ[p]) > 0
  /\ LET i == Len(opQ[p])
     IN  /\ opQ[p][i].reg = Busy
         /\ opQ[p][i].req.op = "Wr"
         /\ Reply(p, NoVal)
         /\ opQ' = [opQ EXCEPT ![p][i].reg = NoVal]
  /\ UpdateOpOrder

RespondToRd(p) ==
  /\ Len(opQ[p]) > 0
  /\ LET i  == Len(opQ[p])
         rq == opQ[p][i].req
     IN  /\ opQ[p][i].reg = Busy
         /\ rq.op = "Rd"
         /\ \E src \in {InitWr} \cup {ow \in opId : IsWriteTo(ow, rq.adr)} :
               LET v == IF src = InitWr THEN InitMem[rq.adr]
                                        ELSE opIdQ(src).req.val
               IN  /\ Reply(p, v)
                   /\ opQ' = [opQ EXCEPT ![p][i] =
                                [@ EXCEPT !.reg = v, !.source = src]]
  /\ UpdateOpOrder

Respond(p) == RespondToRd(p) \/ RespondToWr(p)

Internal ==
  /\ UNCHANGED <<memInt, opQ>>
  /\ UpdateOpOrder

Next ==
  \/ \E p \in Proc, req \in MReq : IssueRequest(p, req)
  \/ \E p \in Proc : Respond(p)
  \/ Internal

OrderPair(oi, oj) ==
  /\ oi # oj
  /\ oi \in opId
  /\ oj \in opId
  /\ Internal
  /\ (<<oi, oj>> \in opOrder') \/ (<<oj, oi>> \in opOrder')

Liveness ==
  /\ \A p \in Proc : WF_vars(Respond(p))
  /\ \A oi, oj \in OpIdSet : WF_vars(OrderPair(oi, oj))

Spec == Init /\ [][Next]_vars /\ Liveness

-----------------------------------------------------------------------------
(* Properties                                                              *)
-----------------------------------------------------------------------------
OrderIsIrreflexive == \A oi \in opId : <<oi, oi>> \notin opOrder

SafetyInv == TypeOK /\ Serializable /\ OrderIsIrreflexive

EventuallyResponds == \A p \in Proc : []<>NoPending(p)

THEOREM Spec => []SafetyInv
=============================================================================