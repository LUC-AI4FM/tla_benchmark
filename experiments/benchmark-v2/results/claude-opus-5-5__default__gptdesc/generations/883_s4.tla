---------------------------- MODULE InnerSerial ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processes
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          InitMem    \* initial memory contents

ASSUME InitMem \in [Adr -> Val]

VARIABLES opQ,       \* opQ[p] : sequence of operations issued by process p
          opOrder,   \* partial order (set of pairs) over operation ids
          memInt     \* the memory interface (last message sent/received)

vars == <<opQ, opOrder, memInt>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Requests, special values                                                *)
(***************************************************************************)
RdReq == [op : {"Rd"}, adr : Adr]
WrReq == [op : {"Wr"}, adr : Adr, val : Val]
MReq  == RdReq \cup WrReq

NoVal    == CHOOSE v : v \notin Val
Done     == CHOOSE v : v \notin Val \cup {NoVal}

OpIdUniverse == [proc : Proc, idx : Nat \ {0}]

InitWr   == CHOOSE w : w \notin OpIdUniverse
NoSource == CHOOSE s : s \notin OpIdUniverse \cup {InitWr}

(***************************************************************************)
(* Operation identifiers                                                   *)
(***************************************************************************)
opId == UNION { [proc : {p}, idx : DOMAIN opQ[p]] : p \in Proc }

opIdQ(oi) == opQ[oi.proc][oi.idx]

IsRead(oi)  == opIdQ(oi).req.op = "Rd"
IsWrite(oi) == opIdQ(oi).req.op = "Wr"

IsCompletedRead(oi) == IsRead(oi) /\ opIdQ(oi).reg # NoVal

OpEntry == [req : MReq,
            reg : Val \cup {NoVal, Done},
            source : OpIdUniverse \cup {InitWr, NoSource}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Serializability: opOrder can be extended to a total order on all issued *)
(* operations that is consistent with program order and with the          *)
(* read-from (source) constraints.                                          *)
(***************************************************************************)
GoodSource(oi, R) ==
  LET a == opIdQ(oi).req.adr
      s == opIdQ(oi).source
      IsWrTo(w) == IsWrite(w) /\ opIdQ(w).req.adr = a
  IN  IF s = InitWr
        THEN \A w \in opId : IsWrTo(w) => (<<oi, w>> \in R)
        ELSE /\ s \in opId
             /\ <<s, oi>> \in R
             /\ \A w \in opId :
                   (IsWrTo(w) /\ w # s) => (<<w, s>> \in R \/ <<oi, w>> \in R)

IsTotalOrder(R, S) ==
  /\ \A oi \in S : <<oi, oi>> \notin R
  /\ \A oi, oj, ok \in S :
        (<<oi, oj>> \in R /\ <<oj, ok>> \in R) => (<<oi, ok>> \in R)
  /\ \A oi, oj \in S : (oi # oj) => (<<oi, oj>> \in R \/ <<oj, oi>> \in R)

Serializable ==
  \E R \in SUBSET (opId \X opId) :
     /\ IsTotalOrder(R, opId)
     /\ opOrder \subseteq R
     /\ \A oi, oj \in opId :
           (oi.proc = oj.proc /\ oi.idx < oj.idx) => (<<oi, oj>> \in R)
     /\ \A oi \in opId : IsCompletedRead(oi) => GoodSource(oi, R)

UpdateOpOrder ==
  /\ opOrder' \in SUBSET (opId' \X opId')
  /\ opOrder \subseteq opOrder'
  /\ Serializable'

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type invariant and other safety properties                              *)
(***************************************************************************)
TypeOK ==
  /\ opQ \in [Proc -> Seq(OpEntry)]
  /\ opOrder \subseteq (opId \X opId)

ReadValuesValid ==
  \A oi \in opId :
     IsCompletedRead(oi) =>
        LET s == opIdQ(oi).source
            a == opIdQ(oi).req.adr
        IN  IF s = InitWr
              THEN opIdQ(oi).reg = InitMem[a]
              ELSE /\ s \in opId
                   /\ IsWrite(s)
                   /\ opIdQ(s).req.adr = a
                   /\ opIdQ(oi).reg = opIdQ(s).req.val

WritesValid ==
  \A oi \in opId : IsWrite(oi) => opIdQ(oi).reg \in {NoVal, Done}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state and actions                                               *)
(***************************************************************************)
Init ==
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = {}
  /\ memInt = <<>>

NoPending(p) == \A i \in DOMAIN opQ[p] : opQ[p][i].reg # NoVal

IssueRequest(p, req) ==
  /\ NoPending(p)
  /\ opQ' = [opQ EXCEPT ![p] =
               Append(@, [req |-> req, reg |-> NoVal, source |-> NoSource])]
  /\ memInt' = <<p, req>>
  /\ UpdateOpOrder

RespondRd(p, i) ==
  /\ i \in DOMAIN opQ[p]
  /\ opQ[p][i].req.op = "Rd"
  /\ opQ[p][i].reg = NoVal
  /\ LET a == opQ[p][i].req.adr
     IN  \E src \in {InitWr} \cup opId :
           /\ \/ src = InitWr
              \/ /\ src \in opId
                 /\ IsWrite(src)
                 /\ opIdQ(src).req.adr = a
           /\ LET v == IF src = InitWr THEN InitMem[a]
                                       ELSE opIdQ(src).req.val
              IN  /\ opQ' = [opQ EXCEPT ![p][i] =
                               [@ EXCEPT !.reg = v, !.source = src]]
                  /\ memInt' = <<p, v>>
  /\ UpdateOpOrder

RespondWr(p, i) ==
  /\ i \in DOMAIN opQ[p]
  /\ opQ[p][i].req.op = "Wr"
  /\ opQ[p][i].reg = NoVal
  /\ opQ' = [opQ EXCEPT ![p][i] = [@ EXCEPT !.reg = Done]]
  /\ memInt' = <<p, Done>>
  /\ UpdateOpOrder

Respond(p) == \E i \in DOMAIN opQ[p] : RespondRd(p, i) \/ RespondWr(p, i)

Internal ==
  /\ UNCHANGED <<opQ, memInt>>
  /\ UpdateOpOrder
  /\ opOrder' # opOrder

Next ==
  \/ \E p \in Proc : \E req \in MReq : IssueRequest(p, req)
  \/ \E p \in Proc : Respond(p)
  \/ Internal

-----------------------------------------------------------------------------
(***************************************************************************)
(* Fairness and specification                                              *)
(***************************************************************************)
OrderStep(oi, oj) ==
  /\ Internal
  /\ oi # oj
  /\ oi \in opId
  /\ oj \in opId
  /\ ({<<oi, oj>>, <<oj, oi>>} \cap opOrder') # {}

Fairness ==
  /\ \A p \in Proc : WF_vars(Respond(p))
  /\ \A oi, oj \in OpIdUniverse : WF_vars(OrderStep(oi, oj))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
EveryRequestAnswered ==
  \A p \in Proc : \A i \in Nat \ {0} :
     (i \in DOMAIN opQ[p] /\ opQ[p][i].reg = NoVal)
        ~> (i \in DOMAIN opQ[p] /\ opQ[p][i].reg # NoVal)

EventuallyOrdered ==
  \A oi, oj \in OpIdUniverse :
     (oi \in opId /\ oj \in opId /\ oi # oj)
        ~> (({<<oi, oj>>, <<oj, oi>>} \cap opOrder) # {})

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Serializable /\ ReadValuesValid /\ WritesValid)
THEOREM Spec => EveryRequestAnswered /\ EventuallyOrdered
=============================================================================