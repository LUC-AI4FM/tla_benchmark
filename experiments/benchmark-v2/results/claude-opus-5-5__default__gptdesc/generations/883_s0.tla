------------------------------ MODULE InnerSerial ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processes
          Adr,       \* set of memory addresses
          Val,       \* set of data values
          InitVal,   \* initial value of every address
          MaxQLen,   \* bound on number of operations issued per process
          NoVal,     \* marker: operation not yet responded / no source yet
          Ack,       \* response value for a completed write
          InitWr     \* fictitious "initial write" a read may read from

ASSUME /\ InitVal \in Val
       /\ MaxQLen \in Nat \ {0}
       /\ NoVal \notin Val
       /\ Ack \notin Val \cup {NoVal}
       /\ InitWr \notin {NoVal, Ack}

VARIABLES opQ,     \* opQ[p] : sequence of operations issued by process p
          opOrder  \* partial order on operation identifiers

vars == <<opQ, opOrder>>

-----------------------------------------------------------------------------
RdRequest == [type : {"Rd"}, adr : Adr]
WrRequest == [type : {"Wr"}, adr : Adr, val : Val]
Request   == RdRequest \cup WrRequest

AllOpIds == [proc : Proc, idx : 1..MaxQLen]

OpRecord == [req : Request,
             rsp : Val \cup {NoVal, Ack},
             src : AllOpIds \cup {InitWr, NoVal}]

OpIdsOf(q) == UNION { {[proc |-> p, idx |-> i] : i \in 1..Len(q[p])} : p \in Proc }

OpIds == OpIdsOf(opQ)

Op(q, oi) == q[oi.proc][oi.idx]

IsRead(q, oi)  == Op(q, oi).req.type = "Rd"
IsWrite(q, oi) == Op(q, oi).req.type = "Wr"
IsDone(q, oi)  == Op(q, oi).rsp # NoVal

ProgramOrder(q) ==
  {pr \in OpIdsOf(q) \X OpIdsOf(q) :
      pr[1].proc = pr[2].proc /\ pr[1].idx < pr[2].idx}

IsPartialOrder(R, S) ==
  /\ R \subseteq S \X S
  /\ \A a \in S : <<a, a>> \notin R
  /\ \A a, b, c \in S : (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R

RECURSIVE CloseN(_, _, _)
CloseN(R, S, n) ==
  IF n = 0 THEN R
  ELSE CloseN(R \cup {pr \in S \X S :
                        \E b \in S : <<pr[1], b>> \in R /\ <<b, pr[2]>> \in R},
              S, n - 1)

TC(R, S) == CloseN(R, S, Cardinality(S))

\* All total orders on S, represented as bijections from 1..|S| to S
Perms(S) ==
  {f \in [1..Cardinality(S) -> S] :
      \A i, j \in 1..Cardinality(S) : i # j => f[i] # f[j]}

\* The history q with order ord is serializable: some total order extending
\* ord makes every completed read return the value of its source write, which
\* is the last write to the same address preceding the read.
Serializable(q, ord) ==
  LET ids == OpIdsOf(q)
  IN \E f \in Perms(ids) :
       LET pos(oi)   == CHOOSE i \in DOMAIN f : f[i] = oi
           Bef(a, b) == pos(a) < pos(b)
       IN /\ \A pr \in ord : Bef(pr[1], pr[2])
          /\ \A r \in ids :
               (IsRead(q, r) /\ IsDone(q, r)) =>
                 (LET o == Op(q, r)
                  IN IF o.src = InitWr
                     THEN /\ o.rsp = InitVal
                          /\ ~ \E w \in ids :
                                 /\ IsWrite(q, w)
                                 /\ Op(q, w).req.adr = o.req.adr
                                 /\ Bef(w, r)
                     ELSE /\ o.src \in ids
                          /\ IsWrite(q, o.src)
                          /\ Op(q, o.src).req.adr = o.req.adr
                          /\ o.rsp = Op(q, o.src).req.val
                          /\ Bef(o.src, r)
                          /\ ~ \E w \in ids :
                                 /\ IsWrite(q, w)
                                 /\ Op(q, w).req.adr = o.req.adr
                                 /\ Bef(o.src, w)
                                 /\ Bef(w, r))

-----------------------------------------------------------------------------
Init == /\ opQ = [p \in Proc |-> << >>]
        /\ opOrder = {}

IssueRequest(p, req) ==
  /\ Len(opQ[p]) < MaxQLen
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, [req |-> req, rsp |-> NoVal, src |-> NoVal])]
  /\ opOrder' = TC(opOrder \cup ProgramOrder(opQ'), OpIdsOf(opQ'))
  /\ Serializable(opQ', opOrder')

RespondWr(p, i) ==
  /\ i \in 1..Len(opQ[p])
  /\ opQ[p][i].req.type = "Wr"
  /\ opQ[p][i].rsp = NoVal
  /\ opQ' = [opQ EXCEPT ![p][i].rsp = Ack]
  /\ UNCHANGED opOrder

RespondRd(p, i) ==
  /\ i \in 1..Len(opQ[p])
  /\ opQ[p][i].req.type = "Rd"
  /\ opQ[p][i].rsp = NoVal
  /\ \E s \in OpIds \cup {InitWr} :
       LET r      == [proc |-> p, idx |-> i]
           v      == IF s = InitWr THEN InitVal ELSE Op(opQ, s).req.val
           newOrd == IF s = InitWr THEN opOrder
                                   ELSE TC(opOrder \cup {<<s, r>>}, OpIds)
       IN /\ (s = InitWr) \/ (IsWrite(opQ, s) /\ Op(opQ, s).req.adr = opQ[p][i].req.adr)
          /\ opQ' = [opQ EXCEPT ![p][i].rsp = v, ![p][i].src = s]
          /\ opOrder' = newOrd
          /\ Serializable(opQ', opOrder')

InternalOrder(a, b) ==
  /\ a \in OpIds
  /\ b \in OpIds
  /\ a # b
  /\ <<a, b>> \notin opOrder
  /\ <<b, a>> \notin opOrder
  /\ opOrder' = TC(opOrder \cup {<<a, b>>}, OpIds)
  /\ Serializable(opQ, opOrder')
  /\ UNCHANGED opQ

Next ==
  \/ \E p \in Proc, req \in Request : IssueRequest(p, req)
  \/ \E p \in Proc, i \in 1..MaxQLen : RespondRd(p, i) \/ RespondWr(p, i)
  \/ \E a, b \in AllOpIds : InternalOrder(a, b)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc, i \in 1..MaxQLen : WF_vars(RespondRd(p, i) \/ RespondWr(p, i))
  /\ \A a, b \in AllOpIds : WF_vars(InternalOrder(a, b) \/ InternalOrder(b, a))

-----------------------------------------------------------------------------
\* Safety invariants
TypeOK ==
  /\ opQ \in [Proc -> Seq(OpRecord)]
  /\ \A p \in Proc : Len(opQ[p]) <= MaxQLen
  /\ opOrder \subseteq OpIds \X OpIds

OrderIsPartialOrder == IsPartialOrder(opOrder, OpIds)

ProgramOrderRespected == ProgramOrder(opQ) \subseteq opOrder

ReadSourceOrdered ==
  \A r \in OpIds :
    (IsRead(opQ, r) /\ IsDone(opQ, r) /\ Op(opQ, r).src # InitWr)
      => <<Op(opQ, r).src, r>> \in opOrder

SerializableInv == Serializable(opQ, opOrder)

\* Liveness properties
EveryOpResponds ==
  \A p \in Proc, i \in 1..MaxQLen :
    (i <= Len(opQ[p])) ~> (i <= Len(opQ[p]) /\ opQ[p][i].rsp # NoVal)

DistinctOpsOrdered ==
  \A a, b \in AllOpIds :
    (a # b) => ((a \in OpIds /\ b \in OpIds)
                  ~> (<<a, b>> \in opOrder \/ <<b, a>> \in opOrder))

THEOREM Spec => [](TypeOK /\ OrderIsPartialOrder /\ ProgramOrderRespected
                   /\ ReadSourceOrdered /\ SerializableInv)
THEOREM Spec => EveryOpResponds /\ DistinctOpsOrdered
=============================================================================