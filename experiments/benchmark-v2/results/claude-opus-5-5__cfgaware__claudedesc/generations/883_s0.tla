--------------------------- MODULE SerialMemory ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Register interface (inlined from RegisterInterface)                    *)
(***************************************************************************)
CONSTANTS Adr, Val, Proc, Reg

VARIABLE regFile

RdRequest    == [adr : Adr, val : Val, op : {"Rd"}]
WrRequest    == [adr : Adr, val : Val, op : {"Wr"}]
FreeRegValue == [adr : Adr, val : Val, op : {"Free"}]
Request      == RdRequest \cup WrRequest

RegFileTypeInvariant ==
  regFile \in [Proc -> [Reg -> Request \cup FreeRegValue]]

(***************************************************************************)
(* Serial memory                                                           *)
(***************************************************************************)
CONSTANT InitMem

ASSUME InitMem \in [Adr -> Val]

VARIABLES opQ, opOrder

vars == <<regFile, opQ, opOrder>>

Done   == CHOOSE v : v \notin Reg
InitWr == CHOOSE v : v \notin [proc : Proc, idx : Nat]

opId == [proc : Proc, idx : Nat \ {0}]

opIdQ(oiq) == {i \in opId : i.idx \in DOMAIN oiq[i.proc]}

OpOf(oiq, i) == oiq[i.proc][i.idx]

goodSource(oiq, i) ==
  {InitWr} \cup
  {j \in opIdQ(oiq) : /\ OpOf(oiq, j).req.op = "Wr"
                      /\ OpOf(oiq, j).req.adr = OpOf(oiq, i).req.adr}

OpType ==
  [req : Request, reg : Reg \cup {Done}]
    \cup [req : RdRequest, reg : {Done}, source : opId \cup {InitWr}]

DataInvariant ==
  LET ops == opIdQ(opQ) \cup {InitWr}
  IN  /\ RegFileTypeInvariant
      /\ opQ \in [Proc -> Seq(OpType)]
      /\ opOrder \subseteq (ops \X ops)
      /\ \A p \in Proc, r \in Reg :
           Cardinality({i \in DOMAIN opQ[p] : opQ[p][i].reg = r}) =
             IF regFile[p][r].op = "Free" THEN 0 ELSE 1
      /\ \A p \in Proc : \A i \in DOMAIN opQ[p] :
           opQ[p][i].reg # Done => regFile[p][opQ[p][i].reg] = opQ[p][i].req

TotalOrders(S) ==
  {R \in SUBSET (S \X S) :
     /\ \A i \in S : <<i, i>> \notin R
     /\ \A i, j \in S : i # j => (<<i, j>> \in R \/ <<j, i>> \in R)
     /\ \A i, j, k \in S : (<<i, j>> \in R /\ <<j, k>> \in R) => <<i, k>> \in R}

Serializable(oiq, oor) ==
  LET ids == opIdQ(oiq)
      ops == ids \cup {InitWr}
  IN  \E R \in TotalOrders(ops) :
        /\ oor \subseteq R
        /\ \A i \in ids : <<InitWr, i>> \in R
        /\ \A i, j \in ids :
             (i.proc = j.proc /\ i.idx < j.idx) => <<i, j>> \in R
        /\ \A i \in ids :
             (OpOf(oiq, i).reg = Done /\ OpOf(oiq, i).req.op = "Rd") =>
               LET src == OpOf(oiq, i).source
               IN  /\ <<src, i>> \in R
                   /\ ~ \E w \in ids :
                          /\ OpOf(oiq, w).req.op = "Wr"
                          /\ OpOf(oiq, w).req.adr = OpOf(oiq, i).req.adr
                          /\ <<src, w>> \in R
                          /\ <<w, i>> \in R

Serializable_ == Serializable(opQ, opOrder)

UpdateOpOrder ==
  LET ops == opIdQ(opQ') \cup {InitWr}
  IN  /\ opOrder' \in SUBSET (ops \X ops)
      /\ opOrder \subseteq opOrder'
      /\ Serializable(opQ', opOrder')

Init ==
  /\ regFile \in [Proc -> [Reg -> FreeRegValue]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = {}

IssueRequest(proc, req, reg) ==
  /\ regFile[proc][reg].op = "Free"
  /\ regFile' = [regFile EXCEPT ![proc][reg] = req]
  /\ opQ' = [opQ EXCEPT ![proc] = Append(@, [req |-> req, reg |-> reg])]
  /\ UpdateOpOrder

RespondWr(i) ==
  LET op == OpOf(opQ, i)
  IN  /\ i \in opIdQ(opQ)
      /\ op.reg # Done
      /\ op.req.op = "Wr"
      /\ regFile' = [regFile EXCEPT ![i.proc][op.reg].op = "Free"]
      /\ opQ' = [opQ EXCEPT ![i.proc][i.idx] = [req |-> op.req, reg |-> Done]]
      /\ UpdateOpOrder

RespondRd(i) ==
  LET op == OpOf(opQ, i)
  IN  /\ i \in opIdQ(opQ)
      /\ op.reg # Done
      /\ op.req.op = "Rd"
      /\ \E src \in goodSource(opQ, i) :
           LET v == IF src = InitWr THEN InitMem[op.req.adr]
                                    ELSE OpOf(opQ, src).req.val
           IN  /\ regFile' = [regFile EXCEPT ![i.proc][op.reg] =
                                [adr |-> op.req.adr, val |-> v, op |-> "Free"]]
               /\ opQ' = [opQ EXCEPT ![i.proc][i.idx] =
                            [req    |-> [op.req EXCEPT !.val = v],
                             reg    |-> Done,
                             source |-> src]]
               /\ UpdateOpOrder

Respond(p, r) ==
  \E i \in opIdQ(opQ) :
     /\ i.proc = p
     /\ OpOf(opQ, i).reg = r
     /\ (RespondWr(i) \/ RespondRd(i))

Internal ==
  /\ UNCHANGED <<regFile, opQ>>
  /\ UpdateOpOrder

Next ==
  \/ \E p \in Proc, req \in Request, reg \in Reg : IssueRequest(p, req, reg)
  \/ \E p \in Proc, r \in Reg : Respond(p, r)
  \/ Internal

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc, r \in Reg : WF_vars(Respond(p, r))
  /\ \A i, j \in opId :
       WF_vars(Internal /\ (<<i, j>> \in opOrder' \/ <<j, i>> \in opOrder'))

=============================================================================