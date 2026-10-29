------------------------------ MODULE MCInnerSerial ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Adr, Val, Proc, Reg, InitMem, MaxQLen

VARIABLES regFile, opQ, opOrder, mem

vars == <<regFile, opQ, opOrder, mem>>

-----------------------------------------------------------------------------
MCNat == 0 .. MaxQLen

MCInitMem == CHOOSE f \in [Adr -> Val] : TRUE

Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen
-----------------------------------------------------------------------------

Request  == [op : {"Rd", "Wr"}, adr : Adr, val : Val]
RegValue == [op : {"Rd", "Wr", "Free"}, adr : Adr, val : Val]

FreeReg == [op  |-> "Free",
            adr |-> CHOOSE a \in Adr : TRUE,
            val |-> CHOOSE v \in Val : TRUE]

OpIdSet == [proc : Proc, idx : Nat]

InitWr == CHOOSE v : v \notin [proc : Proc, idx : Nat]

Done == CHOOSE v : v \notin [req : Request, reg : Reg]

opId == {oi \in OpIdSet : oi.idx \in DOMAIN opQ[oi.proc]}

opIdQ(oi) == opQ[oi.proc][oi.idx]

Ordered(oi) == <<InitWr, oi>> \in opOrder

OrderedOps == {pr[2] : pr \in opOrder}

-----------------------------------------------------------------------------
DataInvariant ==
  /\ regFile \in [Proc -> [Reg -> RegValue]]
  /\ opQ \in [Proc -> Seq([req : Request, reg : Reg] \cup {Done})]
  /\ mem \in [Adr -> Val]
  /\ opOrder \subseteq (OpIdSet \cup {InitWr}) \X OpIdSet
  /\ \A p \in Proc, r \in Reg :
        regFile[p][r].op # "Free" =>
          Cardinality({i \in DOMAIN opQ[p] :
                         opQ[p][i] # Done /\ opQ[p][i].reg = r}) = 1

-----------------------------------------------------------------------------
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeReg]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = {}
  /\ mem = InitMem

IssueRequest(p, req, r) ==
  /\ regFile[p][r].op = "Free"
  /\ regFile' = [regFile EXCEPT ![p][r] = req]
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r])]
  /\ UNCHANGED <<opOrder, mem>>

Serialize(p, i) ==
  LET oi == [proc |-> p, idx |-> i]
      e  == opQ[p][i]
  IN  /\ i \in 1 .. Len(opQ[p])
      /\ e # Done
      /\ ~Ordered(oi)
      /\ \A j \in 1 .. (i - 1) :
            \/ opQ[p][j] = Done
            \/ Ordered([proc |-> p, idx |-> j])
      /\ opOrder' = opOrder \cup
                      {<<x, oi>> : x \in OrderedOps \cup {InitWr}}
      /\ IF e.req.op = "Wr"
           THEN /\ mem' = [mem EXCEPT ![e.req.adr] = e.req.val]
                /\ UNCHANGED opQ
           ELSE /\ opQ' = [opQ EXCEPT ![p][i] =
                             [req |-> [e.req EXCEPT !.val = mem[e.req.adr]],
                              reg |-> e.reg]]
                /\ UNCHANGED mem
      /\ UNCHANGED regFile

Respond(p, r) ==
  /\ regFile[p][r].op # "Free"
  /\ \E i \in 1 .. Len(opQ[p]) :
        /\ opQ[p][i] # Done
        /\ opQ[p][i].reg = r
        /\ Ordered([proc |-> p, idx |-> i])
        /\ regFile' = [regFile EXCEPT ![p][r] =
                         [op  |-> "Free",
                          adr |-> opQ[p][i].req.adr,
                          val |-> opQ[p][i].req.val]]
        /\ opQ' = [opQ EXCEPT ![p][i] = Done]
  /\ UNCHANGED <<opOrder, mem>>

Ren(p, x) ==
  IF x # InitWr /\ x.proc = p
    THEN [proc |-> p, idx |-> x.idx - 1]
    ELSE x

RemoveOp(p) ==
  LET rem == [proc |-> p, idx |-> 1]
  IN  /\ Len(opQ[p]) > 0
      /\ Head(opQ[p]) = Done
      /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]
      /\ opOrder' = {<<Ren(p, pr[1]), Ren(p, pr[2])>> :
                       pr \in {q \in opOrder : q[1] # rem /\ q[2] # rem}}
      /\ UNCHANGED <<regFile, mem>>

Next ==
  \/ \E p \in Proc, req \in Request, r \in Reg : IssueRequest(p, req, r)
  \/ \E p \in Proc, i \in MCNat : Serialize(p, i)
  \/ \E p \in Proc, r \in Reg : Respond(p, r)
  \/ \E p \in Proc : RemoveOp(p)

Liveness ==
  /\ \A p \in Proc : WF_vars(\E i \in Nat : Serialize(p, i))
  /\ \A p \in Proc, r \in Reg : WF_vars(Respond(p, r))
  /\ \A p \in Proc : WF_vars(RemoveOp(p))

Spec == Init /\ [][Next]_vars /\ Liveness

-----------------------------------------------------------------------------
AlwaysResponds ==
  /\ \A p \in Proc, r \in Reg :
        (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")
  /\ \A oi \in [proc : Proc, idx : Nat] :
        (oi \in opId /\ opIdQ(oi) # Done) ~>
            (oi \in opId => opIdQ(oi) = Done)
=============================================================================