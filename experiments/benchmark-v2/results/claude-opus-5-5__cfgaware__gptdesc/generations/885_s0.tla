---------------------------- MODULE MCInnerSerial ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Adr, Val, Proc, Reg, InitMem, InitWr, Done, MaxQLen

VARIABLES regFile, opQ, opOrder

vars == <<regFile, opQ, opOrder>>

-----------------------------------------------------------------------------
(* Register interface *)

RdRequest    == [adr : Adr, val : Val, op : {"Rd"}]
WrRequest    == [adr : Adr, val : Val, op : {"Wr"}]
Request      == RdRequest \cup WrRequest
FreeRegValue == [adr : Adr, val : Val, op : {"Free"}]

RegFileTypeInvariant ==
  regFile \in [Proc -> [Reg -> Request \cup FreeRegValue]]

-----------------------------------------------------------------------------
(* InnerSerial *)

opId == UNION {[proc : {p}, idx : DOMAIN opQ[p]] : p \in Proc}

opIdQ(oi) == opQ[oi.proc][oi.idx]

Ordered == {oi \in opId : <<InitWr, oi>> \in opOrder}

DataInvariant ==
  /\ RegFileTypeInvariant
  /\ opQ \in [Proc -> Seq([req : Request, reg : Reg \cup {Done}])]
  /\ opOrder \subseteq (opId \cup {InitWr}) \X opId
  /\ \A p \in Proc, r \in Reg :
       Cardinality({i \in DOMAIN opQ[p] : opQ[p][i].reg = r}) =
         IF regFile[p][r].op = "Free" THEN 0 ELSE 1
  /\ \A oi \in opId :
       (opIdQ(oi).reg = Done) => (oi \in Ordered)
  /\ \A oi, oj \in Ordered :
       oi # oj => (<<oi, oj>> \in opOrder \/ <<oj, oi>> \in opOrder)

ReadVal(oi) ==
  LET a == opIdQ(oi).req.adr
      W == {oj \in opId : /\ <<oj, oi>> \in opOrder
                          /\ opIdQ(oj).req.op = "Wr"
                          /\ opIdQ(oj).req.adr = a}
  IN  IF W = {}
        THEN InitMem[a]
        ELSE opIdQ(CHOOSE w \in W :
                     \A x \in W : x = w \/ <<x, w>> \in opOrder).req.val

Init ==
  /\ regFile \in [Proc -> [Reg -> FreeRegValue]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = {}

IssueRequest(p, req, r) ==
  /\ regFile[p][r].op = "Free"
  /\ regFile' = [regFile EXCEPT ![p][r] = req]
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r])]
  /\ UNCHANGED opOrder

Serialize(oi) ==
  /\ oi \in opId
  /\ oi \notin Ordered
  /\ \A j \in 1..(oi.idx - 1) : [proc |-> oi.proc, idx |-> j] \in Ordered
  /\ opOrder' = opOrder \cup {<<oj, oi>> : oj \in Ordered \cup {InitWr}}
  /\ UNCHANGED <<regFile, opQ>>

Respond(p, r) ==
  /\ regFile[p][r].op # "Free"
  /\ \E i \in DOMAIN opQ[p] : opQ[p][i].reg = r
  /\ LET i  == CHOOSE k \in DOMAIN opQ[p] : opQ[p][k].reg = r
         oi == [proc |-> p, idx |-> i]
     IN  /\ oi \in Ordered
         /\ regFile' = [regFile EXCEPT ![p][r] =
                          [op  |-> "Free",
                           adr |-> @.adr,
                           val |-> IF @.op = "Rd" THEN ReadVal(oi) ELSE @.val]]
         /\ opQ' = [opQ EXCEPT ![p][i].reg = Done]
         /\ UNCHANGED opOrder

Next ==
  \/ \E p \in Proc, req \in Request, r \in Reg : IssueRequest(p, req, r)
  \/ \E oi \in opId : Serialize(oi)
  \/ \E p \in Proc, r \in Reg : Respond(p, r)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc : WF_vars(\E i \in DOMAIN opQ[p] :
                                Serialize([proc |-> p, idx |-> i]))
  /\ \A p \in Proc, r \in Reg : WF_vars(Respond(p, r))

-----------------------------------------------------------------------------
(* Model-checking definitions *)

MCNat == 0..MaxQLen

MCInitMem == CHOOSE f \in [Adr -> Val] : TRUE

Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

AlwaysResponds ==
  /\ \A p \in Proc, r \in Reg :
       (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")
  /\ \A oi \in [proc : Proc, idx : Nat \ {0}] :
       (oi \in opId) ~> (oi \in opId /\ opIdQ(oi).reg = Done)
=============================================================================