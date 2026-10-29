---------------------------- MODULE MCInnerSerial ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the InnerSerial specification.  The         *)
(* InnerSerial memory model is included inline so that this module parses *)
(* on its own.                                                             *)
(*                                                                         *)
(* Each process issues read/write requests into its registers.  Every     *)
(* operation is appended to the process's operation queue opQ[p].          *)
(* Operations are serialized into a single total order opOrder that is     *)
(* consistent with each process's program order.  A read returns the       *)
(* value of the most recent preceding write to the same address in         *)
(* opOrder, or InitMem[adr] if no such write exists.  An operation can be  *)
(* responded to (its register freed) once it has been serialized.         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processes
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          Reg,       \* set of registers per process
          InitMem,   \* initial memory contents, a function in [Adr -> Val]
          MaxQLen    \* bound on the length of each operation queue

VARIABLES regFile, opQ, opOrder

vars == <<regFile, opQ, opOrder>>

-----------------------------------------------------------------------------
(* Model-checking definitions                                              *)
-----------------------------------------------------------------------------
MCNat == 0..MaxQLen

MCInitMem == CHOOSE f \in [Adr -> Val] : TRUE

Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

-----------------------------------------------------------------------------
(* Register interface                                                      *)
-----------------------------------------------------------------------------
RdRequest     == [adr : Adr, val : Val, op : {"Rd"}]
WrRequest     == [adr : Adr, val : Val, op : {"Wr"}]
Request       == RdRequest \cup WrRequest
FreeRegValue  == [adr : Adr, val : Val, op : {"Free"}]
RegFileType   == [Proc -> [Reg -> Request \cup FreeRegValue]]

OpQEntry      == [req : Request, reg : Reg \cup {"Done"}]
OpIdType      == [proc : Proc, idx : Nat \ {0}]

-----------------------------------------------------------------------------
(* Inner serial memory                                                     *)
-----------------------------------------------------------------------------
Max(S) == CHOOSE x \in S : \A y \in S : y \leq x

opId == UNION { [proc : {p}, idx : DOMAIN opQ[p]] : p \in Proc }

opIdQ(oi) == opQ[oi.proc][oi.idx]

InOrder(oi) == \E k \in 1..Len(opOrder) : opOrder[k] = oi

LastWrVal(a) ==
  LET W == { k \in 1..Len(opOrder) :
               /\ opIdQ(opOrder[k]).req.op = "Wr"
               /\ opIdQ(opOrder[k]).req.adr = a }
  IN  IF W = {} THEN InitMem[a]
                ELSE opIdQ(opOrder[Max(W)]).req.val

TypeOK ==
  /\ regFile \in RegFileType
  /\ opQ \in [Proc -> Seq(OpQEntry)]
  /\ opOrder \in Seq(OpIdType)

Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |->
                  [adr |-> CHOOSE a \in Adr : TRUE,
                   val |-> CHOOSE v \in Val : TRUE,
                   op  |-> "Free"]]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ opOrder = << >>

IssueRequest(p, r, req) ==
  /\ regFile[p][r].op = "Free"
  /\ regFile' = [regFile EXCEPT ![p][r] = req]
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r])]
  /\ UNCHANGED opOrder

Serialize(p) ==
  LET i == Cardinality({k \in 1..Len(opOrder) : opOrder[k].proc = p}) + 1
  IN  /\ i \leq Len(opQ[p])
      /\ LET e      == opQ[p][i]
             newReq == IF e.req.op = "Rd"
                         THEN [e.req EXCEPT !.val = LastWrVal(e.req.adr)]
                         ELSE e.req
         IN  /\ opQ' = [opQ EXCEPT ![p][i] = [e EXCEPT !.req = newReq]]
             /\ opOrder' = Append(opOrder, [proc |-> p, idx |-> i])
             /\ UNCHANGED regFile

Respond(p, r) ==
  \E i \in DOMAIN opQ[p] :
    /\ opQ[p][i].reg = r
    /\ InOrder([proc |-> p, idx |-> i])
    /\ regFile' = [regFile EXCEPT ![p][r] =
                     [adr |-> @.adr, val |-> opQ[p][i].req.val, op |-> "Free"]]
    /\ opQ' = [opQ EXCEPT ![p][i].reg = "Done"]
    /\ UNCHANGED opOrder

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : IssueRequest(p, r, req)
  \/ \E p \in Proc : Serialize(p)
  \/ \E p \in Proc, r \in Reg : Respond(p, r)

Fairness ==
  /\ \A p \in Proc : WF_vars(Serialize(p))
  /\ \A p \in Proc, r \in Reg : WF_vars(Respond(p, r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties                                                              *)
-----------------------------------------------------------------------------
\* Every read in the serialization order returns the last preceding write.
SerialReads ==
  \A k \in 1..Len(opOrder) :
    LET e == opIdQ(opOrder[k])
        W == { j \in 1..(k-1) : /\ opIdQ(opOrder[j]).req.op = "Wr"
                                /\ opIdQ(opOrder[j]).req.adr = e.req.adr }
    IN  e.req.op = "Rd" =>
          e.req.val = IF W = {} THEN InitMem[e.req.adr]
                                ELSE opIdQ(opOrder[Max(W)]).req.val

AlwaysResponds ==
  /\ \A p \in Proc, r \in Reg :
       (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")
  /\ \A oi \in [proc : Proc, idx : MCNat] :
       (oi \in opId) ~> (IF oi \in opId THEN opIdQ(oi).reg = "Done"
                                        ELSE TRUE)

THEOREM Spec => [](TypeOK /\ SerialReads)
THEOREM Spec => AlwaysResponds
=============================================================================