---------------------------- MODULE InnerSequential ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(* Constants and definitions of the RegisterInterface                      *)
(***************************************************************************)
CONSTANTS Proc, Reg, Adr, Val

Request == [adr : Adr, val : Val, op : {"Rd", "Wr"}]

RdRequest == {req \in Request : req.op = "Rd"}
WrRequest == {req \in Request : req.op = "Wr"}

FreeRegValue == CHOOSE v : v \notin Request

VARIABLES regFile, opQ, mem

vars == <<regFile, opQ, mem>>

RegFileTypeInvariant ==
  regFile \in [Proc -> [Reg -> Request \cup {FreeRegValue}]]

(***************************************************************************)
(* Inner sequential memory                                                 *)
(***************************************************************************)
Done == CHOOSE v : v \notin Reg

InitMem == CHOOSE m \in [Adr -> Val] : TRUE

DataInvariant ==
  /\ RegFileTypeInvariant
  /\ opQ \in [Proc -> Seq([req : Request, reg : Reg \cup {Done}])]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc, r \in Reg :
        Cardinality({i \in DOMAIN opQ[p] : opQ[p][i].reg = r}) =
           IF regFile[p][r] = FreeRegValue THEN 0 ELSE 1

Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeRegValue]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem = InitMem

IssueRequest(proc, req, reg) ==
  /\ regFile[proc][reg] = FreeRegValue
  /\ regFile' = [regFile EXCEPT ![proc][reg] = req]
  /\ opQ' = [opQ EXCEPT ![proc] = Append(@, [req |-> req, reg |-> reg])]
  /\ UNCHANGED mem

RespondToRd(proc, reg) ==
  /\ regFile[proc][reg] \in RdRequest
  /\ \E i \in DOMAIN opQ[proc], v \in Val :
        /\ opQ[proc][i].reg = reg
        /\ regFile' = [regFile EXCEPT ![proc][reg] = FreeRegValue]
        /\ opQ' = [opQ EXCEPT ![proc][i] =
                     [req |-> [opQ[proc][i].req EXCEPT !.val = v],
                      reg |-> Done]]
  /\ UNCHANGED mem

RespondToWr(proc, reg) ==
  /\ regFile[proc][reg] \in WrRequest
  /\ \E i \in DOMAIN opQ[proc] :
        /\ opQ[proc][i].reg = reg
        /\ regFile' = [regFile EXCEPT ![proc][reg] = FreeRegValue]
        /\ opQ' = [opQ EXCEPT ![proc][i].reg = Done]
  /\ UNCHANGED mem

RemoveOp(proc) ==
  /\ opQ[proc] # << >>
  /\ Head(opQ[proc]).reg = Done
  /\ LET op == Head(opQ[proc]).req
     IN  /\ (op.op = "Rd") => (op.val = mem[op.adr])
         /\ mem' = IF op.op = "Wr"
                     THEN [mem EXCEPT ![op.adr] = op.val]
                     ELSE mem
  /\ opQ' = [opQ EXCEPT ![proc] = Tail(@)]
  /\ UNCHANGED regFile

Internal == \E proc \in Proc : RemoveOp(proc)

Next ==
  \/ \E proc \in Proc, reg \in Reg :
        \/ \E req \in Request : IssueRequest(proc, req, reg)
        \/ RespondToRd(proc, reg)
        \/ RespondToWr(proc, reg)
  \/ Internal

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A proc \in Proc, reg \in Reg :
        /\ WF_vars(RespondToRd(proc, reg))
        /\ WF_vars(RespondToWr(proc, reg))
  /\ \A proc \in Proc : WF_vars(RemoveOp(proc))

(***************************************************************************)
(* Liveness: every pending request in a register is eventually answered.   *)
(***************************************************************************)
Liveness ==
  \A proc \in Proc, reg \in Reg :
     (regFile[proc][reg] # FreeRegValue) ~> (regFile[proc][reg] = FreeRegValue)

THEOREM Spec => []DataInvariant
THEOREM Spec => Liveness
================================================================================