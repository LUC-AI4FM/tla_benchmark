---------------------------- MODULE InnerSequential ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, Reg, Adr, Val

RdRequest == [adr : Adr, op : {"Rd"}]
WrRequest == [adr : Adr, val : Val, op : {"Wr"}]
Request   == RdRequest \cup WrRequest

FreeRegValue == [op |-> "Free"]
RegContents  == Request \cup {FreeRegValue} \cup [adr : Adr, val : Val, op : {"Free"}]

CompletedRd == [adr : Adr, val : Val, op : {"Rd"}]

Done == CHOOSE v : v \notin Reg

VARIABLES regFile, opQ, mem

vars == <<regFile, opQ, mem>>

OpQEntry == [req : Request \cup CompletedRd, reg : Reg \cup {Done}]

DataInvariant ==
  /\ regFile \in [Proc -> [Reg -> RegContents]]
  /\ opQ \in [Proc -> Seq(OpQEntry)]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc, r \in Reg :
        LET idx == {i \in DOMAIN opQ[p] : opQ[p][i].reg = r}
        IN  IF regFile[p][r].op = "Free"
              THEN idx = {}
              ELSE Cardinality(idx) = 1

Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeRegValue]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem \in [Adr -> Val]

IssueRequest(proc, req, reg) ==
  /\ regFile[proc][reg].op = "Free"
  /\ regFile' = [regFile EXCEPT ![proc][reg] = req]
  /\ opQ' = [opQ EXCEPT ![proc] = Append(@, [req |-> req, reg |-> reg])]
  /\ UNCHANGED mem

RespondToWr(proc, reg) ==
  /\ regFile[proc][reg].op = "Wr"
  /\ \E i \in DOMAIN opQ[proc] :
        /\ opQ[proc][i].reg = reg
        /\ opQ' = [opQ EXCEPT ![proc][i] = [req |-> opQ[proc][i].req, reg |-> Done]]
  /\ regFile' = [regFile EXCEPT ![proc][reg] = FreeRegValue]
  /\ UNCHANGED mem

RespondToRd(proc, reg) ==
  /\ regFile[proc][reg].op = "Rd"
  /\ \E v \in Val :
       /\ \E i \in DOMAIN opQ[proc] :
            /\ opQ[proc][i].reg = reg
            /\ opQ' = [opQ EXCEPT ![proc][i] =
                         [req |-> [adr |-> regFile[proc][reg].adr, val |-> v, op |-> "Rd"],
                          reg |-> Done]]
       /\ regFile' = [regFile EXCEPT ![proc][reg] =
                         [adr |-> regFile[proc][reg].adr, val |-> v, op |-> "Free"]]
  /\ UNCHANGED mem

RemoveOp(proc) ==
  /\ opQ[proc] # << >>
  /\ Head(opQ[proc]).reg = Done
  /\ LET req == Head(opQ[proc]).req
     IN  IF req.op = "Rd"
           THEN /\ req.val = mem[req.adr]
                /\ mem' = mem
           ELSE mem' = [mem EXCEPT ![req.adr] = req.val]
  /\ opQ' = [opQ EXCEPT ![proc] = Tail(@)]

Internal == \E p \in Proc : RemoveOp(p) /\ UNCHANGED regFile

Next ==
  \/ \E p \in Proc, req \in Request, r \in Reg : IssueRequest(p, req, r)
  \/ \E p \in Proc, r \in Reg : RespondToRd(p, r) \/ RespondToWr(p, r)
  \/ Internal

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc, r \in Reg :
        /\ WF_vars(RespondToRd(p, r))
        /\ WF_vars(RespondToWr(p, r))
  /\ \A p \in Proc : WF_vars(RemoveOp(p) /\ UNCHANGED regFile)

THEOREM Spec => []DataInvariant
=============================================================================