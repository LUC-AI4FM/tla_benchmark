--------------------------- MODULE InnerSequential ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Adr, Val, Proc, Reg

VARIABLES regFile, opQ, mem

vars == <<regFile, opQ, mem>>

-----------------------------------------------------------------------------
(* Auxiliary definitions                                                   *)
-----------------------------------------------------------------------------

Done == CHOOSE v : v \notin Reg

RdRequest == [adr : Adr, val : Val, op : {"Rd"}]
WrRequest == [adr : Adr, val : Val, op : {"Wr"}]
Request   == RdRequest \cup WrRequest

FreeRegValues == [adr : Adr, val : Val, op : {"Free"}]

RegValue == [adr : Adr, val : Val, op : {"Rd", "Wr", "Free"}]

OpQEntry == [req : Request, reg : Reg \cup {Done}]

\* Indices of entries in opQ[p] that are still bound to register r
PendingIdx(p, r) == {i \in DOMAIN opQ[p] : opQ[p][i].reg = r}

-----------------------------------------------------------------------------
(* Data invariant                                                          *)
-----------------------------------------------------------------------------

DataInvariant ==
  /\ regFile \in [Proc -> [Reg -> RegValue]]
  /\ opQ \in [Proc -> Seq(OpQEntry)]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc, r \in Reg :
        /\ (regFile[p][r].op = "Free") <=> (PendingIdx(p, r) = {})
        /\ Cardinality(PendingIdx(p, r)) <= 1
        /\ \A i \in PendingIdx(p, r) :
              /\ opQ[p][i].req.op  = regFile[p][r].op
              /\ opQ[p][i].req.adr = regFile[p][r].adr

-----------------------------------------------------------------------------
(* Initial state                                                           *)
-----------------------------------------------------------------------------

Init ==
  /\ regFile \in [Proc -> [Reg -> FreeRegValues]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem \in [Adr -> Val]

-----------------------------------------------------------------------------
(* Actions                                                                 *)
-----------------------------------------------------------------------------

IssueRequest(proc, req, reg) ==
  /\ regFile[proc][reg].op = "Free"
  /\ regFile' = [regFile EXCEPT ![proc][reg] = req]
  /\ opQ' = [opQ EXCEPT ![proc] =
               Append(opQ[proc], [req |-> req, reg |-> reg])]
  /\ UNCHANGED mem

RespondToWr(proc, reg) ==
  /\ regFile[proc][reg].op = "Wr"
  /\ regFile' = [regFile EXCEPT ![proc][reg].op = "Free"]
  /\ LET q == opQ[proc]
     IN  opQ' = [opQ EXCEPT ![proc] =
                   [i \in DOMAIN q |->
                      IF q[i].reg = reg
                        THEN [req |-> q[i].req, reg |-> Done]
                        ELSE q[i]]]
  /\ UNCHANGED mem

RespondToRd(proc, reg) ==
  /\ regFile[proc][reg].op = "Rd"
  /\ \E v \in Val :
       /\ regFile' = [regFile EXCEPT ![proc][reg].val = v,
                                     ![proc][reg].op  = "Free"]
       /\ LET q == opQ[proc]
          IN  opQ' = [opQ EXCEPT ![proc] =
                        [i \in DOMAIN q |->
                           IF q[i].reg = reg
                             THEN [req |-> [adr |-> q[i].req.adr,
                                            val |-> v,
                                            op  |-> "Rd"],
                                   reg |-> Done]
                             ELSE q[i]]]
  /\ UNCHANGED mem

RemoveOp(proc) ==
  /\ opQ[proc] # << >>
  /\ Head(opQ[proc]).reg = Done
  /\ LET req == Head(opQ[proc]).req
     IN  /\ \/ req.op = "Wr"
            \/ /\ req.op = "Rd"
               /\ req.val = mem[req.adr]
         /\ mem' = IF req.op = "Wr"
                     THEN [mem EXCEPT ![req.adr] = req.val]
                     ELSE mem
  /\ opQ' = [opQ EXCEPT ![proc] = Tail(opQ[proc])]
  /\ UNCHANGED regFile

Internal(proc) == RemoveOp(proc)

Next ==
  \E proc \in Proc :
     \/ \E req \in Request, reg \in Reg : IssueRequest(proc, req, reg)
     \/ \E reg \in Reg : RespondToRd(proc, reg)
     \/ \E reg \in Reg : RespondToWr(proc, reg)
     \/ Internal(proc)

-----------------------------------------------------------------------------
(* Temporal specification                                                  *)
-----------------------------------------------------------------------------

Fairness ==
  /\ \A proc \in Proc, reg \in Reg :
        /\ WF_vars(RespondToRd(proc, reg))
        /\ WF_vars(RespondToWr(proc, reg))
  /\ \A proc \in Proc : WF_vars(RemoveOp(proc))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties                                                              *)
-----------------------------------------------------------------------------

\* Every issued request eventually receives a response.
EventualResponse ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")

THEOREM Spec => []DataInvariant
THEOREM Spec => EventualResponse
=============================================================================