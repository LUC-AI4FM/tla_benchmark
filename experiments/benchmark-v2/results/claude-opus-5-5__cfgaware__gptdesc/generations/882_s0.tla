------------------------------ MODULE InnerSequential ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, Adr, Val, Reg

VARIABLES regFile, opQ, mem

vars == <<regFile, opQ, mem>>

-----------------------------------------------------------------------------
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

Done == "Done"

AnyReq == CHOOSE rq \in MReq : TRUE
AnyVal == CHOOSE v \in Val : TRUE

RegContents == [busy : BOOLEAN, req : MReq, val : Val]

FreeReg == [busy |-> FALSE, req |-> AnyReq, val |-> AnyVal]

OpEntry == [req : MReq, reg : Reg \cup {Done}, val : Val]

DataInvariant ==
  /\ regFile \in [Proc -> [Reg -> RegContents]]
  /\ opQ \in [Proc -> Seq(OpEntry)]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc, r \in Reg :
        regFile[p][r].busy <=>
           \E i \in 1..Len(opQ[p]) : opQ[p][i].reg = r
  /\ \A p \in Proc : \A i, j \in 1..Len(opQ[p]) :
        (i # j /\ opQ[p][i].reg # Done) => opQ[p][i].reg # opQ[p][j].reg

-----------------------------------------------------------------------------
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeReg]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem \in [Adr -> Val]

(* Value a read at position i of p's queue should observe:                 *)
(* the latest earlier write to the same address in the queue, else memory. *)
ReadVal(p, i) ==
  LET a  == opQ[p][i].req.adr
      ws == {j \in 1..(i-1) : /\ opQ[p][j].req.op = "Wr"
                              /\ opQ[p][j].req.adr = a}
  IN  IF ws = {} THEN mem[a]
      ELSE opQ[p][CHOOSE j \in ws : \A k \in ws : k <= j].req.val

IssueRequest(p, req, r) ==
  /\ regFile[p][r].busy = FALSE
  /\ regFile' = [regFile EXCEPT ![p][r] =
                   [busy |-> TRUE, req |-> req, val |-> AnyVal]]
  /\ opQ' = [opQ EXCEPT ![p] =
               Append(@, [req |-> req, reg |-> r,
                          val |-> IF req.op = "Wr" THEN req.val ELSE AnyVal])]
  /\ UNCHANGED mem

RespondRd(p, r) ==
  /\ regFile[p][r].busy = TRUE
  /\ regFile[p][r].req.op = "Rd"
  /\ \E i \in 1..Len(opQ[p]) :
        /\ opQ[p][i].reg = r
        /\ LET v == ReadVal(p, i) IN
             /\ opQ' = [opQ EXCEPT ![p][i] = [@ EXCEPT !.reg = Done, !.val = v]]
             /\ regFile' = [regFile EXCEPT ![p][r] =
                              [busy |-> FALSE, req |-> AnyReq, val |-> v]]
  /\ UNCHANGED mem

RespondWr(p, r) ==
  /\ regFile[p][r].busy = TRUE
  /\ regFile[p][r].req.op = "Wr"
  /\ \E i \in 1..Len(opQ[p]) :
        /\ opQ[p][i].reg = r
        /\ opQ' = [opQ EXCEPT ![p][i] = [@ EXCEPT !.reg = Done]]
  /\ regFile' = [regFile EXCEPT ![p][r] = FreeReg]
  /\ UNCHANGED mem

Rsp(p, r) == RespondRd(p, r) \/ RespondWr(p, r)

RemoveOp(p) ==
  /\ opQ[p] # << >>
  /\ Head(opQ[p]).reg = Done
  /\ LET e == Head(opQ[p]) IN
       IF e.req.op = "Wr"
         THEN mem' = [mem EXCEPT ![e.req.adr] = e.req.val]
         ELSE /\ e.val = mem[e.req.adr]
              /\ UNCHANGED mem
  /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED regFile

Next ==
  \/ \E p \in Proc, req \in MReq, r \in Reg : IssueRequest(p, req, r)
  \/ \E p \in Proc, r \in Reg : Rsp(p, r)
  \/ \E p \in Proc : RemoveOp(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc, r \in Reg : WF_vars(Rsp(p, r))
  /\ \A p \in Proc : WF_vars(RemoveOp(p))

-----------------------------------------------------------------------------
THEOREM Spec => []DataInvariant
=============================================================================