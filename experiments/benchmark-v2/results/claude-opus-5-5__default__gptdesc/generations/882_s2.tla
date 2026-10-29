--------------------------- MODULE InnerSequential ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processes
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          Reg,       \* set of register names (per-process register file)
          InitMem    \* initial memory contents

ASSUME InitMem \in [Adr -> Val]

VARIABLES regFile,   \* regFile[p][r] : contents of register r of process p
          opQ,       \* opQ[p] : sequence of operations issued by p
          mem        \* the memory array

vars == <<regFile, opQ, mem>>

-----------------------------------------------------------------------------
(* Requests, values and helper sets                                        *)
-----------------------------------------------------------------------------
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val
NoReq == CHOOSE r : r \notin MReq

RegState == {"Free", "Busy", "Done"}

RegEntry == [state : RegState, req : MReq \cup {NoReq}, val : Val \cup {NoVal}]

OpEntry == [req : MReq, reg : Reg, val : Val \cup {NoVal}, responded : BOOLEAN]

FreeReg == [state |-> "Free", req |-> NoReq, val |-> NoVal]

-----------------------------------------------------------------------------
(* Data invariant                                                          *)
-----------------------------------------------------------------------------
TypeOK ==
  /\ regFile \in [Proc -> [Reg -> RegEntry]]
  /\ opQ \in [Proc -> Seq(OpEntry)]
  /\ mem \in [Adr -> Val]

DataInvariant ==
  /\ TypeOK
  \* A register is busy iff exactly one pending (unresponded) op uses it
  /\ \A p \in Proc, r \in Reg :
        (regFile[p][r].state = "Busy") <=>
           (\E i \in 1..Len(opQ[p]) : /\ ~opQ[p][i].responded
                                      /\ opQ[p][i].reg = r)
  /\ \A p \in Proc : \A i, j \in 1..Len(opQ[p]) :
        (/\ i # j
         /\ ~opQ[p][i].responded
         /\ ~opQ[p][j].responded) => opQ[p][i].reg # opQ[p][j].reg
  \* A pending op's register holds the same request
  /\ \A p \in Proc : \A i \in 1..Len(opQ[p]) :
        ~opQ[p][i].responded =>
            regFile[p][opQ[p][i].reg].req = opQ[p][i].req
  \* Responded writes carry no value; responded reads carry a value
  /\ \A p \in Proc : \A i \in 1..Len(opQ[p]) :
        opQ[p][i].responded =>
           IF opQ[p][i].req.op = "Rd" THEN opQ[p][i].val \in Val
                                      ELSE opQ[p][i].val = NoVal

-----------------------------------------------------------------------------
(* Initial state                                                           *)
-----------------------------------------------------------------------------
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeReg]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem = InitMem

-----------------------------------------------------------------------------
(* Actions                                                                 *)
-----------------------------------------------------------------------------
\* Process p issues request req into a register r that is not busy
Issue(p, r, req) ==
  /\ regFile[p][r].state # "Busy"
  /\ regFile' = [regFile EXCEPT ![p][r] =
                   [state |-> "Busy", req |-> req, val |-> NoVal]]
  /\ opQ' = [opQ EXCEPT ![p] =
               Append(@, [req |-> req, reg |-> r,
                          val |-> NoVal, responded |-> FALSE])]
  /\ UNCHANGED mem

\* Response to a read operation at position i in p's queue
RespondRd(p, i, v) ==
  /\ i \in 1..Len(opQ[p])
  /\ ~opQ[p][i].responded
  /\ opQ[p][i].req.op = "Rd"
  /\ regFile' = [regFile EXCEPT ![p][opQ[p][i].reg] =
                   [state |-> "Done", req |-> opQ[p][i].req, val |-> v]]
  /\ opQ' = [opQ EXCEPT ![p][i].responded = TRUE, ![p][i].val = v]
  /\ UNCHANGED mem

\* Response to a write operation at position i in p's queue
RespondWr(p, i) ==
  /\ i \in 1..Len(opQ[p])
  /\ ~opQ[p][i].responded
  /\ opQ[p][i].req.op = "Wr"
  /\ regFile' = [regFile EXCEPT ![p][opQ[p][i].reg] =
                   [state |-> "Done", req |-> opQ[p][i].req, val |-> NoVal]]
  /\ opQ' = [opQ EXCEPT ![p][i].responded = TRUE]
  /\ UNCHANGED mem

Respond(p) ==
  \E i \in 1..Len(opQ[p]) :
     \/ \E v \in Val : RespondRd(p, i, v)
     \/ RespondWr(p, i)

\* Internal action: remove a completed operation from the head of p's queue,
\* updating memory for writes and checking consistency for reads.
RemoveOp(p) ==
  /\ Len(opQ[p]) > 0
  /\ LET h == Head(opQ[p]) IN
       /\ h.responded
       /\ IF h.req.op = "Wr"
            THEN mem' = [mem EXCEPT ![h.req.adr] = h.req.val]
            ELSE /\ h.val = mem[h.req.adr]
                 /\ UNCHANGED mem
  /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED regFile

Next ==
  \E p \in Proc :
     \/ \E r \in Reg, req \in MReq : Issue(p, r, req)
     \/ Respond(p)
     \/ RemoveOp(p)

-----------------------------------------------------------------------------
(* Specification                                                           *)
-----------------------------------------------------------------------------
Fairness ==
  \A p \in Proc : /\ WF_vars(Respond(p))
                  /\ WF_vars(RemoveOp(p))

Spec == Init /\ [][Next]_vars /\ Fairness

THEOREM Spec => []DataInvariant
=============================================================================