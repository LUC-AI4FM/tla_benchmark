---------------------------- MODULE InnerSequential ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Proc,   \* set of processes
          Adr,    \* set of memory addresses
          Val,    \* set of memory values
          Reg     \* set of register names (per process)

VARIABLES regFile,  \* regFile[p][r] : register file entry of process p
          opQ,      \* opQ[p] : queue of operations issued by p
          mem       \* mem[a] : memory contents

vars == <<regFile, opQ, mem>>

-----------------------------------------------------------------------------
Request == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val
NoReq == CHOOSE q : q \notin Request

RegFileEntry == [busy : BOOLEAN, req : Request \cup {NoReq}, val : Val \cup {NoVal}]

OpQEntry == [req : Request, reg : Reg, val : Val \cup {NoVal}, done : BOOLEAN]

FreeEntry == [busy |-> FALSE, req |-> NoReq, val |-> NoVal]

DataInvariant ==
  /\ regFile \in [Proc -> [Reg -> RegFileEntry]]
  /\ opQ \in [Proc -> Seq(OpQEntry)]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc, r \in Reg :
        regFile[p][r].busy => regFile[p][r].req \in Request

-----------------------------------------------------------------------------
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeEntry]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem \in [Adr -> Val]

\* Indices of not-yet-completed queue entries issued through register r
PendingIdx(p, r) ==
  {i \in 1..Len(opQ[p]) : opQ[p][i].reg = r /\ ~opQ[p][i].done}

\* Process p issues request req into a free register r
IssueRequest(p, req, r) ==
  /\ ~regFile[p][r].busy
  /\ regFile' = [regFile EXCEPT ![p][r] = [busy |-> TRUE, req |-> req, val |-> NoVal]]
  /\ opQ' = [opQ EXCEPT ![p] =
                Append(@, [req |-> req, reg |-> r, val |-> NoVal, done |-> FALSE])]
  /\ UNCHANGED mem

\* Response to a read request in register r
RespondRd(p, r) ==
  /\ regFile[p][r].busy
  /\ regFile[p][r].req.op = "Rd"
  /\ PendingIdx(p, r) # {}
  /\ \E v \in Val :
       LET i == CHOOSE j \in PendingIdx(p, r) : TRUE
       IN  /\ regFile' = [regFile EXCEPT ![p][r].busy = FALSE,
                                         ![p][r].val  = v]
           /\ opQ' = [opQ EXCEPT ![p][i].val  = v,
                                 ![p][i].done = TRUE]
  /\ UNCHANGED mem

\* Response to a write request in register r
RespondWr(p, r) ==
  /\ regFile[p][r].busy
  /\ regFile[p][r].req.op = "Wr"
  /\ PendingIdx(p, r) # {}
  /\ LET i == CHOOSE j \in PendingIdx(p, r) : TRUE
     IN  /\ regFile' = [regFile EXCEPT ![p][r].busy = FALSE]
         /\ opQ' = [opQ EXCEPT ![p][i].done = TRUE]
  /\ UNCHANGED mem

\* Internal step: remove a completed operation from the head of p's queue,
\* updating memory for writes and checking consistency for reads.
RemoveOp(p) ==
  /\ opQ[p] # << >>
  /\ LET h == Head(opQ[p])
     IN  /\ h.done
         /\ IF h.req.op = "Wr"
              THEN mem' = [mem EXCEPT ![h.req.adr] = h.req.val]
              ELSE /\ h.val = mem[h.req.adr]
                   /\ UNCHANGED mem
  /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED regFile

Next ==
  \E p \in Proc :
     \/ \E req \in Request, r \in Reg : IssueRequest(p, req, r)
     \/ \E r \in Reg : RespondRd(p, r) \/ RespondWr(p, r)
     \/ RemoveOp(p)

Fairness ==
  /\ \A p \in Proc, r \in Reg : WF_vars(RespondRd(p, r) \/ RespondWr(p, r))
  /\ \A p \in Proc : WF_vars(RemoveOp(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Liveness: every issued request is eventually responded to
EventuallyResponded ==
  \A p \in Proc, r \in Reg : regFile[p][r].busy ~> ~regFile[p][r].busy

THEOREM Spec => []DataInvariant
THEOREM Spec => EventuallyResponded
=============================================================================