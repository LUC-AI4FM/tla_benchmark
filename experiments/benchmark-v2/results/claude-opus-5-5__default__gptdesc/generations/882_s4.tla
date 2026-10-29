--------------------------- MODULE InnerSequential ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,   \* set of processes
          Adr,    \* set of memory addresses
          Val,    \* set of memory values
          Reg     \* set of register names (per process)

ASSUME Adr # {} /\ Val # {} /\ Reg # {}

Done == CHOOSE d : d \notin Reg

FreeOp == "Free"

Request == [op : {"Rd", "Wr"}, adr : Adr, val : Val]

RegContents == [op : {"Rd", "Wr", FreeOp}, adr : Adr, val : Val]

OpEntry == [req : Request, reg : Reg \cup {Done}]

VARIABLES regFile,  \* regFile[p][r] : contents of register r of process p
          opQ,      \* opQ[p] : sequence of operations issued by p
          mem       \* mem[a] : contents of memory address a

vars == <<regFile, opQ, mem>>

-----------------------------------------------------------------------------
TypeOK ==
  /\ regFile \in [Proc -> [Reg -> RegContents]]
  /\ opQ \in [Proc -> Seq(OpEntry)]
  /\ mem \in [Adr -> Val]

DataInvariant ==
  /\ TypeOK
  /\ \A p \in Proc, r \in Reg :
        /\ (regFile[p][r].op # FreeOp) <=>
              (\E i \in 1..Len(opQ[p]) : opQ[p][i].reg = r)
        /\ \A i, j \in 1..Len(opQ[p]) :
              (opQ[p][i].reg = r /\ opQ[p][j].reg = r) => (i = j)
        /\ \A i \in 1..Len(opQ[p]) :
              (opQ[p][i].reg = r) =>
                 /\ opQ[p][i].req.op = regFile[p][r].op
                 /\ opQ[p][i].req.adr = regFile[p][r].adr
                 /\ (opQ[p][i].req.op = "Wr" =>
                        opQ[p][i].req.val = regFile[p][r].val)

-----------------------------------------------------------------------------
Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |->
                  [op  |-> FreeOp,
                   adr |-> CHOOSE a \in Adr : TRUE,
                   val |-> CHOOSE v \in Val : TRUE]]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem \in [Adr -> Val]

\* Process p issues request req into free register r
Issue(p, r, req) ==
  /\ regFile[p][r].op = FreeOp
  /\ regFile' = [regFile EXCEPT ![p][r] = req]
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r])]
  /\ UNCHANGED mem

\* Index of the queue entry associated with register r of process p
HasEntry(p, r) == \E i \in 1..Len(opQ[p]) : opQ[p][i].reg = r
EntryIdx(p, r) == CHOOSE i \in 1..Len(opQ[p]) : opQ[p][i].reg = r

\* Response to a read request in register r, returning value v
RespondRd(p, r, v) ==
  /\ regFile[p][r].op = "Rd"
  /\ HasEntry(p, r)
  /\ LET i == EntryIdx(p, r) IN
       opQ' = [opQ EXCEPT ![p][i] = [req |-> [@.req EXCEPT !.val = v],
                                     reg |-> Done]]
  /\ regFile' = [regFile EXCEPT ![p][r] = [@ EXCEPT !.op = FreeOp, !.val = v]]
  /\ UNCHANGED mem

\* Response to a write request in register r
RespondWr(p, r) ==
  /\ regFile[p][r].op = "Wr"
  /\ HasEntry(p, r)
  /\ LET i == EntryIdx(p, r) IN
       opQ' = [opQ EXCEPT ![p][i].reg = Done]
  /\ regFile' = [regFile EXCEPT ![p][r].op = FreeOp]
  /\ UNCHANGED mem

Respond(p, r) == (\E v \in Val : RespondRd(p, r, v)) \/ RespondWr(p, r)

\* Internal: remove completed operation from head of p's queue
RemoveOp(p) ==
  /\ opQ[p] # << >>
  /\ Head(opQ[p]).reg = Done
  /\ LET req == Head(opQ[p]).req IN
       IF req.op = "Wr"
         THEN mem' = [mem EXCEPT ![req.adr] = req.val]
         ELSE /\ req.val = mem[req.adr]   \* consistency check for reads
              /\ UNCHANGED mem
  /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED regFile

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : Issue(p, r, req)
  \/ \E p \in Proc, r \in Reg : Respond(p, r)
  \/ \E p \in Proc : RemoveOp(p)

Fairness ==
  /\ \A p \in Proc, r \in Reg : WF_vars(Respond(p, r))
  /\ \A p \in Proc : WF_vars(RemoveOp(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety
THEOREM Spec => []DataInvariant

\* Liveness: every issued request is eventually responded to
EventuallyResponded ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r].op # FreeOp) ~> (regFile[p][r].op = FreeOp)

\* Liveness: completed operations are eventually removed from the queue
EventuallyRemoved ==
  \A p \in Proc :
     (opQ[p] # << >> /\ Head(opQ[p]).reg = Done) ~>
        (opQ[p] = << >> \/ Head(opQ[p]).reg # Done \/ ENABLED RemoveOp(p) = FALSE)

=============================================================================