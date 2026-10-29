---------------------------- MODULE MemoryService ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,   \* finite set of clients
          Reg,    \* finite set of per-client registers
          Adr,    \* finite set of memory addresses
          Val     \* finite set of memory values

ASSUME IsFiniteSet(Proc) /\ IsFiniteSet(Reg) /\ IsFiniteSet(Adr) /\ IsFiniteSet(Val)
ASSUME Val # {}

-----------------------------------------------------------------------------
(* Marker that replaces the register field of a completed queue entry.     *)
Done == CHOOSE v : v \notin Reg

(* Request records *)
RdReq == [op : {"Rd"}, adr : Adr]
WrReq == [op : {"Wr"}, adr : Adr, val : Val]
Request == RdReq \cup WrReq

(* Contents of a register slot *)
FreeReg == [op |-> "Free"]

(* Response recorded for a register *)
NoResp == [op |-> "None"]
Response == [op : {"Rd"}, adr : Adr, val : Val] \cup [op : {"Wr"}, adr : Adr]

(* Entries of the per-client FIFO queue *)
QEntry == [req : Request, reg : Reg \cup {Done}]

MaxQ == Cardinality(Reg)

VARIABLES mem,      \* shared memory: Adr -> Val
          regFile,  \* regFile[p][r] : outstanding request or FreeReg
          opQ,      \* opQ[p] : FIFO queue of QEntry
          resp      \* resp[p][r] : last response delivered for register r

vars == <<mem, regFile, opQ, resp>>

-----------------------------------------------------------------------------
DataInvariant ==
  /\ mem \in [Adr -> Val]
  /\ regFile \in [Proc -> [Reg -> Request \cup {FreeReg}]]
  /\ opQ \in [Proc -> Seq(QEntry)]
  /\ \A p \in Proc : Len(opQ[p]) <= MaxQ
  /\ resp \in [Proc -> [Reg -> Response \cup {NoResp}]]

(* Number of outstanding (not yet done) queue entries for client p, reg r *)
Outstanding(p, r) ==
  Cardinality({i \in 1..Len(opQ[p]) : opQ[p][i].reg = r})

AtMostOneOutstanding ==
  \A p \in Proc, r \in Reg :
     /\ Outstanding(p, r) <= 1
     /\ (regFile[p][r] = FreeReg) <=> (Outstanding(p, r) = 0)
     /\ \A i \in 1..Len(opQ[p]) :
          opQ[p][i].reg = r => opQ[p][i].req = regFile[p][r]

Inv == DataInvariant /\ AtMostOneOutstanding

-----------------------------------------------------------------------------
Init ==
  /\ mem \in [Adr -> Val]
  /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeReg]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ resp = [p \in Proc |-> [r \in Reg |-> NoResp]]

(* A client issues a request into a currently free register. *)
Issue(p, r, req) ==
  /\ regFile[p][r] = FreeReg
  /\ Len(opQ[p]) < MaxQ
  /\ regFile' = [regFile EXCEPT ![p][r] = req]
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r])]
  /\ resp' = [resp EXCEPT ![p][r] = NoResp]
  /\ UNCHANGED mem

(* The service processes the head request of p's queue: it responds,  *)
(* frees the register and marks the queue entry as Done.               *)
Respond(p) ==
  /\ Len(opQ[p]) > 0
  /\ LET e == Head(opQ[p])
         r == e.reg
         req == e.req
     IN  /\ r # Done
         /\ resp' = [resp EXCEPT ![p][r] =
                       IF req.op = "Rd"
                         THEN [op |-> "Rd", adr |-> req.adr, val |-> mem[req.adr]]
                         ELSE [op |-> "Wr", adr |-> req.adr]]
         /\ regFile' = [regFile EXCEPT ![p][r] = FreeReg]
         /\ opQ' = [opQ EXCEPT ![p][1] = [req |-> req, reg |-> Done]]
  /\ UNCHANGED mem

(* A completed entry is removed from the head of the queue; a write   *)
(* becomes visible in memory exactly at this step.                     *)
RemoveHead(p) ==
  /\ Len(opQ[p]) > 0
  /\ Head(opQ[p]).reg = Done
  /\ LET req == Head(opQ[p]).req
     IN  mem' = IF req.op = "Wr"
                  THEN [mem EXCEPT ![req.adr] = req.val]
                  ELSE mem
  /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<regFile, resp>>

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : Issue(p, r, req)
  \/ \E p \in Proc : Respond(p)
  \/ \E p \in Proc : RemoveHead(p)

Fairness ==
  \A p \in Proc : WF_vars(Respond(p)) /\ WF_vars(RemoveHead(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Read consistency: a read response carries the memory value at its *)
(* address at the moment it is responded to.                          *)
ReadConsistency ==
  [][\A p \in Proc :
        Respond(p) /\ Head(opQ[p]).req.op = "Rd"
          => resp'[p][Head(opQ[p]).reg].val = mem[Head(opQ[p]).req.adr]]_vars

(* Memory changes only when a completed write is removed from a head. *)
MemoryAtomicity ==
  [][mem' # mem =>
       \E p \in Proc :
          /\ Len(opQ[p]) > 0
          /\ Head(opQ[p]).reg = Done
          /\ Head(opQ[p]).req.op = "Wr"
          /\ opQ'[p] = Tail(opQ[p])
          /\ mem' = [mem EXCEPT ![Head(opQ[p]).req.adr] = Head(opQ[p]).req.val]]_vars

(* Liveness: every issued request is eventually responded to and its  *)
(* queue entry eventually removed.                                    *)
EventuallyResponded ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r] # FreeReg) ~> (regFile[p][r] = FreeReg)

EventuallyRemoved ==
  \A p \in Proc : (Len(opQ[p]) > 0) ~> (Len(opQ[p]) = 0 \/ Head(opQ[p]).reg # Done)

QueuesDrain ==
  \A p \in Proc : []<>(Len(opQ[p]) = 0) \/ []<>(\E r \in Reg : regFile[p][r] = FreeReg)

Liveness == EventuallyResponded /\ EventuallyRemoved

THEOREM Spec => [](DataInvariant /\ AtMostOneOutstanding)
THEOREM Spec => ReadConsistency /\ MemoryAtomicity /\ Liveness
=============================================================================