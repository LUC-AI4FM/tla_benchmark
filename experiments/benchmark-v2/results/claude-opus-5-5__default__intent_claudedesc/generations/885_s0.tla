------------------------- MODULE SerialMemoryQueues -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          Reg,       \* set of registers per processor
          InitMem,   \* initial memory contents
          QLen,      \* maximum length of each processor's operation queue
          MaxId      \* bound on operation sequence numbers (model checking)

ASSUME /\ InitMem \in [Adr -> Val]
       /\ QLen \in Nat /\ QLen > 0
       /\ MaxId \in Nat
       /\ Reg # {}

NoVal == CHOOSE v : v \notin Val

Request == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoReq == CHOOSE r : r \notin Request

\* Register states. Operation ids start at 1; id 0 means "no operation".
RegState == [status : {"Free", "Pending", "Done"},
             id     : Nat,
             req    : Request \cup {NoReq},
             val    : Val \cup {NoVal}]

FreeReg == [status |-> "Free", id |-> 0, req |-> NoReq, val |-> NoVal]

QEntry == [reg : Reg, id : Nat, req : Request]

VARIABLES mem,      \* mem[a] : value at address a
          regFile,  \* regFile[p][r] : state of register r of processor p
          opQ,      \* opQ[p] : queue of pending operations of processor p
          nextId    \* nextId[p] : sequence number of p's next operation

vars == <<mem, regFile, opQ, nextId>>

-----------------------------------------------------------------------------
TypeOK ==
  /\ mem \in [Adr -> Val]
  /\ regFile \in [Proc -> [Reg -> RegState]]
  /\ opQ \in [Proc -> Seq(QEntry)]
  /\ nextId \in [Proc -> Nat \ {0}]

Init ==
  /\ mem = InitMem
  /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeReg]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ nextId = [p \in Proc |-> 1]

-----------------------------------------------------------------------------
\* Processor p issues request req using its free register r.
Req(p, r, req) ==
  /\ regFile[p][r].status = "Free"
  /\ Len(opQ[p]) < QLen
  /\ regFile' = [regFile EXCEPT ![p][r] =
                   [status |-> "Pending", id |-> nextId[p],
                    req |-> req, val |-> NoVal]]
  /\ opQ' = [opQ EXCEPT ![p] = Append(@, [reg |-> r, id |-> nextId[p],
                                           req |-> req])]
  /\ nextId' = [nextId EXCEPT ![p] = @ + 1]
  /\ UNCHANGED mem

\* The memory atomically executes the operation at the head of p's queue.
\* Atomic execution in a single step yields a serial order of all operations.
Do(p) ==
  /\ opQ[p] # << >>
  /\ LET e   == Head(opQ[p])
         req == e.req
         res == IF req.op = "Rd" THEN mem[req.adr] ELSE NoVal
     IN  /\ mem' = IF req.op = "Wr"
                     THEN [mem EXCEPT ![req.adr] = req.val]
                     ELSE mem
         /\ regFile' = [regFile EXCEPT ![p][e.reg].status = "Done",
                                       ![p][e.reg].val = res]
  /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED nextId

\* The response in register r is delivered to processor p; register freed.
Rsp(p, r) ==
  /\ regFile[p][r].status = "Done"
  /\ regFile' = [regFile EXCEPT ![p][r] = FreeReg]
  /\ UNCHANGED <<mem, opQ, nextId>>

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : Req(p, r, req)
  \/ \E p \in Proc : Do(p)
  \/ \E p \in Proc, r \in Reg : Rsp(p, r)

Fairness ==
  /\ \A p \in Proc : WF_vars(Do(p))
  /\ \A p \in Proc, r \in Reg : WF_vars(Rsp(p, r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety: serialization / queue-register consistency

\* Every queued entry corresponds to a pending register with matching id/req.
QueueConsistent ==
  \A p \in Proc : \A k \in 1..Len(opQ[p]) :
     LET e == opQ[p][k] IN
       /\ regFile[p][e.reg].status = "Pending"
       /\ regFile[p][e.reg].id = e.id
       /\ regFile[p][e.reg].req = e.req

\* Every pending register has exactly one entry in its processor's queue.
PendingQueued ==
  \A p \in Proc, r \in Reg :
     regFile[p][r].status = "Pending" =>
        Cardinality({k \in 1..Len(opQ[p]) : opQ[p][k].reg = r}) = 1

\* Operations of a processor are serialized in issue order (FIFO).
FIFOOrder ==
  \A p \in Proc : \A i, j \in 1..Len(opQ[p]) :
     i < j => opQ[p][i].id < opQ[p][j].id

\* Operation ids are unique and below the next id to be issued.
UniqueIds ==
  \A p \in Proc : \A r1, r2 \in Reg :
     /\ (regFile[p][r1].status # "Free" =>
            /\ regFile[p][r1].id \in 1..(nextId[p] - 1)
            /\ (r1 # r2 /\ regFile[p][r2].status # "Free") =>
                   regFile[p][r1].id # regFile[p][r2].id)

Serialization ==
  /\ QueueConsistent
  /\ PendingQueued
  /\ FIFOOrder
  /\ UniqueIds

-----------------------------------------------------------------------------
\* Liveness

\* Every issued operation eventually completes and frees its register.
RequestCompletion ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r].status = "Pending") ~> (regFile[p][r].status = "Free")

InQueue(p, i) == \E k \in 1..Len(opQ[p]) : opQ[p][k].id = i
IsDone(p, i)  == \E r \in Reg : /\ regFile[p][r].status = "Done"
                                /\ regFile[p][r].id = i

\* Every operation <<p, i>> that enters the system eventually reaches "done".
ResponseDelivery ==
  \A p \in Proc, i \in 1..MaxId : InQueue(p, i) ~> IsDone(p, i)

-----------------------------------------------------------------------------
\* Model-checking constraints

\* Bounds the natural-number domain (operation ids) to a finite range.
NatConstraint == \A p \in Proc : nextId[p] <= MaxId + 1

\* Queue length bound (also enforced by Req).
QueueConstraint == \A p \in Proc : Len(opQ[p]) <= QLen

StateConstraint == NatConstraint /\ QueueConstraint

THEOREM Spec => [](TypeOK /\ Serialization)
THEOREM Spec => RequestCompletion /\ ResponseDelivery
=============================================================================