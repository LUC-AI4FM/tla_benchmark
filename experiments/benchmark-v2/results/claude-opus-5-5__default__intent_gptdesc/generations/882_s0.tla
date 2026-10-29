------------------------------ MODULE MemoryRequestService ------------------------------
(***************************************************************************)
(* A concurrent request-processing service. Clients in Proc submit read   *)
(* and write requests through per-client registers in Reg. Each issued     *)
(* request is appended to a per-client FIFO queue. The service processes  *)
(* the head of each queue asynchronously: it answers reads from memory and *)
(* frees the register. The completed entry is marked done and later       *)
(* removed from the head of the queue. Removing a completed write updates  *)
(* shared memory atomically. Removing a completed read leaves memory       *)
(* unchanged.                                                              *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of clients
          Reg,       \* set of registers per client
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          NoVal,     \* distinguished "no value" marker
          MaxReq     \* bound on the number of requests per client (finite model)

ASSUME /\ NoVal \notin Val
       /\ MaxReq \in Nat
       /\ Adr # {}
       /\ Val # {}

VARIABLES mem,       \* shared memory: Adr -> Val
          regFile,   \* regFile[p][r] : register state of client p, register r
          queue,     \* queue[p] : FIFO of request entries of client p
          reqCount   \* reqCount[p] : number of requests issued so far by p

vars == <<mem, regFile, queue, reqCount>>

-----------------------------------------------------------------------------
(* Data types *)

ReqId == 0..(MaxReq - 1)

Request == [op : {"rd"}, adr : Adr, val : {NoVal}]
             \cup [op : {"wr"}, adr : Adr, val : Val]

RegEntry == [status : {"free", "busy"},
             op     : {"rd", "wr"},
             adr    : Adr,
             val    : Val \cup {NoVal},
             resp   : Val \cup {NoVal}]

QEntry == [id   : ReqId,
           reg  : Reg,
           op   : {"rd", "wr"},
           adr  : Adr,
           val  : Val \cup {NoVal},
           done : BOOLEAN,
           ans  : Val \cup {NoVal}]

DefaultAdr == CHOOSE a \in Adr : TRUE

FreeReg == [status |-> "free", op |-> "rd", adr |-> DefaultAdr,
            val |-> NoVal, resp |-> NoVal]

-----------------------------------------------------------------------------
(* Initial state *)

Init == /\ mem \in [Adr -> Val]
        /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeReg]]
        /\ queue = [p \in Proc |-> << >>]
        /\ reqCount = [p \in Proc |-> 0]

-----------------------------------------------------------------------------
(* Actions *)

(* Client p issues request req into its free register r. *)
Issue(p, r, req) ==
  /\ regFile[p][r].status = "free"
  /\ reqCount[p] < MaxReq
  /\ regFile' = [regFile EXCEPT ![p][r] =
                   [status |-> "busy", op |-> req.op, adr |-> req.adr,
                    val |-> req.val, resp |-> NoVal]]
  /\ queue' = [queue EXCEPT ![p] =
                 Append(@, [id |-> reqCount[p], reg |-> r, op |-> req.op,
                            adr |-> req.adr, val |-> req.val,
                            done |-> FALSE, ans |-> NoVal])]
  /\ reqCount' = [reqCount EXCEPT ![p] = @ + 1]
  /\ UNCHANGED mem

(* The service processes the head of client p's queue. Reads are answered *)
(* with the current memory value. Both reads and writes free the register *)
(* and mark the queue entry done.                                          *)
Process(p) ==
  /\ queue[p] # << >>
  /\ ~Head(queue[p]).done
  /\ LET e   == Head(queue[p])
         ans == IF e.op = "rd" THEN mem[e.adr] ELSE NoVal
     IN  /\ queue' = [queue EXCEPT ![p][1] =
                        [e EXCEPT !.done = TRUE, !.ans = ans]]
         /\ regFile' = [regFile EXCEPT ![p][e.reg] =
                          [@ EXCEPT !.status = "free", !.resp = ans]]
  /\ UNCHANGED <<mem, reqCount>>

(* Remove a completed entry from the head of client p's queue. A write    *)
(* becomes visible in memory exactly at this step.                         *)
Remove(p) ==
  /\ queue[p] # << >>
  /\ Head(queue[p]).done
  /\ LET e == Head(queue[p])
     IN  mem' = IF e.op = "wr"
                  THEN [mem EXCEPT ![e.adr] = e.val]
                  ELSE mem
  /\ queue' = [queue EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<regFile, reqCount>>

Next == \/ \E p \in Proc, r \in Reg, req \in Request : Issue(p, r, req)
        \/ \E p \in Proc : Process(p)
        \/ \E p \in Proc : Remove(p)

(* Fairness: the service eventually processes and removes every request. *)
Fairness == \A p \in Proc : WF_vars(Process(p)) /\ WF_vars(Remove(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
  /\ mem \in [Adr -> Val]
  /\ regFile \in [Proc -> [Reg -> RegEntry]]
  /\ queue \in [Proc -> Seq(QEntry)]
  /\ reqCount \in [Proc -> 0..MaxReq]

(* Structural constraints on queues *)
QueueStructure ==
  \A p \in Proc :
    /\ Len(queue[p]) <= reqCount[p]
    \* only the head entry can be marked done
    /\ \A i \in 2..Len(queue[p]) : ~queue[p][i].done
    \* ids are strictly increasing (FIFO order) and below the issue count
    /\ \A i, j \in 1..Len(queue[p]) : i < j => queue[p][i].id < queue[p][j].id
    /\ \A i \in 1..Len(queue[p]) : queue[p][i].id < reqCount[p]
    \* entries are well formed with respect to operation kind
    /\ \A i \in 1..Len(queue[p]) :
         LET e == queue[p][i] IN
           /\ (e.op = "wr") => (e.val \in Val /\ e.ans = NoVal)
           /\ (e.op = "rd") => (e.val = NoVal)
           /\ (e.op = "rd" /\ e.done) => e.ans \in Val
           /\ (~e.done) => e.ans = NoVal

OutstandingEntries(p, r) ==
  {i \in 1..Len(queue[p]) : queue[p][i].reg = r /\ ~queue[p][i].done}

(* At most one outstanding request per (client, register), and the       *)
(* register is busy exactly when such a request is outstanding.           *)
AtMostOneOutstanding ==
  \A p \in Proc, r \in Reg :
    /\ Cardinality(OutstandingEntries(p, r)) <= 1
    /\ (regFile[p][r].status = "busy") <=> (OutstandingEntries(p, r) # {})

(* A busy register agrees with its outstanding queue entry *)
RegisterMatchesQueue ==
  \A p \in Proc, r \in Reg :
    \A i \in OutstandingEntries(p, r) :
      /\ queue[p][i].op = regFile[p][r].op
      /\ queue[p][i].adr = regFile[p][r].adr
      /\ queue[p][i].val = regFile[p][r].val

Invariants == TypeOK /\ QueueStructure /\ AtMostOneOutstanding
                     /\ RegisterMatchesQueue

-----------------------------------------------------------------------------
(* Action (step) properties *)

(* Read consistency: when a read is responded to (its register goes from *)
(* busy to free), the returned value is the memory value at the read's    *)
(* address at that moment.                                                 *)
ReadConsistency ==
  [][\A p \in Proc, r \in Reg :
       ( /\ regFile[p][r].status = "busy"
         /\ regFile[p][r].op = "rd"
         /\ regFile'[p][r].status = "free" )
       => /\ regFile'[p][r].resp = mem[regFile[p][r].adr]
          /\ mem' = mem
    ]_vars

RemovedDoneHead(p) ==
  /\ queue[p] # << >>
  /\ Head(queue[p]).done
  /\ queue'[p] = Tail(queue[p])

(* Memory update atomicity: memory changes only when a completed write is *)
(* removed from the head of a queue, and such a removal sets memory to the *)
(* write's value. Removing a completed read leaves memory unchanged.       *)
MemoryUpdateAtomicity ==
  [][ /\ \A p \in Proc :
           RemovedDoneHead(p) =>
             IF Head(queue[p]).op = "wr"
               THEN mem' = [mem EXCEPT ![Head(queue[p]).adr] = Head(queue[p]).val]
               ELSE mem' = mem
      /\ (mem' # mem) =>
           \E p \in Proc :
             /\ RemovedDoneHead(p)
             /\ Head(queue[p]).op = "wr"
             /\ mem' = [mem EXCEPT ![Head(queue[p]).adr] = Head(queue[p]).val]
    ]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

InQueue(p, n) == \E i \in 1..Len(queue[p]) : queue[p][i].id = n

DoneInQueue(p, n) == \E i \in 1..Len(queue[p]) :
                        queue[p][i].id = n /\ queue[p][i].done

(* Every busy register is eventually freed, so every request is responded to. *)
EventuallyResponded ==
  \A p \in Proc, r \in Reg :
    (regFile[p][r].status = "busy") ~> (regFile[p][r].status = "free")

(* Every issued request is eventually marked done *)
EventuallyProcessed ==
  \A p \in Proc, n \in ReqId :
    (InQueue(p, n) /\ ~DoneInQueue(p, n)) ~> (DoneInQueue(p, n) \/ ~InQueue(p, n))

(* Every issued request is eventually removed from its queue *)
EventuallyRemoved ==
  \A p \in Proc, n \in ReqId :
    InQueue(p, n) ~> ~InQueue(p, n)

Liveness == EventuallyResponded /\ EventuallyProcessed /\ EventuallyRemoved

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => ReadConsistency /\ MemoryUpdateAtomicity
THEOREM Spec => Liveness
=============================================================================