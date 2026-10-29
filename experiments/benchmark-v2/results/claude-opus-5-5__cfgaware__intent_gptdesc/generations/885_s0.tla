------------------------------- MODULE MemoryCoordinator -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          InitMem,   \* initial memory contents, a function Adr -> Val
          MaxQLen    \* bound on the per-processor queue length

ASSUME MaxQLen \in Nat /\ MaxQLen > 0

-----------------------------------------------------------------------------
(* Register identifiers per processor: one register per outstanding operation. *)
Reg == 1..MaxQLen

(* Status marking that a response has been delivered to the processor. *)
Done == "Done"

Status == {"free", "enq", "busy", "committed", Done}
OpKind == {"Rd", "Wr"}

(* Initial (idle) contents of a register. *)
InitWr == [state |-> "free",
           op    |-> "Wr",
           adr   |-> CHOOSE a \in Adr : TRUE,
           val   |-> CHOOSE v \in Val : TRUE,
           id    |-> 0]

(* Model-checking overrides. *)
MCInitMem == [a \in Adr |-> CHOOSE v \in Val : TRUE]
MCNat == 0..2

-----------------------------------------------------------------------------
VARIABLES mem,    \* shared memory state, Adr -> Val
          reg,    \* reg[p][r]: per-processor operation registers
          queue,  \* queue[p]: sequence of registers awaiting service (FIFO)
          ctr,    \* ctr[p]: next operation identifier for processor p
          log     \* log[a]: the total (linearization) order of committed ops on a

vars == <<mem, reg, queue, ctr, log>>

LogEntry == [proc : Proc, id : Nat, op : OpKind, val : Val]

-----------------------------------------------------------------------------
Init == /\ mem = InitMem
        /\ reg = [p \in Proc |-> [r \in Reg |-> InitWr]]
        /\ queue = [p \in Proc |-> << >>]
        /\ ctr = [p \in Proc |-> 0]
        /\ log = [a \in Adr |-> << >>]

(* A processor creates and enqueues a new read or write operation. *)
Issue(p, r, op, a, v) ==
  /\ reg[p][r].state = "free"
  /\ Len(queue[p]) < MaxQLen
  /\ reg' = [reg EXCEPT ![p][r] = [state |-> "enq", op |-> op, adr |-> a,
                                   val |-> v, id |-> ctr[p]]]
  /\ queue' = [queue EXCEPT ![p] = Append(@, r)]
  /\ ctr' = [ctr EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<mem, log>>

IssueRead(p, r, a) == Issue(p, r, "Rd", a, CHOOSE v \in Val : TRUE)
IssueWrite(p, r, a, v) == Issue(p, r, "Wr", a, v)

(* The coordinator starts serving the oldest pending operation of p.
   At most one operation per processor is in service, preserving program order. *)
Start(p) ==
  /\ queue[p] # << >>
  /\ \A r \in Reg : reg[p][r].state # "busy"
  /\ LET r == Head(queue[p]) IN
       /\ reg[p][r].state = "enq"
       /\ reg' = [reg EXCEPT ![p][r].state = "busy"]
  /\ queue' = [queue EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED <<mem, ctr, log>>

(* Linearization point: the operation takes effect atomically on memory. *)
Commit(p, r) ==
  /\ reg[p][r].state = "busy"
  /\ LET o == reg[p][r]
         a == o.adr
         rv == IF o.op = "Rd" THEN mem[a] ELSE o.val
     IN /\ mem' = IF o.op = "Wr" THEN [mem EXCEPT ![a] = o.val] ELSE mem
        /\ reg' = [reg EXCEPT ![p][r].state = "committed", ![p][r].val = rv]
        /\ log' = [log EXCEPT ![a] = Append(@, [proc |-> p, id |-> o.id,
                                                op |-> o.op, val |-> rv])]
  /\ UNCHANGED <<queue, ctr>>

(* The response (read value or write acknowledgement) is delivered. *)
Respond(p, r) ==
  /\ reg[p][r].state = "committed"
  /\ reg' = [reg EXCEPT ![p][r].state = Done]
  /\ UNCHANGED <<mem, queue, ctr, log>>

(* The processor observes the response and frees the register. *)
Free(p, r) ==
  /\ reg[p][r].state = Done
  /\ reg' = [reg EXCEPT ![p][r] = InitWr]
  /\ UNCHANGED <<mem, queue, ctr, log>>

Next == \E p \in Proc :
          \/ \E r \in Reg, a \in Adr : IssueRead(p, r, a)
          \/ \E r \in Reg, a \in Adr, v \in Val : IssueWrite(p, r, a, v)
          \/ Start(p)
          \/ \E r \in Reg : Commit(p, r) \/ Respond(p, r) \/ Free(p, r)

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A p \in Proc : WF_vars(Start(p))
        /\ \A p \in Proc, r \in Reg : WF_vars(Commit(p, r)) /\ WF_vars(Respond(p, r))

-----------------------------------------------------------------------------
(* Helpers for the serializability check. *)
MaxOf(S) == CHOOSE m \in S : \A n \in S : n <= m

ValBefore(a, i) ==
  LET W == {j \in 1..(i-1) : log[a][j].op = "Wr"}
  IN IF W = {} THEN InitMem[a] ELSE log[a][MaxOf(W)].val

CurrentVal(a) == ValBefore(a, Len(log[a]) + 1)

TypeOK ==
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc, r \in Reg :
        /\ reg[p][r].state \in Status
        /\ reg[p][r].op \in OpKind
        /\ reg[p][r].adr \in Adr
        /\ reg[p][r].val \in Val
        /\ reg[p][r].id >= 0
  /\ \A p \in Proc : /\ queue[p] \in Seq(Reg)
                     /\ ctr[p] >= 0
  /\ \A a \in Adr : \A i \in 1..Len(log[a]) :
        /\ log[a][i].proc \in Proc
        /\ log[a][i].op \in OpKind
        /\ log[a][i].val \in Val

QueueBound == \A p \in Proc : Len(queue[p]) <= MaxQLen

(* Memory equals the result of executing the per-address log sequentially. *)
MemMatchesLog == \A a \in Adr : mem[a] = CurrentVal(a)

(* Every read in the per-address total order returns the latest preceding write. *)
ReadsSerializable ==
  \A a \in Adr : \A i \in 1..Len(log[a]) :
     log[a][i].op = "Rd" => log[a][i].val = ValBefore(a, i)

(* The per-address order respects program order of each processor. *)
ProgramOrder ==
  \A a \in Adr : \A i, j \in 1..Len(log[a]) :
     (i < j /\ log[a][i].proc = log[a][j].proc) => log[a][i].id < log[a][j].id

(* Each committed / responded operation occurs exactly once in the order of its
   address, with the value delivered in the response. *)
ResponsesLinearized ==
  \A p \in Proc, r \in Reg :
     reg[p][r].state \in {"committed", Done} =>
       LET o == reg[p][r] IN
         \E i \in 1..Len(log[o.adr]) :
            /\ log[o.adr][i].proc = p
            /\ log[o.adr][i].id = o.id
            /\ log[o.adr][i].op = o.op
            /\ log[o.adr][i].val = o.val

(* Operations not yet committed have no linearization point. *)
PendingNotLinearized ==
  \A p \in Proc, r \in Reg :
     reg[p][r].state \in {"enq", "busy"} =>
        \A i \in 1..Len(log[reg[p][r].adr]) :
           ~(log[reg[p][r].adr][i].proc = p /\ log[reg[p][r].adr][i].id = reg[p][r].id)

(* Queue contents are exactly the enqueued-but-not-started registers. *)
QueueConsistent ==
  \A p \in Proc :
     /\ \A i \in 1..Len(queue[p]) : reg[p][queue[p][i]].state = "enq"
     /\ \A r \in Reg : reg[p][r].state = "enq" =>
                         \E i \in 1..Len(queue[p]) : queue[p][i] = r

DataInvariant ==
  /\ TypeOK
  /\ QueueBound
  /\ MemMatchesLog
  /\ ReadsSerializable
  /\ ProgramOrder
  /\ ResponsesLinearized
  /\ PendingNotLinearized
  /\ QueueConsistent

-----------------------------------------------------------------------------
(* Progress: every issued operation eventually receives a response. *)
AlwaysResponds ==
  \A p \in Proc, r \in Reg :
     (reg[p][r].state = "enq") ~> (reg[p][r].state = Done)

(* State constraint for model checking: bounded queues and operation counters. *)
Constraint ==
  /\ \A p \in Proc : Len(queue[p]) <= MaxQLen
  /\ \A p \in Proc : ctr[p] \in Nat

THEOREM Spec => [](DataInvariant) /\ AlwaysResponds
=============================================================================