---------------------------- MODULE MemoryCoordinator ----------------------------
(***************************************************************************)
(* Abstract model of a multi-processor memory-access coordinator.          *)
(* Processors issue reads and writes on shared addresses.  Each operation  *)
(* is enqueued in a bounded per-processor FIFO queue.  The coordinator     *)
(* abstractly starts and commits the head operation of a queue; the commit *)
(* is the operation's linearization point.  Committing updates shared      *)
(* memory and records the operation in a per-address log, which is the     *)
(* total order for that address.  Processor registers track each           *)
(* operation's status until the processor observes the response.           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,      \* finite set of processors
    Adr,       \* finite set of memory addresses
    Val,       \* finite set of data values
    InitMem,   \* initial memory contents
    QLen,      \* bound on the length of each per-processor queue
    MaxOps,    \* number of operations each processor may issue (finiteness)
    NoVal,     \* "no value" marker
    Ack        \* acknowledgement returned by writes

ASSUME /\ Proc # {}
       /\ Adr # {}
       /\ Val # {}
       /\ InitMem \in [Adr -> Val]
       /\ QLen \in Nat \ {0}
       /\ MaxOps \in Nat \ {0}
       /\ NoVal \notin Val
       /\ Ack \notin Val \cup {NoVal}

OpId     == 0 .. (MaxOps - 1)
OpType   == {"Rd", "Wr"}
Status   == {"free", "pending", "started", "committed", "done"}
RetVal   == Val \cup {Ack, NoVal}
SomeAdr  == CHOOSE a \in Adr : TRUE

QueueEntry == [id : OpId, type : OpType, adr : Adr, val : Val \cup {NoVal}]

RegEntry == [status  : Status,
             type    : OpType,
             adr     : Adr,
             val     : Val \cup {NoVal},
             ret     : RetVal,
             tIssue  : Nat,
             tCommit : Nat,
             tResp   : Nat]

LogEntry == [proc : Proc,
             id   : OpId,
             type : OpType,
             val  : Val \cup {NoVal},
             ret  : RetVal,
             time : Nat]

EmptyReg == [status  |-> "free",
             type    |-> "Rd",
             adr     |-> SomeAdr,
             val     |-> NoVal,
             ret     |-> NoVal,
             tIssue  |-> 0,
             tCommit |-> 0,
             tResp   |-> 0]

VARIABLES
    mem,     \* shared memory state: [Adr -> Val]
    queue,   \* per-processor queues of outstanding operations
    reg,     \* per-processor registers: reg[p][i] tracks operation i of p
    nextId,  \* next operation identifier for each processor
    log,     \* per-address total order of committed operations
    clock    \* abstract real-time clock (ticks on every step)

vars == <<mem, queue, reg, nextId, log, clock>>

-----------------------------------------------------------------------------
Init ==
    /\ mem    = InitMem
    /\ queue  = [p \in Proc |-> << >>]
    /\ reg    = [p \in Proc |-> [i \in OpId |-> EmptyReg]]
    /\ nextId = [p \in Proc |-> 0]
    /\ log    = [a \in Adr |-> << >>]
    /\ clock  = 0

(***************************************************************************)
(* Processor p creates and enqueues a new operation.  A read carries no    *)
(* value; a write carries the value to be written.                         *)
(***************************************************************************)
Issue(p, t, a, v) ==
    /\ nextId[p] < MaxOps
    /\ Len(queue[p]) < QLen
    /\ (t = "Wr") <=> (v \in Val)
    /\ LET i  == nextId[p]
           op == [id |-> i, type |-> t, adr |-> a, val |-> v]
       IN  /\ reg[p][i].status = "free"
           /\ queue'  = [queue EXCEPT ![p] = Append(@, op)]
           /\ reg'    = [reg EXCEPT ![p][i] =
                           [status  |-> "pending",
                            type    |-> t,
                            adr     |-> a,
                            val     |-> v,
                            ret     |-> NoVal,
                            tIssue  |-> clock,
                            tCommit |-> 0,
                            tResp   |-> 0]]
           /\ nextId' = [nextId EXCEPT ![p] = @ + 1]
    /\ clock' = clock + 1
    /\ UNCHANGED <<mem, log>>

(***************************************************************************)
(* The coordinator begins servicing the oldest outstanding operation of p. *)
(***************************************************************************)
Start(p) ==
    /\ queue[p] # << >>
    /\ LET i == Head(queue[p]).id
       IN  /\ reg[p][i].status = "pending"
           /\ reg' = [reg EXCEPT ![p][i].status = "started"]
    /\ clock' = clock + 1
    /\ UNCHANGED <<mem, queue, nextId, log>>

(***************************************************************************)
(* The coordinator commits the started head operation of p atomically.     *)
(* This step is the linearization point: memory is read/updated, the       *)
(* operation is appended to its address's total order, and the response   *)
(* value is produced.                                                      *)
(***************************************************************************)
Commit(p) ==
    /\ queue[p] # << >>
    /\ LET op == Head(queue[p])
           i  == op.id
           a  == op.adr
           r  == IF op.type = "Rd" THEN mem[a] ELSE Ack
       IN  /\ reg[p][i].status = "started"
           /\ mem'   = IF op.type = "Wr"
                         THEN [mem EXCEPT ![a] = op.val]
                         ELSE mem
           /\ reg'   = [reg EXCEPT ![p][i].status  = "committed",
                                   ![p][i].ret     = r,
                                   ![p][i].tCommit = clock]
           /\ log'   = [log EXCEPT ![a] =
                          Append(@, [proc |-> p,
                                     id   |-> i,
                                     type |-> op.type,
                                     val  |-> op.val,
                                     ret  |-> r,
                                     time |-> clock])]
           /\ queue' = [queue EXCEPT ![p] = Tail(@)]
    /\ clock' = clock + 1
    /\ UNCHANGED nextId

(***************************************************************************)
(* Processor p observes the response of its committed operation i.         *)
(***************************************************************************)
Respond(p, i) ==
    /\ reg[p][i].status = "committed"
    /\ reg' = [reg EXCEPT ![p][i].status = "done",
                          ![p][i].tResp  = clock]
    /\ clock' = clock + 1
    /\ UNCHANGED <<mem, queue, nextId, log>>

(* Stutter once all work is finished, to avoid spurious deadlock. *)
Terminated ==
    /\ \A p \in Proc : nextId[p] = MaxOps
    /\ \A p \in Proc : \A i \in OpId : reg[p][i].status = "done"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Proc, t \in OpType, a \in Adr, v \in Val \cup {NoVal} :
           Issue(p, t, a, v)
    \/ \E p \in Proc : Start(p)
    \/ \E p \in Proc : Commit(p)
    \/ \E p \in Proc, i \in OpId : Respond(p, i)
    \/ Terminated

Fairness ==
    \A p \in Proc :
        /\ WF_vars(Start(p))
        /\ WF_vars(Commit(p))
        /\ \A i \in OpId : WF_vars(Respond(p, i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(*                              INVARIANTS                                  *)
(***************************************************************************)
TypeOK ==
    /\ mem    \in [Adr -> Val]
    /\ queue  \in [Proc -> Seq(QueueEntry)]
    /\ reg    \in [Proc -> [OpId -> RegEntry]]
    /\ nextId \in [Proc -> 0 .. MaxOps]
    /\ log    \in [Adr -> Seq(LogEntry)]
    /\ clock  \in Nat

(* Queue bounds are never exceeded. *)
QueueBound == \A p \in Proc : Len(queue[p]) <= QLen

(* Value of address a after executing the first k entries of log[a]. *)
ValueAfter(a, k) ==
    IF \E j \in 1 .. k : log[a][j].type = "Wr"
    THEN log[a][CHOOSE j \in 1 .. k :
                    /\ log[a][j].type = "Wr"
                    /\ \A j2 \in (j + 1) .. k : log[a][j2].type # "Wr"].val
    ELSE InitMem[a]

(* Per-address serializability: executing the log of each address         *)
(* sequentially from the initial memory yields exactly the recorded        *)
(* responses, and the final value equals the current memory contents.      *)
SerializablePerAddress ==
    \A a \in Adr :
        /\ \A k \in 1 .. Len(log[a]) :
               IF log[a][k].type = "Rd"
               THEN log[a][k].ret = ValueAfter(a, k - 1)
               ELSE log[a][k].ret = Ack
        /\ mem[a] = ValueAfter(a, Len(log[a]))

(* The per-address total order respects program order of each processor. *)
ProgramOrder ==
    \A a \in Adr : \A j, k \in 1 .. Len(log[a]) :
        (j < k /\ log[a][j].proc = log[a][k].proc)
            => log[a][j].id < log[a][k].id

(* The linearization point lies within the operation's real-time interval, *)
(* and the per-address order respects real-time order.                     *)
RealTimeOrder ==
    \A a \in Adr :
        /\ \A k \in 1 .. Len(log[a]) :
               LET e == log[a][k]
                   r == reg[e.proc][e.id]
               IN  /\ r.tIssue < e.time
                   /\ r.tCommit = e.time
                   /\ r.status = "done" => e.time < r.tResp
        /\ \A j, k \in 1 .. Len(log[a]) :
               j < k =>
                 /\ log[a][j].time < log[a][k].time
                 /\ LET rj == reg[log[a][j].proc][log[a][j].id]
                        rk == reg[log[a][k].proc][log[a][k].id]
                    IN  ~(rk.status = "done" /\ rk.tResp < rj.tIssue)

(* Linearizability per address: all of the above combined. *)
Linearizable ==
    SerializablePerAddress /\ ProgramOrder /\ RealTimeOrder

(* Atomicity: every committed operation takes effect at exactly one point  *)
(* (one entry in the log of its own address and none elsewhere); an       *)
(* uncommitted operation has taken no effect at all.                       *)
Occ(p, i, a) ==
    {k \in 1 .. Len(log[a]) : log[a][k].proc = p /\ log[a][k].id = i}

Atomicity ==
    \A p \in Proc : \A i \in OpId :
        LET r == reg[p][i]
        IN  /\ r.status \in {"committed", "done"} =>
                   /\ Cardinality(Occ(p, i, r.adr)) = 1
                   /\ \A k \in Occ(p, i, r.adr) :
                          /\ log[r.adr][k].ret  = r.ret
                          /\ log[r.adr][k].type = r.type
                          /\ log[r.adr][k].val  = r.val
                   /\ \A a \in Adr \ {r.adr} : Occ(p, i, a) = {}
            /\ r.status \in {"free", "pending", "started"} =>
                   \A a \in Adr : Occ(p, i, a) = {}

(* Queues hold exactly the issued-but-uncommitted operations, in order. *)
QueueConsistent ==
    \A p \in Proc :
        /\ \A k \in 1 .. Len(queue[p]) :
               reg[p][queue[p][k].id].status \in {"pending", "started"}
        /\ \A j, k \in 1 .. Len(queue[p]) :
               j < k => queue[p][j].id < queue[p][k].id
        /\ \A i \in OpId :
               reg[p][i].status \in {"pending", "started"} =>
                   \E k \in 1 .. Len(queue[p]) : queue[p][k].id = i
        /\ \A i \in OpId : (i >= nextId[p]) <=> (reg[p][i].status = "free")

Safety ==
    /\ TypeOK
    /\ QueueBound
    /\ Linearizable
    /\ Atomicity
    /\ QueueConsistent

-----------------------------------------------------------------------------
(***************************************************************************)
(*                              LIVENESS                                    *)
(***************************************************************************)
(* Every issued operation eventually receives (and has observed) a response. *)
EveryOpResponds ==
    \A p \in Proc : \A i \in OpId :
        (reg[p][i].status \in {"pending", "started", "committed"})
            ~> (reg[p][i].status = "done")

(* No operation is lost: once committed, it is eventually observed. *)
NoLostResponse ==
    \A p \in Proc : \A i \in OpId :
        (reg[p][i].status = "committed") ~> (reg[p][i].status = "done")

THEOREM Spec => []Safety
THEOREM Spec => EveryOpResponds /\ NoLostResponse
=============================================================================