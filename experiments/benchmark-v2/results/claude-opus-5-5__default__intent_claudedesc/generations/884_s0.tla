---------------------------- MODULE SequentialRegisterQueues ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processes
          Reg,       \* set of registers
          Val,       \* set of values that may be written
          MaxQLen    \* bound on each process's operation queue (for model checking)

ASSUME /\ MaxQLen \in Nat
       /\ Proc # {}
       /\ Reg # {}
       /\ Val # {}

NoVal == CHOOSE v : v \notin Val

OpKind == {"Rd", "Wr"}

\* An operation in a process's queue
Request == [op : OpKind, reg : Reg, val : Val \cup {NoVal}]

\* Per-process view of a register:
\*   "Free"    : no operation in progress
\*   "Rd"/"Wr" : operation issued, awaiting execution
\*   "Done"    : operation executed, awaiting response to the process
RegState == [op : {"Free", "Rd", "Wr", "Done"}, val : Val \cup {NoVal}]

FreeEntry == [op |-> "Free", val |-> NoVal]

VARIABLES queue,     \* queue[p] : sequence of pending requests of process p
          regFile,   \* regFile[p][r] : process p's view of register r
          mem,       \* mem[r] : actual contents of register r
          result     \* result[p] : last value returned to process p

vars == <<queue, regFile, mem, result>>

-----------------------------------------------------------------------------------------
TypeOK ==
    /\ queue \in [Proc -> Seq(Request)]
    /\ regFile \in [Proc -> [Reg -> RegState]]
    /\ mem \in [Reg -> Val]
    /\ result \in [Proc -> Val \cup {NoVal}]

Init ==
    /\ queue = [p \in Proc |-> << >>]
    /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeEntry]]
    /\ mem \in [Reg -> Val]
    /\ result = [p \in Proc |-> NoVal]

\* A process is idle when no register in its register file is busy
Idle(p) == \A r \in Reg : regFile[p][r].op = "Free"

-----------------------------------------------------------------------------------------
\* Process p enqueues a read of register r
EnqueueRead(p, r) ==
    /\ Len(queue[p]) < MaxQLen
    /\ queue' = [queue EXCEPT ![p] = Append(@, [op |-> "Rd", reg |-> r, val |-> NoVal])]
    /\ UNCHANGED <<regFile, mem, result>>

\* Process p enqueues a write of value v to register r
EnqueueWrite(p, r, v) ==
    /\ Len(queue[p]) < MaxQLen
    /\ queue' = [queue EXCEPT ![p] = Append(@, [op |-> "Wr", reg |-> r, val |-> v])]
    /\ UNCHANGED <<regFile, mem, result>>

\* Process p takes the head of its queue and puts it in progress
\* (sequential: only when the process has no operation in progress)
Issue(p) ==
    /\ queue[p] # << >>
    /\ Idle(p)
    /\ LET req == Head(queue[p]) IN
         regFile' = [regFile EXCEPT ![p][req.reg] = [op |-> req.op, val |-> req.val]]
    /\ queue' = [queue EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<mem, result>>

\* The in-progress operation of p on r is executed against the register
Execute(p, r) ==
    /\ regFile[p][r].op \in OpKind
    /\ IF regFile[p][r].op = "Wr"
         THEN /\ mem' = [mem EXCEPT ![r] = regFile[p][r].val]
              /\ regFile' = [regFile EXCEPT ![p][r] = [op |-> "Done", val |-> NoVal]]
         ELSE /\ regFile' = [regFile EXCEPT ![p][r] = [op |-> "Done", val |-> mem[r]]]
              /\ UNCHANGED mem
    /\ UNCHANGED <<queue, result>>

\* The response is delivered to process p and register r becomes free again
Respond(p, r) ==
    /\ regFile[p][r].op = "Done"
    /\ result' = [result EXCEPT ![p] = regFile[p][r].val]
    /\ regFile' = [regFile EXCEPT ![p][r] = FreeEntry]
    /\ UNCHANGED <<queue, mem>>

Next ==
    \E p \in Proc :
        \/ \E r \in Reg : EnqueueRead(p, r)
        \/ \E r \in Reg, v \in Val : EnqueueWrite(p, r, v)
        \/ Issue(p)
        \/ \E r \in Reg : Execute(p, r)
        \/ \E r \in Reg : Respond(p, r)

Fairness ==
    \A p \in Proc, r \in Reg :
        /\ WF_vars(Execute(p, r))
        /\ WF_vars(Respond(p, r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------------
\* Safety: at most one operation in progress per process (sequential processing)
Sequential ==
    \A p \in Proc :
        Cardinality({r \in Reg : regFile[p][r].op # "Free"}) <= 1

\* Safety: queues respect the bound
QueueBounded == \A p \in Proc : Len(queue[p]) <= MaxQLen

\* Liveness: every request eventually receives a response
EventualResponse ==
    \A p \in Proc, r \in Reg :
        (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")

\* State constraint for bounding queue length during model checking
QueueConstraint == \A p \in Proc : Len(queue[p]) <= MaxQLen

THEOREM Spec => [](TypeOK /\ Sequential /\ QueueBounded)
THEOREM Spec => EventualResponse
=========================================================================================