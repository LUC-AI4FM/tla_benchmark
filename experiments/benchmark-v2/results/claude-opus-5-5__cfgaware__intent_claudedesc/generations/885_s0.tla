------------------------------ MODULE MCSerialMemory ------------------------------
(***************************************************************************)
(* Serializable memory with per-processor operation queues.               *)
(*                                                                         *)
(* A processor p issues a request using a free register r of its register  *)
(* file.  The request is appended to p's operation queue opQ[p].  Requests *)
(* are executed atomically against the shared memory, taken from the head  *)
(* of a processor's queue.  This serializes all operations: the order of   *)
(* the Execute steps is the serialization order, and each processor's      *)
(* operations keep their program order.  The result is stored in the       *)
(* register, which becomes "done".  The processor then frees the register  *)
(* so that it can be reused.                                               *)
(*                                                                         *)
(* An operation is identified by its processor and its position in that    *)
(* processor's queue.  lastWr[a] records which operation last wrote        *)
(* address a.  Its initial value is InitWr, the fictitious initial write.  *)
(*                                                                         *)
(* Nat is defined locally so that the configuration can override it with   *)
(* MCNat.  For this reason Naturals and Sequences are used through named   *)
(* instances and are not extended.                                         *)
(***************************************************************************)

N == INSTANCE Naturals
S == INSTANCE Sequences

CONSTANTS Reg,      \* registers per processor
          Adr,      \* memory addresses
          Val,      \* memory values
          Proc,     \* processors
          InitMem,  \* initial memory contents
          InitWr,   \* marker for the fictitious initial write
          Done,     \* result value returned by a completed write
          MaxQLen   \* bound on queue length, used for model checking

Nat == N!Nat

MCNat == {0, 1, 2, 3, 4}

MCInitMem == [a \in Adr |-> CHOOSE v \in Val : TRUE]

VARIABLES mem,     \* mem[a] : current value at address a
          ctl,     \* ctl[p][r] \in {"rdy", "busy", "done"}
          buf,     \* buf[p][r] : the request while busy, the result when done
          opQ,     \* opQ[p] : sequence of pending operations of p
          lastWr   \* lastWr[a] : InitWr, or <<p, r>> of the last writer

vars == <<mem, ctl, buf, opQ, lastWr>>

-----------------------------------------------------------------------------
\* Requests, results and queue entries

Request == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

Result == Val \cup {Done}

Entry == [req : Request, reg : Reg]

-----------------------------------------------------------------------------
\* Invariant

DataInvariant ==
  /\ InitMem \in [Adr -> Val]
  /\ mem \in [Adr -> Val]
  /\ ctl \in [Proc -> [Reg -> {"rdy", "busy", "done"}]]
  /\ buf \in [Proc -> [Reg -> Request \cup Result \cup {"none"}]]
  /\ opQ \in [Proc -> S!Seq(Entry)]
  /\ lastWr \in [Adr -> {InitWr} \cup (Proc \X Reg)]
  \* A register is busy exactly when its operation is waiting in the queue
  /\ \A p \in Proc, r \in Reg :
        /\ (ctl[p][r] = "busy") <=>
              (\E i \in 1..S!Len(opQ[p]) : opQ[p][i].reg = r)
        /\ (ctl[p][r] = "busy") => buf[p][r] = opQ[p][CHOOSE i \in 1..S!Len(opQ[p]) :
                                                         opQ[p][i].reg = r].req
        /\ (ctl[p][r] = "done") => buf[p][r] \in Result
  \* Every operation in a queue has a unique register
  /\ \A p \in Proc : \A i, j \in 1..S!Len(opQ[p]) :
        (opQ[p][i].reg = opQ[p][j].reg) => (i = j)

-----------------------------------------------------------------------------
\* Initial state

Init ==
  /\ mem = InitMem
  /\ ctl = [p \in Proc |-> [r \in Reg |-> "rdy"]]
  /\ buf = [p \in Proc |-> [r \in Reg |-> "none"]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ lastWr = [a \in Adr |-> InitWr]

-----------------------------------------------------------------------------
\* Actions

\* Processor p issues request req using its free register r
Issue(p, r, req) ==
  /\ ctl[p][r] = "rdy"
  /\ ctl' = [ctl EXCEPT ![p][r] = "busy"]
  /\ buf' = [buf EXCEPT ![p][r] = req]
  /\ opQ' = [opQ EXCEPT ![p] = S!Append(@, [req |-> req, reg |-> r])]
  /\ UNCHANGED <<mem, lastWr>>

\* The operation at the head of p's queue is executed atomically
Execute(p) ==
  /\ opQ[p] # << >>
  /\ LET e   == S!Head(opQ[p])
         req == e.req
         r   == e.reg
     IN  /\ IF req.op = "Rd"
               THEN /\ buf' = [buf EXCEPT ![p][r] = mem[req.adr]]
                    /\ UNCHANGED <<mem, lastWr>>
               ELSE /\ mem' = [mem EXCEPT ![req.adr] = req.val]
                    /\ lastWr' = [lastWr EXCEPT ![req.adr] = <<p, r>>]
                    /\ buf' = [buf EXCEPT ![p][r] = Done]
         /\ ctl' = [ctl EXCEPT ![p][r] = "done"]
         /\ opQ' = [opQ EXCEPT ![p] = S!Tail(@)]

\* Processor p takes the result from register r and frees the register
Free(p, r) ==
  /\ ctl[p][r] = "done"
  /\ ctl' = [ctl EXCEPT ![p][r] = "rdy"]
  /\ buf' = [buf EXCEPT ![p][r] = "none"]
  /\ UNCHANGED <<mem, opQ, lastWr>>

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : Issue(p, r, req)
  \/ \E p \in Proc : Execute(p)
  \/ \E p \in Proc, r \in Reg : Free(p, r)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc : WF_vars(Execute(p))
  /\ \A p \in Proc, r \in Reg : WF_vars(Free(p, r))

-----------------------------------------------------------------------------
\* Liveness: every issued operation reaches "done", and its register is
\* eventually freed for reuse.

AlwaysResponds ==
  /\ \A p \in Proc, r \in Reg : (ctl[p][r] = "busy") ~> (ctl[p][r] = "done")
  /\ \A p \in Proc, r \in Reg : (ctl[p][r] = "busy") ~> (ctl[p][r] = "rdy")

-----------------------------------------------------------------------------
\* State constraint for model checking

Constraint == \A p \in Proc : S!Len(opQ[p]) \in N!..(0, MaxQLen)

=============================================================================