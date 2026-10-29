---- MODULE RegisterQueues ----
EXTENDS Naturals, Sequences

CONSTANTS Reg,      \* set of registers (per process)
          Adr,      \* set of memory addresses
          Val,      \* set of data values
          Proc,     \* set of processes
          Done,     \* value returned in response to a write (not in Val)
          MaxQLen   \* bound on queue length, used only by Constraint

ASSUME Done \notin Val
ASSUME MaxQLen \in Nat

VARIABLES mem, regFile, queue

vars == <<mem, regFile, queue>>

(* A request is either a read of an address or a write of a value to an address *)
Request == [op : {"Rd"}, adr : Adr]
             \cup [op : {"Wr"}, adr : Adr, val : Val]

(* A register entry is either free (holding the last result) or holds a pending op *)
RegState == [op : {"Free", "Rd", "Wr"}, adr : Adr, val : Val \cup {Done}]

InitAdr == CHOOSE a \in Adr : TRUE
InitVal == CHOOSE v \in Val : TRUE

DataInvariant ==
  /\ mem \in [Adr -> Val]
  /\ regFile \in [Proc -> [Reg -> RegState]]
  /\ queue \in [Proc -> Seq(Request)]

Init ==
  /\ mem \in [Adr -> Val]
  /\ regFile = [p \in Proc |-> [r \in Reg |->
                  [op |-> "Free", adr |-> InitAdr, val |-> InitVal]]]
  /\ queue = [p \in Proc |-> << >>]

(* Process p enqueues a new operation in its queue *)
Enqueue(p) ==
  /\ \E req \in Request :
        queue' = [queue EXCEPT ![p] = Append(@, req)]
  /\ UNCHANGED <<mem, regFile>>

(* Process p dequeues its next operation and starts it on a free register r *)
Issue(p, r) ==
  /\ queue[p] # << >>
  /\ regFile[p][r].op = "Free"
  /\ LET req == Head(queue[p])
     IN  regFile' = [regFile EXCEPT ![p][r] =
                        [op  |-> req.op,
                         adr |-> req.adr,
                         val |-> IF req.op = "Wr" THEN req.val ELSE regFile[p][r].val]]
  /\ queue' = [queue EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED mem

(* The pending operation on register r of process p executes and completes *)
Respond(p, r) ==
  /\ regFile[p][r].op # "Free"
  /\ LET e == regFile[p][r]
     IN  IF e.op = "Rd"
           THEN /\ regFile' = [regFile EXCEPT ![p][r] =
                                 [op |-> "Free", adr |-> e.adr, val |-> mem[e.adr]]]
                /\ UNCHANGED mem
           ELSE /\ mem' = [mem EXCEPT ![e.adr] = e.val]
                /\ regFile' = [regFile EXCEPT ![p][r] =
                                 [op |-> "Free", adr |-> e.adr, val |-> Done]]
  /\ UNCHANGED queue

Next ==
  \E p \in Proc :
     \/ Enqueue(p)
     \/ \E r \in Reg : Issue(p, r) \/ Respond(p, r)

Fairness ==
  \A p \in Proc : \A r \in Reg : WF_vars(Respond(p, r))

Spec == Init /\ [][Next]_vars /\ Fairness

AlwaysResponds ==
  \A p \in Proc : \A r \in Reg :
     (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")

Constraint == \A p \in Proc : Len(queue[p]) <= MaxQLen

THEOREM Spec => []DataInvariant
====