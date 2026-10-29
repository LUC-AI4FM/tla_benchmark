------------------------- MODULE MCInnerSequential -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processes
          Reg,       \* set of register indices per process
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          InitMem,   \* initial memory contents, a function Adr -> Val
          MaxQLen    \* bound on the length of every process's operation queue

ASSUME MaxQLen \in Nat
ASSUME InitMem \in [Adr -> Val]

NoVal == CHOOSE v : v \notin Val
NoAdr == CHOOSE a : a \notin Adr

-----------------------------------------------------------------------------
(* Register file entries.  An entry is "Free" when its op field is "Free". *)
-----------------------------------------------------------------------------
FreeEntry == [op |-> "Free", adr |-> NoAdr, val |-> NoVal, done |-> FALSE]

Request == [op : {"Rd"}, adr : Adr, val : {NoVal}]
             \cup [op : {"Wr"}, adr : Adr, val : Val]

EntryType == {FreeEntry}
               \cup [op : {"Rd", "Wr"}, adr : Adr,
                     val : Val \cup {NoVal}, done : BOOLEAN]

QEntry == [reg : Reg, op : {"Rd", "Wr"}, adr : Adr, val : Val \cup {NoVal}]

VARIABLES regFile,   \* regFile[p][r] : register entry r of process p
          opQ,       \* opQ[p] : queue of pending operations of process p
          mem        \* the memory

vars == <<regFile, opQ, mem>>

TypeOK ==
  /\ regFile \in [Proc -> [Reg -> EntryType]]
  /\ opQ \in [Proc -> Seq(QEntry)]
  /\ mem \in [Adr -> Val]

Init ==
  /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeEntry]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem = InitMem

-----------------------------------------------------------------------------
(* Actions                                                                   *)
-----------------------------------------------------------------------------

\* Process p issues request req in free register r.
Issue(p, r, req) ==
  /\ regFile[p][r].op = "Free"
  /\ regFile' = [regFile EXCEPT ![p][r] =
                    [op |-> req.op, adr |-> req.adr,
                     val |-> req.val, done |-> FALSE]]
  /\ opQ' = [opQ EXCEPT ![p] =
                Append(@, [reg |-> r, op |-> req.op,
                           adr |-> req.adr, val |-> req.val])]
  /\ UNCHANGED mem

\* The memory executes the operation at the head of p's queue (sequentially).
Execute(p) ==
  /\ opQ[p] # << >>
  /\ LET e == Head(opQ[p])
     IN  /\ IF e.op = "Wr"
              THEN /\ mem' = [mem EXCEPT ![e.adr] = e.val]
                   /\ regFile' = [regFile EXCEPT ![p][e.reg].done = TRUE]
              ELSE /\ mem' = mem
                   /\ regFile' = [regFile EXCEPT
                                    ![p][e.reg].val  = mem[e.adr],
                                    ![p][e.reg].done = TRUE]
         /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]

\* Process p receives the response in register r, freeing the register.
Respond(p, r) ==
  /\ regFile[p][r].op # "Free"
  /\ regFile[p][r].done
  /\ regFile' = [regFile EXCEPT ![p][r] = FreeEntry]
  /\ UNCHANGED <<opQ, mem>>

Next ==
  \/ \E p \in Proc, r \in Reg, req \in Request : Issue(p, r, req)
  \/ \E p \in Proc : Execute(p)
  \/ \E p \in Proc, r \in Reg : Respond(p, r)

Fairness ==
  /\ \A p \in Proc : WF_vars(Execute(p))
  /\ \A p \in Proc, r \in Reg : WF_vars(Respond(p, r))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* State constraint: every process's operation queue is bounded by MaxQLen.  *)
-----------------------------------------------------------------------------
Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

-----------------------------------------------------------------------------
(* Liveness: every non-free register entry eventually becomes free again.    *)
-----------------------------------------------------------------------------
AlwaysResponds ==
  \A p \in Proc, r \in Reg :
     (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")

THEOREM Spec => []TypeOK
THEOREM Spec => AlwaysResponds
=============================================================================