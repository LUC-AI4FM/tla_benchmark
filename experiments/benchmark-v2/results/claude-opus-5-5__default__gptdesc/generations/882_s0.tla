--------------------------- MODULE InnerSequential ---------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,     \* set of processes
          Adr,      \* set of memory addresses
          Val,      \* set of memory values
          Reg,      \* set of register names (per process)
          InitMem   \* initial contents of memory

ASSUME InitMem \in [Adr -> Val]

NoVal == CHOOSE v : v \notin Val
Done  == CHOOSE d : d \notin Reg

VARIABLES regFile,  \* regFile[p][r] : contents of register r of process p
          opQ,      \* opQ[p] : sequence of issued (not yet removed) operations of p
          mem       \* the memory array

vars == <<regFile, opQ, mem>>

-----------------------------------------------------------------------------
(* Types *)

RdRequest == [op : {"Rd"}, adr : Adr, val : {NoVal}]
WrRequest == [op : {"Wr"}, adr : Adr, val : Val]
Request   == RdRequest \cup WrRequest

\* A register entry: either holds a pending request ("Rd"/"Wr"),
\* or is "Free" (holding the result of the last completed operation).
RegEntry == [op : {"Rd", "Wr", "Free"}, adr : Adr, val : Val \cup {NoVal}]

\* A queue entry: the request (with the value read/written filled in
\* once responded) and the register it occupies, or Done once responded.
OpEntry == [req : [op : {"Rd", "Wr"}, adr : Adr, val : Val \cup {NoVal}],
            reg : Reg \cup {Done}]

-----------------------------------------------------------------------------
(* Data invariant *)

DataInvariant ==
  /\ regFile \in [Proc -> [Reg -> RegEntry]]
  /\ opQ \in [Proc -> Seq(OpEntry)]
  /\ mem \in [Adr -> Val]
  /\ \A p \in Proc :
       /\ \A r \in Reg :
            Cardinality({i \in DOMAIN opQ[p] : opQ[p][i].reg = r}) =
              IF regFile[p][r].op = "Free" THEN 0 ELSE 1
       /\ \A i \in DOMAIN opQ[p] :
            /\ opQ[p][i].reg # Done =>
                 /\ regFile[p][opQ[p][i].reg].op = opQ[p][i].req.op
                 /\ regFile[p][opQ[p][i].reg].adr = opQ[p][i].req.adr
            /\ opQ[p][i].reg = Done => opQ[p][i].req.val \in Val
            /\ opQ[p][i].req.op = "Wr" => opQ[p][i].req.val \in Val

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
  /\ regFile \in [Proc -> [Reg -> [op : {"Free"}, adr : Adr,
                                   val : Val \cup {NoVal}]]]
  /\ opQ = [p \in Proc |-> << >>]
  /\ mem = InitMem

-----------------------------------------------------------------------------
(* Actions *)

\* Process p issues request req into free register r.
Req(p, r) ==
  /\ regFile[p][r].op = "Free"
  /\ \E req \in Request :
       /\ regFile' = [regFile EXCEPT ![p][r] = req]
       /\ opQ' = [opQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r])]
  /\ UNCHANGED mem

\* Response to the operation pending in register r of process p.
\* A write is acknowledged with its value; a read returns some value v,
\* which is recorded in the queue to be checked against memory later.
Respond(p, r) ==
  /\ regFile[p][r].op # "Free"
  /\ \E i \in DOMAIN opQ[p] :
       /\ opQ[p][i].reg = r
       /\ \E v \in Val :
            LET rv == IF opQ[p][i].req.op = "Wr"
                        THEN opQ[p][i].req.val
                        ELSE v
            IN  /\ opQ[p][i].req.op = "Wr" => v = opQ[p][i].req.val
                /\ regFile' = [regFile EXCEPT ![p][r] =
                                 [op |-> "Free", adr |-> @.adr, val |-> rv]]
                /\ opQ' = [opQ EXCEPT ![p][i] =
                             [req |-> [@.req EXCEPT !.val = rv],
                              reg |-> Done]]
  /\ UNCHANGED mem

\* Internal action: remove a completed operation from the head of p's queue.
\* Writes update memory; reads must agree with the current memory value.
RemoveOp(p) ==
  /\ opQ[p] # << >>
  /\ Head(opQ[p]).reg = Done
  /\ LET req == Head(opQ[p]).req
     IN  IF req.op = "Wr"
           THEN mem' = [mem EXCEPT ![req.adr] = req.val]
           ELSE /\ mem[req.adr] = req.val
                /\ UNCHANGED mem
  /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED regFile

Next ==
  \/ \E p \in Proc, r \in Reg : Req(p, r) \/ Respond(p, r)
  \/ \E p \in Proc : RemoveOp(p)

-----------------------------------------------------------------------------
(* Specification *)

Fairness ==
  /\ \A p \in Proc, r \in Reg : WF_vars(Respond(p, r))
  /\ \A p \in Proc : WF_vars(RemoveOp(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

\* Every issued request eventually receives a response.
EventuallyResponded ==
  \A p \in Proc, r \in Reg :
    (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")

THEOREM Spec => []DataInvariant
THEOREM Spec => EventuallyResponded
=============================================================================