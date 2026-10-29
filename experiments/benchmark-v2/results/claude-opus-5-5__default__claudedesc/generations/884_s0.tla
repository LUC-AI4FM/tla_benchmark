------------------------------ MODULE MCInnerSequential ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors           (model: {p1, p2})
          Reg,       \* set of registers per proc   (model: {r1})
          Adr,       \* set of memory addresses     (model: {a1})
          Val,       \* set of memory values        (model: {v1, v2})
          Done,      \* model value: write ack / "no value"
          MaxQLen    \* bound on operation queue length (model: 2)

ASSUME /\ Proc # {} /\ Reg # {} /\ Adr # {} /\ Val # {}
       /\ Done \notin Val
       /\ MaxQLen \in Nat

VARIABLES regFile,   \* regFile[p][r] : state of register r of processor p
          opQ,       \* opQ[p]        : queue of pending memory operations of p
          mem        \* mem[a]        : current contents of address a

vars == <<regFile, opQ, mem>>

-----------------------------------------------------------------------------
(* Data definitions                                                        *)
-----------------------------------------------------------------------------
RdRequest == [op : {"Rd"}, adr : Adr, val : {Done}]
WrRequest == [op : {"Wr"}, adr : Adr, val : Val]
Request   == RdRequest \cup WrRequest

FreeReg   == [op |-> "Free", adr |-> Done, val |-> Done]

RegState  ==    {FreeReg}
             \cup Request
             \cup [op : {"Resp"}, adr : Adr, val : Val \cup {Done}]

QEntry    == [req : Request, reg : Reg]

InitMem   == CHOOSE m \in [Adr -> Val] : TRUE

-----------------------------------------------------------------------------
(* Inner sequential memory specification                                   *)
-----------------------------------------------------------------------------
Init == /\ regFile = [p \in Proc |-> [r \in Reg |-> FreeReg]]
        /\ opQ     = [p \in Proc |-> << >>]
        /\ mem     \in [Adr -> Val]

\* Processor p issues request req using free register r
Req(p, r, req) ==
    /\ regFile[p][r].op = "Free"
    /\ regFile' = [regFile EXCEPT ![p][r] = req]
    /\ opQ'     = [opQ EXCEPT ![p] = Append(@, [req |-> req, reg |-> r])]
    /\ UNCHANGED mem

\* The memory executes the oldest pending operation of processor p
Do(p) ==
    /\ opQ[p] # << >>
    /\ LET e   == Head(opQ[p])
           req == e.req
           res == IF req.op = "Rd" THEN mem[req.adr] ELSE Done
       IN  /\ mem' = IF req.op = "Wr"
                       THEN [mem EXCEPT ![req.adr] = req.val]
                       ELSE mem
           /\ regFile' = [regFile EXCEPT ![p][e.reg] =
                            [op |-> "Resp", adr |-> req.adr, val |-> res]]
           /\ opQ' = [opQ EXCEPT ![p] = Tail(@)]

\* Processor p consumes the response in register r, freeing it
Rsp(p, r) ==
    /\ regFile[p][r].op = "Resp"
    /\ regFile' = [regFile EXCEPT ![p][r] = FreeReg]
    /\ UNCHANGED <<opQ, mem>>

Next ==
    \/ \E p \in Proc, r \in Reg, req \in Request : Req(p, r, req)
    \/ \E p \in Proc : Do(p)
    \/ \E p \in Proc, r \in Reg : Rsp(p, r)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Proc : WF_vars(Do(p))
    /\ \A p \in Proc, r \in Reg : WF_vars(Rsp(p, r))

-----------------------------------------------------------------------------
(* Safety invariant                                                        *)
-----------------------------------------------------------------------------
DataInvariant ==
    /\ regFile \in [Proc -> [Reg -> RegState]]
    /\ opQ     \in [Proc -> Seq(QEntry)]
    /\ mem     \in [Adr -> Val]

-----------------------------------------------------------------------------
(* Model-checking configuration definitions                                *)
-----------------------------------------------------------------------------
Constraint == \A p \in Proc : Len(opQ[p]) \leq MaxQLen

\* Every issued operation eventually completes (register returns to Free)
AlwaysResponds ==
    \A p \in Proc, r \in Reg :
        (regFile[p][r].op # "Free") ~> (regFile[p][r].op = "Free")

THEOREM Spec => []DataInvariant
THEOREM Spec => AlwaysResponds
=============================================================================