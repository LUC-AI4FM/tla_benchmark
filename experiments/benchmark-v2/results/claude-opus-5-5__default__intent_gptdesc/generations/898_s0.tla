------------------------- MODULE WriteThroughCacheController -------------------------
(***************************************************************************)
(* High-level model of a write-through cache controller that mediates     *)
(* access to a shared atomic memory for a fixed set of processors.        *)
(*                                                                         *)
(* Externally visible interface, per processor p:                         *)
(*   ctl[p] : control state  "rdy" | "busy" | "waiting" | "done"           *)
(*   buf[p] : request buffer while busy or waiting, reply when done        *)
(*                                                                         *)
(* Internal state:                                                         *)
(*   mem    : the underlying memory                                        *)
(*   cache  : per-processor write-through caches                           *)
(*   memQ   : abstract internal memory interface, a FIFO of requests       *)
(*            that the memory serves one at a time (atomically)            *)
(*                                                                         *)
(* Ghost (history) variables, used only for specification:                 *)
(*   curReq     : the request currently issued by p                        *)
(*   memAtServe : value of mem[adr] at the moment p's request was served   *)
(*   pending    : TRUE iff p has an issued request with no accepted reply  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,   \* set of processors
          Adr,    \* set of memory addresses
          Val     \* set of memory values

ASSUME Proc # {} /\ Adr # {} /\ Val # {}

-----------------------------------------------------------------------------
(* Request and reply domains *)

RdReq == [op : {"Rd"}, adr : Adr]
WrReq == [op : {"Wr"}, adr : Adr, val : Val]
MReq  == RdReq \cup WrReq

NoVal == CHOOSE v : v \notin Val      \* write acknowledgement / empty cache slot
NoReq == CHOOSE r : r \notin MReq     \* "no request issued yet"

CtlStates == {"rdy", "busy", "waiting", "done"}

VARIABLES mem, ctl, buf, cache, memQ,     \* real state
          curReq, memAtServe, pending     \* ghost state

vars == <<mem, ctl, buf, cache, memQ, curReq, memAtServe, pending>>

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
  /\ mem        \in [Adr -> Val]
  /\ ctl        \in [Proc -> CtlStates]
  /\ buf        \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache      \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ       \in Seq(Proc \X MReq)
  /\ curReq     \in [Proc -> MReq \cup {NoReq}]
  /\ memAtServe \in [Proc -> Val \cup {NoVal}]
  /\ pending    \in [Proc -> BOOLEAN]

-----------------------------------------------------------------------------
(* Initial state: memory holds some mapping from addresses to values,     *)
(* every processor is idle, caches are empty, and nothing is outstanding. *)

Init ==
  /\ mem        \in [Adr -> Val]
  /\ ctl        = [p \in Proc |-> "rdy"]
  /\ buf        = [p \in Proc |-> NoVal]
  /\ cache      = [p \in Proc |-> [a \in Adr |-> NoVal]]
  /\ memQ       = << >>
  /\ curReq     = [p \in Proc |-> NoReq]
  /\ memAtServe = [p \in Proc |-> NoVal]
  /\ pending    = [p \in Proc |-> FALSE]

-----------------------------------------------------------------------------
(* Actions *)

(* Processor p issues a read or write request. *)
Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E r \in MReq :
        /\ buf'    = [buf    EXCEPT ![p] = r]
        /\ curReq' = [curReq EXCEPT ![p] = r]
  /\ ctl'     = [ctl     EXCEPT ![p] = "busy"]
  /\ pending' = [pending EXCEPT ![p] = TRUE]
  /\ UNCHANGED <<mem, cache, memQ, memAtServe>>

(* The controller forwards p's request to the memory interface. *)
Forward(p) ==
  /\ ctl[p] = "busy"
  /\ memQ' = Append(memQ, <<p, buf[p]>>)
  /\ ctl'  = [ctl EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<mem, buf, cache, curReq, memAtServe, pending>>

(* A read that hits in p's cache is answered locally. *)
CacheHit(p) ==
  /\ ctl[p] = "busy"
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] # NoVal
  /\ buf'        = [buf        EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ memAtServe' = [memAtServe EXCEPT ![p] = mem[buf[p].adr]]
  /\ ctl'        = [ctl        EXCEPT ![p] = "done"]
  /\ UNCHANGED <<mem, cache, memQ, curReq, pending>>

(* The memory atomically serves the request at the head of the queue.     *)
(* A write updates memory immediately (write-through), updates the        *)
(* writer's cache and invalidates the address in every other cache.       *)
(* A read returns the current memory value and fills the reader's cache.  *)
MemServe ==
  /\ memQ # << >>
  /\ LET p == Head(memQ)[1]
         r == Head(memQ)[2]
         a == r.adr
     IN  /\ memQ'       = Tail(memQ)
         /\ ctl'        = [ctl        EXCEPT ![p] = "done"]
         /\ memAtServe' = [memAtServe EXCEPT ![p] = mem[a]]
         /\ IF r.op = "Wr"
              THEN /\ mem'   = [mem EXCEPT ![a] = r.val]
                   /\ buf'   = [buf EXCEPT ![p] = NoVal]
                   /\ cache' = [q \in Proc |->
                                  IF q = p THEN [cache[q] EXCEPT ![a] = r.val]
                                           ELSE [cache[q] EXCEPT ![a] = NoVal]]
              ELSE /\ mem'   = mem
                   /\ buf'   = [buf   EXCEPT ![p] = mem[a]]
                   /\ cache' = [cache EXCEPT ![p][a] = mem[a]]
  /\ UNCHANGED <<curReq, pending>>

(* Processor p accepts its reply and returns to idle. *)
Rsp(p) ==
  /\ ctl[p] = "done"
  /\ ctl'     = [ctl     EXCEPT ![p] = "rdy"]
  /\ pending' = [pending EXCEPT ![p] = FALSE]
  /\ UNCHANGED <<mem, buf, cache, memQ, curReq, memAtServe>>

(* The controller may evict any cache line at any time. *)
Evict(p, a) ==
  /\ cache[p][a] # NoVal
  /\ cache' = [cache EXCEPT ![p][a] = NoVal]
  /\ UNCHANGED <<mem, ctl, buf, memQ, curReq, memAtServe, pending>>

Next ==
  \/ \E p \in Proc : Req(p) \/ Forward(p) \/ CacheHit(p) \/ Rsp(p)
  \/ MemServe
  \/ \E p \in Proc, a \in Adr : Evict(p, a)

Fairness ==
  /\ \A p \in Proc : WF_vars(Forward(p) \/ CacheHit(p))
  /\ \A p \in Proc : WF_vars(Rsp(p))
  /\ WF_vars(MemServe)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

(* Write-through caches never hold stale data. *)
CacheCoherence ==
  \A p \in Proc, a \in Adr : cache[p][a] \in {NoVal, mem[a]}

(* A read reply equals the memory value at the time the read was served. *)
ReadCoherence ==
  \A p \in Proc :
     (ctl[p] = "done" /\ curReq[p] \in RdReq) => buf[p] = memAtServe[p]

(* Buffers hold the issued request while it is outstanding. *)
BufferOK ==
  \A p \in Proc :
     /\ (ctl[p] # "rdy") => curReq[p] \in MReq
     /\ (ctl[p] \in {"busy", "waiting"}) => buf[p] = curReq[p]
     /\ (ctl[p] = "done" /\ curReq[p] \in WrReq) => buf[p] = NoVal

(* The memory interface holds exactly the requests of waiting processors, *)
(* each exactly once, matched to the issuing processor.                   *)
QueueOK ==
  /\ \A i \in 1..Len(memQ) :
        /\ ctl[memQ[i][1]] = "waiting"
        /\ memQ[i][2] = curReq[memQ[i][1]]
  /\ \A p \in Proc :
        (ctl[p] = "waiting") <=>
           (Cardinality({i \in 1..Len(memQ) : memQ[i][1] = p}) = 1)
  /\ \A p \in Proc :
        Cardinality({i \in 1..Len(memQ) : memQ[i][1] = p}) <= 1

(* No lost or spurious replies. *)
NoLostOrSpurious ==
  \A p \in Proc : pending[p] <=> (ctl[p] # "rdy")

Inv ==
  /\ TypeOK
  /\ CacheCoherence
  /\ ReadCoherence
  /\ BufferOK
  /\ QueueOK
  /\ NoLostOrSpurious

(* Action-level safety properties *)

(* Every read reply equals the memory value at the step it is produced,   *)
(* and every write updates memory in the very step it is performed.       *)
ReplyCoherenceProp ==
  [][\A p \in Proc :
        (ctl[p] # "done" /\ ctl'[p] = "done") =>
           IF curReq[p] \in RdReq
             THEN buf'[p] = mem[curReq[p].adr]
             ELSE mem'[curReq[p].adr] = curReq[p].val]_vars

(* A reply is only produced for a pending, issued request. *)
NoSpuriousReplyProp ==
  [][\A p \in Proc :
        (ctl[p] # "done" /\ ctl'[p] = "done") =>
           (pending[p] /\ ctl[p] \in {"busy", "waiting"})]_vars

(* After a reply is accepted the processor returns to idle. *)
ReturnToIdleProp ==
  [][\A p \in Proc :
        (ctl[p] = "done" /\ ctl'[p] # "done") =>
           (ctl'[p] = "rdy" /\ ~pending'[p])]_vars

-----------------------------------------------------------------------------
(* Liveness *)

EventuallyServiced ==
  \A p \in Proc : (ctl[p] \in {"busy", "waiting"}) ~> (ctl[p] = "done")

EventuallyReplied ==
  \A p \in Proc : pending[p] ~> ~pending[p]

-----------------------------------------------------------------------------
(* Refinement mapping to an abstract atomic memory interface.             *)
(* The abstract memory has, per processor, a control state in             *)
(* {"rdy","busy","done"} and a buffer; a request is performed atomically  *)
(* in one step.  The controller's "waiting" state, the memory queue, and  *)
(* the caches are internal and hidden.  Linearization points are          *)
(* MemServe (for p at the head of memQ) and CacheHit(p).                  *)

barMem == mem
barCtl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
barBuf == buf

absVars == <<barMem, barCtl, barBuf>>

AInit ==
  /\ barMem \in [Adr -> Val]
  /\ barCtl = [p \in Proc |-> "rdy"]
  /\ barBuf = [p \in Proc |-> NoVal]

AReq(p) ==
  /\ barCtl[p] = "rdy"
  /\ \E r \in MReq : barBuf' = [barBuf EXCEPT ![p] = r]
  /\ barCtl' = [barCtl EXCEPT ![p] = "busy"]
  /\ barMem' = barMem

ADo(p) ==
  /\ barCtl[p] = "busy"
  /\ barCtl' = [barCtl EXCEPT ![p] = "done"]
  /\ LET r == barBuf[p] IN
       IF r.op = "Rd"
         THEN /\ barBuf' = [barBuf EXCEPT ![p] = barMem[r.adr]]
              /\ barMem' = barMem
         ELSE /\ barMem' = [barMem EXCEPT ![r.adr] = r.val]
              /\ barBuf' = [barBuf EXCEPT ![p] = NoVal]

ARsp(p) ==
  /\ barCtl[p] = "done"
  /\ barCtl' = [barCtl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<barMem, barBuf>>

AbsNext == \E p \in Proc : AReq(p) \/ ADo(p) \/ ARsp(p)

AbsSpec ==
  /\ AInit
  /\ [][AbsNext]_absVars
  /\ \A p \in Proc : WF_absVars(ADo(p))
  /\ \A p \in Proc : WF_absVars(ARsp(p))

-----------------------------------------------------------------------------
(* Proof obligations *)

THEOREM TypeCorrect      == Spec => []TypeOK
THEOREM InvariantHolds   == Spec => []Inv
THEOREM SafetyActions    == Spec => (ReplyCoherenceProp /\ NoSpuriousReplyProp
                                     /\ ReturnToIdleProp)
THEOREM Liveness         == Spec => (EventuallyServiced /\ EventuallyReplied)

(* Refinement obligations:                                                 *)
(*  R1: initial states map to abstract initial states;                     *)
(*  R2: under Inv each concrete step is an abstract step or a stutter:     *)
(*      Req -> AReq, CacheHit/MemServe -> ADo, Rsp -> ARsp,                *)
(*      Forward/Evict -> stuttering (uses CacheCoherence and QueueOK);     *)
(*  R3: concrete fairness implies abstract fairness.                       *)
THEOREM RefInit          == Init => AInit
THEOREM RefStep          == (Inv /\ Inv' /\ [Next]_vars) => [AbsNext]_absVars
THEOREM Refinement       == Spec => AbsSpec
==================================================================================