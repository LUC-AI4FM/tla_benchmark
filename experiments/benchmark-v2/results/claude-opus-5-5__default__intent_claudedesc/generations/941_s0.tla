------------------------ MODULE WriteThroughCacheLive ------------------------
EXTENDS Naturals, Sequences

CONSTANTS Proc,             \* set of processors
          Adr,              \* set of memory addresses
          Val,              \* set of memory values
          QLen,             \* maximum length of the main-memory queue
          NoVal,            \* value distinct from all elements of Val
          InitMemInt,       \* set of initial values of memInt
          Send(_, _, _, _), \* Send(p, d, memInt, memInt')
          Reply(_, _, _, _) \* Reply(p, d, memInt, memInt')

ASSUME /\ QLen \in Nat
       /\ QLen > 0
       /\ NoVal \notin Val

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

VARIABLES memInt, wmem, ctl, buf, cache, memQ

vars == <<memInt, wmem, buf, ctl, cache, memQ>>

-----------------------------------------------------------------------------
TypeInvariant ==
  /\ wmem  \in [Adr -> Val]
  /\ ctl   \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf   \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ  \in Seq(Proc \X MReq)
  /\ Len(memQ) \leq QLen

Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

-----------------------------------------------------------------------------
Init == /\ memInt \in InitMemInt
        /\ wmem \in [Adr -> Val]
        /\ ctl = [p \in Proc |-> "rdy"]
        /\ buf = [p \in Proc |-> NoVal]
        /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
        /\ memQ = << >>

Req(p) == /\ ctl[p] = "rdy"
          /\ \E req \in MReq :
                /\ Send(p, req, memInt, memInt')
                /\ buf' = [buf EXCEPT ![p] = req]
                /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ UNCHANGED <<wmem, cache, memQ>>

Rsp(p) == /\ ctl[p] = "done"
          /\ Reply(p, buf[p], memInt, memInt')
          /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
          /\ UNCHANGED <<wmem, buf, cache, memQ>>

RdMiss(p) == /\ ctl[p] = "busy"
             /\ buf[p].op = "Rd"
             /\ cache[p][buf[p].adr] = NoVal
             /\ Len(memQ) < QLen
             /\ memQ' = Append(memQ, <<p, buf[p]>>)
             /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
             /\ UNCHANGED <<memInt, wmem, buf, cache>>

DoRd(p) == /\ ctl[p] \in {"busy", "waiting"}
           /\ buf[p].op = "Rd"
           /\ cache[p][buf[p].adr] # NoVal
           /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
           /\ ctl' = [ctl EXCEPT ![p] = "done"]
           /\ UNCHANGED <<memInt, wmem, cache, memQ>>

DoWr(p) == LET r == buf[p]
           IN  /\ ctl[p] = "busy"
               /\ r.op = "Wr"
               /\ Len(memQ) < QLen
               /\ cache' = [q \in Proc |->
                              IF (p = q) \/ (cache[q][r.adr] # NoVal)
                                THEN [cache[q] EXCEPT ![r.adr] = r.val]
                                ELSE cache[q]]
               /\ memQ' = Append(memQ, <<p, r>>)
               /\ buf' = [buf EXCEPT ![p] = NoVal]
               /\ ctl' = [ctl EXCEPT ![p] = "done"]
               /\ UNCHANGED <<memInt, wmem>>

\* Value memory would have after all queued writes are performed
vmem == LET f[i \in 0..Len(memQ)] ==
              IF i = 0 THEN wmem
              ELSE IF memQ[i][2].op = "Rd"
                     THEN f[i-1]
                     ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
        IN  f[Len(memQ)]

MemQWr == LET r == Head(memQ)[2]
          IN  /\ memQ # << >>
              /\ r.op = "Wr"
              /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
              /\ memQ' = Tail(memQ)
              /\ UNCHANGED <<memInt, buf, ctl, cache>>

MemQRd == LET p == Head(memQ)[1]
              r == Head(memQ)[2]
          IN  /\ memQ # << >>
              /\ r.op = "Rd"
              /\ memQ' = Tail(memQ)
              /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
              /\ UNCHANGED <<memInt, wmem, buf, ctl>>

Evict(p, a) == /\ (ctl[p] = "waiting") => (buf[p].adr # a)
               /\ cache' = [cache EXCEPT ![p][a] = NoVal]
               /\ UNCHANGED <<memInt, wmem, buf, ctl, memQ>>

Next == \/ \E p \in Proc : \/ Req(p) \/ Rsp(p)
                           \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
                           \/ \E a \in Adr : Evict(p, a)
        \/ MemQWr
        \/ MemQRd

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Liveness / fairness conditions                                          *)
-----------------------------------------------------------------------------
QCond == \/ Len(memQ) = QLen
         \/ \E i \in 1..Len(memQ) : memQ[i][2].op = "Rd"

Liveness ==
  /\ \A p \in Proc : /\ WF_vars(Rsp(p) \/ DoRd(p))
                     /\ SF_vars(RdMiss(p) \/ DoWr(p))
  /\ WF_vars(QCond /\ (MemQWr \/ MemQRd))

LSpec == Spec /\ Liveness

\* Every issued request eventually receives a response
RequestCompletion == \A p \in Proc : (ctl[p] # "rdy") ~> (ctl[p] = "rdy")

-----------------------------------------------------------------------------
(* Refinement mapping to the live internal memory specification            *)
-----------------------------------------------------------------------------
omem == vmem
octl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
ovars == <<memInt, omem, octl, buf>>

IInit == /\ memInt \in InitMemInt
         /\ omem \in [Adr -> Val]
         /\ octl = [p \in Proc |-> "rdy"]
         /\ buf = [p \in Proc |-> NoVal]

IReq(p) == /\ octl[p] = "rdy"
           /\ \E req \in MReq :
                 /\ Send(p, req, memInt, memInt')
                 /\ buf' = [buf EXCEPT ![p] = req]
                 /\ octl' = [octl EXCEPT ![p] = "busy"]
           /\ omem' = omem

IDo(p) == /\ octl[p] = "busy"
          /\ omem' = IF buf[p].op = "Wr"
                       THEN [omem EXCEPT ![buf[p].adr] = buf[p].val]
                       ELSE omem
          /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                         THEN NoVal
                                         ELSE omem[buf[p].adr]]
          /\ octl' = [octl EXCEPT ![p] = "done"]
          /\ memInt' = memInt

IRsp(p) == /\ octl[p] = "done"
           /\ Reply(p, buf[p], memInt, memInt')
           /\ octl' = [octl EXCEPT ![p] = "rdy"]
           /\ omem' = omem
           /\ buf' = buf

INext == \E p \in Proc : IReq(p) \/ IDo(p) \/ IRsp(p)

ISafety == IInit /\ [][INext]_ovars

\* Weak fairness of IDo(p) and IRsp(p) of the live internal memory, written
\* with their enabling conditions under the refinement mapping
\* (ENABLED IDo(p) = octl[p]="busy"; ENABLED IRsp(p) = octl[p]="done").
ILiveness ==
  \A p \in Proc :
    /\ \/ []<>(octl[p] # "busy")
       \/ []<><<IDo(p)>>_ovars
    /\ \/ []<>(octl[p] # "done")
       \/ []<><<IRsp(p)>>_ovars

ILSpec == ISafety /\ ILiveness

THEOREM LSpec => [](TypeInvariant /\ Coherence)
THEOREM LSpec => ILSpec
THEOREM LSpec => RequestCompletion

-----------------------------------------------------------------------------
(* Concrete substitutions for model checking                               *)
(*   Send <- MCSend, Reply <- MCReply, InitMemInt <- MCInitMemInt          *)
-----------------------------------------------------------------------------
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}
=============================================================================