---------------------------- MODULE WriteThroughCache ----------------------------
EXTENDS Naturals, Sequences

CONSTANTS Proc, Adr, Val, QLen

ASSUME (QLen \in Nat) /\ (QLen > 0)

VARIABLES memInt, vmem, buf, ctl, cache, memQ

vars == <<memInt, vmem, buf, ctl, cache, memQ>>

-----------------------------------------------------------------------------
(* Definitions normally obtained from the MemoryInterface module *)

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

Send(p, d, miOld, miNew) == miNew = <<p, d>>

Reply(p, d, miOld, miNew) == miNew = <<p, d>>

InitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------
(* Expanded InternalMemory instance, with wmem renamed vmem *)

IInit == /\ vmem \in [Adr -> Val]
         /\ ctl = [p \in Proc |-> "rdy"]
         /\ buf = [p \in Proc |-> NoVal]
         /\ memInt \in InitMemInt

IReq(p) == /\ ctl[p] = "rdy"
           /\ \E req \in MReq :
                 /\ Send(p, req, memInt, memInt')
                 /\ buf' = [buf EXCEPT ![p] = req]
                 /\ ctl' = [ctl EXCEPT ![p] = "busy"]
           /\ UNCHANGED vmem

IRsp(p) == /\ ctl[p] = "done"
           /\ Reply(p, buf[p], memInt, memInt')
           /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
           /\ UNCHANGED <<vmem, buf>>

-----------------------------------------------------------------------------
(* Write-through cache *)

TypeInvariant ==
  /\ vmem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ \in Seq(Proc \X MReq)

Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

Init == /\ IInit
        /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
        /\ memQ = <<>>

Req(p) == IReq(p) /\ UNCHANGED <<cache, memQ>>

Rsp(p) == IRsp(p) /\ UNCHANGED <<cache, memQ>>

RdMiss(p) == /\ ctl[p] = "busy"
             /\ buf[p].op = "Rd"
             /\ cache[p][buf[p].adr] = NoVal
             /\ Len(memQ) < QLen
             /\ memQ' = Append(memQ, <<p, buf[p]>>)
             /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
             /\ UNCHANGED <<memInt, vmem, buf, cache>>

DoRd(p) == /\ ctl[p] \in {"busy", "waiting"}
           /\ buf[p].op = "Rd"
           /\ cache[p][buf[p].adr] # NoVal
           /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
           /\ ctl' = [ctl EXCEPT ![p] = "done"]
           /\ UNCHANGED <<memInt, vmem, cache, memQ>>

DoWr(p) ==
  LET r == buf[p]
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
      /\ UNCHANGED <<memInt, vmem>>

MemQWr ==
  LET r == Head(memQ)[2]
  IN  /\ memQ # <<>>
      /\ r.op = "Wr"
      /\ vmem' = [vmem EXCEPT ![r.adr] = r.val]
      /\ memQ' = Tail(memQ)
      /\ UNCHANGED <<memInt, buf, ctl, cache>>

MemQRd ==
  LET p == Head(memQ)[1]
      r == Head(memQ)[2]
  IN  /\ memQ # <<>>
      /\ r.op = "Rd"
      /\ memQ' = Tail(memQ)
      /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
      /\ UNCHANGED <<memInt, vmem, buf, ctl>>

Evict(p, a) == /\ (ctl[p] = "waiting") => (buf[p].adr # a)
               /\ cache[p][a] # NoVal
               /\ cache' = [cache EXCEPT ![p][a] = NoVal]
               /\ UNCHANGED <<memInt, vmem, buf, ctl, memQ>>

Next == \/ \E p \in Proc : \/ Req(p) \/ Rsp(p)
                           \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
                           \/ \E a \in Adr : Evict(p, a)
        \/ MemQWr
        \/ MemQRd

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeInvariant /\ Coherence)
=============================================================================