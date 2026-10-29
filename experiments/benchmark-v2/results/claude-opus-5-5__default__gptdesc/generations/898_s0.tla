------------------------- MODULE MCWriteThroughCache -------------------------
(***************************************************************************)
(* TLC model-checking wrapper for the write-through cache specification.  *)
(* The WriteThroughCache module, and the MemoryInterface constants it     *)
(* uses, are written out in this file so that it parses on its own.       *)
(* The constants Send, Reply and InitMemInt get concrete replacements     *)
(* MCSend, MCReply and MCInitMemInt. Substitute them in the TLC config:   *)
(*    Send <- MCSend   Reply <- MCReply   InitMemInt <- MCInitMemInt       *)
(* The InternalMemory refinement target is instantiated by hand, because  *)
(* the TLC version in question cannot handle module instantiation.        *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

(***************************************************************************)
(*                        Memory interface                                *)
(***************************************************************************)
VARIABLE memInt

CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val

ASSUME \A p, d, miOld, miNew :
          /\ Send(p, d, miOld, miNew)  \in BOOLEAN
          /\ Reply(p, d, miOld, miNew) \in BOOLEAN

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

(***************************************************************************)
(*                     Write-through cache                                *)
(***************************************************************************)
CONSTANT QLen
ASSUME (QLen \in Nat) /\ (QLen > 0)

VARIABLES wmem, ctl, buf, cache, memQ

vars == <<memInt, wmem, buf, ctl, cache, memQ>>

TypeInvariant ==
  /\ wmem  \in [Adr -> Val]
  /\ ctl   \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf   \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ  \in Seq(Proc \X MReq)

Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

Init ==
  /\ wmem   \in [Adr -> Val]
  /\ ctl    = [p \in Proc |-> "rdy"]
  /\ buf    = [p \in Proc |-> NoVal]
  /\ cache  = [p \in Proc |-> [a \in Adr |-> NoVal]]
  /\ memQ   = << >>
  /\ memInt \in InitMemInt

Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
        /\ buf' = [buf EXCEPT ![p] = req]
  /\ UNCHANGED <<cache, memQ, wmem>>

Rsp(p) ==
  /\ ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<cache, memQ, wmem, buf>>

RdMiss(p) ==
  /\ ctl[p] = "busy"
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] = NoVal
  /\ Len(memQ) < QLen
  /\ memQ' = Append(memQ, <<p, buf[p]>>)
  /\ ctl'  = [ctl EXCEPT ![p] = "waiting"]
  /\ UNCHANGED <<memInt, wmem, buf, cache>>

DoRd(p) ==
  /\ ctl[p] \in {"busy", "waiting"}
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] # NoVal
  /\ buf' = [buf EXCEPT ![p] = cache[p][buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED <<memInt, wmem, cache, memQ>>

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
      /\ buf'  = [buf EXCEPT ![p] = NoVal]
      /\ ctl'  = [ctl EXCEPT ![p] = "done"]
      /\ UNCHANGED <<memInt, wmem>>

(***************************************************************************)
(* vmem is the memory contents after every write in memQ has been done.   *)
(***************************************************************************)
vmem ==
  LET f[i \in 0 .. Len(memQ)] ==
        IF i = 0 THEN wmem
        ELSE IF memQ[i][2].op = "Rd"
               THEN f[i-1]
               ELSE [f[i-1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
  IN  f[Len(memQ)]

MemQWr ==
  LET r == Head(memQ)[2]
  IN  /\ memQ # << >>
      /\ r.op = "Wr"
      /\ wmem' = [wmem EXCEPT ![r.adr] = r.val]
      /\ memQ' = Tail(memQ)
      /\ UNCHANGED <<memInt, buf, ctl, cache>>

MemQRd ==
  LET p == Head(memQ)[1]
      r == Head(memQ)[2]
  IN  /\ memQ # << >>
      /\ r.op = "Rd"
      /\ memQ'  = Tail(memQ)
      /\ cache' = [cache EXCEPT ![p][r.adr] = wmem[r.adr]]
      /\ UNCHANGED <<memInt, wmem, buf, ctl>>

Evict(p, a) ==
  /\ (ctl[p] = "waiting") => (buf[p].adr # a)
  /\ cache' = [cache EXCEPT ![p][a] = NoVal]
  /\ UNCHANGED <<memInt, wmem, buf, ctl, memQ>>

Next ==
  \/ \E p \in Proc : \/ Req(p) \/ Rsp(p)
                     \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
                     \/ \E a \in Adr : Evict(p, a)
  \/ MemQWr
  \/ MemQRd

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(*         Concrete replacements for the memory-interface constants       *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

(***************************************************************************)
(* Hand-instantiated InternalMemory, under the refinement mapping         *)
(*    mem <- vmem,                                                         *)
(*    ctl <- ctl with "waiting" mapped to "busy",                          *)
(*    buf <- buf.                                                          *)
(***************************************************************************)
ictl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]

IInit ==
  /\ vmem   \in [Adr -> Val]
  /\ ictl   = [p \in Proc |-> "rdy"]
  /\ buf    = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

ITypeInvariant ==
  /\ vmem \in [Adr -> Val]
  /\ ictl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf  \in [Proc -> MReq \cup Val \cup {NoVal}]

IReq(p) ==
  /\ ictl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf'  = [buf EXCEPT ![p] = req]
        /\ ictl' = [ictl EXCEPT ![p] = "busy"]
  /\ UNCHANGED vmem

IDo(p) ==
  /\ ictl[p] = "busy"
  /\ vmem' = IF buf[p].op = "Wr"
               THEN [vmem EXCEPT ![buf[p].adr] = buf[p].val]
               ELSE vmem
  /\ buf'  = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                  THEN NoVal
                                  ELSE vmem[buf[p].adr]]
  /\ ictl' = [ictl EXCEPT ![p] = "done"]
  /\ UNCHANGED memInt

IRsp(p) ==
  /\ ictl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ictl' = [ictl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<vmem, buf>>

INext == \E p \in Proc : IReq(p) \/ IDo(p) \/ IRsp(p)

ISpec == IInit /\ [][INext]_<<memInt, vmem, ictl, buf>>

THEOREM ISpec => []ITypeInvariant

(***************************************************************************)
(* Liveness: every busy controller eventually becomes ready.              *)
(***************************************************************************)
Liveness == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

=============================================================================