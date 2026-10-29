------------------------- MODULE MCWriteThroughCache -------------------------
(***************************************************************************)
(* TLC model-checking wrapper for the write-through cache specification.  *)
(* The cache specification and its memory interface are inlined so the    *)
(* module is self-contained. The model overrides Send, Reply and           *)
(* InitMemInt with the concrete MCSend, MCReply and MCInitMemInt. The      *)
(* refinement target (an InternalMemory-style specification) is inlined   *)
(* by hand because the referenced TLC version cannot handle module         *)
(* instantiation.                                                          *)
(***************************************************************************)
EXTENDS Naturals, Sequences

-----------------------------------------------------------------------------
(***************************************************************************)
(* Memory interface                                                        *)
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

-----------------------------------------------------------------------------
(***************************************************************************)
(* Write-through cache                                                     *)
(***************************************************************************)
VARIABLES wmem, ctl, buf, cache, memQ

CONSTANT QLen

ASSUME (QLen \in Nat) /\ (QLen > 0)

vars == <<memInt, wmem, buf, ctl, cache, memQ>>

Init == /\ wmem \in [Adr -> Val]
        /\ ctl = [p \in Proc |-> "rdy"]
        /\ buf = [p \in Proc |-> NoVal]
        /\ memInt \in InitMemInt
        /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
        /\ memQ = << >>

TypeInvariant ==
  /\ wmem  \in [Adr -> Val]
  /\ ctl   \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf   \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ memQ  \in Seq(Proc \X MReq)

Coherence ==
  \A p, q \in Proc, a \in Adr :
     (NoVal \notin {cache[p][a], cache[q][a]}) => (cache[p][a] = cache[q][a])

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

vmem == LET f[i \in 0 .. Len(memQ)] ==
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

THEOREM Spec => [](TypeInvariant /\ Coherence)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete replacements for the memory-interface constants (used in the  *)
(* model configuration as Send <- MCSend, Reply <- MCReply,                *)
(* InitMemInt <- MCInitMemInt).                                           *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Hand-inlined instance of InternalMemory with                            *)
(*    mem <- vmem,                                                         *)
(*    ctl <- [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]],*)
(*    buf <- buf                                                           *)
(* written out explicitly since the TLC version cannot handle INSTANCE.    *)
(***************************************************************************)
IMmem == vmem
IMctl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
IMbuf == buf

IMvars == <<memInt, IMmem, IMctl, IMbuf>>

IMTypeInvariant ==
  /\ IMmem \in [Adr -> Val]
  /\ IMctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ IMbuf \in [Proc -> MReq \cup Val \cup {NoVal}]

IMInit == /\ IMmem \in [Adr -> Val]
          /\ IMctl = [p \in Proc |-> "rdy"]
          /\ IMbuf = [p \in Proc |-> NoVal]
          /\ memInt \in InitMemInt

IMReq(p) == /\ IMctl[p] = "rdy"
            /\ \E req \in MReq :
                  /\ Send(p, req, memInt, memInt')
                  /\ IMbuf' = [IMbuf EXCEPT ![p] = req]
                  /\ IMctl' = [IMctl EXCEPT ![p] = "busy"]
            /\ UNCHANGED IMmem

IMDo(p) == /\ IMctl[p] = "busy"
           /\ IMmem' = IF IMbuf[p].op = "Wr"
                         THEN [IMmem EXCEPT ![IMbuf[p].adr] = IMbuf[p].val]
                         ELSE IMmem
           /\ IMbuf' = [IMbuf EXCEPT ![p] = IF IMbuf[p].op = "Wr"
                                              THEN NoVal
                                              ELSE IMmem[IMbuf[p].adr]]
           /\ IMctl' = [IMctl EXCEPT ![p] = "done"]
           /\ UNCHANGED memInt

IMRsp(p) == /\ IMctl[p] = "done"
            /\ Reply(p, IMbuf[p], memInt, memInt')
            /\ IMctl' = [IMctl EXCEPT ![p] = "rdy"]
            /\ UNCHANGED <<IMmem, IMbuf>>

IMNext == \E p \in Proc : IMReq(p) \/ IMDo(p) \/ IMRsp(p)

IMSpec == IMInit /\ [][IMNext]_IMvars

THEOREM IMSpec => []IMTypeInvariant

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: every busy controller eventually becomes ready.              *)
(***************************************************************************)
Liveness == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

=============================================================================