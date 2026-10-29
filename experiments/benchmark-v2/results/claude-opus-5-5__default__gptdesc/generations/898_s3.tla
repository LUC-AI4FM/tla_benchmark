------------------------- MODULE MCWriteThroughCache -------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

-----------------------------------------------------------------------------
(* Memory interface                                                         *)
-----------------------------------------------------------------------------
CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val,
          QLen

ASSUME (QLen \in Nat) /\ (QLen > 0)

VARIABLE memInt

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

-----------------------------------------------------------------------------
(* Write-through cache                                                      *)
-----------------------------------------------------------------------------
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

(* The internal memory M with mem <- wmem, inlined *)
M_IInit ==
  /\ wmem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

M_Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED wmem

M_Rsp(p) ==
  /\ ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<wmem, buf>>

Init ==
  /\ M_IInit
  /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
  /\ memQ = << >>

Req(p) == M_Req(p) /\ UNCHANGED <<cache, memQ>>

Rsp(p) == M_Rsp(p) /\ UNCHANGED <<cache, memQ>>

RdMiss(p) ==
  /\ ctl[p] = "busy"
  /\ buf[p].op = "Rd"
  /\ cache[p][buf[p].adr] = NoVal
  /\ Len(memQ) < QLen
  /\ memQ' = Append(memQ, <<p, buf[p]>>)
  /\ ctl' = [ctl EXCEPT ![p] = "waiting"]
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
                     IF (p # q) /\ (cache[q][r.adr] # NoVal)
                       THEN [cache[q] EXCEPT ![r.adr] = r.val]
                       ELSE cache[q]]
      /\ memQ' = Append(memQ, <<p, r>>)
      /\ buf' = [buf EXCEPT ![p] = NoVal]
      /\ ctl' = [ctl EXCEPT ![p] = "done"]
      /\ UNCHANGED <<memInt, wmem>>

vmem ==
  LET f[i \in 0 .. Len(memQ)] ==
        IF i = 0 THEN wmem
        ELSE IF memQ[i][2].op = "Rd"
               THEN f[i - 1]
               ELSE [f[i - 1] EXCEPT ![memQ[i][2].adr] = memQ[i][2].val]
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
      /\ memQ' = Tail(memQ)
      /\ cache' = [cache EXCEPT ![p][r.adr] = vmem[r.adr]]
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

-----------------------------------------------------------------------------
(* Model-checking replacements for the memory-interface constants           *)
-----------------------------------------------------------------------------
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------
(* Hand-inlined instance                                                    *)
(*   LM == INSTANCE InternalMemory WITH mem <- vmem,                        *)
(*            ctl <- [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy"      *)
(*                                                         ELSE ctl[p]]     *)
(* (TLC version used cannot handle module instantiation.)                   *)
-----------------------------------------------------------------------------
LM_Inner_mem == vmem

LM_Inner_ctl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]

LM_Inner_IInit ==
  /\ LM_Inner_mem \in [Adr -> Val]
  /\ LM_Inner_ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

LM_Inner_TypeInvariant ==
  /\ LM_Inner_mem \in [Adr -> Val]
  /\ LM_Inner_ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

LM_Inner_Req(p) ==
  /\ LM_Inner_ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ LM_Inner_ctl' = [LM_Inner_ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED LM_Inner_mem

LM_Inner_Do(p) ==
  /\ LM_Inner_ctl[p] = "busy"
  /\ LM_Inner_mem' = IF buf[p].op = "Wr"
                       THEN [LM_Inner_mem EXCEPT ![buf[p].adr] = buf[p].val]
                       ELSE LM_Inner_mem
  /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                 THEN NoVal
                                 ELSE LM_Inner_mem[buf[p].adr]]
  /\ LM_Inner_ctl' = [LM_Inner_ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED memInt

LM_Inner_Rsp(p) ==
  /\ LM_Inner_ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ LM_Inner_ctl' = [LM_Inner_ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<LM_Inner_mem, buf>>

LM_Inner_INext ==
  \E p \in Proc : LM_Inner_Req(p) \/ LM_Inner_Do(p) \/ LM_Inner_Rsp(p)

LM_Inner_ISpec ==
  LM_Inner_IInit /\ [][LM_Inner_INext]_<<memInt, LM_Inner_mem, LM_Inner_ctl, buf>>

THEOREM LM_Inner_ISpec => []LM_Inner_TypeInvariant

-----------------------------------------------------------------------------
(* Liveness: every busy controller eventually becomes ready                 *)
-----------------------------------------------------------------------------
LM_Inner_Liveness ==
  \A p \in Proc : (LM_Inner_ctl[p] = "busy") ~> (LM_Inner_ctl[p] = "rdy")

=============================================================================