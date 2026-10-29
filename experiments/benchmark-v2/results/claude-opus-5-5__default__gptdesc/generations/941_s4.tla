---------------------- MODULE MCLiveWriteThroughCache ----------------------
(***************************************************************************)
(* TLC model-checking wrapper for the live write-through cache.  The      *)
(* write-through cache and its liveness conditions are included here so   *)
(* that the module is self-contained.  The internal-memory liveness spec  *)
(* (LiveInternalMemory) is instantiated by hand, because the TLC version   *)
(* targeted here cannot handle the INSTANCE                                *)
(*                                                                         *)
(*    LM == INSTANCE LiveInternalMemory                                    *)
(*            WITH mem <- omem, ctl <- octl, buf <- obuf                   *)
(*                                                                         *)
(* The refinement mapping maps the cache state to the abstract memory     *)
(* variables omem, octl and obuf.                                          *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

(***************************************************************************)
(*                        Memory interface parameters                      *)
(***************************************************************************)
CONSTANTS Send(_, _, _, _), Reply(_, _, _, _), InitMemInt,
          Proc, Adr, Val, QLen

ASSUME (QLen \in Nat) /\ (QLen > 0)

(***************************************************************************)
(* Model values and overrides used by TLC.                                *)
(***************************************************************************)
CONSTANTS a1, a2, p1, p2, v1, v2

VARIABLES memInt, wmem, buf, ctl, cache, memQ

vars == <<memInt, wmem, buf, ctl, cache, memQ>>

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<p1, NoVal>>}

(***************************************************************************)
(*                         Write-through cache                             *)
(***************************************************************************)
Init ==
  /\ wmem \in [Adr -> Val]
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

Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED <<wmem, cache, memQ>>

Rsp(p) ==
  /\ ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<wmem, buf, cache, memQ>>

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
                     IF (p = q) \/ (cache[q][r.adr] # NoVal)
                       THEN [cache[q] EXCEPT ![r.adr] = r.val]
                       ELSE cache[q]]
      /\ memQ' = Append(memQ, <<p, r>>)
      /\ buf' = [buf EXCEPT ![p] = NoVal]
      /\ ctl' = [ctl EXCEPT ![p] = "done"]
      /\ UNCHANGED <<memInt, wmem>>

vmem ==
  LET f[i \in 0..Len(memQ)] ==
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

(***************************************************************************)
(*                     Liveness of the write-through cache                 *)
(***************************************************************************)
Liveness ==
  /\ \A p \in Proc :
        /\ WF_vars(Rsp(p) \/ DoRd(p))
        /\ SF_vars(RdMiss(p) \/ DoWr(p))
  /\ WF_vars(MemQWr \/ MemQRd)

LSpec == Spec /\ Liveness

(***************************************************************************)
(*                         Refinement mapping                              *)
(***************************************************************************)
omem == vmem
octl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
obuf == buf

ovars == <<memInt, omem, octl, obuf>>

(***************************************************************************)
(* Hand-instantiated definitions of LiveInternalMemory with               *)
(*   mem <- omem, ctl <- octl, buf <- obuf.                                *)
(***************************************************************************)
LM_Inner_IInit ==
  /\ omem \in [Adr -> Val]
  /\ octl = [p \in Proc |-> "rdy"]
  /\ obuf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

LM_Inner_TypeInvariant ==
  /\ omem \in [Adr -> Val]
  /\ octl \in [Proc -> {"rdy", "busy", "done"}]
  /\ obuf \in [Proc -> MReq \cup Val \cup {NoVal}]

LM_Inner_Req(p) ==
  /\ octl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ obuf' = [obuf EXCEPT ![p] = req]
        /\ octl' = [octl EXCEPT ![p] = "busy"]
  /\ UNCHANGED omem

LM_Inner_Do(p) ==
  /\ octl[p] = "busy"
  /\ omem' = IF obuf[p].op = "Wr"
               THEN [omem EXCEPT ![obuf[p].adr] = obuf[p].val]
               ELSE omem
  /\ obuf' = [obuf EXCEPT ![p] = IF obuf[p].op = "Wr"
                                   THEN NoVal
                                   ELSE omem[obuf[p].adr]]
  /\ octl' = [octl EXCEPT ![p] = "done"]
  /\ UNCHANGED memInt

LM_Inner_Rsp(p) ==
  /\ octl[p] = "done"
  /\ Reply(p, obuf[p], memInt, memInt')
  /\ octl' = [octl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<omem, obuf>>

LM_Inner_INext ==
  \E p \in Proc : LM_Inner_Req(p) \/ LM_Inner_Do(p) \/ LM_Inner_Rsp(p)

LM_Inner_ISpec == LM_Inner_IInit /\ [][LM_Inner_INext]_ovars

(***************************************************************************)
(* Enabledness of Do(p) \/ Rsp(p) in the abstract memory, written out by  *)
(* hand since TLC cannot compute ENABLED of the mapped actions.           *)
(***************************************************************************)
LM_Inner_ENABLEDDo(p)  == octl[p] = "busy"

LM_Inner_ENABLEDRsp(p) ==
  /\ octl[p] = "done"
  /\ \E newMemInt \in {<<p, obuf[p]>>} : Reply(p, obuf[p], memInt, newMemInt)

LM_Inner_ENABLEDDoOrRsp(p) == LM_Inner_ENABLEDDo(p) \/ LM_Inner_ENABLEDRsp(p)

(***************************************************************************)
(* WF_ovars(Do(p) \/ Rsp(p)) expanded using the hand-written enabledness. *)
(***************************************************************************)
LM_Inner_Liveness ==
  \A p \in Proc :
     \/ []<>(~LM_Inner_ENABLEDDoOrRsp(p))
     \/ []<><<LM_Inner_Do(p) \/ LM_Inner_Rsp(p)>>_ovars

LM_Inner_LISpec == LM_Inner_ISpec /\ LM_Inner_Liveness

(***************************************************************************)
(* Properties to be checked by TLC.                                        *)
(***************************************************************************)
THEOREM LSpec => [](TypeInvariant /\ Coherence /\ LM_Inner_TypeInvariant)
THEOREM LSpec => LM_Inner_LISpec

(***************************************************************************)
(* PostCondition: a value with the shape of a TLC counterexample, i.e. a  *)
(* record with a set of numbered states and a set of numbered actions     *)
(* (edges between states), describing a two-state lasso.                  *)
(***************************************************************************)
PCState1 == [ memInt |-> <<p1, "NoVal">>,
              omem   |-> [a \in {a1, a2} |-> v1],
              octl   |-> [p \in {p1, p2} |-> "rdy"] ]

PCState2 == [ memInt |-> <<p1, [op |-> "Rd", adr |-> a1]>>,
              omem   |-> [a \in {a1, a2} |-> v1],
              octl   |-> [p \in {p1, p2} |-> IF p = p1 THEN "busy" ELSE "rdy"] ]

PostCondition ==
  [ state  |-> { <<1, PCState1>>, <<2, PCState2>> },
    action |-> { << <<1, PCState1>>, [name |-> "Req"],   <<2, PCState2>> >>,
                 << <<2, PCState2>>, [name |-> "Evict"], <<2, PCState2>> >> } ]

=============================================================================