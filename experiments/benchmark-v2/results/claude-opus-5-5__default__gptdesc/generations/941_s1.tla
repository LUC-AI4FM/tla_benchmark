---------------------- MODULE MCLiveWriteThroughCache ----------------------
(***************************************************************************)
(* TLC model-checking wrapper for the live write-through cache.            *)
(*                                                                         *)
(* The intended way to check that the write-through cache implements the  *)
(* live internal memory would be                                           *)
(*                                                                         *)
(*    LM == INSTANCE LiveInternalMemory                                    *)
(*            WITH mem <- vmem,                                            *)
(*                 ctl <- [p \in Proc |-> IF ctl[p] = "waiting"           *)
(*                                          THEN "busy" ELSE ctl[p]]      *)
(*                                                                         *)
(* and then to check LM!LISpec as a property.  The version of TLC targeted *)
(* here cannot handle that instantiation, in particular the substitution   *)
(* under ENABLED in the fairness conditions.  This module therefore writes *)
(* the instantiated definitions out by hand, in terms of the refinement    *)
(* mapping omem, octl, obuf.  The module is self-contained: the memory     *)
(* interface, internal memory, and write-through cache definitions on      *)
(* which it relies are written out first.                                  *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

-----------------------------------------------------------------------------
(***************************************************************************)
(* Constants.  NoVal is a model value that is not in Val; TLC cannot       *)
(* evaluate CHOOSE v : v \notin Val.                                       *)
(***************************************************************************)
CONSTANTS Proc, Adr, Val, QLen, NoVal

(***************************************************************************)
(* Model values used for instantiating the constants in a TLC model.       *)
(***************************************************************************)
CONSTANTS p1, p2, a1, a2, v1, v2, MaxQLen

ASSUME /\ QLen \in Nat
       /\ QLen > 0
       /\ NoVal \notin Val
       /\ MaxQLen \in Nat

MCProc == {p1, p2}
MCAdr  == {a1, a2}
MCVal  == {v1, v2}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Memory interface: concrete versions of Send, Reply, InitMemInt.         *)
(***************************************************************************)
VARIABLES memInt, wmem, ctl, buf, cache, memQ

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

Send(p, d, miOld, miNew)  == miNew = <<p, d>>
Reply(p, d, miOld, miNew) == miNew = <<p, d>>

InitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

vars == <<memInt, wmem, ctl, buf, cache, memQ>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* The write-through cache (WriteThroughCache).                            *)
(***************************************************************************)
Init ==
  /\ wmem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt
  /\ cache = [p \in Proc |-> [a \in Adr |-> NoVal]]
  /\ memQ = << >>

TypeInvariant ==
  /\ wmem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "waiting", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cache \in [Proc -> [Adr -> Val \cup {NoVal}]]
  /\ Len(memQ) \in 0..QLen
  /\ \A i \in 1..Len(memQ) : memQ[i] \in Proc \X MReq

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

(***************************************************************************)
(* vmem is the value the memory will have once all writes in memQ are      *)
(* performed.                                                              *)
(***************************************************************************)
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
      /\ UNCHANGED <<memInt, wmem, ctl, buf>>

Evict(p, a) ==
  /\ (ctl[p] = "waiting") => (buf[p].adr # a)
  /\ cache' = [cache EXCEPT ![p][a] = NoVal]
  /\ UNCHANGED <<memInt, wmem, ctl, buf, memQ>>

Next ==
  \/ \E p \in Proc :
        \/ Req(p) \/ Rsp(p)
        \/ RdMiss(p) \/ DoRd(p) \/ DoWr(p)
        \/ \E a \in Adr : Evict(p, a)
  \/ MemQWr
  \/ MemQRd

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Liveness of the cache (LiveWriteThroughCache).                          *)
(***************************************************************************)
Liveness ==
  /\ \A p \in Proc :
        /\ WF_vars(Rsp(p) \/ DoRd(p))
        /\ SF_vars(RdMiss(p) \/ DoWr(p))
  /\ WF_vars(MemQWr \/ MemQRd)

LSpec == Spec /\ Liveness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement mapping to the internal memory's variables.                  *)
(***************************************************************************)
omem == vmem
octl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
obuf == buf

ovars == <<memInt, omem, octl, obuf>>

(***************************************************************************)
(* Hand-instantiated definitions of LiveInternalMemory with                *)
(* mem <- omem, ctl <- octl, buf <- obuf.                                  *)
(***************************************************************************)
OIInit ==
  /\ omem \in [Adr -> Val]
  /\ octl = [p \in Proc |-> "rdy"]
  /\ obuf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

OTypeInvariant ==
  /\ omem \in [Adr -> Val]
  /\ octl \in [Proc -> {"rdy", "busy", "done"}]
  /\ obuf \in [Proc -> MReq \cup Val \cup {NoVal}]

OReq(p) ==
  /\ octl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ obuf' = [obuf EXCEPT ![p] = req]
        /\ octl' = [octl EXCEPT ![p] = "busy"]
  /\ UNCHANGED omem

ODo(p) ==
  /\ octl[p] = "busy"
  /\ omem' = IF obuf[p].op = "Wr"
               THEN [omem EXCEPT ![obuf[p].adr] = obuf[p].val]
               ELSE omem
  /\ obuf' = [obuf EXCEPT ![p] = IF obuf[p].op = "Wr"
                                   THEN NoVal
                                   ELSE omem[obuf[p].adr]]
  /\ octl' = [octl EXCEPT ![p] = "done"]
  /\ UNCHANGED memInt

ORsp(p) ==
  /\ octl[p] = "done"
  /\ Reply(p, obuf[p], memInt, memInt')
  /\ octl' = [octl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<omem, obuf>>

OINext == \E p \in Proc : OReq(p) \/ ODo(p) \/ ORsp(p)

OISpec == OIInit /\ [][OINext]_ovars

(***************************************************************************)
(* Enabledness of the instantiated actions, computed by hand, since TLC    *)
(* cannot evaluate ENABLED applied to the substituted actions.             *)
(* With the concrete Reply, ENABLED ORsp(p) reduces to octl[p] = "done".   *)
(***************************************************************************)
OEnabledDo(p)  == octl[p] = "busy"
OEnabledRsp(p) == octl[p] = "done"

(***************************************************************************)
(* Weak fairness of ODo(p) and ORsp(p), expanded using the definitions     *)
(* of enabledness above:                                                   *)
(*   WF_v(A) == []<>(~ENABLED <<A>>_v) \/ []<><<A>>_v                      *)
(***************************************************************************)
OLiveness ==
  \A p \in Proc :
     /\ []<>(~OEnabledDo(p))  \/ []<><<ODo(p)>>_ovars
     /\ []<>(~OEnabledRsp(p)) \/ []<><<ORsp(p)>>_ovars

OLISpec == OISpec /\ OLiveness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking aids.                                                    *)
(***************************************************************************)
Constraint == Len(memQ) <= MaxQLen

(***************************************************************************)
(* A value shaped like a TLC counterexample trace: a sequence of states,   *)
(* each recording the action taken and the values of the cache variables. *)
(***************************************************************************)
PostCondition ==
  << [ action |-> "Init",
       state  |-> [ memInt |-> <<p1, NoVal>>,
                    wmem   |-> [a \in {a1, a2} |-> v1],
                    ctl    |-> [p \in {p1, p2} |-> "rdy"],
                    buf    |-> [p \in {p1, p2} |-> NoVal],
                    cache  |-> [p \in {p1, p2} |-> [a \in {a1, a2} |-> NoVal]],
                    memQ   |-> << >> ] ],
     [ action |-> "Req",
       state  |-> [ memInt |-> <<p1, [op |-> "Rd", adr |-> a1]>>,
                    wmem   |-> [a \in {a1, a2} |-> v1],
                    ctl    |-> [p \in {p1, p2} |-> IF p = p1 THEN "busy" ELSE "rdy"],
                    buf    |-> [p \in {p1, p2} |->
                                  IF p = p1 THEN [op |-> "Rd", adr |-> a1]
                                            ELSE NoVal],
                    cache  |-> [p \in {p1, p2} |-> [a \in {a1, a2} |-> NoVal]],
                    memQ   |-> << >> ] ] >>

(***************************************************************************)
(* Properties to check with TLC against LSpec:                             *)
(*   INVARIANTS  TypeInvariant  Coherence  OTypeInvariant                  *)
(*   PROPERTIES  OLISpec                                                   *)
(***************************************************************************)
THEOREM LSpec => [](TypeInvariant /\ Coherence /\ OTypeInvariant)
THEOREM LSpec => OLISpec
=============================================================================