---------------------- MODULE WriteThroughCacheController ----------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc, Adr, Val

ASSUME /\ Proc # {} /\ IsFiniteSet(Proc)
       /\ Adr  # {} /\ IsFiniteSet(Adr)
       /\ Val  # {} /\ IsFiniteSet(Val)

NoVal == CHOOSE v : v \notin Val

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

(***************************************************************************)
(* Abstract live memory interface (the specification to be implemented).   *)
(***************************************************************************)
---------------------------- MODULE LiveMemory ----------------------------------
VARIABLES mem, ctl, buf, memInt

avars == <<mem, ctl, buf, memInt>>

ATypeInvariant ==
  /\ mem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

AInit ==
  /\ mem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ memInt = <<>>

AReq(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ memInt' = <<p, req>>
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED mem

ADo(p) ==
  /\ ctl[p] = "busy"
  /\ mem' = IF buf[p].op = "Wr"
              THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
              ELSE mem
  /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                 THEN NoVal
                                 ELSE mem[buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED memInt

ARsp(p) ==
  /\ ctl[p] = "done"
  /\ memInt' = <<p, buf[p]>>
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<mem, buf>>

ANext == \E p \in Proc : AReq(p) \/ ADo(p) \/ ARsp(p)

ASpec == /\ AInit
         /\ [][ANext]_avars
         /\ \A p \in Proc : WF_avars(ADo(p)) /\ WF_avars(ARsp(p))
=================================================================================