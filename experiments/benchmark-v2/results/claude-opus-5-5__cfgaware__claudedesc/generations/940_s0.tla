---------------------------- MODULE MCLiveInternalMemory ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the LiveInternalMemory specification.        *)
(* Self-contained: it includes the MemoryInterface, InternalMemory and     *)
(* LiveInternalMemory definitions, plus TLC-friendly substitutions.        *)
(***************************************************************************)

CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val,
          NoVal

CONSTANTS p1, p2, a1, a2, a3, v1, v2

ASSUME NoVal \notin Val

VARIABLES mem, ctl, buf, memInt

-----------------------------------------------------------------------------
(* MemoryInterface *)

MReq == [op : {"Rd"}, adr : Adr]
          \cup [op : {"Wr"}, adr : Adr, val : Val]

-----------------------------------------------------------------------------
(* InternalMemory *)

vars == <<memInt, mem, ctl, buf>>

IInit == /\ mem \in [Adr -> Val]
         /\ ctl = [p \in Proc |-> "rdy"]
         /\ buf = [p \in Proc |-> NoVal]
         /\ memInt \in InitMemInt

TypeInvariant ==
  /\ mem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

Req(p) == /\ ctl[p] = "rdy"
          /\ \E req \in MReq :
                /\ Send(p, req, memInt, memInt')
                /\ buf' = [buf EXCEPT ![p] = req]
                /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ UNCHANGED mem

Do(p) == /\ ctl[p] = "busy"
         /\ mem' = IF buf[p].op = "Wr"
                     THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
                     ELSE mem
         /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                        THEN NoVal
                                        ELSE mem[buf[p].adr]]
         /\ ctl' = [ctl EXCEPT ![p] = "done"]
         /\ UNCHANGED memInt

Rsp(p) == /\ ctl[p] = "done"
          /\ Reply(p, buf[p], memInt, memInt')
          /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
          /\ UNCHANGED <<mem, buf>>

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

ISpec == IInit /\ [][INext]_vars

-----------------------------------------------------------------------------
(* LiveInternalMemory *)

LISpec == ISpec /\ \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

LivenessProperty == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

Liveness == \A p \in Proc : []<>(ctl[p] = "rdy")

-----------------------------------------------------------------------------
(* Model-checking substitutions *)

MCSend(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

=============================================================================