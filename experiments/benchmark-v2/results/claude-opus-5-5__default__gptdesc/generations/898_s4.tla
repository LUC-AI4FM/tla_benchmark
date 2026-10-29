------------------------ MODULE MCWriteThroughCache -------------------------
(***************************************************************************)
(* TLC model-checking wrapper for the write-through cache specification.  *)
(* It extends the cache module, which already defines the refinement     *)
(* mapping vmem.                                                          *)
(*                                                                         *)
(* The constants Send, Reply and InitMemInt of MemoryInterface are         *)
(* replaced by MCSend, MCReply and MCInitMemInt in the TLC configuration   *)
(* file.                                                                   *)
(***************************************************************************)
EXTENDS WriteThroughCache

-----------------------------------------------------------------------------
(***************************************************************************)
(* Concrete replacements for the memory-interface constants.               *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  ==  newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) ==  newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------
(***************************************************************************)
(* The following definitions inline the InternalMemory specification,     *)
(* instantiated with mem <- vmem. They are written out by hand because     *)
(* the TLC version in use cannot handle module instantiation. LM_Inner_X   *)
(* corresponds to LM!Inner!X.                                              *)
(***************************************************************************)
LM_Inner_IInit ==
  /\ vmem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

LM_Inner_TypeInvariant ==
  /\ vmem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

LM_Inner_Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED vmem

LM_Inner_Do(p) ==
  /\ ctl[p] = "busy"
  /\ vmem' = IF buf[p].op = "Wr"
               THEN [vmem EXCEPT ![buf[p].adr] = buf[p].val]
               ELSE vmem
  /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                 THEN NoVal
                                 ELSE vmem[buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED memInt

LM_Inner_Rsp(p) ==
  /\ ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<vmem, buf>>

LM_Inner_INext ==
  \E p \in Proc : LM_Inner_Req(p) \/ LM_Inner_Do(p) \/ LM_Inner_Rsp(p)

LM_Inner_ISpec ==
  LM_Inner_IInit /\ [][LM_Inner_INext]_<<memInt, vmem, ctl, buf>>

-----------------------------------------------------------------------------
THEOREM LM_Inner_ISpec => []LM_Inner_TypeInvariant

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: every busy controller eventually becomes ready.               *)
(***************************************************************************)
LM_Inner_Liveness ==
  \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

=============================================================================