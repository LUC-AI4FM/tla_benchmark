------------------------- MODULE WriteThroughCacheLive -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val,
          NoVal,
          QLen

ASSUME /\ NoVal \notin Val
       /\ QLen \in Nat
       /\ QLen > 0

VARIABLES memInt,   \* interface between processors and controller
          wmem,     \* the single coherent main memory
          ctl,      \* processor-visible control state of each processor
          buf,      \* per-processor request / result buffer
          cmsg      \* internal controller<->memory message (not visible)

vars == <<memInt, wmem, ctl, buf, cmsg>>

-----------------------------------------------------------------------------
(* Model-checking instantiations of the interface constants                *)
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoMsg == [op |-> "none"]

TypeInvariant ==
  /\ wmem \in [Adr -> Val]
  /\ ctl  \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf  \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ cmsg \in [Proc -> {NoMsg}]

-----------------------------------------------------------------------------
(* The write-through controller                                            *)

Init == /\ wmem \in [Adr -> Val]
        /\ ctl = [p \in Proc |-> "rdy"]
        /\ buf = [p \in Proc |-> NoVal]
        /\ cmsg = [p \in Proc |-> NoMsg]
        /\ memInt \in InitMemInt

\* A processor issues a request; the controller buffers it.
Req(p) == /\ ctl[p] = "rdy"
          /\ \E req \in MReq :
                /\ Send(p, req, memInt, memInt')
                /\ buf' = [buf EXCEPT ![p] = req]
                /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ UNCHANGED <<wmem, cmsg>>

\* The controller forwards the request immediately to memory (write-through):
\* a write updates memory synchronously, a read returns the current value.
Do(p) == /\ ctl[p] = "busy"
         /\ wmem' = IF buf[p].op = "Wr"
                      THEN [wmem EXCEPT ![buf[p].adr] = buf[p].val]
                      ELSE wmem
         /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                        THEN NoVal
                                        ELSE wmem[buf[p].adr]]
         /\ ctl' = [ctl EXCEPT ![p] = "done"]
         /\ UNCHANGED <<memInt, cmsg>>

\* The controller returns the result to the processor.
Rsp(p) == /\ ctl[p] = "done"
          /\ Reply(p, buf[p], memInt, memInt')
          /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
          /\ UNCHANGED <<wmem, buf, cmsg>>

Next == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

Spec == Init /\ [][Next]_vars

Fairness == \A p \in Proc : WF_vars(Do(p) \/ Rsp(p))

LSpec == Spec /\ Fairness

-----------------------------------------------------------------------------
(* Refinement mapping to the abstract (live) internal memory               *)

LM_mem == wmem
LM_ctl == ctl
LM_buf == buf

LM_vars == <<memInt, LM_mem, LM_ctl, LM_buf>>

LM_Inner_IInit ==
  /\ LM_mem \in [Adr -> Val]
  /\ LM_ctl = [p \in Proc |-> "rdy"]
  /\ LM_buf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

LM_Inner_Req(p) ==
  /\ LM_ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ LM_buf' = [LM_buf EXCEPT ![p] = req]
        /\ LM_ctl' = [LM_ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED LM_mem

LM_Inner_Do(p) ==
  /\ LM_ctl[p] = "busy"
  /\ LM_mem' = IF LM_buf[p].op = "Wr"
                 THEN [LM_mem EXCEPT ![LM_buf[p].adr] = LM_buf[p].val]
                 ELSE LM_mem
  /\ LM_buf' = [LM_buf EXCEPT ![p] = IF LM_buf[p].op = "Wr"
                                       THEN NoVal
                                       ELSE LM_mem[LM_buf[p].adr]]
  /\ LM_ctl' = [LM_ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED memInt

LM_Inner_Rsp(p) ==
  /\ LM_ctl[p] = "done"
  /\ Reply(p, LM_buf[p], memInt, memInt')
  /\ LM_ctl' = [LM_ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<LM_mem, LM_buf>>

LM_Inner_INext ==
  \E p \in Proc : LM_Inner_Req(p) \/ LM_Inner_Do(p) \/ LM_Inner_Rsp(p)

LM_Inner_ISpec == LM_Inner_IInit /\ [][LM_Inner_INext]_LM_vars

LM_Inner_Liveness ==
  \A p \in Proc : WF_LM_vars(LM_Inner_Do(p) \/ LM_Inner_Rsp(p))

LM_Inner_LISpec == LM_Inner_ISpec /\ LM_Inner_Liveness

-----------------------------------------------------------------------------
(* Additional properties                                                   *)

NoPermanentBusy ==
  \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

THEOREM LSpec => [](TypeInvariant)
THEOREM LSpec => LM_Inner_LISpec
THEOREM LSpec => NoPermanentBusy
=============================================================================