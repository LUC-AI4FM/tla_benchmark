------------------------ MODULE MCWriteThroughCache ------------------------
EXTENDS WriteThroughCache

(***************************************************************************)
(* Concrete replacements for the memory-interface constants of             *)
(* MemoryInterface (Send, Reply, InitMemInt), substituted through the TLC  *)
(* configuration file.                                                     *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  ==  newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) ==  newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

(***************************************************************************)
(* Hand-instantiation of the module InternalMemory, with mem <- vmem.      *)
(* This is needed because the referenced TLC version cannot handle module  *)
(* instantiation.                                                          *)
(***************************************************************************)
IInit == /\ vmem \in [Adr -> Val]
         /\ ctl = [p \in Proc |-> "rdy"]
         /\ buf = [p \in Proc |-> NoVal]
         /\ memInt \in InitMemInt

ITypeInvariant ==
  /\ vmem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

IReq(p) == /\ ctl[p] = "rdy"
           /\ \E req \in MReq :
                 /\ Send(p, req, memInt, memInt')
                 /\ buf' = [buf EXCEPT ![p] = req]
                 /\ ctl' = [ctl EXCEPT ![p] = "busy"]
           /\ UNCHANGED vmem

IDo(p) ==
  /\ ctl[p] = "busy"
  /\ vmem' = IF buf[p].op = "Wr"
               THEN [vmem EXCEPT ![buf[p].adr] = buf[p].val]
               ELSE vmem
  /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                 THEN NoVal
                                 ELSE vmem[buf[p].adr]]
  /\ ctl' = [ctl EXCEPT ![p] = "done"]
  /\ UNCHANGED memInt

IRsp(p) == /\ ctl[p] = "done"
           /\ Reply(p, buf[p], memInt, memInt')
           /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
           /\ UNCHANGED <<vmem, buf>>

INext == \E p \in Proc : IReq(p) \/ IDo(p) \/ IRsp(p)

ISpec == IInit /\ [][INext]_<<memInt, vmem, ctl, buf>>

(***************************************************************************)
(* The hand-instantiated InternalMemory specification satisfies its type   *)
(* invariant.                                                              *)
(***************************************************************************)
THEOREM ISpec => []ITypeInvariant

(***************************************************************************)
(* Liveness: every busy controller eventually becomes ready.               *)
(***************************************************************************)
IReadyLiveness == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")
=============================================================================