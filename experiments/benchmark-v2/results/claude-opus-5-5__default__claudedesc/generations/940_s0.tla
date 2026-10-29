------------------------ MODULE MCLiveInternalMemory ------------------------
(***************************************************************************)
(* Model-checking wrapper for the LiveInternalMemory specification.        *)
(* The MemoryInterface, InternalMemory and LiveInternalMemory definitions  *)
(* are inlined so the module is self-contained. The abstract Send, Reply   *)
(* and InitMemInt operators are replaced by MCSend, MCReply and            *)
(* MCInitMemInt.                                                           *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS p1, p2,        \* processors (model values)
          a1, a2, a3,    \* addresses  (model values)
          v1, v2,        \* values     (model values)
          NoVal          \* special "no value" constant

(***************************************************************************)
(* Finite domains for model checking                                       *)
(***************************************************************************)
Proc == {p1, p2}
Adr  == {a1, a2, a3}
Val  == {v1, v2}

ASSUME NoVal \notin Val

VARIABLES memInt, mem, ctl, buf

vars == <<memInt, mem, ctl, buf>>

(***************************************************************************)
(* Operator substitutions for the abstract memory interface                *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>
MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>
MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

Send(p, d, oldMemInt, newMemInt)  == MCSend(p, d, oldMemInt, newMemInt)
Reply(p, d, oldMemInt, newMemInt) == MCReply(p, d, oldMemInt, newMemInt)
InitMemInt == MCInitMemInt

(***************************************************************************)
(* MemoryInterface                                                         *)
(***************************************************************************)
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

(***************************************************************************)
(* InternalMemory                                                          *)
(***************************************************************************)
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

Init == IInit
Next == INext

(***************************************************************************)
(* LiveInternalMemory                                                      *)
(***************************************************************************)
LISpec == /\ ISpec
          /\ \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

Spec == LISpec

(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)
\* Every issued request is eventually answered.
LivenessProperty ==
    \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

\* Every processor is infinitely often ready (never starved or stuck).
Liveness ==
    \A p \in Proc : []<>(ctl[p] = "rdy")

=============================================================================