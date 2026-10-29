------------------------- MODULE MCInternalMemory --------------------------
(***************************************************************************)
(* TLC model-checking companion for the InternalMemory specification.      *)
(*                                                                         *)
(* The constant operators Send, Reply and InitMemInt of the memory         *)
(* interface cannot be evaluated by TLC directly. This module defines      *)
(* concrete replacements for them:                                         *)
(*                                                                         *)
(*   MCSend(p, d, old, new)  : the next internal-memory interface value    *)
(*                             is the tuple <<p, d>>.                      *)
(*   MCReply(p, d, old, new) : the next internal-memory interface value    *)
(*                             is the tuple <<p, d>>.                      *)
(*   MCInitMemInt            : the singleton set {<<p, NoVal>>}, where p   *)
(*                             is an arbitrarily chosen processor.         *)
(*                                                                         *)
(* In the TLC configuration you substitute:                                *)
(*   Send <- MCSend, Reply <- MCReply, InitMemInt <- MCInitMemInt          *)
(*                                                                         *)
(* The InternalMemory and MemoryInterface definitions are given here so    *)
(* the module is self-contained. This module states no temporal            *)
(* properties or proofs of its own.                                        *)
(***************************************************************************)

CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val

VARIABLES memInt, mem, ctl, buf

vars == <<memInt, mem, ctl, buf>>

---------------------------------------------------------------------------
(*************************** MemoryInterface ******************************)

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

---------------------------------------------------------------------------
(*************************** InternalMemory *******************************)

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

---------------------------------------------------------------------------
(******************** TLC replacement operators ***************************)

MCSend(p, d, oldMemInt, newMemInt)  ==  newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) ==  newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

---------------------------------------------------------------------------
(****************** Top-level definitions for TLC ************************)

Init == IInit

Next == INext

Spec == ISpec

=============================================================================