--------------------------- MODULE MCInternalMemory ---------------------------
(***************************************************************************)
(* TLC model-checking companion module for the InternalMemory              *)
(* specification.  It gives concrete definitions for the constant          *)
(* operators Send, Reply, and InitMemInt of the MemoryInterface, so that   *)
(* TLC can evaluate the internal-memory interface.                         *)
(*                                                                         *)
(* Design choice: both a send and a reply are modeled by setting the next  *)
(* value of the memory interface to the tuple <<p, d>>.  The set of        *)
(* initial memory-interface values is the singleton containing             *)
(* <<p, NoVal>> for an arbitrarily chosen processor p.                     *)
(*                                                                         *)
(* So that this module parses standalone, the MemoryInterface and          *)
(* InternalMemory definitions are reproduced here.  The MC operators are   *)
(* used in place of the constant operators Send, Reply, and InitMemInt.    *)
(* This module contains no temporal properties or proofs.                  *)
(***************************************************************************)

CONSTANTS Proc,   \* The set of processors
          Adr,    \* The set of memory addresses
          Val     \* The set of memory values

VARIABLE memInt

(***************************************************************************)
(* Definitions from MemoryInterface.                                       *)
(***************************************************************************)
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

(***************************************************************************)
(* Concrete replacements for the constant operators.                       *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

Send(p, d, oldMemInt, newMemInt)  == MCSend(p, d, oldMemInt, newMemInt)
Reply(p, d, oldMemInt, newMemInt) == MCReply(p, d, oldMemInt, newMemInt)
InitMemInt                        == MCInitMemInt

(***************************************************************************)
(* Definitions from InternalMemory.                                        *)
(***************************************************************************)
VARIABLES mem, ctl, buf

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

(***************************************************************************)
(* Standard names for the model checker.                                   *)
(***************************************************************************)
Init == IInit
Next == INext
Spec == ISpec

=============================================================================