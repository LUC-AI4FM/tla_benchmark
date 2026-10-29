------------------------- MODULE MCInternalMemory -------------------------
(***************************************************************************)
(* TLC model-checking companion for the InternalMemory specification.      *)
(*                                                                         *)
(* In InternalMemory, Send, Reply and InitMemInt are constant operators.   *)
(* TLC cannot evaluate unspecified constant operators, so this module      *)
(* gives them concrete definitions:                                        *)
(*                                                                         *)
(*   - Send and Reply both set the next memory-interface value to the      *)
(*     tuple <<p, d>>.                                                     *)
(*   - InitMemInt is a singleton set containing <<p, NoVal>> for some      *)
(*     arbitrarily chosen processor p.                                     *)
(*                                                                         *)
(* The InternalMemory specification is restated here with these concrete   *)
(* operators, so the module stands alone and SANY can parse it. This       *)
(* module contains no temporal properties or proofs; TypeInvariant is the  *)
(* only invariant, and it comes from InternalMemory.                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,    \* set of processors
          Adr,     \* set of memory addresses
          Val      \* set of memory values

VARIABLES memInt, mem, ctl, buf

vars == <<memInt, mem, ctl, buf>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Concrete replacements for the constant operators of InternalMemory.     *)
(***************************************************************************)
NoVal == CHOOSE v : v \notin Val

Send(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>

Reply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

InitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

---------------------------------------------------------------------------
(***************************************************************************)
(* Memory interface definitions (from MemoryInterface).                    *)
(***************************************************************************)
MReq == [op : {"Rd"}, adr : Adr]
          \cup [op : {"Wr"}, adr : Adr, val : Val]

---------------------------------------------------------------------------
(***************************************************************************)
(* InternalMemory specification, using the concrete operators above.       *)
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

---------------------------------------------------------------------------
(***************************************************************************)
(* Names used by the TLC configuration.                                    *)
(***************************************************************************)
Init == IInit

Next == INext

Spec == Init /\ [][Next]_vars

\* Safety invariant to check with TLC
Inv == TypeInvariant

=============================================================================