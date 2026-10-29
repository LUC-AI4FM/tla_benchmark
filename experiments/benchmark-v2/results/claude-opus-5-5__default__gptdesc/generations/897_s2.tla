--------------------------- MODULE MCInternalMemory ---------------------------
(***************************************************************************)
(* TLC model-checking companion for the InternalMemory specification.      *)
(* Send, Reply and InitMemInt are constant operators in the underlying     *)
(* MemoryInterface/InternalMemory specification, so TLC cannot evaluate    *)
(* them directly. This module gives concrete replacement operators:        *)
(*                                                                         *)
(*   - Both a send and a reply set the next internal-memory interface      *)
(*     value to the tuple <<p, d>>.                                        *)
(*   - The initial memory-interface values form a singleton set holding    *)
(*     <<p, NoVal>> for an arbitrarily chosen processor p.                 *)
(*                                                                         *)
(* The InternalMemory spec is inlined here, with the MC operators in place *)
(* of the constant operators, so the module is self-contained.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Proc,   \* The set of processor identifiers
          Adr,    \* The set of memory addresses
          Val     \* The set of memory values

VARIABLES memInt, \* The memory interface
          mem,    \* The memory contents
          ctl,    \* Per-processor control state
          buf     \* Per-processor buffer

vars == <<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------
(* Definitions from MemoryInterface *)

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

-----------------------------------------------------------------------------
(* Concrete replacements for the constant operators *)

MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

-----------------------------------------------------------------------------
(* InternalMemory specification, using the MC operators *)

TypeInvariant ==
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

Init ==
    /\ mem \in [Adr -> Val]
    /\ ctl = [p \in Proc |-> "rdy"]
    /\ buf = [p \in Proc |-> NoVal]
    /\ memInt \in MCInitMemInt

Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq :
          /\ MCSend(p, req, memInt, memInt')
          /\ buf' = [buf EXCEPT ![p] = req]
          /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

Do(p) ==
    /\ ctl[p] = "busy"
    /\ mem' = IF buf[p].op = "Wr"
                THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
                ELSE mem
    /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                   THEN NoVal
                                   ELSE mem[buf[p].adr]]
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED memInt

Rsp(p) ==
    /\ ctl[p] = "done"
    /\ MCReply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED <<mem, buf>>

Next == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

Spec == Init /\ [][Next]_vars

=============================================================================