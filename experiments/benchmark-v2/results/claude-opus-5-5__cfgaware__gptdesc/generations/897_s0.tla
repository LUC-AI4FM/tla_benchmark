---------------------------- MODULE MCInternalMemory ----------------------------
(***************************************************************************)
(* TLC model-checking companion for the InternalMemory specification.     *)
(* It gives concrete replacements for the constant operators Send, Reply,  *)
(* and InitMemInt so that TLC can evaluate the memory interface.           *)
(*                                                                         *)
(* Design choice: both a send and a reply set the next value of memInt to  *)
(* the tuple <<p, d>>. The initial memory-interface values form the        *)
(* singleton set {<<p, NoVal>>}, where p is an arbitrarily chosen          *)
(* processor.                                                              *)
(***************************************************************************)

VARIABLE memInt

CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val,
          NoVal

ASSUME NoVal \notin Val

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

---------------------------------------------------------------------------
(*************************** InternalMemory ********************************)

VARIABLES mem, ctl, buf

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

ISpec == IInit /\ [][INext]_<<memInt, mem, ctl, buf>>

---------------------------------------------------------------------------
(********************* Model-checking replacements *************************)

MCSend(p, d, oldMemInt, newMemInt)  == newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

=============================================================================