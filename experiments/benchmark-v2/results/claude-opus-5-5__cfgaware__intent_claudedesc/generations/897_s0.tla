--------------------------- MODULE MCInternalMemory ---------------------------
(***************************************************************************)
(* Internal memory specification, together with concrete instantiations   *)
(* of the memory-interface primitives for model checking with TLC.         *)
(***************************************************************************)

CONSTANTS Send(_, _, _, _),   \* Send(p, d, miOld, miNew): processor p sends d
          Reply(_, _, _, _),  \* Reply(p, d, miOld, miNew): memory replies d to p
          InitMemInt,         \* set of possible initial values of memInt
          Proc,               \* set of processor identifiers
          Adr,                \* set of memory addresses
          Val                 \* set of memory values

VARIABLE memInt

(***************************************************************************)
(* Memory interface definitions                                            *)
(***************************************************************************)
MReq == [op : {"Rd"}, adr : Adr]
          \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

-----------------------------------------------------------------------------
(***************************************************************************)
(* Internal memory                                                          *)
(***************************************************************************)
VARIABLES mem, ctl, buf

ivars == <<memInt, mem, ctl, buf>>

TypeInvariant ==
  /\ mem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

IInit ==
  /\ mem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
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
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<mem, buf>>

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

ISpec == IInit /\ [][INext]_ivars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking instantiations of the interface primitives.  They keep   *)
(* only the last processor and datum in memInt to limit the state space.   *)
(***************************************************************************)
MCSend(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCInitMemInt == {<<CHOOSE p \in Proc : TRUE, NoVal>>}

THEOREM ISpec => []TypeInvariant
=============================================================================