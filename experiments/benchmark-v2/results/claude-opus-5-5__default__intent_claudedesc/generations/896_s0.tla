--------------------------- MODULE InternalMemory ---------------------------
(***************************************************************************)
(* Internal (implementation) view of a shared memory accessed by a set of  *)
(* processors.  The memory interface (normally the MemoryInterface module) *)
(* is inlined here so that the module is self-contained.                   *)
(***************************************************************************)

(***************************************************************************)
(* ---------------------- Memory Interface ------------------------------- *)
(***************************************************************************)
VARIABLE memInt

CONSTANTS Send(_, _, _, _),   \* Send(p, d, memInt, memInt') : processor p
                              \* sends request d through the interface.
          Reply(_, _, _, _),  \* Reply(p, d, memInt, memInt') : the memory
                              \* sends response d to processor p.
          InitMemInt,         \* The set of possible initial values of memInt.
          Proc,               \* The set of processor identifiers.
          Adr,                \* The set of memory addresses.
          Val                 \* The set of memory values.

ASSUME \A p, d, miOld, miNew :
          /\ Send(p, d, miOld, miNew)  \in BOOLEAN
          /\ Reply(p, d, miOld, miNew) \in BOOLEAN

MReq == [op : {"Rd"}, adr : Adr]
          \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

(***************************************************************************)
(* ---------------------- Internal Memory -------------------------------- *)
(***************************************************************************)
VARIABLES mem,   \* mem[a] : the value stored at address a
          ctl,   \* ctl[p] : lifecycle phase of processor p
          buf    \* buf[p] : request being processed, or response to send

vars == <<memInt, mem, ctl, buf>>

IInit ==
  /\ mem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

ITypeInvariant ==
  /\ mem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ \A p \in Proc :
        /\ (ctl[p] = "rdy")  => (buf[p] = NoVal)
        /\ (ctl[p] = "busy") => (buf[p] \in MReq)
        /\ (ctl[p] = "done") => (buf[p] \in Val \cup {NoVal})

(* Processor p issues a request req through the interface. *)
Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ buf' = [buf EXCEPT ![p] = req]
        /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED mem

(* The memory performs processor p's pending request. *)
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

(* The memory returns the response to processor p. *)
Rsp(p) ==
  /\ ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ buf' = [buf EXCEPT ![p] = NoVal]
  /\ UNCHANGED mem

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

ISpec == IInit /\ [][INext]_vars

(* Generic names requested for the specification *)
Init == IInit
Next == INext
Spec == ISpec

TypeInvariant == ITypeInvariant

THEOREM Spec => []TypeInvariant
=============================================================================