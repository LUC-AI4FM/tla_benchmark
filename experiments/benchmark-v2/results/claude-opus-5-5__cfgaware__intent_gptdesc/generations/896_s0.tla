---------------------------- MODULE InternalMemory ----------------------------
(***************************************************************************)
(* Abstract model of a shared-memory controller that serializes and        *)
(* services load/store requests from a fixed set of clients.               *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS Proc,   \* the set of clients
          Adr,    \* the set of memory addresses
          Val     \* the set of storable values

VARIABLES mem,    \* mem[a] : current value stored at address a
          ctl,    \* ctl[p] : status of client p ("rdy", "busy", "done")
          buf     \* buf[p] : per-client slot (request, response, or NoVal)

vars == <<mem, ctl, buf>>

(***************************************************************************)
(* Request / response formats.                                             *)
(***************************************************************************)
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoVal == CHOOSE v : v \notin Val

Status == {"rdy", "busy", "done"}

(***************************************************************************)
(* Initial condition.                                                      *)
(***************************************************************************)
IInit == /\ mem \in [Adr -> Val]
         /\ ctl = [p \in Proc |-> "rdy"]
         /\ buf = [p \in Proc |-> NoVal]

(***************************************************************************)
(* Accept a request from a ready client.  Memory is unchanged.             *)
(***************************************************************************)
Req(p) == /\ ctl[p] = "rdy"
          /\ \E req \in MReq :
                /\ buf' = [buf EXCEPT ![p] = req]
                /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ UNCHANGED mem

(***************************************************************************)
(* Perform the pending request of a busy client atomically.                *)
(***************************************************************************)
Do(p) == /\ ctl[p] = "busy"
         /\ buf[p] \in MReq
         /\ mem' = IF buf[p].op = "Wr"
                      THEN [mem EXCEPT ![buf[p].adr] = buf[p].val]
                      ELSE mem
         /\ buf' = [buf EXCEPT ![p] = IF buf[p].op = "Wr"
                                         THEN NoVal
                                         ELSE mem[buf[p].adr]]
         /\ ctl' = [ctl EXCEPT ![p] = "done"]

(***************************************************************************)
(* Return the response to the client; client consumes it and is ready.     *)
(***************************************************************************)
Rsp(p) == /\ ctl[p] = "done"
          /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
          /\ buf' = [buf EXCEPT ![p] = NoVal]
          /\ UNCHANGED mem

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

ISpec == IInit /\ [][INext]_vars

(***************************************************************************)
(* Invariants.                                                             *)
(***************************************************************************)
TypeInvariant ==
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> Status]
    /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]

\* Each client has at most one outstanding request, held only while busy.
SingleOutstanding ==
    \A p \in Proc :
        /\ (ctl[p] = "busy") <=> (buf[p] \in MReq)
        /\ ctl[p] = "rdy"  => buf[p] = NoVal
        /\ ctl[p] = "done" => buf[p] \in Val \cup {NoVal}

\* Memory is always a total mapping to legal values.
MemConsistent == \A a \in Adr : mem[a] \in Val

Inv == TypeInvariant /\ SingleOutstanding /\ MemConsistent

THEOREM ISpec => [](TypeInvariant /\ SingleOutstanding /\ MemConsistent)
=============================================================================