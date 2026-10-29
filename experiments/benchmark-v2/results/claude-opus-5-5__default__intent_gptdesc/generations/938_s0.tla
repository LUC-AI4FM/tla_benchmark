---------------------------- MODULE BufferedSharedMemory ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of storable values
          NoVal      \* response value returned for a write

ASSUME NoVal \notin Val
ASSUME Proc # {} /\ Adr # {} /\ Val # {}

VARIABLES mem,      \* internal memory: Adr -> Val
          ctl,      \* processor control state: "rdy", "busy", "done"
          req,      \* per-processor outstanding request
          resp,     \* per-processor response buffer
          memQ,     \* internal FIFO buffer of pending operations (processor ids)
          written   \* ghost: for each address, every value it has ever held

vars == <<mem, ctl, req, resp, memQ, written>>

-------------------------------------------------------------------------------------
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

NoReq == [op |-> "None"]

Distinct(s) == \A i, j \in 1..Len(s) : i # j => s[i] # s[j]

InQueue(p) == \E i \in 1..Len(memQ) : memQ[i] = p

-------------------------------------------------------------------------------------
TypeOK ==
    /\ mem \in [Adr -> Val]
    /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
    /\ req \in [Proc -> MReq \cup {NoReq}]
    /\ resp \in [Proc -> Val \cup {NoVal}]
    /\ memQ \in Seq(Proc)
    /\ written \in [Adr -> SUBSET Val]

Init ==
    /\ mem \in [Adr -> Val]
    /\ ctl = [p \in Proc |-> "rdy"]
    /\ req = [p \in Proc |-> NoReq]
    /\ resp = [p \in Proc |-> NoVal]
    /\ memQ = << >>
    /\ written = [a \in Adr |-> {mem[a]}]

-------------------------------------------------------------------------------------
(* Request step: a ready processor issues a read or write and becomes busy.  *)
(* The request is placed into the internal buffer.                           *)
Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E r \in MReq :
          /\ req' = [req EXCEPT ![p] = r]
          /\ ctl' = [ctl EXCEPT ![p] = "busy"]
          /\ memQ' = Append(memQ, p)
    /\ UNCHANGED <<mem, resp, written>>

(* Internal step: the memory atomically performs the oldest buffered       *)
(* operation, updating the memory state and producing a response.          *)
Do ==
    /\ memQ # << >>
    /\ LET p == Head(memQ)
           r == req[p]
       IN  /\ ctl[p] = "busy"
           /\ IF r.op = "Rd"
                 THEN /\ resp' = [resp EXCEPT ![p] = mem[r.adr]]
                      /\ UNCHANGED <<mem, written>>
                 ELSE /\ mem' = [mem EXCEPT ![r.adr] = r.val]
                      /\ written' = [written EXCEPT ![r.adr] = @ \cup {r.val}]
                      /\ resp' = [resp EXCEPT ![p] = NoVal]
           /\ ctl' = [ctl EXCEPT ![p] = "done"]
           /\ memQ' = Tail(memQ)
           /\ UNCHANGED req

(* Response step: the processor receives its response and becomes ready.   *)
Rsp(p) ==
    /\ ctl[p] = "done"
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ req' = [req EXCEPT ![p] = NoReq]
    /\ UNCHANGED <<mem, resp, memQ, written>>

Next ==
    \/ \E p \in Proc : Req(p) \/ Rsp(p)
    \/ Do

Fairness ==
    /\ WF_vars(Do)
    /\ \A p \in Proc : WF_vars(Rsp(p))
    /\ \A p \in Proc : WF_vars(Req(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-------------------------------------------------------------------------------------
(* Safety invariants *)

\* Responses reflect a valid effect of an earlier request: no phantom reads/writes.
NoPhantom ==
    \A p \in Proc :
        /\ ctl[p] = "rdy" => req[p] = NoReq
        /\ ctl[p] \in {"busy", "done"} => req[p] \in MReq
        /\ (ctl[p] = "done" /\ req[p].op = "Rd") => resp[p] \in written[req[p].adr]
        /\ (ctl[p] = "done" /\ req[p].op = "Wr") =>
               /\ resp[p] = NoVal
               /\ req[p].val \in written[req[p].adr]

\* Memory consistency: every stored value was either initial or actually written.
MemConsistent ==
    /\ mem \in [Adr -> Val]
    /\ \A a \in Adr : mem[a] \in written[a]

\* Internal buffer consistency: exactly the busy processors have a pending
\* operation, each at most once (no duplicated/conflicting operations).
BufferConsistent ==
    /\ Distinct(memQ)
    /\ \A p \in Proc : (ctl[p] = "busy") <=> InQueue(p)

Safety == TypeOK /\ NoPhantom /\ MemConsistent /\ BufferConsistent

-------------------------------------------------------------------------------------
(* Liveness properties *)

\* Every issued request is eventually answered.
EventualResponse == \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

\* No processor is starved: each one issues and completes requests infinitely often.
NoStarvation ==
    \A p \in Proc : /\ []<>(ctl[p] = "busy")
                    /\ []<>(ctl[p] = "rdy")

Liveness == EventualResponse /\ NoStarvation

-------------------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Liveness
=====================================================================================