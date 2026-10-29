---------------------------- MODULE LiveInternalMemory ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processors
          Adr,       \* set of memory addresses
          Val,       \* set of memory values
          NoVal      \* a value not in Val (model value)

ASSUME NoVal \notin Val

VARIABLES mem,     \* mem[a] : current contents of address a
          ctl,     \* ctl[p] : "rdy", "busy" or "done"
          buf,     \* buf[p] : pending request or pending reply of p
          memInt   \* the processor/memory communication interface

vars == <<memInt, mem, ctl, buf>>

-----------------------------------------------------------------------------------
(* Requests that processors may send *)
MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

(* Concrete instantiation of the communication interface for model checking *)
InitMemInt == {<<p, NoVal>> : p \in Proc}

Send(p, d, miOld, miNew)  == miNew = <<p, d>>
Reply(p, d, miOld, miNew) == miNew = <<p, d>>

-----------------------------------------------------------------------------------
TypeInvariant ==
  /\ mem \in [Adr -> Val]
  /\ ctl \in [Proc -> {"rdy", "busy", "done"}]
  /\ buf \in [Proc -> MReq \cup Val \cup {NoVal}]
  /\ memInt \in Proc \X (MReq \cup Val \cup {NoVal})

Init ==
  /\ memInt \in InitMemInt
  /\ mem \in [Adr -> Val]
  /\ ctl = [p \in Proc |-> "rdy"]
  /\ buf = [p \in Proc |-> NoVal]

(* Processor p issues a request *)
Req(p) ==
  /\ ctl[p] = "rdy"
  /\ \E req \in MReq :
       /\ Send(p, req, memInt, memInt')
       /\ buf' = [buf EXCEPT ![p] = req]
       /\ ctl' = [ctl EXCEPT ![p] = "busy"]
  /\ UNCHANGED mem

(* Memory performs the request of processor p *)
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

(* Memory replies to processor p *)
Rsp(p) ==
  /\ ctl[p] = "done"
  /\ Reply(p, buf[p], memInt, memInt')
  /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
  /\ UNCHANGED <<mem, buf>>

INext == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

Next == INext

(* Fairness: memory must eventually perform and answer every pending request *)
Liveness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

Spec == Init /\ [][Next]_vars /\ Liveness

-----------------------------------------------------------------------------------
(* Safety properties *)

(* A busy processor's buffer holds a well-formed request; a done processor's
   buffer holds a proper reply value. *)
BufConsistent ==
  \A p \in Proc :
     /\ (ctl[p] = "busy") => buf[p] \in MReq
     /\ (ctl[p] = "done") => buf[p] \in Val \cup {NoVal}

(* While a request is pending in memory, the interface carries that request *)
InterfaceConsistent ==
  \A p \in Proc :
     (ctl[p] = "busy" /\ memInt[1] = p) => memInt[2] = buf[p]

(* A read that has been performed returns a legitimate memory value *)
ReadReturnsValue ==
  \A p \in Proc :
     (ctl[p] = "done" /\ buf[p] # NoVal) => buf[p] \in Val

Safety == TypeInvariant /\ BufConsistent /\ InterfaceConsistent /\ ReadReturnsValue

(* Writes update memory properly: after a write is performed, mem holds its value *)
WriteCorrect ==
  [][\A p \in Proc :
        (ctl[p] = "busy" /\ ctl'[p] = "done" /\ buf[p].op = "Wr")
           => mem'[buf[p].adr] = buf[p].val]_vars

(* Reads return the current memory contents at the time they are performed *)
ReadCorrect ==
  [][\A p \in Proc :
        (ctl[p] = "busy" /\ ctl'[p] = "done" /\ buf[p].op = "Rd")
           => buf'[p] = mem[buf[p].adr]]_vars

-----------------------------------------------------------------------------------
(* Liveness properties *)

(* Every request that is sent eventually receives a reply *)
EveryRequestAnswered ==
  \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy")

(* The system never stalls with a pending operation *)
NoStall ==
  \A p \in Proc : (ctl[p] # "rdy") ~> (ctl[p] = "rdy")

(* No processor is starved forever *)
NoStarvation ==
  \A p \in Proc : []<>(ctl[p] = "rdy")

LivenessProperty == EveryRequestAnswered /\ NoStall /\ NoStarvation

-----------------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => WriteCorrect /\ ReadCorrect
THEOREM Spec => LivenessProperty
===================================================================================