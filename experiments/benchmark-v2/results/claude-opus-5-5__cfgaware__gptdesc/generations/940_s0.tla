---------------------- MODULE MCLiveInternalMemory ----------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Send(_, _, _, _),
          Reply(_, _, _, _),
          InitMemInt,
          Proc,
          Adr,
          Val,
          NoVal

VARIABLES mem, ctl, buf, memInt

vars == <<memInt, mem, ctl, buf>>

MReq == [op : {"Rd"}, adr : Adr] \cup [op : {"Wr"}, adr : Adr, val : Val]

-----------------------------------------------------------------------------
(* Internal memory specification *)

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

-----------------------------------------------------------------------------
(* Live internal memory specification *)

Liveness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

LISpec == ISpec /\ Liveness

-----------------------------------------------------------------------------
(* TLC replacements for constant operators *)

MCSend(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCReply(p, d, oldMemInt, newMemInt) == newMemInt = <<p, d>>

MCInitMemInt == {<<p, NoVal>> : p \in Proc}

LivenessProperty == \A p \in Proc : []<>(ctl[p] = "busy")

-----------------------------------------------------------------------------
(* Description of a counterexample trace: a processor that stops issuing   *)
(* requests, so it is never busy again although the spec is satisfied.    *)

PostCondition ==
  [ property |-> "LivenessProperty",
    loopsBackTo |-> 1,
    trace |->
      << [ action |-> "Initial predicate",
           state  |-> [ ctl |-> "all rdy", buf |-> "all NoVal",
                        memInt |-> "InitMemInt", mem |-> "arbitrary" ] ],
         [ action |-> "Req",
           state  |-> [ ctl |-> "busy", buf |-> "request",
                        memInt |-> "Send", mem |-> "unchanged" ] ],
         [ action |-> "Do",
           state  |-> [ ctl |-> "done", buf |-> "result",
                        memInt |-> "unchanged", mem |-> "possibly updated" ] ],
         [ action |-> "Rsp",
           state  |-> [ ctl |-> "rdy", buf |-> "result",
                        memInt |-> "Reply", mem |-> "unchanged" ] ],
         [ action |-> "Stuttering",
           state  |-> [ ctl |-> "rdy", buf |-> "result",
                        memInt |-> "unchanged", mem |-> "unchanged" ] ] >> ]

=============================================================================