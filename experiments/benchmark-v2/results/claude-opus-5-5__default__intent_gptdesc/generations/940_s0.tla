------------------------- MODULE CacheCoherentInternalMemory -------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Proc,      \* set of processor identifiers
          Adr,       \* set of memory addresses
          Val,       \* set of data values
          NoVal      \* distinguished "no value" element

ASSUME /\ Proc # {}
       /\ Adr  # {}
       /\ NoVal \notin Val

-----------------------------------------------------------------------------
(* Well-formed messages                                                     *)
-----------------------------------------------------------------------------
MReq ==   [op : {"Rd"}, adr : Adr]
        \cup [op : {"Wr"}, adr : Adr, val : Val]

MRsp == Val \cup {NoVal}

Payload == MReq \cup MRsp

\* Abstract contents of the internal memory: the identifier of the
\* processor of the most recent interaction, paired with its payload.
MemIntVal == Proc \X Payload

\* Single, well-defined default entry: "no value" associated with some processor.
InitMemInt == << CHOOSE p \in Proc : TRUE, NoVal >>

-----------------------------------------------------------------------------
VARIABLES mem,     \* abstract shared memory contents
          ctl,     \* per-processor control state
          buf,     \* per-processor pending request / reply buffer
          memInt   \* internal memory component state

vars == << mem, ctl, buf, memInt >>

-----------------------------------------------------------------------------
(* Atomic update semantics for handling messages.                           *)
(* Each operator replaces the previous stored value (miOld) by the new      *)
(* value (miNew) consisting of the sender identifier and the payload.       *)
-----------------------------------------------------------------------------
Send(p, d, miOld, miNew)  == miNew = << p, d >>
Reply(p, d, miOld, miNew) == miNew = << p, d >>

-----------------------------------------------------------------------------
TypeOK ==
    /\ mem    \in [Adr -> Val]
    /\ ctl    \in [Proc -> {"rdy", "busy", "done"}]
    /\ buf    \in [Proc -> Payload]
    /\ memInt \in MemIntVal

Init ==
    /\ mem    \in [Adr -> Val]
    /\ ctl    = [p \in Proc |-> "rdy"]
    /\ buf    = [p \in Proc |-> NoVal]
    /\ memInt = InitMemInt

-----------------------------------------------------------------------------
(* Processor p issues a well-formed request; the "send" message is          *)
(* delivered to the internal memory, atomically replacing its contents.     *)
-----------------------------------------------------------------------------
Req(p) ==
    /\ ctl[p] = "rdy"
    /\ \E req \in MReq :
          /\ Send(p, req, memInt, memInt')
          /\ buf' = [buf EXCEPT ![p] = req]
          /\ ctl' = [ctl EXCEPT ![p] = "busy"]
    /\ UNCHANGED mem

(* Asynchronous processing of a pending request by the memory/coherence    *)
(* manager; the internal memory component is not modified.                 *)
Do(p) ==
    /\ ctl[p] = "busy"
    /\ LET req == buf[p] IN
         IF req.op = "Rd"
           THEN /\ buf' = [buf EXCEPT ![p] = mem[req.adr]]
                /\ UNCHANGED mem
           ELSE /\ mem' = [mem EXCEPT ![req.adr] = req.val]
                /\ buf' = [buf EXCEPT ![p] = NoVal]
    /\ ctl' = [ctl EXCEPT ![p] = "done"]
    /\ UNCHANGED memInt

(* The "reply" message is delivered asynchronously back to processor p,    *)
(* atomically replacing the internal memory contents.                      *)
Rsp(p) ==
    /\ ctl[p] = "done"
    /\ Reply(p, buf[p], memInt, memInt')
    /\ ctl' = [ctl EXCEPT ![p] = "rdy"]
    /\ UNCHANGED << mem, buf >>

Next == \E p \in Proc : Req(p) \/ Do(p) \/ Rsp(p)

Fairness == \A p \in Proc : WF_vars(Do(p)) /\ WF_vars(Rsp(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties                                                        *)
-----------------------------------------------------------------------------
\* Internal memory always holds a well-formed (sender, payload) entry.
MemIntWellFormed == memInt \in MemIntVal

\* A send step sets memInt deterministically to <<sender, request>>.
SendDeterministic ==
    [][ \A p \in Proc :
          (ctl[p] = "rdy" /\ ctl'[p] = "busy")
             => memInt' = << p, buf'[p] >> ]_vars

\* A reply step sets memInt deterministically to <<receiver, reply>>.
ReplyDeterministic ==
    [][ \A p \in Proc :
          (ctl[p] = "done" /\ ctl'[p] = "rdy")
             => memInt' = << p, buf[p] >> ]_vars

\* No implicit modification: memInt changes only via a send or reply step,
\* and then only to the payload of that step, attributed to its processor.
NoImplicitUpdate ==
    [][ memInt' # memInt =>
          \E p \in Proc :
             \/ /\ ctl[p] = "rdy" /\ ctl'[p] = "busy"
                /\ memInt' = << p, buf'[p] >>
             \/ /\ ctl[p] = "done" /\ ctl'[p] = "rdy"
                /\ memInt' = << p, buf[p] >> ]_vars

\* Updates are attributed to the correct sender.
Attribution ==
    [][ \A p \in Proc :
          (Req(p) \/ Rsp(p)) => memInt'[1] = p ]_vars

-----------------------------------------------------------------------------
(* Liveness properties                                                      *)
-----------------------------------------------------------------------------
\* Every issued request is eventually processed and answered, updating the
\* internal memory with a reply attributed to the requesting processor.
RequestEventuallyServed ==
    \A p \in Proc : (ctl[p] = "busy") ~> (ctl[p] = "rdy" /\ memInt[1] = p)

\* A processor that repeatedly issues requests is never permanently starved.
NoStarvation ==
    \A p \in Proc : []<>(ctl[p] = "busy") => []<>(ctl[p] = "rdy")

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []MemIntWellFormed
THEOREM Spec => SendDeterministic /\ ReplyDeterministic
THEOREM Spec => NoImplicitUpdate /\ Attribution
THEOREM Spec => RequestEventuallyServed /\ NoStarvation
=============================================================================