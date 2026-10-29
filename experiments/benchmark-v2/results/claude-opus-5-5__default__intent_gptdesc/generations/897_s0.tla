-------------------------- MODULE MemoryMessageBuffer --------------------------
(***************************************************************************)
(* Abstract message-passing substrate for a simple cache-coherent memory   *)
(* protocol.  The internal buffer has two channels:                        *)
(*   "req" : holds the single most recent memory command (Send)            *)
(*   "rep" : holds the single most recent reply (Reply)                    *)
(* Each message is a pair <<p, d>>.  Here p is the originating processor   *)
(* and d is either a data value or the special value NoVal.                *)
(*                                                                         *)
(* A processor issues a message into a one-slot per-channel issue latch.   *)
(* The substrate then atomically commits it into the buffer, replacing     *)
(* the channel's previous contents.  The model has no timing and no loss.  *)
(* Every buffer update is a single atomic step.                            *)
(* The model is finite for finite Proc and Val, so TLC can check it        *)
(* exhaustively.                                                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,   \* finite set of processor identifiers
          Val     \* finite set of data values

ASSUME /\ Proc # {}
       /\ IsFiniteSet(Proc)
       /\ IsFiniteSet(Val)

NoVal    == CHOOSE v : v \notin Val          \* special "no data" payload
InitProc == CHOOSE p \in Proc : TRUE         \* chosen default processor id

Channels   == {"req", "rep"}
Data       == Val \cup {NoVal}
Msg        == Proc \X Data                   \* well-formed messages
DefaultMsg == <<InitProc, NoVal>>

VARIABLES
    buf,    \* buf[ch]  : the single message currently held on channel ch
    pend,   \* pend[ch] : message issued on ch that is not yet committed
    full    \* full[ch] : TRUE iff an issued message on ch is outstanding

vars == <<buf, pend, full>>

-----------------------------------------------------------------------------
TypeOK ==
    /\ buf  \in [Channels -> Msg]
    /\ pend \in [Channels -> Msg]
    /\ full \in [Channels -> BOOLEAN]

Init ==
    /\ buf  = [ch \in Channels |-> DefaultMsg]
    /\ pend = [ch \in Channels |-> DefaultMsg]
    /\ full = [ch \in Channels |-> FALSE]

-----------------------------------------------------------------------------
(* A processor issues a message on channel ch.  A channel can hold at most *)
(* one outstanding message.                                                *)
Issue(ch, p, d) ==
    /\ ~full[ch]
    /\ pend' = [pend EXCEPT ![ch] = <<p, d>>]
    /\ full' = [full EXCEPT ![ch] = TRUE]
    /\ UNCHANGED buf

Send(p, d)  == Issue("req", p, d)
Reply(p, d) == Issue("rep", p, d)

(* Atomic delivery: the outstanding message replaces the channel contents. *)
Commit(ch) ==
    /\ full[ch]
    /\ buf'  = [buf  EXCEPT ![ch] = pend[ch]]
    /\ full' = [full EXCEPT ![ch] = FALSE]
    /\ UNCHANGED pend

Next ==
    \/ \E p \in Proc, d \in Data : Send(p, d) \/ Reply(p, d)
    \/ \E ch \in Channels : Commit(ch)

Fairness == \A ch \in Channels : WF_vars(Commit(ch))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************** Safety ************************************)

(* Buffer contents are always well-formed (processor id, data-or-NoVal).  *)
WellFormed ==
    \A ch \in Channels :
        /\ buf[ch] \in Msg
        /\ buf[ch][1] \in Proc
        /\ buf[ch][2] \in Data

(* Single-message containment: each channel holds exactly one message,    *)
(* and at most one message is outstanding per channel.                    *)
SingleMessage ==
    \A ch \in Channels :
        /\ buf[ch] \in Msg
        /\ Cardinality({buf[ch]}) = 1
        /\ Cardinality(IF full[ch] THEN {pend[ch]} ELSE {}) <= 1

(* No illegal concurrent interleaving: a step updates at most one channel. *)
AtomicUpdate ==
    [][\A c1, c2 \in Channels :
          c1 # c2 => (buf'[c1] = buf[c1] \/ buf'[c2] = buf[c2])]_vars

(* Determinism: a buffer change on a channel is exactly the issued pair.  *)
(* An issue also records exactly the requested (p, d) pair.               *)
Deterministic ==
    [][ /\ \A ch \in Channels :
             buf'[ch] # buf[ch] =>
                 /\ full[ch]
                 /\ ~full'[ch]
                 /\ buf'[ch] = pend[ch]
        /\ \A ch \in Channels :
             (full[ch] /\ ~full'[ch]) => buf'[ch] = pend[ch]
        /\ \A ch \in Channels :
             (~full[ch] /\ full'[ch]) =>
                 /\ pend'[ch] \in Msg
                 /\ buf'[ch] = buf[ch]
      ]_vars

(* Outstanding messages cannot be overwritten before they are committed.  *)
NoOverwrite ==
    [][\A ch \in Channels : full[ch] => (full'[ch] = FALSE \/ pend'[ch] = pend[ch])]_vars

Invariants == TypeOK /\ WellFormed /\ SingleMessage

(**************************** Liveness ***********************************)

(* No silent loss: every issued Send/Reply is eventually in the buffer.   *)
EventualDelivery ==
    \A ch \in Channels, m \in Msg :
        (full[ch] /\ pend[ch] = m) ~> (buf[ch] = m)

SendDelivered  == \A m \in Msg : (full["req"] /\ pend["req"] = m) ~> (buf["req"] = m)
ReplyDelivered == \A m \in Msg : (full["rep"] /\ pend["rep"] = m) ~> (buf["rep"] = m)

-----------------------------------------------------------------------------
THEOREM Spec => []Invariants
THEOREM Spec => AtomicUpdate /\ Deterministic /\ NoOverwrite
THEOREM Spec => EventualDelivery /\ SendDelivered /\ ReplyDelivered
=============================================================================