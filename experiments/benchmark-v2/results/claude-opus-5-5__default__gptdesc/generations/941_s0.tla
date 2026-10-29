------------------------ MODULE MCLiveWriteThroughCache ------------------------
(***************************************************************************)
(* TLC model-checking wrapper for the write-through cache specification   *)
(* of module LiveWriteThroughCache.                                        *)
(*                                                                         *)
(* We want to check that the cache implements the liveness specification  *)
(* of the internal memory (module LiveInternalMemory) under the            *)
(* refinement mapping                                                      *)
(*                                                                         *)
(*      mem <- omem,   ctl <- octl,   buf <- obuf                          *)
(*                                                                         *)
(* This would normally be written with an INSTANCE statement:             *)
(*                                                                         *)
(*    LM == INSTANCE LiveInternalMemory                                    *)
(*             WITH mem <- omem, ctl <- octl, buf <- obuf                  *)
(*                                                                         *)
(* The version of TLC targeted here cannot handle that INSTANCE, so the   *)
(* instantiated definitions are written out by hand below.                 *)
(***************************************************************************)
EXTENDS LiveWriteThroughCache

-----------------------------------------------------------------------------
(***************************************************************************)
(* Constants used to build a model for TLC.                                *)
(***************************************************************************)
CONSTANTS p1, p2, a1, a2, v1, v2

MCProc == {p1, p2}
MCAdr  == {a1, a2}
MCVal  == {v1, v2}

-----------------------------------------------------------------------------
(***************************************************************************)
(* The refinement mapping.                                                 *)
(***************************************************************************)
omem == vmem
octl == [p \in Proc |-> IF ctl[p] = "waiting" THEN "busy" ELSE ctl[p]]
obuf == buf

ovars == <<memInt, omem, octl, obuf>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Instantiated InternalMemory definitions.                                *)
(***************************************************************************)
OInit ==
  /\ omem \in [Adr -> Val]
  /\ octl = [p \in Proc |-> "rdy"]
  /\ obuf = [p \in Proc |-> NoVal]
  /\ memInt \in InitMemInt

OTypeInvariant ==
  /\ omem \in [Adr -> Val]
  /\ octl \in [Proc -> {"rdy", "busy", "done"}]
  /\ obuf \in [Proc -> MReq \cup Val \cup {NoVal}]

OReq(p) ==
  /\ octl[p] = "rdy"
  /\ \E req \in MReq :
        /\ Send(p, req, memInt, memInt')
        /\ obuf' = [obuf EXCEPT ![p] = req]
        /\ octl' = [octl EXCEPT ![p] = "busy"]
  /\ omem' = omem

ODo(p) ==
  /\ octl[p] = "busy"
  /\ omem' = IF obuf[p].op = "Wr"
               THEN [omem EXCEPT ![obuf[p].adr] = obuf[p].val]
               ELSE omem
  /\ obuf' = [obuf EXCEPT ![p] = IF obuf[p].op = "Wr"
                                   THEN NoVal
                                   ELSE omem[obuf[p].adr]]
  /\ octl' = [octl EXCEPT ![p] = "done"]
  /\ memInt' = memInt

ORsp(p) ==
  /\ octl[p] = "done"
  /\ Reply(p, obuf[p], memInt, memInt')
  /\ octl' = [octl EXCEPT ![p] = "rdy"]
  /\ omem' = omem
  /\ obuf' = obuf

ONext == \E p \in Proc : OReq(p) \/ ODo(p) \/ ORsp(p)

OSpec == OInit /\ [][ONext]_ovars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Enabledness predicates, written explicitly instead of using ENABLED    *)
(* on the instantiated actions.                                            *)
(***************************************************************************)
ODoEnabled(p)  == octl[p] = "busy"
ORspEnabled(p) == octl[p] = "done"

(***************************************************************************)
(* Liveness: weak fairness of Do(p) and Rsp(p) for every processor,       *)
(* expressed directly in terms of the enabledness predicates.             *)
(*   WF_v(A)  ==  []<>~ENABLED <<A>>_v  \/  []<><<A>>_v                   *)
(***************************************************************************)
OLiveness ==
  \A p \in Proc :
     /\ ([]<>(~ODoEnabled(p))  \/ []<><<ODo(p)>>_ovars)
     /\ ([]<>(~ORspEnabled(p)) \/ []<><<ORsp(p)>>_ovars)

OLISpec == OSpec /\ OLiveness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model-checking entry points.                                            *)
(***************************************************************************)
MCInit == Init
MCNext == Next
MCSpec == LISpec

MCTypeInvariant == OTypeInvariant

THEOREM MCSpec => [](OTypeInvariant) /\ OLISpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* PostCondition: a value with the shape of a TLC counterexample, i.e. a  *)
(* record of the states and actions of an error trace.                    *)
(***************************************************************************)
PostCondition ==
  [ state  |-> {},
    action |-> {} ]
=============================================================================