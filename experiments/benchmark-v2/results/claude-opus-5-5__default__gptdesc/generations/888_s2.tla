---------------------------- MODULE ApaAsynchInterface ----------------------------
(***************************************************************************)
(* Apalache typing interface for the AsynchInterface specification.        *)
(*                                                                         *)
(* This module declares typed versions of the constant and variables of    *)
(* AsynchInterface, so that the original specification can remain free of  *)
(* tool-specific type annotations. It also provides a concrete enumerated  *)
(* value for the constant Data, used by external model configuration       *)
(* (Apalache: --cinit=ConstInit; TLC: Data <- DataValue).                  *)
(*                                                                         *)
(* The underlying AsynchInterface definitions are reproduced in this       *)
(* module so that the file is self-contained and passes SANY. When the     *)
(* AsynchInterface module is on the search path, the block of definitions  *)
(* below can be replaced by a single "INSTANCE AsynchInterface" statement. *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Set(Int);
    Data

VARIABLES
    \* @type: Int;
    val,
    \* @type: Int;
    rdy,
    \* @type: Int;
    ack

vars == <<val, rdy, ack>>

(***************************************************************************)
(* Concrete enumerated value for the data constant.                        *)
(***************************************************************************)
DataValue == {0, 1, 2}

\* Constant initializer for Apalache (--cinit=ConstInit)
ConstInit == Data = DataValue

(***************************************************************************)
(* Contents of the instantiated AsynchInterface specification.            *)
(***************************************************************************)
TypeInvariant ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack \in {0, 1}

Init ==
    /\ val \in Data
    /\ rdy \in {0, 1}
    /\ ack = rdy

Send ==
    /\ rdy = ack
    /\ val' \in Data
    /\ rdy' = 1 - rdy
    /\ UNCHANGED ack

Rcv ==
    /\ rdy # ack
    /\ ack' = 1 - ack
    /\ UNCHANGED <<val, rdy>>

Next == Send \/ Rcv

Spec == Init /\ [][Next]_vars

THEOREM Spec => []TypeInvariant
====================================================================================