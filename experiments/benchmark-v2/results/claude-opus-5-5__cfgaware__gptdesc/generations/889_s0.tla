------------------------------ MODULE MC_Channel ------------------------------
(***************************************************************************)
(* A thin wrapper around the Channel specification that adds              *)
(* Apalache-specific type annotations, leaving Channel itself unchanged.  *)
(* All behavior (Init, Next, Spec, TypeInvariant, ...) is inherited from  *)
(* Channel through INSTANCE.                                              *)
(***************************************************************************)

CONSTANT
    \* @type: Set(Int);
    Data

VARIABLE
    \* @type: [val: Int, rdy: Int, ack: Int];
    chan

\* A concrete set of data values, usable to instantiate the constant Data.
\* @type: Set(Int);
DataVal == {0, 1, 2}

INSTANCE Channel

===============================================================================