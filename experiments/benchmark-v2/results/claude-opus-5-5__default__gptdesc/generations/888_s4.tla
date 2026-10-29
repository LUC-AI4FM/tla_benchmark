-------------------------- MODULE APAsynchInterface --------------------------
(***************************************************************************)
(* Apalache typing interface for the AsynchInterface specification.        *)
(*                                                                         *)
(* This module only adds Apalache type annotations to the constant and the *)
(* variables of AsynchInterface, then instantiates that module. The        *)
(* original specification therefore stays free of tool-specific            *)
(* annotations.                                                            *)
(*                                                                         *)
(* Everything else comes from AsynchInterface through the unnamed          *)
(* INSTANCE below:                                                         *)
(*   - Init, Next and Spec                                                 *)
(*   - TypeInvariant                                                       *)
(* Redefining any of those names here would cause a multiple-definition    *)
(* error in SANY, so this module does not do so.                           *)
(*                                                                         *)
(* External model configuration can use CInit (Apalache --cinit=CInit)     *)
(* or ConstData (TLC: Data <- ConstData) to fix a concrete, enumerated     *)
(* value for Data.                                                         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    \* @typeAlias: DATA = Int;
    \* @type: Set(DATA);
    Data

VARIABLES
    \* @type: DATA;
    val,
    \* @type: Int;
    rdy,
    \* @type: Int;
    ack

(***************************************************************************)
(* Concrete enumerated value for the Data constant, for use by external    *)
(* model configuration.                                                    *)
(***************************************************************************)
ConstData == {0, 1, 2}

\* Constant initializer for Apalache
CInit == Data = ConstData

(***************************************************************************)
(* Instantiate the untyped specification. The constant Data and the        *)
(* variables val, rdy, ack are substituted implicitly by name.             *)
(***************************************************************************)
INSTANCE AsynchInterface

=============================================================================