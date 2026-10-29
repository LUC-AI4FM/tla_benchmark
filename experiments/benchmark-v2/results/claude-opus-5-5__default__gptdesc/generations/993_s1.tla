------------------------------ MODULE APAACP_SB ------------------------------
(***************************************************************************)
(* Apalache type annotations for the specification ACP_SB.                 *)
(*                                                                         *)
(* This module keeps ACP_SB free of tool-specific annotations. It declares *)
(* the constants and variables of ACP_SB with Apalache type annotations    *)
(* and then instantiates ACP_SB. All protocol behavior, actions, and       *)
(* temporal properties are defined in ACP_SB itself.                       *)
(*                                                                         *)
(* Typing conventions:                                                     *)
(*   - participants are strings                                            *)
(*   - tag constants (yes, no, undecided, commit, abort, waiting,          *)
(*     notsent) are strings                                                *)
(*   - participant maps each participant to a record holding its local     *)
(*     state                                                               *)
(*   - coordinator is a record holding the coordinator state               *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    \* @type: Set(Str);
    participants,
    \* @type: Str;
    yes,
    \* @type: Str;
    no,
    \* @type: Str;
    undecided,
    \* @type: Str;
    commit,
    \* @type: Str;
    abort,
    \* @type: Str;
    waiting,
    \* @type: Str;
    notsent

VARIABLES
    \* @type: Str -> [vote: Str, alive: Bool, decision: Str, faulty: Bool, voteSent: Bool, forward: Str -> Str];
    participant,
    \* @type: [request: Str -> Bool, vote: Str -> Str, alive: Bool, decision: Str, broadcast: Str -> Bool, faulty: Bool];
    coordinator

(***************************************************************************)
(* Concrete set of participants, used by the model configuration           *)
(* (e.g. "participants <- ConstParticipants" or via CInit in Apalache).    *)
(***************************************************************************)
ConstParticipants == { "p1", "p2", "p3" }

\* Constant initialization predicate for Apalache (ConstInit).
CInit ==
    /\ participants = ConstParticipants
    /\ yes = "yes"
    /\ no = "no"
    /\ undecided = "undecided"
    /\ commit = "commit"
    /\ abort = "abort"
    /\ waiting = "waiting"
    /\ notsent = "notsent"

(***************************************************************************)
(* Instantiate the original, annotation-free specification.                *)
(* All definitions of ACP_SB (Init, Next, Spec, invariants, properties)    *)
(* become available in this module.                                        *)
(***************************************************************************)
INSTANCE ACP_SB

=============================================================================