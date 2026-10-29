---------------------------- MODULE MC_ACP_SB ----------------------------
(***************************************************************************)
(* Apalache type annotations for ACP_SB.                                   *)
(*                                                                         *)
(* This module keeps the original specification ACP_SB free of            *)
(* tool-specific annotations. It declares typed constants and variables    *)
(* and then instantiates ACP_SB. The protocol behavior (Init, Next, Spec)  *)
(* and its properties are defined in ACP_SB and are made available here    *)
(* through the instantiation.                                              *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    \* the set of participants
    \* @type: Set(Str);
    participants,
    \* tag: a participant votes yes
    \* @type: Str;
    yes,
    \* tag: a participant votes no
    \* @type: Str;
    no,
    \* tag: no decision has been made yet
    \* @type: Str;
    undecided,
    \* tag: the decision is to commit
    \* @type: Str;
    commit,
    \* tag: the decision is to abort
    \* @type: Str;
    abort,
    \* tag: the coordinator is waiting for a vote
    \* @type: Str;
    waiting,
    \* tag: the coordinator has not sent its decision yet
    \* @type: Str;
    notsent

VARIABLES
    \* the state of each participant
    \* @type: Str -> [vote: Str, alive: Bool, decision: Str, faulty: Bool, voteSent: Bool];
    participant,
    \* the state of the coordinator
    \* @type: [request: Str -> Bool, vote: Str -> Str, alive: Bool, decision: Str, broadcast: Str -> Str];
    coordinator

(***************************************************************************)
(* Concrete values used by the model configuration.                        *)
(***************************************************************************)

\* A concrete set of participants, to be substituted for `participants`
\* in the configuration (participants <- ParticipantsValue).
ParticipantsValue == { "p1", "p2", "p3" }

\* Constant initialization for Apalache (alternative to the .cfg file).
ConstInit ==
    /\ participants = ParticipantsValue
    /\ yes = "yes"
    /\ no = "no"
    /\ undecided = "undecided"
    /\ commit = "commit"
    /\ abort = "abort"
    /\ waiting = "waiting"
    /\ notsent = "notsent"

(***************************************************************************)
(* Instantiate the original specification. All of its definitions,         *)
(* including Init, Next, Spec, invariants, and temporal properties,        *)
(* become available in this module.                                        *)
(***************************************************************************)
INSTANCE ACP_SB

=============================================================================