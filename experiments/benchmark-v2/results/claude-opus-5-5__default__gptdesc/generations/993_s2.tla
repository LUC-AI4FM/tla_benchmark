---------------------------- MODULE APA_ACP_SB ----------------------------
(***************************************************************************)
(* Apalache type annotations for the specification ACP_SB.                 *)
(*                                                                         *)
(* This module keeps the original specification ACP_SB free of any         *)
(* tool-specific annotations. It declares typed copies of the constants    *)
(* and variables of ACP_SB and then instantiates that module, so the       *)
(* model checker gets concrete typing information without changes to the  *)
(* original text.                                                          *)
(*                                                                         *)
(* Participants are modelled by the uninterpreted type PARTICIPANT. The    *)
(* tag constants (yes, no, undecided, commit, abort, waiting, notsent)     *)
(* are typed as strings.                                                   *)
(*                                                                         *)
(* This file does not define the protocol behavior. Init, Next and Spec    *)
(* are taken unchanged from ACP_SB through the instance below.             *)
(***************************************************************************)

EXTENDS Naturals, FiniteSets

CONSTANTS
    \* @type: Set(PARTICIPANT);
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
    \* Participant state: one record per participant.
    \* @type: PARTICIPANT -> [vote: Str, alive: Bool, decision: Str, faulty: Bool, voteSent: Bool];
    participant,
    \* Coordinator state.
    \* @type: [request: PARTICIPANT -> Bool, vote: Str, alive: Bool, decision: Str, broadcast: PARTICIPANT -> Bool];
    coordinator

\* @type: <<PARTICIPANT -> [vote: Str, alive: Bool, decision: Str, faulty: Bool, voteSent: Bool], [request: PARTICIPANT -> Bool, vote: Str, alive: Bool, decision: Str, broadcast: PARTICIPANT -> Bool]>>;
vars == <<participant, coordinator>>

(***************************************************************************)
(* Instantiate the untyped specification. Constants and variables are      *)
(* substituted by the identically named typed declarations above.          *)
(***************************************************************************)
ACP == INSTANCE ACP_SB

(***************************************************************************)
(* Concrete value for the set of participants, used from a model           *)
(* configuration (e.g. "participants <- ConstParticipants"). Values are    *)
(* written in Apalache's "<name>_OF_<TYPE>" form for uninterpreted types.  *)
(***************************************************************************)
\* @type: Set(PARTICIPANT);
ConstParticipants == { "1_OF_PARTICIPANT", "2_OF_PARTICIPANT", "3_OF_PARTICIPANT" }

(***************************************************************************)
(* Behavior is delegated entirely to ACP_SB.                               *)
(***************************************************************************)
Init == ACP!Init

Next == ACP!Next

Spec == Init /\ [][Next]_vars

=============================================================================