---- MODULE SimpleStateMachine ----
EXTENDS Integers, TLC, FiniteSets

CONSTANTS NODESET, COLORS

ASSUME
    /\ IsFiniteSet(NODESET)
    /\ Cardinality(COLORS) = 2

VARIABLES
    \* @type: [NODESET -> BOOLEAN];
    active,
    \* @type: [NODESET -> COLORS];
    color,
    \* @type: NODESET;
    token_pos,
    \* @type: COLORS;
    token_color

vars == <<active, color, token_pos, token_color>>

TypeOK ==
    /\ active \in [NODESET -> BOOLEAN]
    /\ color \in [NODESET -> COLORS]
    /\ token_pos \in NODESET
    /\ token_color \in COLORS

Init ==
    TypeOK

Next ==
    TypeOK'

Spec == Init /\ [][Next]_vars

Invariant == TypeOK

=============================================================================