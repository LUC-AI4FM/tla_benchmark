MODULE SimpleStateMachine
EXTENDS Naturals, TLC

CONSTANTS NODES, COLORS

VARIABLES active, colors, tokenPos, tokenColor

(* Type constraints *)
TypeInv == 
  active \in [NODES -> BOOLEAN] /\ 
  colors \in [NODES -> COLORS] /\
  tokenPos \in NODES /\ 
  tokenColor \in COLORS

Init ==
  \E act \in [NODES -> BOOLEAN],
        col \in [NODES -> COLORS],
        pos \in NODES,
        c \in COLORS :
    (act[pos] /\ col[pos] = c) /\
    active = act /\ colors = col /\ tokenPos = pos /\ tokenColor = c

Next ==
  \E act' \in [NODES -> BOOLEAN],
        col' \in [NODES -> COLORS],
        pos' \in NODES,
        c' \in COLORS :
    (act'[pos'] /\ col'[pos'] = c') /\
    active' = act' /\ colors' = col' /\ tokenPos' = pos' /\ tokenColor' = c'

Spec == Init /\ [] [][Next]_vars

===============================================================================