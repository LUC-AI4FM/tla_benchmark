---------------------------- MODULE MutualExclusionRefinement ----------------------------
EXTENDS Naturals, TLC

CONSTANTS Procs
ASSUME Procs = {0, 1}

Other(p) == 1 - p

(* ====================